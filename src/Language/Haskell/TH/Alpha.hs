{-# LANGUAGE
      FunctionalDependencies
    , GeneralizedNewtypeDeriving
    , RankNTypes
    , FlexibleContexts
    , BangPatterns
    #-}
{-|
Module      : Language.Haskell.TH.Alpha
Description : Alpha equivalence in TH
Copyright   : (c) Julian K. Arni, 2014
License     : BSD3
Maintainer  : jkarni@gmail.com
Stability   : experimental

Compare TH expressions (or clauses, patterns, etc.) for alpha equivalence.
That is, compare for equality modulo the renaming of bound variables.

>>> areExpAEq [| \x -> x |] [| \y -> y |]
True

This can be useful when for instance testing libraries that use Template
Haskell: usually correctness is only defined up to alpha equivalence.

For most cases, 'areExpAEq' is the only function you'll need. The 'AlphaEq'
class is only exported to make it easier to expand alpha-equality
comparison to other instances, or to be used (in combination with the
package __th-desugar__) for alpha equality comparisons of non-expression
types (e.g. TyVarBndr).

/N.B.:/ This package doesn't yet handle type annotations correctly!
-}

module Language.Haskell.TH.Alpha (
    areExpAEq,
    expEqual,
    (@=),
    AlphaEq(..)
    ) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax  (Quasi)
import Language.Haskell.TH.Desugar
import Data.Function               (on)
import Control.Monad.State
import Control.Monad.Identity
import Control.Monad.Trans.Maybe
import Control.Monad.Morph
import Data.Maybe                  (isJust)
import qualified Data.Map as Map
import Control.Applicative



--  A poor man's bound variable lookup table.
type Lookup = (Map.Map Name Int, Map.Map Name Int, Int)

emptyLookup :: Lookup
emptyLookup = (Map.empty, Map.empty, 0)

data LookupTbl = LookupTbl
               { insertLR :: Name -> Name -> LookupTbl
               , eqInTbl  :: Name -> Name -> Bool
               , isInL    :: Name -> Bool
               , isInR    :: Name -> Bool
               }

mapLookup :: Lookup -> LookupTbl
mapLookup !(ls,rs,cnt) = LookupTbl
           { insertLR = \a b -> mapLookup (Map.insert a cnt ls,
                                           Map.insert b cnt rs,
                                           cnt + 1)
           , eqInTbl  = \a b -> Map.lookup a ls == Map.lookup b rs
           , isInL    = \a   -> isJust $ Map.lookup a ls
           , isInR    = \b   -> isJust $ Map.lookup b rs
           }


-- Monad holding lookup table if alpha equivalence is still possible,
-- Nothing otherwise. Parametrized also on an extra monad 'm', which is
-- needed for a single, unified interface for th and th-desugar types (the
-- former will use a Quasi monad, the latter Identity).
newtype LookupSTM m b = LookupST {
    unLookupST :: StateT LookupTbl (MaybeT m) b
    } deriving (Functor, Applicative, Monad, MonadState LookupTbl
               , MonadPlus, Alternative)

---------------------------------------------------------------------------
-- Lifting and hoisting
--
--   This section is primarily concerned with making moving from a pure
--   (Identity) context to other monads easy. We do this because desugaring
--   (and other TH-related activities) end us up in some Quasi monad, so
--   when a AlphaEq instance uses th-desugar for its arguments, but a pure
--   function for its subexpressions, it ends up crossing a signature
--   boundary that ideally shouldn't be annoying.
---------------------------------------------------------------------------
instance MonadTrans (LookupSTM) where
    -- Laws:
    --     1. lift . return == return
    --        LookupST $ StateT (\tbl -> MaybeT $ return n >>= \x -> return $ Just (x, tbl))
    --        LookupST $ StateT (\tbl -> MaybeT $ Just (n, tbl))
    --     2. lift (m >>= f) == lift m >>= (lift . f)
    lift m = LookupST $ StateT (\tbl -> MaybeT $ m >>= \x -> return $ Just (x, tbl))


-- This is ugly, but the signature and name should explain it well enough.
hoist' :: (Monad m) => (forall a . m a -> n a) -> LookupSTM m b -> LookupSTM n b
hoist' nat lkstm = LookupST $ StateT (\tbl -> MaybeT . nat . runMaybeT $ runStateT (unLookupST lkstm) tbl)

instance MFunctor LookupSTM where
    hoist = hoist'

toQ :: LookupST b -> LookupSTQ b
toQ = hoist generalize

type LookupST b  = LookupSTM Identity b
type LookupSTQ b = LookupSTM Q b


runLookupST :: Monad m => LookupSTM m a -> LookupTbl -> m (Maybe (a, LookupTbl))
runLookupST st tbl = runMaybeT $ runStateT (unLookupST st) tbl

runLookupST' :: LookupST a -> LookupTbl -> Maybe (a, LookupTbl)
runLookupST' = (runIdentity .) . runLookupST

-- | The main Alpha Equivalence class. '@=' is by default defined in terms
-- of 'lkEq'. 'lkEq' is exposed for composability: it is easy to
-- recursively build 'AlphaEq' instances from other 'AlphaEq' instances by
-- delegating the lookup update to the subinstances.
class AlphaEq a m | a -> m where
    -- | Given a variable binding lookup compares arguments for alpha
    -- equivalence, setting the state to Just of updated lookup in case of
    -- equivalence, Nothing otherwise.
    lkEq :: a -> a -> LookupSTM m ()

-- | Compares its arguments for alpha equivalence. The default
-- implementation uses Lookup for its LookupTbl, but more efficient
-- datatypes can be used.
(@=) :: (Monad m, AlphaEq a m) => a -> a -> m Bool
x @= y = liftM isJust $ runLookupST (lkEq x y) (mapLookup emptyLookup)

infix 4 @=     -- Same as (==)


---------------------------------------------------------------------------
-- Exp
---------------------------------------------------------------------------

-- | Convenience function that uses 'runQ' on 'expEqual'.
--
-- >>> areExpAEq [| let x = 5 in x |] [| let y = 5 in y |]
-- True
areExpAEq :: DsMonad m
         => ExpQ    -- ^ Quoted expression
         -> ExpQ    -- ^ Quoted expression
         -> m Bool
areExpAEq e1 e2 = let expM = (join .) . liftM2 expEqual
                 in expM (runQ e1) (runQ e2)

instance AlphaEq Exp Q where
        lkEq e1 e2 = do
            e1' <- lift $ dsExp e1
            e2' <- lift $ dsExp e2
            toQ $ expEqual' e1' e2'


{--- | Compare two expressions for alpha-equivalence. Since this uses-}
{--- th-desugar to desugar the expressions, returns a Bool in the Quasi-}
{--- context.-}
expEqual :: DsMonad m => Exp -> Exp -> m Bool
expEqual t1 t2 = do
    t1' <- dsExp t1
    t2' <- dsExp t2
    let lkt = mapLookup emptyLookup
    return $ isJust $ runLookupST' (lkEq t1' t2') lkt


instance AlphaEq DExp Identity where
    lkEq = expEqual'


expEqual' :: DExp -> DExp -> LookupST ()
expEqual' (DVarE a1    ) (DVarE a2    ) = a1 ~=~ a2
expEqual' (DConE a1    ) (DConE a2    ) = a1 ~=~ a2
expEqual' (DLitE l1    ) (DLitE l2    ) = guard $ l1 == l2
expEqual' (DAppE a1 b1 ) (DAppE a2 b2 ) = lkEq a1 a2 >> lkEq b1 b2
expEqual' (DLamE a1 b1 ) (DLamE a2 b2 ) = do
    guard $ ((==) `on` length) a1 a2
    zipWithM_ insertLRLST a1 a2
    lkEq b1 b2
    return ()
expEqual' (DCaseE a1 b1) (DCaseE a2 b2) = do
    guard $ length b1 == length b2
    lkEq a1 a2
    zipWithM_ lkEq b1 b2
    return ()
expEqual' (DLetE a1 b1 ) (DLetE a2 b2 ) = zipWithM_ lkEq a1 a2 >> lkEq b1 b2
expEqual' (DSigE a1 b1 ) (DSigE a2 b2 ) = lkEq a1 a2 >> lkEq b1 b2
expEqual' _               _             = mzero

{-----------------------------------------------------------------------------}
{--- Match-}
{-----------------------------------------------------------------------------}
instance AlphaEq DMatch Identity where
        lkEq = matchEqual

matchEqual :: DMatch -> DMatch -> LookupST ()
matchEqual (DMatch pat1 exp1) (DMatch pat2 exp2) = lkEq pat1 pat2
                                                 >> lkEq exp1 exp2

{-----------------------------------------------------------------------------}
{--- LetDec-}
{-----------------------------------------------------------------------------}

instance AlphaEq DLetDec Identity where
    lkEq = letDecEqual

letDecEqual :: DLetDec -> DLetDec -> LookupST ()
letDecEqual (DFunD n1 cls1    ) (DFunD n2 cls2    ) = do
    guard $ n1 == n2
    zipWithM_ lkEq cls1 cls2
letDecEqual (DValD pat1 exp1  ) (DValD pat2 exp2  ) =
    lkEq exp1 exp2 >> lkEq pat1 pat2
letDecEqual (DSigD _name1 typ1) (DSigD _name2 typ2) =
    -- Hard to tell how the name will be bound, so just check types
    lkEq typ1 typ2
letDecEqual (DInfixD fx1 name1) (DInfixD fx2 name2) = guard $ fx1 == fx2
                                                    && name1 == name2
letDecEqual _                   _                   = mzero

{-----------------------------------------------------------------------------}
{--- Type-}
{-----------------------------------------------------------------------------}

instance AlphaEq DType Identity where
    lkEq = typeEqual

{--- TODO:-}
typeEqual :: DType -> DType -> LookupST ()
-- Type-level and value-level variable names don't conflict, so we can keep
-- both in the same mapping
typeEqual (DForallT tybs1 ctx1 typ1) (DForallT tybs2 ctx2 typ2) = do
    zipWithM_ insertLRLSTty tybs1 tybs2
    zipWithM_ lkEq ctx1 ctx2
    lkEq typ1 typ2
typeEqual (DAppT ty1 arg1          ) (DAppT ty2 arg2          ) =
    lkEq ty1 ty2 >> lkEq arg1 arg2
typeEqual (DSigT ty1 knd1          ) (DSigT ty2 knd2          ) = do
    guard $ show knd1 == show knd2
    lkEq ty1 ty2
typeEqual (DConT n1                ) (DConT n2                ) =
    guard $ show n1 == show n2
typeEqual (DVarT n1                ) (DVarT n2                ) =
    n1 ~=~ n2
typeEqual _                          _                          = mzero

---------------------------------------------------------------------------
-- Kind
---------------------------------------------------------------------------
instance AlphaEq DKind Identity where
    lkEq = kindEqual

kindEqual :: DKind -> DKind -> LookupST ()
kindEqual (DForallK ns1 typ1  ) (DForallK ns2 typ2  ) = do
    zipWithM_ insertLRLST ns1 ns2
    lkEq typ1 typ2
kindEqual (DVarK n1           ) (DVarK n2           ) = n1 ~=~ n2
{-kindEqual (DConK n1 knds1     ) (DConK n2 knds2     ) = n1 ~=~ n2-}
kindEqual (DArrowK knda1 kndb1) (DArrowK knda2 kndb2) = lkEq knda1 knda2
                                                      >> lkEq kndb1 kndb2
kindEqual DStarK                DStarK                = return ()
kindEqual _                     _                     = mzero

---------------------------------------------------------------------------
-- Clause
---------------------------------------------------------------------------
instance AlphaEq DClause Identity where
        lkEq = clauseEqual

clauseEqual :: DClause -> DClause -> LookupST ()
clauseEqual (DClause pats1 exp1) (DClause pats2 exp2) =
    zipWithM_ lkEq pats1 pats2 >> lkEq exp1 exp2
---------------------------------------------------------------------------
-- Clause
---------------------------------------------------------------------------
instance AlphaEq DPred Identity where
    lkEq = predEqual

predEqual :: DPred -> DPred -> LookupST ()
predEqual (DAppPr pred1 typ1 ) (DAppPr pred2 typ2 ) = lkEq pred1 pred2
                                                    >> lkEq typ1 typ2
predEqual (DSigPr pred1 kind1) (DSigPr pred2 kind2) = lkEq pred1 pred2
                                                    >> lkEq kind1 kind2
predEqual (DVarPr n1         ) (DVarPr n2         ) = n1 ~=~ n2
predEqual (DConPr n1         ) (DConPr n2         ) = n1 ~=~ n2
predEqual _                    _                    = mzero

---------------------------------------------------------------------------
-- Pat
---------------------------------------------------------------------------

instance AlphaEq DPat Identity where
    lkEq = patEqual

patEqual :: DPat -> DPat -> LookupST ()
patEqual (DLitPa lit1  ) (DLitPa lit2  ) = guard $ lit1 == lit2
patEqual (DVarPa n1    ) (DVarPa n2    ) = insertLRLST  n1 n2
patEqual (DConPa n1 p1 ) (DConPa n2 p2 ) = do
     n1 ~=~ n2
     guard $ length p1 == length p2
     zipWithM_ lkEq p1 p2  -- Does this allow bindings across
                           -- patterns?
patEqual (DTildePa pat1) (DTildePa pat2) = lkEq pat1 pat2
patEqual (DBangPa pat1 ) (DBangPa pat2 ) = lkEq pat1 pat2
patEqual DWildPa         DWildPa         = return ()
patEqual _               _               = mzero


---------------------------------------------------------------------------
-- Utils
---------------------------------------------------------------------------

(~=~) :: Name -> Name -> LookupST ()
a ~=~ b = do
    tbl <- get
    guard $ eqInTbl tbl a b
    bol <- isInL' a
    unless bol $ guard $ show a == show b


isInL' :: Name -> LookupST Bool
isInL' n = do
    tbl <- get
    return $ isInL tbl n


insertLRLST :: Name -> Name -> LookupST ()
insertLRLST a b = modify $ \tbl -> insertLR tbl a b

insertLRLSTty :: DTyVarBndr -> DTyVarBndr -> LookupST ()
insertLRLSTty (DPlainTV n1    ) (DPlainTV n2    ) = insertLRLST n1 n2
insertLRLSTty (DKindedTV n1 k1) (DKindedTV n2 k2) = do
    guard $ show k1 == show k2   -- Duck-show-template-kinding:
                                 -- If it shows like a duck, it is
                                 -- a duck
    insertLRLST n1 n2
insertLRLSTty _                 _                 = mzero

