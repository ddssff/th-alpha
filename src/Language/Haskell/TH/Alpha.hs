{-# LANGUAGE NoMonomorphismRestriction, TypeFamilies, FlexibleInstances
    , MultiParamTypeClasses, FunctionalDependencies, GADTs
    , StandaloneDeriving, GeneralizedNewtypeDeriving
    , FlexibleContexts
    , OverlappingInstances
    , ScopedTypeVariables
    , TemplateHaskell #-}
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
    {-areExpAEq,-}
    {-exp_equal,-}
    {-AlphaEq(..)-}
    ) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax  (Quasi, Q)
import Language.Haskell.TH.Desugar
import Data.Function               (on)
import Control.Monad.State
import Control.Monad.Identity
import Control.Monad.Trans.Maybe
import Control.Monad.Morph
import Data.Maybe                  (isJust)
import Control.Applicative



--  A poor man's bound variable lookup table.
type Lookup = ([(Name,Int)], [(Name,Int)], Int)

data LookupTbl = LookupTbl
               { insertLR :: Name -> Name -> LookupTbl
               , eqInTbl  :: Name -> Name -> Bool
               , isInL    :: Name -> Bool
               , isInR    :: Name -> Bool
               }

listLookup :: Lookup -> LookupTbl
listLookup (ls,rs,cnt) = LookupTbl
           { insertLR = \a b -> listLookup ((a,cnt):ls, (b,cnt):rs, cnt + 1)
           , eqInTbl  = \a b -> lookup a ls == lookup b rs
           , isInL    = \a   -> isJust $ lookup a ls
           , isInR    = \b   -> isJust $ lookup b rs
           }

-- Monad holding lookup table if alpha equivalence is still possible,
-- nothing otherwise. Parametrized also on an extra monad 'm', which is
-- needed for a single, unified interface for th and th-desugar types (the
-- former will use a Quasi monad, the latter Identity).
newtype LookupSTM m b = LookupST {
    unLookupST :: StateT LookupTbl (MaybeT m) b
    } deriving (Functor, Applicative, Monad, MonadState LookupTbl
               , MonadPlus, MFunctor, Alternative)

type LookupST b  = LookupSTM Identity b
type LookupSTQ b = LookupSTM Q b

toQ :: LookupST b -> LookupSTQ b
toQ = hoist generalize

runLookupST :: LookupST a -> LookupTbl -> Maybe (a, LookupTbl)
runLookupST st tbl = runIdentity $ runMaybeT $ runStateT (unLookupST $ st) tbl

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
(@=) :: AlphaEq a Identity => a -> a -> Bool
x @= y = isJust $ runLookupST (lkEq x y) (listLookup ([], [], 0))

type family Ds th where
    Ds Exp       = DExp
    Ds Type      = DType
    Ds Cxt       = DCxt
    Ds TyVarBndr = DTyVarBndr
    Ds [Dec]     = [DDec]
    Ds Con       = DCon

{-instance (Desugar th (Ds th), AlphaEq (Ds th) Identity) => AlphaEq th Q where-}
    {-lkEq a b = lkEq (desugar a) (desugar b)-}

---------------------------------------------------------------------------
-- Exp
---------------------------------------------------------------------------

-- | Convenience function that uses 'runQ' on 'exp_equal'.
--
-- >>> areExpAEq [| let x = 5 in x |] [| let y = 5 in y |]
-- True
{-areExpAEq :: Quasi m-}
         {-=> ExpQ    -- ^ Quoted expression-}
         {--> ExpQ    -- ^ Quoted expression-}
         {--> m Bool-}
{-areExpAEq e1 e2 = let expM = (join .) . liftM2 exp_equal-}
                 {-in expM (runQ e1) (runQ e2)-}

{-[>instance AlphaEq Exp where<]-}
        {-[>lkEq = eeq<]-}
          {-[>where eeq e1 e2 = do<]-}
                            {-[>e1' <- dsExp e1<]-}
                            {-[>e2' <- dsExp e2<]-}
                            {-[>exp_equal' e1' e2'<]-}


{--- | Compare two expressions for alpha-equivalence. Since this uses-}
{--- th-desugar to desugar the expressions, returns a Bool in the Quasi-}
{--- context.-}
{-exp_equal :: Quasi m => Exp -> Exp -> m Bool-}
{-exp_equal t1 t2 = do-}
    {-t1' <- dsExp t1-}
    {-t2' <- dsExp t2-}
    {-let lkt = listLookup ([], [], 0)-}
    {-return $ isJust $ runLookupST (lkEq t1' t2') lkt-}


{-instance AlphaEq DExp where-}
    {-lkEq = exp_equal'-}


{-exp_equal' :: DExp -> DExp -> LookupST ()-}
{-exp_equal' (DVarE a1    ) (DVarE a2    ) = a1 ~=~ a2-}
{-exp_equal' (DConE a1    ) (DConE a2    ) = a1 ~=~ a2-}
{-exp_equal' (DLitE l1    ) (DLitE l2    ) = guard $ l1 == l2-}
{-exp_equal' (DAppE a1 b1 ) (DAppE a2 b2 ) = lkEq a1 a2 >> lkEq b1 b2-}
{-exp_equal' (DLamE a1 b1 ) (DLamE a2 b2 ) = do-}
    {-guard $ ((==) `on` length) a1 a2-}
    {-zipWithM_ insertLRLST a1 a2-}
    {-lkEq b1 b2-}
    {-return ()-}
{-exp_equal' (DCaseE a1 b1) (DCaseE a2 b2) = do-}
    {-guard $ length b1 == length b2-}
    {-lkEq a1 a2-}
    {-zipWithM_ lkEq b1 b2-}
    {-return ()-}
{-exp_equal' (DLetE a1 b1 ) (DLetE a2 b2 ) = zipWithM_ lkEq a1 a2 >> lkEq b1 b2-}
{-exp_equal' (DSigE a1 b1 ) (DSigE a2 b2 ) = lkEq a1 a2 >> lkEq b1 b2-}
{-exp_equal' _               _             = mzero-}

{-----------------------------------------------------------------------------}
{--- Match-}
{-----------------------------------------------------------------------------}
{-instance AlphaEq DMatch where-}
        {-lkEq = match_equal-}

{-match_equal :: DMatch -> DMatch -> LookupST ()-}
{-match_equal (DMatch pat1 exp1) (DMatch pat2 exp2) = lkEq pat1 pat2-}
                                                 {->> lkEq exp1 exp2-}

{-----------------------------------------------------------------------------}
{--- LetDec-}
{-----------------------------------------------------------------------------}

{-instance AlphaEq DLetDec where-}
    {-lkEq = letDec_equal-}

{-letDec_equal :: DLetDec -> DLetDec -> LookupST ()-}
{-letDec_equal (DFunD n1 cls1    ) (DFunD n2 cls2    ) = do-}
    {-guard $ n1 == n2-}
    {-zipWithM_ lkEq cls1 cls2-}
{-letDec_equal (DValD pat1 exp1  ) (DValD pat2 exp2  ) =-}
    {-lkEq exp1 exp2 >> lkEq pat1 pat2-}
{-letDec_equal (DSigD _name1 typ1) (DSigD _name2 typ2) =-}
    {--- Hard to tell how the name will be bound, so just check types-}
    {-lkEq typ1 typ2-}
{-letDec_equal (DInfixD fx1 name1) (DInfixD fx2 name2) = guard $ fx1 == fx2-}
                                                    {-&& name1 == name2-}
{-letDec_equal _                   _                   = mzero-}

{-----------------------------------------------------------------------------}
{--- Type-}
{-----------------------------------------------------------------------------}

{-instance AlphaEq DType where-}
    {-lkEq = type_equal-}

{-[>-- TODO:<]-}
{-type_equal :: DType -> DType -> LookupST ()-}
{--- Type-level and value-level variable names don't conflict, so we can keep-}
{--- both in the same mapping-}
{-type_equal (DForallT tybs1 ctx1 typ1) (DForallT tybs2 ctx2 typ2) = do-}
    {-zipWithM_ insertLRLSTty tybs1 tybs2-}
    {-zipWithM_ lkEq ctx1 ctx2-}
    {-lkEq typ1 typ2-}
{-type_equal (DAppT ty1 arg1          ) (DAppT ty2 arg2          ) =-}
    {-lkEq ty1 ty2 >> lkEq arg1 arg2-}
{-type_equal (DSigT ty1 knd1          ) (DSigT ty2 knd2          ) = do-}
    {-guard $ show knd1 == show knd2-}
    {-lkEq ty1 ty2-}
{-type_equal (DConT n1                ) (DConT n2                ) =-}
    {-guard $ show n1 == show n2-}
{-type_equal (DVarT n1                ) (DVarT n2                ) =-}
    {-n1 ~=~ n2-}
{-type_equal _                          _                          = mzero-}

{-----------------------------------------------------------------------------}
{--- Kind-}
{-----------------------------------------------------------------------------}
{-instance AlphaEq DKind where-}
    {-lkEq = kind_equal-}

{-kind_equal :: DKind -> DKind -> LookupST ()-}
{-kind_equal (DForallK ns1 typ1  ) (DForallK ns2 typ2  ) = do-}
    {-zipWithM_ insertLRLST ns1 ns2-}
    {-lkEq typ1 typ2-}
{-kind_equal (DVarK n1           ) (DVarK n2           ) = n1 ~=~ n2-}
{-[>kind_equal (DConK n1 knds1     ) (DConK n2 knds2     ) = n1 ~=~ n2<]-}
{-kind_equal (DArrowK knda1 kndb1) (DArrowK knda2 kndb2) = lkEq knda1 knda2-}
                                                      {->> lkEq kndb1 kndb2-}
{-kind_equal DStarK                DStarK                = return ()-}
{-kind_equal _                     _                     = mzero-}

{-----------------------------------------------------------------------------}
{--- Clause-}
{-----------------------------------------------------------------------------}
{-instance AlphaEq DClause where-}
        {-lkEq = clause_equal-}

{-clause_equal :: DClause -> DClause -> LookupST ()-}
{-clause_equal (DClause pats1 exp1) (DClause pats2 exp2) =-}
    {-zipWithM_ lkEq pats1 pats2 >> lkEq exp1 exp2-}
{-----------------------------------------------------------------------------}
{--- Clause-}
{-----------------------------------------------------------------------------}
{-instance AlphaEq DPred where-}
    {-lkEq = pred_equal-}

{-pred_equal :: DPred -> DPred -> LookupST ()-}
{-pred_equal (DAppPr pred1 typ1 ) (DAppPr pred2 typ2 ) = lkEq pred1 pred2-}
                                                    {->> lkEq typ1 typ2-}
{-pred_equal (DSigPr pred1 kind1) (DSigPr pred2 kind2) = lkEq pred1 pred2-}
                                                    {->> lkEq kind1 kind2-}
{-pred_equal (DVarPr n1         ) (DVarPr n2         ) = n1 ~=~ n2-}
{-pred_equal (DConPr n1         ) (DConPr n2         ) = n1 ~=~ n2-}
{-pred_equal _                    _                    = mzero-}

{-----------------------------------------------------------------------------}
{--- Pat-}
{-----------------------------------------------------------------------------}

{-instance AlphaEq DPat where-}
    {-lkEq = pat_equal-}

{-pat_equal :: DPat -> DPat -> LookupST ()-}
{-pat_equal (DLitPa lit1  ) (DLitPa lit2  ) = guard $ lit1 == lit2-}
{-pat_equal (DVarPa n1    ) (DVarPa n2    ) = insertLRLST  n1 n2-}
{-pat_equal (DConPa n1 p1 ) (DConPa n2 p2 ) = do-}
     {-n1 ~=~ n2-}
     {-guard $ length p1 == length p2-}
     {-zipWithM_ lkEq p1 p2  -- Does this allow bindings across-}
                           {--- patterns?-}
{-pat_equal (DTildePa pat1) (DTildePa pat2) = lkEq pat1 pat2-}
{-pat_equal (DBangPa pat1 ) (DBangPa pat2 ) = lkEq pat1 pat2-}
{-pat_equal DWildPa         DWildPa         = return ()-}
{-pat_equal _               _               = mzero-}


{-----------------------------------------------------------------------------}
{--- Utils-}
{-----------------------------------------------------------------------------}

{-(~=~) :: Name -> Name -> LookupST ()-}
{-a ~=~ b = do-}
    {-tbl <- get-}
    {-guard $ (eqInTbl tbl) a b-}
    {-bol <- isInL' a-}
    {-if bol-}
        {-then return ()-}
        {-else guard $ show a == show b-}


{-isInL' :: Name -> LookupST Bool-}
{-isInL' n = do-}
    {-tbl <- get-}
    {-return $ (isInL tbl) n-}


{-insertLRLST :: Name -> Name -> LookupST ()-}
{-insertLRLST a b = modify $ \tbl -> insertLR tbl a b-}

{-insertLRLSTty :: DTyVarBndr -> DTyVarBndr -> LookupST ()-}
{-insertLRLSTty (DPlainTV n1    ) (DPlainTV n2    ) = insertLRLST n1 n2-}
{-insertLRLSTty (DKindedTV n1 k1) (DKindedTV n2 k2) = do-}
    {-guard $ show k1 == show k2   -- Duck-show-template-kinding:-}
                                 {--- If it shows like a duck, it is-}
                                 {--- a duck-}
    {-insertLRLST n1 n2-}
{-insertLRLSTty _                 _                 = mzero-}

