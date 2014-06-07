{-# LANGUAGE NoMonomorphismRestriction, TypeFamilies, FlexibleInstances
    , MultiParamTypeClasses, FunctionalDependencies #-}
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
    exp_equal,
    AlphaEq(..)
    ) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax  (Quasi, returnQ)
import Language.Haskell.TH.Desugar
import Data.Function               (on)
import Control.Monad               (liftM, liftM2, liftM3, join, foldM)
import Data.Data                   (toConstr, Data)
import Data.Maybe                  (isJust)



--  A poor man's bound variable lookup table.
type Lookup = ([(Name,Int)], [(Name,Int)], Int)


-- | The main Alpha Equivalence class. '@=' is by default defined in terms
-- of 'lkEq'. 'lkEq' is exposed for composability: it is easy to
-- recursively build 'AlphaEq' instances from other 'AlphaEq' instances by
-- delegating the lookup update to the subinstances.
class AlphaEq a where
    -- | Compares its arguments for alpha equivalence.
    (@=) :: a -> a -> Bool
    -- | Given a variable binding lookup compares arguments for alpha
    -- equivalence, returning Just of updated lookup in case of
    -- equivalence, Nothing otherwise.
    lkEq :: a -> a -> Lookup -> Maybe Lookup
    x @= y = isJust $ lkEq x y ([], [], 0)


---------------------------------------------------------------------------
-- Exp
---------------------------------------------------------------------------

-- | Convenience function that uses 'runQ' on 'exp_equal'.
--
-- >>> areExpAEq [| let x = 5 in x |] [| let y = 5 in y |]
-- True
areExpAEq :: Quasi m
         => ExpQ    -- ^ Quoted expression
         -> ExpQ    -- ^ Quoted expression
         -> m Bool
areExpAEq e1 e2 = let expM = (join .) . liftM2 exp_equal
                 in expM (runQ e1) (runQ e2)

-- | Compare two expressions for alpha-equivalence. Since this uses
-- th-desugar to desugar the expressions, returns a Bool in the Quasi
-- context.
exp_equal :: Quasi m => Exp -> Exp -> m Bool
exp_equal t1 t2 = (liftM3 exp_equal') (dsExp t1) (dsExp t2) (return ([], [], 0))

instance AlphaEq DExp where
        lkEq a b lk = if exp_equal' a b lk then Just lk else Nothing

exp_equal' :: DExp -> DExp -> Lookup -> Bool
exp_equal' (DVarE a1) (DVarE a2) (m1,m2,_) = lookup a1 m1 == lookup a2 m2
exp_equal' (DConE a1) (DConE a2) (m1,m2,_) = lookup a1 m1 == lookup a2 m2
                                        && (isJust $ lookup a1 m1)
exp_equal' (DLitE l1) (DLitE l2) _       = l1 == l2
exp_equal' (DAppE a1 b1) (DAppE a2 b2) c = (exp_equal' a1 a2 c)
                                         && (exp_equal' b1 b2 c)
exp_equal' (DLamE a1 b1) (DLamE a2 b2) (m1,m2,cnt) =
        if ((/=) `on` length) a1 a2
            then False
            else exp_equal' b1 b2 ((ato a1 ++ m1),(ato a2 ++ m2), l)
      where ato x = zip x [cnt..]
            l     = cnt + length a1
exp_equal' (DCaseE a1 b1) (DCaseE a2 b2) c =
        if length b1 == length b2
            then exp_equal' a1 a2 c && (any id $ zipWith mec b1 b2)
            else False
      where mec x y = match_equal x y c
exp_equal' (DLetE a1 b1) (DLetE a2 b2) c =
        isJust (foldM lkEqC c (zip a1 a2) >>= lkEq b1 b2)
      where lkEqC l (a,b) = lkEq a b l
exp_equal' (DSigE a1 b1) (DSigE a2 b2) c@(m1,m2,_) =
        lkEqB a1 a2 c && lkEqB b1 b2 c
exp_equal' _ _ _ = False

---------------------------------------------------------------------------
-- Match
---------------------------------------------------------------------------

match_equal :: DMatch -> DMatch -> Lookup -> Bool
match_equal (DMatch pat1 exp1) (DMatch pat2 exp2) c =
        case lkEq pat1 pat2 c of
            Just d  -> exp_equal' exp1 exp2 d
            Nothing -> False

---------------------------------------------------------------------------
-- LetDec
---------------------------------------------------------------------------

instance AlphaEq DLetDec where
        lkEq = letDec_equal

letDec_equal :: DLetDec -> DLetDec -> Lookup -> Maybe Lookup
letDec_equal (DFunD n1 cls1) (DFunD n2 cls2) c =
        if n1 == n2
            then foldM lkEqC c (zip cls1 cls2)
            else Nothing
      where lkEqC l (a,b) = lkEq a b l
letDec_equal (DValD pat1 exp1) (DValD pat2 exp2) c =
        lkEq exp1 exp2 c >>= lkEq pat1 pat2
letDec_equal (DSigD name1 typ1) (DSigD name2 typ2) c@(m1,m2,_) =
        -- Hard to tell how the name will be bound, so just check types
        lkEq typ1 typ2 c
letDec_equal (DInfixD fx1 name1) (DInfixD fx2 name2) c =
        if fx1 == fx2 && name1 == name2 then Just c else Nothing
letDec_equal _ _ _ = Nothing

---------------------------------------------------------------------------
-- LetDec
---------------------------------------------------------------------------

instance AlphaEq DType where
        lkEq = type_equal

-- TODO: For now just ignore type signatures.
type_equal :: DType -> DType -> Lookup -> Maybe Lookup
type_equal _ _ c = Just c
{-type_equal (DForallT tybs1 ctx1 typ1) (DForallT tybs2 ctx2 typ2) c = do-}
        {-nlk <- type_equal typ1 typ2 c-}
        {-if all (\y -> cmpTYvar y nlk) (zip tybs1 tybs2)-}
            {-then Just nlk-}
            {-else Nothing-}
     {-where cmpTYvar ((DPlainTV n1),(DPlainTV n2)) c' = cmpLk n1 n2 c'-}
           {-cmpTYvar ((DKindedTV n1 k1),(DKindedTV n2 k2)) c' =-}
                {-cmpLk n1 n2 c' && lkEqB k1 k2 c'-}
           {-cmpTYvar _ _ = False-}
{-type_equal (DAppT ty1 arg1) (DAppT ty2 arg2) c = undefined-}
{-type_equal (DSigT ty1 knd1) (DAppT ty2 knd2) c = undefined-}
{-type_equal (DVarT n1) (DVarT n2) c = undefined-}

---------------------------------------------------------------------------
-- Kind
---------------------------------------------------------------------------
-- TODO:
instance AlphaEq DKind where
        lkEq = undefined

-- TODO: For now just ignore kind signatures.
kind_equal :: DKind -> DKind -> Lookup -> Maybe Lookup
kind_equal _ _ c = Just c

---------------------------------------------------------------------------
-- Clause
---------------------------------------------------------------------------
instance AlphaEq DClause where
        lkEq = clause_equal

clause_equal :: DClause -> DClause -> Lookup -> Maybe Lookup
clause_equal (DClause pats1 exp1) (DClause pats2 exp2) lk =
        pat_res >>= lkEq exp1 exp2
    where lkEqC l (a,b) = lkEq a b l
          pat_res       = foldM lkEqC lk (zip pats1 pats2)
---------------------------------------------------------------------------
-- Pat
---------------------------------------------------------------------------

instance AlphaEq DPat where
        lkEq = pat_equal

pat_equal :: DPat -> DPat -> Lookup -> Maybe Lookup
pat_equal (DLitPa lit1) (DLitPa lit2)     c = if lit1 == lit2
                                                then Just c
                                                else Nothing
pat_equal (DVarPa n1  ) (DVarPa n2)       c = Just (addn n1 n2 c)
    where addn x y (m1,m2,i) = ((x,i):m1,(y,i):m2,i+1)
pat_equal (DConPa n1 p1) (DConPa n2 p2) c@(m1,m2,i)  =
    if (lookup n1 m1 == lookup n2 m2 && length p1 == length p2)
        then foldM cmbn c (zip p1 p2) -- Does this allow bindings across
                                      -- patterns?
        else Nothing
      where cmbn cn (x,y) = lkEq x y c
pat_equal (DTildePa pat1) (DTildePa pat2) c = lkEq pat1 pat2 c
pat_equal (DBangPa pat1 ) (DBangPa pat2)  c = lkEq pat1 pat2 c
pat_equal DWildPa         DWildPa         c = Just c
pat_equal _               _               _ = Nothing


---------------------------------------------------------------------------
-- Utils
---------------------------------------------------------------------------

fst3  (a,_,_) = a
snd3  (_,b,_) = b
thrd3 (_,_,c) = c
cmpLk a b (m1,m2,_) = lookup a m1 == lookup b m2
cmpLkC (a,b) c = cmpLk a b c
lkEqB a b c = isJust $ lkEq a b c
