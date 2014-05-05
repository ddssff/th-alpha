{-# LANGUAGE NoMonomorphismRestriction, TypeFamilies, FlexibleInstances
    , MultiParamTypeClasses, FunctionalDependencies #-}
{-|
Module      : Language.Haskell.TH.Alpha
Description : Alpha equivalence in TH
Copyright   : (c) Julian K. Arni, 2014
License     : BSD3
Maintainer  : jkarni@gmail.com
Stability   : experimental
-}

module Language.Haskell.TH.Alpha where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax (Quasi, Q)
import Language.Haskell.TH.Desugar
import Data.Function (on)
import Control.Monad (liftM3, foldM)
import Data.Data (toConstr, Data)
import Data.Boolean
import Data.Maybe (isJust)

-- The Alpha Equivalence class.
-- Laws:
--      * a @= (n @~< a)
--      * Equivalence class laws:
--          > a @= a
--          > a @= b == b @ a
--          > a @= b == b @ c  -> a @= c
class (Boolean b) => AlphaEq a b | a -> b where
    type AEName a
    (@=)  :: a -> a -> b                 -- ^ Alpha equivalence
    (@~>) :: AEName a -> a -> a          -- ^ Alpha conversion; change all
                                         -- occurrences of the name in the
                                         -- argument.

-- The fundep is ugly, but required to satisfy the compiler
class (Boolean b) => LookupTable lt name b | lt -> b where
    lookupEq                :: name -> name -> lt -> b
    insertLeft, insertRight :: name -> lt -> lt
    insertLAndR             :: name -> name -> lt -> lt
    insertLAndR x y lt      = insertRight y $ insertLeft x lt

type Lookup = ([(Name,Int)], [(Name,Int)], Int)

-- A simple, Prelude.lookup based LookupTable
instance LookupTable Lookup Name Bool where
    lookupEq a b tbl = lookup a (fst3 tbl) == lookup b (fst3 tbl)
    insertLeft name (as, bs, i) = ((name,i):as, bs, i + 1)
    insertRight name (as, bs, i) = (as, (name,i):bs, i + 1)


instance AlphaEq Exp (Q Bool) where
    type AEName Exp = Name
    (@=)            = exp_equal
    {-(@~>)           =-}

instance (Quasi m) => Boolean (m Bool) where
    true  = return True
    false = return False


---------------------------------------------------------------------------
-- Exp
---------------------------------------------------------------------------
exp_equal :: Quasi m => Exp -> Exp -> m Bool
exp_equal t1 t2 = (liftM3 exp_equal') (dsExp t1) (dsExp t2) (return ([], [], 0))


exp_equal' :: DExp -> DExp -> Lookup -> Bool
exp_equal' (DVarE a) (DVarE b) (m1,m2,_) = lookup a m1 == lookup b m2
exp_equal' (DConE a) (DConE b) (m1,m2,_) = lookup a m1 == lookup b m2
                                        && (isJust $ lookup a m1)
exp_equal' (DLitE l1) (DLitE l2) _       = l1 == l2
exp_equal' (DAppE a1 a2) (DAppE b1 b2) c = (exp_equal' a1 b1 c)
                                         && (exp_equal' a2 b2 c)
exp_equal' (DLamE a1 a2) (DLamE b1 b2) (m1,m2,cnt) =
        if ((/=) `on` length) a1 b1
            then False
            else exp_equal' a2 b2 ((ato a1 ++ m1),(ato b1 ++ m2), l)
                where ato x = zip x [cnt..]
                      l     = cnt + length a1
exp_equal' (DCaseE a1 a2) (DCaseE b1 b2) c =
        if length a2 == length b2
            then exp_equal' a1 b1 c && (any id $ zipWith mec a2 b2)
            else False
        where mec x y = match_equal x y c

---------------------------------------------------------------------------
-- Match
---------------------------------------------------------------------------

match_equal :: DMatch -> DMatch -> Lookup -> Bool
match_equal (DMatch pat1 exp1) (DMatch pat2 exp2) c =
        case pat_equal pat1 pat2 c of
            Just d  -> exp_equal' exp1 exp2 d
            Nothing -> False


---------------------------------------------------------------------------
-- Pat
---------------------------------------------------------------------------

-- Attempts to match two patterns. If the match succeeds, returns an
-- updated lookup; otherwise returns Nothing.
pat_equal :: DPat -> DPat -> Lookup -> Maybe Lookup
pat_equal (DLitPa lit1) (DLitPa lit2) c   = if lit1 == lit2
                                                then Just c
                                                else Nothing
pat_equal (DVarPa n1) (DVarPa n2) c       = Just (addn n1 n2 c)
    where addn x y (m1,m2,i) = ((x,i):m1,(y,i):m2,i+1)
pat_equal (DConPa n1 p1) (DConPa n2 p2) c@(m1,m2,i)  =
        if (lookup n1 m1 == lookup n2 m2 && length p1 == length p2)
            then foldM cmbn c (zip p1 p2) -- Does this allow bindings across patterns?
            else Nothing
        where cmbn cn (x,y) = pat_equal x y c
pat_equal (DTildePa pat1) (DTildePa pat2) c = pat_equal pat1 pat2 c
pat_equal (DBangPa pat1) (DBangPa pat2)   c = pat_equal pat1 pat2 c
pat_equal DWildPa DWildPa c               = Just c
pat_equal _ _ _                           = Nothing


---------------------------------------------------------------------------
-- Utils
---------------------------------------------------------------------------

fst3  (a,_,_) = a
snd3  (_,b,_) = b
thrd3 (_,_,c) = c
