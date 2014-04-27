{-# LANGUAGE NoMonomorphismRestriction #-}
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
import Language.Haskell.TH.Syntax (Quasi)
import Language.Haskell.TH.Desugar
import Data.Function (on)
import Control.Monad (liftM3, foldM)
import Data.Data (toConstr, Data)
import Data.Maybe (isJust)

-- | Compares two expressions for alpha-equivalence.
exp_equal :: Quasi m => Exp -> Exp -> m Bool
exp_equal t1 t2 = (liftM3 exp_equal') (dsExp t1) (dsExp t2) (return ([], [], 0))


type Lookup = ([(Name,Int)], [(Name,Int)], Int)

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

match_equal :: DMatch -> DMatch -> Lookup -> Bool
match_equal (DMatch pat1 exp1) (DMatch pat2 exp2) c =
        case pat_equal pat1 pat2 c of
            Just d  -> exp_equal' exp1 exp2 d
            Nothing -> False


-- | Attempts to match two patterns. If the match succeeds, returns an
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


-- Compares values by constructor.
const_eq :: Data a => a -> a -> Bool
const_eq = (==) `on` toConstr


