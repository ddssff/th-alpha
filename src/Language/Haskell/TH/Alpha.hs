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
import Data.Function (on)
import Data.Data (toConstr, Data)

exp_equal :: Exp -> Exp -> Bool
exp_equal t1 t2 = exp_equal' t1 t2 ([], [], 0)

type Lookup = ([(Name,Int)], [(Name,Int)], Int)

exp_equal' :: Exp -> Exp -> Lookup -> Bool
exp_equal' (VarE n1) (VarE n2) (m1,m2,_) = lookup n1 m1 == lookup n2 m2
exp_equal' (ConE n1) (ConE n2) (m1,m2,_) = lookup n1 m1 == lookup n2 m2
exp_equal' (LitE l1) (LitE l2) _         = l1 == l2
exp_equal' (AppE a1 a2) (AppE b1 b2) c   = (exp_equal' a1 b1 c)
                                        && (exp_equal' a2 b2 c)

exp_equal' (InfixE (Just a1) a2 (Just a3)) (InfixE (Just b1) b2 (Just b3)) c
    = (exp_equal' a1 b1 c) && (exp_equal' a2 b2 c) && (exp_equal' a3 b3 c)
exp_equal' (InfixE (Just a1) a2 Nothing) (InfixE (Just b1) b2 Nothing) c
    = (exp_equal' a1 b1 c) && (exp_equal' a2 b2 c)
exp_equal' (InfixE Nothing a2 (Just a3)) (InfixE Nothing b2 (Just b3)) c
    = (exp_equal' a2 b2 c) && (exp_equal' a3 b3 c)
exp_equal' (InfixE Nothing a2 Nothing) (InfixE Nothing b2 Nothing) c
    = (exp_equal' a2 b2 c)
exp_equal' _ _ _ = False

exp_equal' (UInfixE a1 a2 a3) (UInfixE b1 b2 b3) c = (exp_equal' a1 b1 c)
                                                  && (exp_equal' a2 b2 c)
                                                  && (exp_equal' a3 b3 c)
exp_equal' (ParensE a) (ParensE b) c         = exp_equal' a b c
{-exp_equal' (LamE pat_as a) (LamE pat_bs b) (m1,m2,cnt) =-}
        {-if length pat_as /= length pat_bs-}
            {-then False-}
            {-else exp_equal' a b ((ato pat_as ++ m1),(ato pat_bs ++ m2), cnt + length pat_as)-}
                {-where ato x = zip x [cnt..]-}

-- Compares values by constructor.
const_eq :: Data a => a -> a -> Bool
const_eq = (==) `on` toConstr


