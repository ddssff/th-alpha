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
import Control.Monad (liftM3)
import Data.Data (toConstr, Data)

exp_equal :: Quasi m => Exp -> Exp -> m Bool
exp_equal t1 t2 = (liftM3 exp_equal') (dsExp t1) (dsExp t2) (return ([], [], 0))

type Lookup = ([(Name,Int)], [(Name,Int)], Int)

exp_equal' :: DExp -> DExp -> Lookup -> Bool
exp_equal' (DVarE a) (DVarE b) (m1,m2,_) = lookup a m1 == lookup b m2
exp_equal' (DConE a) (DConE b) (m1,m2,_) = lookup a m1 == lookup b m2
exp_equal' (DLitE l1) (DLitE l2) _       = l1 == l2
exp_equal' (DAppE a1 a2) (DAppE b1 b2) c = (exp_equal' a1 b1 c)
                                         && (exp_equal' a2 b2 c)
exp_equal' (DLamE a1 a2) (DLamE b1 b2) (m1,m2,cnt) =
        if ((/=) `on` length) a1 b1
            then False
            else exp_equal' a2 b2 ((ato a1 ++ m1),(ato b1 ++ m2), l)
                where ato x = zip x [cnt..]
                      l     = cnt + length a1
exp_equal' (DCaseE a1 a2) (DCaseE b1 b2) c = exp_equal' a1 b1 c
                                          && match_equal a2 b2 c


match_equal = undefined

-- Compares values by constructor.
const_eq :: Data a => a -> a -> Bool
const_eq = (==) `on` toConstr


