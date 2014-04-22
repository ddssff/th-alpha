{-# LANGUAGE TemplateHaskell #-}
module Main where

import Test.Tasty
import Test.Tasty.HUnit

import Language.Haskell.TH
import Control.Monad (liftM2)

import Language.Haskell.TH.Alpha

main = defaultMain tests


tests :: TestTree
tests = testGroup "Tests" [unitTests]

unitTests = testGroup "Unit tests"
  [ testCase "Lambda expressions with different bound variables" $
    do
       -- TODO: FIX THIS!
       b' <- (exp_equalM (runQ [| \x -> x|]) (runQ [| \y -> y|]))
       b <- b'
       assertBool "Expressions not considered equal!" b
  , testCase "Equal literals" $
    do
       b' <- (exp_equalM (runQ [| 5 |]) (runQ [| 5 |]))
       b <- b'
       assertBool "Expressions not considered equal!" b
  ]

exp_equalM = liftM2 exp_equal
