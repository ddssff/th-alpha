{-# LANGUAGE TemplateHaskell #-}
module Main where

import Test.Tasty
import Test.Tasty.HUnit

import Language.Haskell.TH
import Control.Monad (liftM2, join)

import Language.Haskell.TH.Alpha

main = defaultMain tests


tests :: TestTree
tests = testGroup "Tests" [unitTests]

unitTests = testGroup "Unit tests"
  [ testCase "Lambda expressions with different bound variables" $
    do
       b <- areEq [| \x -> x|]  [| \y -> y|]
       assertBool "Expressions not considered equal!" b
  , testCase "Equal literals" $
    do
       b <- areEq [| 5 |] [| 5 |]
       assertBool "Expressions not considered equal!" b
  , testCase "Different constructors" $
    do
       b <- areEq [| Left 5 |]  [| Right 5 |]
       assertBool "Expressions considered equal!" (not b)
  , testCase "Let bindings" $
    do
       b <- areEq [| let x = 5 in x |] [| let y = 5 in y |]
       assertBool "Expressions not considered equal!" b
  ]
    where areEq e1 e2 = exp_equalM (runQ e1) (runQ e2)

exp_equalM = (join .) . liftM2 exp_equal

