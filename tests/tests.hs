{-# LANGUAGE TemplateHaskell  #-}
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
       b <- areExpAEq [| \x -> x|]  [| \y -> y|]
       assertBool "Expressions not considered equal!" b
  , testCase "Nested lambda expressions with different bound variables" $
    do
       b <- areExpAEq [| \f -> \a -> \b -> f a b |]  [| \g -> \x -> \y -> g x y|]
       assertBool "Expressions not considered equal!" b

  , testCase "Equal literals" $
    do
       b <- areExpAEq [| 5 |] [| 5 |]
       assertBool "Expressions not considered equal!" b
  , testCase "Different constructors" $
    do
       b <- areExpAEq [| Left 5 |]  [| Right 5 |]
       assertBool "Expressions considered equal!" (not b)
  , testCase "Let bindings" $
    do
       b <- areExpAEq [| let x = 5 in x |] [| let y = 5 in y |]
       assertBool "Expressions not considered equal!" b
  ]


