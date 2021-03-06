{-# LANGUAGE TemplateHaskell  #-}
module Main where

import Test.Tasty
import Test.Tasty.HUnit


import Language.Haskell.TH
import Language.Haskell.TH.Alpha

main :: IO ()
main = defaultMain tests


tests :: TestTree
tests = testGroup "Tests" [unitTests]

unitTests :: TestTree
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
  , testCase "Different open terms" $
    do
       b <- areExpAEq [| tail |] [| head |]
       assertBool "Expressions considered equal!" (not b)
  , testCase "Same open terms" $
    do
       b <- areExpAEq [| tail |] [| tail |]
       assertBool "Expressions not considered equal!" b
  , testCase "Same lambda'd terms" $
    do
       b <- areExpAEq [| \x -> tail x |] [| \y -> tail y |]
       assertBool "Expressions not considered equal!" b
  , testCase "@=" $
    do
       let x = mkName "x"
       let y = mkName "y"
       b <- runQ $ (LamE [VarP x] (VarE x)) @= (LamE [VarP y] (VarE y))
       assertBool "Expressions not considered equal!" b
  ]


