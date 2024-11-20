{-# LANGUAGE OverloadedStrings #-}
module Main(main) where

import Spec.MultiSig qualified

import Test.Tasty (TestTree, defaultMain, testGroup)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup "use cases" [
    Spec.MultiSig.tests
    ]
