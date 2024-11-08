{-# LANGUAGE OverloadedStrings #-}
module Main(main) where

import Test.Tasty (defaultMain, testGroup, TestTree)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup "use cases" [ ]
