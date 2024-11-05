{-# LANGUAGE OverloadedStrings #-}
module Main(main) where

import Spec.Escrow qualified

import Test.Tasty
import PlutusTx.Coverage
import Data.IORef (IORef, newIORef)

main :: IO ()
main = do
  ref <- newIORef mempty
  defaultMain (tests ref)

tests :: IORef CoverageData -> TestTree
tests ref =
  testGroup "use cases" [
    Spec.Escrow.tests ref
    ]
