{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Spec.Escrow qualified

import Cardano.Node.Emulator qualified as E
import Control.Exception
import Data.IORef (IORef, newIORef, readIORef)
import PlutusTx.Coverage
import Prettyprinter qualified as Pretty
import System.Exit
import Test.Tasty
import Test.Tasty.Ingredients.Basic

main :: IO ()
main = do
  ref <- newIORef mempty
  defaultMain (tests ref)
    `catch` ( \(e :: ExitCode) -> do
                -- print coverage report
                covData <- readIORef ref
                let opts = Spec.Escrow.optionsCoverage ref
                    report = CoverageReport (E.coverageIndex opts) covData
                print $ Pretty.pretty report
                throwIO e
            )

tests :: IORef CoverageData -> TestTree
tests ref =
  testGroup
    "use cases"
    [ Spec.Escrow.tests ref
    ]
