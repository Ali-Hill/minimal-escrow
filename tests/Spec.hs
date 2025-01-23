{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Spec.Escrow qualified
import Spec.Escrow2 qualified

import Cardano.PTT.Test.Tasty qualified as PTT
import Control.Exception (catch)
import Data.IORef (IORef, newIORef)
import PlutusTx.Coverage (CoverageData)
import System.Exit (ExitCode)
import Test.Tasty (TestTree, defaultMain, testGroup)

_main :: IO ()
_main = do
  ref <- newIORef mempty
  defaultMain (tests ref)
    `catch`
    -- print coverage
    PTT.printCoverage' @ExitCode ref Spec.Escrow.optionsCoverage
 where
  tests :: IORef CoverageData -> TestTree
  tests ref =
    testGroup
      "use cases"
      [ Spec.Escrow.tests ref
      ]

-- with wrapper
main :: IO ()
main =
  PTT.defaultMainWith
    Spec.Escrow2.options
    Spec.Escrow2.tests
    (testGroup "use cases" . (: []))
