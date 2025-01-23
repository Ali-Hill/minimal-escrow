{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeApplications #-}

module Cardano.PTT.Test.Tasty where

import Cardano.Node.Emulator qualified as E
import Control.Exception
import Control.Monad.Reader.Class
import Data.IORef (IORef, newIORef, readIORef)
import PlutusTx.Coverage
import Prettyprinter qualified as Pretty
import Test.Tasty (TestTree)
import Test.Tasty qualified as Tasty
import Test.Tasty.HUnit qualified as Tasty
import Test.Tasty.QuickCheck qualified as Tasty

import Cardano.Node.Emulator.API (
  EmulatorLogs,
  EmulatorM,
 )
import Control.Monad.Reader (Reader, runReader)
import System.Exit

-- define HasCovDataRef
class HasCovDataRef env where
  getCovDataRef :: env -> IORef CoverageData

-- define HasOptions
class HasOptions model env | env -> model where
  getOptions :: env -> E.Options model

getOptionsWithoutCoverage :: (HasOptions model env) => env -> E.Options model
getOptionsWithoutCoverage env =
  (getOptions env){E.coverageRef = Nothing}

getOptionsWithCoverage :: (HasOptions model env, HasCovDataRef env) => env -> E.Options model
getOptionsWithCoverage env =
  (getOptions env){E.coverageRef = Just $ getCovDataRef env}

-- declare monad functional constraints for Tasty wrapper

type PTTMonad env model m =
  ( MonadReader env m
  , HasCovDataRef env
  , HasOptions model env
  )

-- MonadReader instance for Tasty wrapper
type PTTWrapper env model = Reader (env model)

data Env model = Env
  { envCovDataRef :: !(IORef CoverageData)
  , envOptions :: !(E.Options model)
  }

instance HasCovDataRef (Env model) where
  getCovDataRef = envCovDataRef

instance HasOptions model (Env model) where
  getOptions = envOptions

-- bind functions to the Tasty wrapper

testGroup :: (Monad f) => Tasty.TestName -> [f TestTree] -> f TestTree
testGroup name xs = do
  Tasty.testGroup name <$> sequence xs

testCase :: (Functor f) => Tasty.TestName -> f Tasty.Assertion -> f TestTree
testCase name prop = do
  Tasty.testCase name <$> prop

type EmulatorPredicate = EmulatorLogs -> EmulatorM (Maybe String)

checkPredicateOptions ::
  (PTTMonad env model m) =>
  Tasty.TestName ->
  EmulatorPredicate ->
  EmulatorM a ->
  m TestTree
checkPredicateOptions testName predicate em = do
  E.checkPredicateOptions
    <$> asks getOptionsWithCoverage
    <*> pure testName
    <*> pure predicate
    <*> pure em

checkPredicateOptionsWithoutCoverage ::
  (PTTMonad env model m) =>
  Tasty.TestName ->
  EmulatorPredicate ->
  EmulatorM a ->
  m TestTree
checkPredicateOptionsWithoutCoverage testName predicate em = do
  E.checkPredicateOptions
    <$> asks getOptionsWithoutCoverage
    <*> pure testName
    <*> pure predicate
    <*> pure em

testPropertyWithOptions ::
  forall a env model m.
  (Tasty.Testable a, PTTMonad env model m) =>
  Tasty.TestName ->
  (E.Options model -> a) ->
  m TestTree
testPropertyWithOptions testName prop = do
  Tasty.testProperty testName <$> asks (prop . getOptionsWithCoverage)

testPropertyWithOptionsWithoutCoverage ::
  forall a env model m.
  (Tasty.Testable a, PTTMonad env model m) =>
  Tasty.TestName ->
  (E.Options model -> a) ->
  m TestTree
testPropertyWithOptionsWithoutCoverage testName prop = do
  Tasty.testProperty testName <$> asks (prop . getOptionsWithoutCoverage)

testProperty ::
  forall a env model m.
  (Tasty.Testable a, PTTMonad env model m) =>
  Tasty.TestName ->
  a ->
  m TestTree
testProperty testName prop =
  pure $ Tasty.testProperty testName prop

--------------------------------------------------------------------------------
--  utility functions

defaultMain :: E.Options model -> PTTWrapper Env model TestTree -> IO ()
defaultMain opts tests = defaultMainWith opts tests id

defaultMainWith ::
  E.Options model ->
  PTTWrapper Env model TestTree ->
  (Tasty.TestTree -> Tasty.TestTree) ->
  IO ()
defaultMainWith opts testsWrapper f = do
  (tests, env) <- initTests
  Tasty.defaultMain
    (f tests)
    `catch` printCoverage @ExitCode env
 where
  initTests = do
    ref <- newIORef mempty
    let env = Env ref opts
    pure $ (runReader testsWrapper env, env)

printCoverage ::
  (Exception e, HasCovDataRef env, HasOptions model env) =>
  env ->
  e ->
  IO b
printCoverage env e = do
  printCoverage'
    (getCovDataRef env)
    (const (getOptionsWithCoverage env))
    e

printCoverage' ::
  (Exception e) =>
  IORef CoverageData ->
  (IORef CoverageData -> E.Options state) ->
  e ->
  IO b
printCoverage' ref getOpts e = do
  -- print coverage report
  covData <- readIORef ref
  let
    opts = getOpts ref -- Spec.Escrow.optionsCoverage ref
    report = CoverageReport (E.coverageIndex opts) covData
  print $ Pretty.pretty report
  throwIO e
