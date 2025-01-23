{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeApplications #-}

module Cardano.PTT.Test.Tasty where

import Cardano.Node.Emulator qualified as E
import Control.Arrow ((&&&))
import Control.Exception (
  Exception,
  catch,
  throwIO,
 )
import Control.Monad.Reader.Class (MonadReader, asks)
import Data.IORef (IORef, newIORef, readIORef)
import PlutusTx.Coverage (
  CoverageData,
  CoverageReport (CoverageReport),
 )
import Prettyprinter qualified as Pretty
import Test.Tasty (TestTree)
import Test.Tasty qualified as Tasty
import Test.Tasty.HUnit qualified as Tasty
import Test.Tasty.Options qualified as Tasty
import Test.Tasty.QuickCheck qualified as Tasty

import Cardano.Node.Emulator.API (
  EmulatorLogs,
  EmulatorM,
 )
import Cardano.PTT.Test.Options (TestCoverage (TestCoverage))
import Control.Monad.Reader (Reader, runReader)
import Data.Data (Proxy (Proxy))
import System.Environment (getArgs)
import System.Exit (ExitCode (ExitSuccess))

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

askCoverageOptionsM ::
  (PTTMonad env model m) =>
  m (E.Options model -> TestTree) ->
  m TestTree
askCoverageOptionsM m = do
  f <- m
  (withCov, withoutCov) <- asks $ getOptionsWithCoverage &&& getOptionsWithoutCoverage
  pure $ Tasty.askOption $ \(TestCoverage enabled) -> f (if enabled then withCov else withoutCov)

askCoverageOptions ::
  (PTTMonad env model m) =>
  (E.Options model -> TestTree) ->
  m TestTree
askCoverageOptions f = askCoverageOptionsM $ pure f

checkPredicateOptions ::
  (PTTMonad env model m) =>
  Tasty.TestName ->
  EmulatorPredicate ->
  EmulatorM a ->
  m TestTree
checkPredicateOptions testName predicate em = askCoverageOptions $
  \options -> E.checkPredicateOptions options testName predicate em

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
testPropertyWithOptions testName prop =
  askCoverageOptions $
    Tasty.testProperty testName . prop

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

coverageArguments :: IO Bool
coverageArguments = do
  args <- getArgs
  let shouldPrintCoverage = any (`elem` args) ["--test-coverage", "-c"]
      -- Skip coverage if help was requested
      skipPrinting = any (`elem` args) ["--help", "-h", "-l", "--list-tests", "-q", "--quiet"]
  pure $ shouldPrintCoverage && not skipPrinting

defaultMainWith ::
  E.Options model ->
  PTTWrapper Env model TestTree ->
  (Tasty.TestTree -> Tasty.TestTree) ->
  IO ()
defaultMainWith opts testsWrapper f = do
  shouldPrintCoverage <- coverageArguments
  (tests, env) <- initTests
  Tasty.defaultMainWithIngredients
    (Tasty.includingOptions [Tasty.Option (Proxy @TestCoverage)] : Tasty.defaultIngredients)
    (f tests)
    `catch` ( \(e :: ExitCode) -> do
                -- print coverage report
                if e == ExitSuccess && shouldPrintCoverage
                  then printCoverage env e
                  else throwIO e
            )
 where
  initTests = do
    ref <- newIORef mempty
    let env = Env ref opts
    pure (runReader testsWrapper env, env)

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
