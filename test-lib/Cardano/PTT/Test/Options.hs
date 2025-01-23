module Cardano.PTT.Test.Options where

import Test.Tasty.Options

newtype TestCoverage = TestCoverage Bool

instance IsOption TestCoverage where
  defaultValue = TestCoverage False
  parseValue = const $ Just (TestCoverage True) -- If the flag is present, set to True
  optionName = return "test-coverage"
  optionHelp = return "Enable test coverage. Flag presence implies True."

  -- Define `optionCLParser` to use `flagCLParser`
  optionCLParser = flagCLParser (Just 'c') (TestCoverage True)
