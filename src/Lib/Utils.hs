{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}

module Lib.Utils where

import PlutusLedgerApi.V2.Contexts (ScriptContext(..), TxInInfo(..), TxOut(..), ScriptPurpose(..), txInfoInputs)
import PlutusLedgerApi.V1.Address (Address)
import PlutusLedgerApi.V1.Crypto (PubKeyHash)
import PlutusTx.Prelude
    ( Integer,
      Maybe(Nothing, Just),
      ($),
      length,
      filter,
      find,
      traceError,
      Eq((==)) )
import Prelude (Maybe(..), Eq)

-- Count outputs by a specific address
{-# INLINABLE countOutputsByAddress #-}
countOutputsByAddress :: [TxOut] -> Address -> Integer
countOutputsByAddress utxos address = 
    length $ filter (\utxo -> txOutAddress utxo == address) utxos

-- Count script outputs (outputs with ScriptCredential)
-- {-# INLINABLE countScriptOutputs #-}
-- countScriptOutputs :: [TxOut] -> Integer
-- countScriptOutputs utxos =
--     length $ filter isScriptOutput utxos

-- Find the "own input" based on the script's purpose
{-# INLINABLE ownInput #-}
ownInput :: ScriptContext -> TxInInfo
ownInput ctx =
    case scriptContextPurpose ctx of
        Spending ref -> 
            case find (\input -> txInInfoOutRef input == ref) (txInfoInputs (scriptContextTxInfo ctx)) of
                Just foundInput -> foundInput
                Nothing -> traceError "Input not found for specified reference"
        _ -> traceError "Invalid script purpose"

-- Helper function to check if an output is a script output
-- {-# INLINABLE isScriptOutput #-}
-- isScriptOutput :: TxOut -> Bool
-- isScriptOutput utxo =
--     case addressCredential (txOutAddress utxo) of
--         ScriptCredential _ -> True
--         _ -> False
