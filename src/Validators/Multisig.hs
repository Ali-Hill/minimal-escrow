{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-missing-import-lists #-}

module Validators.Multisig where

import PlutusLedgerApi.V2.Contexts (txOutDatum, txInInfoResolved, txOutAddress, ScriptContext(ScriptContext, scriptContextTxInfo), TxInfo(TxInfo, txInfoInputs, txInfoOutputs, txInfoSignatories))
import PlutusLedgerApi.V1.Address (Address)
import PlutusLedgerApi.V2.Tx
    ( OutputDatum(OutputDatum, NoOutputDatum, OutputDatumHash) )
import PlutusTx.Prelude
    ( Bool(False),
      Integer,
      Maybe(Nothing, Just),
      (&&),
      (||),
      length,
      all,
      any,
      elem,
      find,
      map,
      traceError,
      Eq(..),
      (==),
      AdditiveSemigroup((+)),
      Ord((>)) ) 
import PlutusTx ( FromData(fromBuiltinData) )
import Lib.Types (MultisigDatum(..), MultisigRedeemer(..), VerificationKeyHash)
import Lib.Utils (countOutputsByAddress, ownInput) -- Assuming these are predefined utility functions
import qualified PlutusLedgerApi.V1.Scripts
import Data.Foldable (Foldable(foldl'))

-- Hack, I don't know how to get the Eq instance there
eqMultisigDatum :: MultisigDatum -> MultisigDatum -> Bool
eqMultisigDatum d1 d2 = 
    release_value d1 == release_value d2 &&
    beneficiary d1 == beneficiary d2 &&
    required_signers d1 == required_signers d2 &&
    signed_users d1 == signed_users d2

-- Validator Logic
{-# INLINABLE multisig #-}
multisig :: MultisigDatum -> MultisigRedeemer -> ScriptContext -> Bool
multisig datum redeemer ctx =
    let
        ScriptContext{scriptContextTxInfo = txInfo} = ctx
        TxInfo{txInfoInputs = inputs, txInfoOutputs = outputs, txInfoSignatories = extraSignatories} = txInfo

        -- Using ownInput from Utils to find the specific input UTXO of this script
        ownInputUTxO = ownInput ctx

        multisigScriptAddress :: Address
        multisigScriptAddress = txOutAddress (txInInfoResolved ownInputUTxO)

        multisigInputCount :: Integer
        multisigInputCount = countOutputsByAddress (map txInInfoResolved inputs) multisigScriptAddress

        multisigOutputCount :: Integer
        multisigOutputCount = countOutputsByAddress outputs multisigScriptAddress

        datumSignedUsers :: MultisigDatum -> [VerificationKeyHash]
        datumSignedUsers = signed_users

        datumRequiredSigners :: MultisigDatum -> [VerificationKeyHash]
        datumRequiredSigners = required_signers
    in case redeemer of
        Use ->
            
            -- Redeemer `Use` logic
            multisigInputCount == 1 &&
            multisigOutputCount == 0 &&
            any (`elem` extraSignatories) (datumSignedUsers datum)

        Sign ->
            -- Redeemer `Sign` logic
            case find (\output -> txOutAddress output == multisigScriptAddress) outputs of
                Nothing -> False
                Just ownOutput ->
                    let outputDatum = txOutDatum ownOutput in 
                    let
                        -- Extract MultisigDatum from InlineDatum
                        outputDatum' = fromInlineDatum outputDatum
                    in
                        multisigInputCount == 1 &&
                        multisigOutputCount == 1 &&
                        eqMultisigDatum outputDatum' datum {signed_users = datumSignedUsers datum } &&
                        length (datumSignedUsers outputDatum') > length (datumSignedUsers datum) &&
                        correctlyExtendedSignedUsers (datumSignedUsers datum) (datumSignedUsers outputDatum') (datumRequiredSigners datum) extraSignatories

-- Helper Function: Check proper extension of signed users
{-# INLINABLE correctlyExtendedSignedUsers #-}
correctlyExtendedSignedUsers :: [VerificationKeyHash] -> [VerificationKeyHash] -> [VerificationKeyHash] -> [VerificationKeyHash] -> Bool
correctlyExtendedSignedUsers oldSigned newSigned requiredSigners txSignatures =
    let
        -- Check that no signatures are repeated in newSigned
        noRepeatedSignatures = all (\sig -> count sig newSigned == 1) newSigned

        -- Check that no old signatures were removed
        noRemovedSignatures = all (`elem` newSigned) oldSigned

        -- Check that only required signers are in newSigned
        onlyRelevantSignatures = all (`elem` requiredSigners) newSigned

        -- Ensure all new signatures are actually signed in txSignatures or are in oldSigned
        allNewSignaturesActuallySigned = all (\sig -> sig `elem` oldSigned || sig `elem` txSignatures) newSigned
    in
        noRepeatedSignatures &&
        noRemovedSignatures &&
        onlyRelevantSignatures &&
        allNewSignaturesActuallySigned

-- Utility Functions
{-# INLINABLE count #-}
count :: Eq a => a -> [a] -> Integer
count x = foldl' (\acc y -> if y == x then acc + 1 else acc) 0

fromInlineDatum :: OutputDatum -> MultisigDatum
fromInlineDatum (OutputDatum (PlutusLedgerApi.V1.Scripts.Datum datum)) = case fromBuiltinData datum of
    Just d  -> d
    Nothing -> traceError "Invalid datum"
fromInlineDatum NoOutputDatum = traceError "No datum"
fromInlineDatum (OutputDatumHash _) = traceError "Datum hash not supported"