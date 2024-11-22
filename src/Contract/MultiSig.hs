{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
-- {-# OPTIONS_GHC -g -fplugin-opt PlutusTx.Plugin:coverage-all #-}

module Contract.MultiSig where

--------------------------------------------------------------------------------
-- Imports
import Control.Monad (void)
import Control.Monad.RWS.Class (asks)
import Data.Map qualified as Map

import Cardano.Api qualified as C
import Cardano.Api.Shelley qualified as C
import PlutusTx (ToData)
import PlutusTx (fromBuiltinData)
import PlutusTx qualified
import PlutusTx.Code (getCovIdx)
import PlutusTx.Coverage (CoverageIndex)

import Prelude hiding ((== ), (&&), (||), map, mapMaybe, (>=), length, (+), (-), fromBuiltinData, inv, traceError)
import PlutusTx.Prelude ((==), (&&), (||), map, mapMaybe, (>=), length, (+), (-), inv, traceError)
import PlutusTx.Prelude qualified as PlutusTx

import Cardano.Node.Emulator qualified as E
import Cardano.Node.Emulator.Internal.Node (
  SlotConfig,
  pSlotConfig,
  posixTimeRangeToContainedSlotRange,
 )
import Cardano.Node.Emulator.Test (testnet)
import Data.Maybe (fromJust)
import Ledger (POSIXTime, PaymentPubKeyHash (unPaymentPubKeyHash))
import Ledger qualified
import Ledger.Address (toWitness, Address (..))
import Ledger.Tx.CardanoAPI qualified as C
import Ledger.Typed.Scripts (validatorCardanoAddress)
import Ledger.Typed.Scripts qualified as Scripts
import Plutus.Script.Utils.V2.Contexts (
  scriptOutputsAt,
  txInfoValidRange,
  ownHash,
 )
import Plutus.Script.Utils.V2.Typed.Scripts qualified as V2

import Plutus.Script.Utils.Value (Value, geq)
import PlutusLedgerApi.V1.Interval qualified as Interval
import PlutusLedgerApi.V2 (Datum (Datum), Credential(..), OutputDatum (..))
import PlutusLedgerApi.V2.Tx
    ( TxOut(TxOut, txOutDatum, txOutAddress, txOutValue),
      OutputDatum(..) )
import PlutusLedgerApi.V2.Contexts
      ( findOwnInput,
        txSignedBy,
        ScriptContext(scriptContextTxInfo),
        TxInInfo(TxInInfo, txInInfoResolved),
        TxInfo(txInfoValidRange, txInfoOutputs, txInfoInputs),
        TxOut(TxOut, txOutDatum, txOutAddress, txOutValue),
        valuePaidTo )
import qualified Ledger as Ada
import qualified PlutusTx.List
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- On-chain code

-- | Parameters for a multi-signature contract.
data MultiSigParams = MultiSigParams
  { signatories :: [Ada.PubKeyHash]
  , minNumSignatures :: Integer
  , minimumValue :: Value
  }

PlutusTx.makeLift ''MultiSigParams

-- | The state of the contract.
data Label =
        -- Holding state, where the contract is waiting for a proposal
        Holding
        -- Collecting state, where the contract is gathering signatures
        | Collecting Value Ada.PubKeyHash POSIXTime [Ada.PubKeyHash]

PlutusTx.unstableMakeIsData ''Label
PlutusTx.makeLift ''Label

-- | The input to the contract, i.e. the action that we want to perform.
data Input =
        Propose Value Ada.PubKeyHash POSIXTime
        | Add Ada.PubKeyHash
        | Pay
        | Cancel

PlutusTx.unstableMakeIsData ''Input
PlutusTx.makeLift ''Input

--------------------------------------------------------------------------------
-- Helper gunctions

{-# INLINABLE scriptOutputsAt' #-}
-- | Get the list of 'TxOut' outputs of the pending transaction at
--   a given script address.
scriptOutputsAt' :: Ledger.ScriptHash -> TxInfo -> [(OutputDatum, Value)]
scriptOutputsAt' h p =
    let flt TxOut{txOutDatum=d, txOutAddress=Ledger.Address.Address (ScriptCredential s) _, txOutValue} | s == h = Just (d, txOutValue)
        flt _ = Nothing
    in mapMaybe flt (txInfoOutputs p)

{-# INLINABLE valueLockedBy #-}
-- | Get the total value locked by the given validator in this transaction.
valueLockedBy :: TxInfo -> Ledger.ScriptHash  -> Value
valueLockedBy ptx h =
    let outputs = map snd (scriptOutputsAt' h ptx)
    in mconcat outputs

{-# INLINABLE scriptInputsAt #-}
-- | Get the list of 'TxOut' outputs of the pending transaction at
--   a given script address.
scriptInputsAt :: Ledger.ScriptHash -> TxInfo -> [(OutputDatum, Value)]
scriptInputsAt h p =
    let flt TxOut{txOutDatum=d, txOutAddress=Ledger.Address.Address (ScriptCredential s) _, txOutValue} | s == h = Just (d, txOutValue)
        flt _ = Nothing
    in mapMaybe flt (map txInInfoResolved $ txInfoInputs p)

{-# INLINABLE scriptInputValue #-}
scriptInputValue :: TxInfo -> Ledger.ScriptHash -> Value
scriptInputValue ptx h = mconcat (map snd (scriptInputsAt h ptx))

{-# INLINABLE ownHashes #-}
-- | Get the validator and datum hashes of the output that is curently being validated
ownHashes :: ScriptContext -> (Ledger.ScriptHash, OutputDatum)
ownHashes (findOwnInput -> Just TxInInfo{txInInfoResolved=TxOut{txOutAddress=Ledger.Address.Address (ScriptCredential s) _, txOutDatum=d}}) = (s,d)
ownHashes _ = traceError "Can't get validator and datum hashes"

{-# INLINABLE ownHash' #-}
-- | Get the hash of the validator script that is currently being validated.
ownHash' :: ScriptContext -> Ledger.ScriptHash
ownHash' p = fst (ownHashes p)

{-# INLINABLE getOutputDatum #-}
getOutputDatum :: ScriptContext -> OutputDatum
getOutputDatum s = fst $ PlutusTx.List.head (Plutus.Script.Utils.V2.Contexts.scriptOutputsAt (Plutus.Script.Utils.V2.Contexts.ownHash s) (scriptContextTxInfo s))

-- | Multisig validator
-- The business logic is in here!
{-# INLINABLE multiSigValidator #-}
multiSigValidator :: MultiSigParams -> Label -> Input -> ScriptContext -> Bool
multiSigValidator param lbl inp sc =
  -- Depending on the label (state of the contract) and the input
  case (lbl, inp) of
  -- If the contract is in the holding state,
  (Holding, Propose v pkh deadline) ->
    let outDatum = getOutputDatum sc -- Get the output datum from the script context
        oldValue = scriptInputValue (scriptContextTxInfo sc) (ownHash' sc) -- Get the value of the inputs
        newValue = valueLockedBy (scriptContextTxInfo sc) (ownHash' sc) -- Get the value of the outputs
    in
       oldValue == newValue          -- The value of the input and output should be the same
       && oldValue `geq` v           -- The value of the input should be greater than the value of the proposal
       && v `geq` minimumValue param -- The value of the proposal should be greater than the minimum value
       &&
        case outDatum of           -- Depending on the output datum
        OutputDatum (Datum newDatum) -> case fromBuiltinData newDatum of
            Just Holding -> False  -- If the output datum is holding, we can't propose so we return false
            Just (Collecting v' pkh' deadline' sigs') -> -- If the output datum is collecting
              v == v' -- The value of the proposal should be the same as the value of the collecting state
              && pkh == pkh' -- The public key hash of the proposal should be the same as the public key hash of the collecting state
              && deadline == deadline' -- The deadline of the proposal should be the same as the deadline of the collecting state
              && sigs' == [] -- The list of signatures should be empty
            Nothing -> -- If we can't decode the output datum, we return false
              traceError "Failed to decode output datum"
        OutputDatumHash _ -> -- If the output datum is a hash, we return false
            traceError "Expected OutputDatum, got OutputDatumHash"
        NoOutputDatum -> -- If there is no output datum, we return false
            traceError "Expected OutputDatum, got NoOutputDatum"

  (Holding, _) -> False -- If the contract is in the holding state, we can't do anything else than propose

  (Collecting _ _ _ _, Propose _ _ _) -> False -- If the contract is in the collecting state, we can't propose

  (Collecting v pkh deadline sigs, Add sig) -> -- If the contract is in the collecting state
    let oldValue = scriptInputValue (scriptContextTxInfo sc) (ownHash' sc) -- Get the value of the inputs
        newValue = valueLockedBy (scriptContextTxInfo sc) (ownHash' sc) -- Get the value of the outputs
        outDatum = getOutputDatum sc -- Get the output datum from the script context
    in oldValue == newValue -- The value of the input and output should be the same
      && txSignedBy (scriptContextTxInfo sc) sig -- The transaction should be signed by the public key hash
      && PlutusTx.elem sig (signatories param) -- The public key hash should be in the list of signatories
      && case outDatum of -- Depending on the output datum
      OutputDatum (Datum newDatum) -> case fromBuiltinData newDatum of -- If we can decode the output datum
          Just Holding -> False -- If the output datum is holding, we can't add a signature so we return false
          Just (Collecting v' pkh' deadline' sigs') ->
            v == v' -- The value of the collecting state should be the same as the value of the proposal
            && pkh == pkh' -- The public key hash of the collecting state should be the same as the public key hash of the proposal
            && deadline == deadline' -- The deadline of the collecting state should be the same as the deadline of the proposal
            && sigs' == sig : sigs -- The list of signatures should be the same as the list of signatures of the collecting state with the new signature added
          Nothing -> -- If we can't decode the output datum, we return false
            traceError "Failed to decode output datum"
      OutputDatumHash _ -> -- If the output datum is a hash, we return false
          traceError "Expected OutputDatum, got OutputDatumHash"
      NoOutputDatum -> -- If there is no output datum, we return false
          traceError "Expected OutputDatum, got NoOutputDatum"

  (Collecting v pkh _deadline sigs, Pay) -> -- If the contract is in the collecting state
    let outDatum = getOutputDatum sc -- Get the output datum from the script context
        oldValue = scriptInputValue (scriptContextTxInfo sc) (ownHash' sc) -- Get the value of the inputs
        newValue = valueLockedBy (scriptContextTxInfo sc) (ownHash' sc) -- Get the value of the outputs
    in length sigs >= minNumSignatures param -- The number of signatures should be greater or equal to the minimum number of signatures
       && case outDatum of -- Depending on the output datum
        OutputDatum (Datum newDatum) -> case fromBuiltinData newDatum of
            Just Holding -> -- If the output datum is holding
              valuePaidTo (scriptContextTxInfo sc) pkh == v -- The value paid to the public key hash should be the same as the value of the proposal
              && oldValue == (v + newValue) -- The value of the inputs should be the same as the value of the proposal plus the value of the outputs
            Just (Collecting _ _ _ _) -> False -- The output datum cannot be collecting
            Nothing -> -- If we can't decode the output datum, we return false
              False
        OutputDatumHash _ -> -- If the output datum is a hash, we return false
            traceError "Expected OutputDatum, got OutputDatumHash"
        NoOutputDatum -> -- If there is no output datum, we return false
            traceError "Expected OutputDatum, got NoOutputDatum"

  (Collecting _v _pkh deadline _sigs, Cancel) -> -- If the contract is in the collecting state
    let outDatum = getOutputDatum sc -- Get the output datum from the script context
        oldValue = scriptInputValue (scriptContextTxInfo sc) (ownHash' sc) -- Get the value of the inputs
        newValue = valueLockedBy (scriptContextTxInfo sc) (ownHash' sc) -- Get the value of the outputs
    in oldValue == newValue -- The value of the input and output should be the same
      && case outDatum of -- Depending on the output datum
      OutputDatum (Datum newDatum) -> case fromBuiltinData newDatum of
          Just Holding -> (deadline - 1000) `Interval.before` txInfoValidRange (scriptContextTxInfo sc) -- The deadline should be before the current slot
          Just (Collecting _ _ _ _) -> False -- The output datum cannot be collecting
          Nothing -> -- If we can't decode the output datum, we return false
            traceError "Failed to decode output datum"
      OutputDatumHash _ -> -- If the output datum is a hash, we return false
          traceError "Expected OutputDatum, got OutputDatumHash"
      NoOutputDatum -> -- If there is no output datum, we return false
          traceError "Expected OutputDatum, got NoOutputDatum"

data MultiSig
instance Scripts.ValidatorTypes MultiSig where
  type RedeemerType MultiSig = Input
  type DatumType MultiSig = Label

typedValidator :: MultiSigParams -> V2.TypedValidator MultiSig
typedValidator = V2.mkTypedValidatorParam @MultiSig
    $$(PlutusTx.compile [|| multiSigValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.mkUntypedValidator

mkMultiSigAddress :: MultiSigParams -> Ledger.CardanoAddress
mkMultiSigAddress = validatorCardanoAddress testnet . typedValidator

toTxOutValue :: Value -> C.TxOutValue C.ConwayEra
toTxOutValue = either (error . show) C.toCardanoTxOutValue . C.toCardanoValue

toHashableScriptData :: (PlutusTx.ToData a) => a -> C.HashableScriptData
toHashableScriptData = C.unsafeHashableScriptData . C.fromPlutusData . PlutusTx.toData

toTxOutInlineDatum :: (PlutusTx.ToData a) => a -> C.TxOutDatum C.CtxTx C.ConwayEra
toTxOutInlineDatum = C.TxOutDatumInline C.BabbageEraOnwardsConway . toHashableScriptData

toValidityRange :: SlotConfig
  -> Interval.Interval POSIXTime
  -> (C.TxValidityLowerBound C.ConwayEra, C.TxValidityUpperBound C.ConwayEra)
toValidityRange slotConfig =
  either (error . show) id . C.toCardanoValidityRange . posixTimeRangeToContainedSlotRange slotConfig

mkDatumUpdateTxOut :: Label -> TxOut -> C.TxOut C.CtxTx C.ConwayEra
mkDatumUpdateTxOut datum txout =
  case C.toCardanoAddressInEra testnet (txOutAddress txout) of
    Left _ -> error "Couldn't decode address"
    Right addr -> C.TxOut
                    addr
                    (toTxOutValue (txOutValue txout))
                    (toTxOutInlineDatum datum)
                    C.ReferenceScriptNone

checkEmpty :: [a] -> [a]
checkEmpty [] = error "empty list"
checkEmpty x = x

--------------------------------------------------------------------------------
-- Off-chain code

-- | Build a transaction to propose a payment to the multisig contract.
mkProposeTx :: (E.MonadEmulator m)
  => MultiSigParams
  -- ^ Multisig Params
  -> Ledger.CardanoAddress
  -- ^ Target Wallet Address
  -> Value
  -- ^ How much money to pay in
  -> POSIXTime
  -- ^ Deadline for the money to be paid
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkProposeTx multisig wallet value deadline = do
  let multisigAddr = mkMultiSigAddress multisig
  unspentOutputs <- E.utxosAt multisigAddr
  slotConfig <- asks pSlotConfig
  let
    pkh = Ledger.PaymentPubKeyHash $ fromJust $ Ledger.cardanoPubKeyHash wallet
    uPkh = unPaymentPubKeyHash pkh
    validityRange = toValidityRange slotConfig $ Interval.to $ deadline - 1000
    -- Creation of the new label with a collecting state for a value payment
    -- to the uPkh wallet with a deadline deadline, and an empty signature list to start
    newLabel = Collecting value uPkh deadline []
    witnessHeader =
      C.toCardanoTxInScriptWitnessHeader
        (Ledger.getValidator <$> Scripts.vValidatorScript (typedValidator multisig))

    -- Creating the redeemer to move the contract from holding to collecting state
    redeemer = toHashableScriptData $ Propose value uPkh deadline
    witness =
        C.BuildTxWith $
          C.ScriptWitness C.ScriptWitnessForSpending $
            witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits

    txIns = (,witness) <$> Map.keys (C.unUTxO unspentOutputs)
    txOuts' = map C.fromCardanoTxOutToPV2TxInfoTxOut' $ Map.elems (C.unUTxO unspentOutputs)
    txOuts = checkEmpty $ map (mkDatumUpdateTxOut newLabel) txOuts'

    utx =
      E.emptyTxBodyContent
      { C.txIns = txIns
        , C.txOuts = txOuts
        , C.txValidityLowerBound = fst validityRange
        , C.txValidityUpperBound = snd validityRange
      }
    in pure (C.CardanoBuildTx utx, unspentOutputs)

-- Propose endpoint
propose :: (E.MonadEmulator m)
  => MultiSigParams
  -> Ledger.CardanoAddress
  -> Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> Value
  -> POSIXTime
  -> m ()
propose multisig wallet target privateKey value deadline = do
  E.logInfo @String $ "Proposing" <> show value <> "to: " <> show target <> "by: " <> show deadline
  (utx, utxoIndex) <- mkProposeTx multisig target value deadline
  void $ E.submitTxConfirmed utxoIndex wallet [Ledger.Address.toWitness privateKey] utx

-- | Build a transaction to add a signature to the multisig contract.

-- Build the datum for the new state of the contract after adding a signature
mkAddSigDatum :: Ada.PubKeyHash -> TxOut -> Label
mkAddSigDatum sig txout =
  case txOutDatum txout of
    OutputDatum (Datum newDatum) ->
      case fromBuiltinData newDatum of
          Just Holding -> error "Can't add signature to holding state"
          Just (Collecting v pkh deadline sigs) ->
            Collecting v pkh deadline (sig : sigs)
          Nothing ->
            error "Failed to decode output datum"
    OutputDatumHash _ ->
        error "Expected OutputDatum, got OutputDatumHash"
    NoOutputDatum ->
        error "Expected OutputDatum, got NoOutputDatum"

-- helper: get the deadline from the output datum
getDeadline :: TxOut -> POSIXTime
getDeadline txout =
  case txOutDatum txout of
    OutputDatum (Datum newDatum) ->
      case fromBuiltinData newDatum of
          Just Holding -> error "Can't get deadline in holding state"
          Just (Collecting _ _ deadline _) -> deadline
          Nothing ->
            error "Failed to decode output datum"
    OutputDatumHash _ ->
        error "Expected OutputDatum, got OutputDatumHash"
    NoOutputDatum ->
        error "Expected OutputDatum, got NoOutputDatum"

-- Add a signature, to eventually reach the number of signature required
mkAddSigTx :: (E.MonadEmulator m)
  => MultiSigParams
  -- ^ Multisig Params
  -> Ledger.CardanoAddress
  -- ^ Wallet Address
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkAddSigTx multisig wallet = do
  let multisigAddr = mkMultiSigAddress multisig
  unspentOutputs <- E.utxosAt multisigAddr
  slotConfig <- asks pSlotConfig

  let
    pkh = Ledger.PaymentPubKeyHash $ fromJust $ Ledger.cardanoPubKeyHash wallet
    extraKeyWit = either (error . show) id $ C.toCardanoPaymentKeyHash pkh
    uPkh = unPaymentPubKeyHash pkh
    txOuts' = map C.fromCardanoTxOutToPV2TxInfoTxOut' $ Map.elems (C.unUTxO unspentOutputs)
    deadline = getDeadline $ head txOuts'
    validityRange = toValidityRange slotConfig $ Interval.to $ deadline - 1000
    witnessHeader =
      C.toCardanoTxInScriptWitnessHeader
        (Ledger.getValidator <$> Scripts.vValidatorScript (typedValidator multisig))
    redeemer = toHashableScriptData $ Add uPkh
    witness =
        C.BuildTxWith$
          C.ScriptWitness C.ScriptWitnessForSpending $
            witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits
    txIns = (,witness) <$> Map.keys (C.unUTxO unspentOutputs)

    datum = mkAddSigDatum uPkh (head txOuts')
    txOuts = map (mkDatumUpdateTxOut datum) txOuts'
    utx =
      E.emptyTxBodyContent
      { C.txIns = txIns
        , C.txOuts = txOuts
        , C.txValidityLowerBound = fst validityRange
        , C.txValidityUpperBound = snd validityRange
        , C.txExtraKeyWits = C.TxExtraKeyWitnesses C.AlonzoEraOnwardsConway [extraKeyWit]
      }
    in pure (C.CardanoBuildTx utx, unspentOutputs)

-- Add signature endpoint
addSig :: (E.MonadEmulator m)
  => MultiSigParams
  -> Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> m ()
addSig multisig wallet privateKey = do
  E.logInfo @String $ "Adding signature to contract of wallet: " <> show wallet
  (utx, utxoIndex) <- mkAddSigTx multisig wallet
  void $ E.submitTxConfirmed utxoIndex wallet [Ledger.Address.toWitness privateKey] utx

-- | Build a transaction to pay from the multisig contract.
mkPayUpdateTxOut :: Value -> TxOut -> C.TxOut C.CtxTx C.ConwayEra
mkPayUpdateTxOut vl txout =
  case C.toCardanoAddressInEra testnet (txOutAddress txout) of
    Left _ -> error "Couldn't decode address"
    Right addr -> C.TxOut
                    addr
                    (toTxOutValue ((txOutValue txout) <> (inv vl) ))
                    (toTxOutInlineDatum Holding)
                    C.ReferenceScriptNone

mkPayTxOut :: TxOut -> [ C.TxOut C.CtxTx C.ConwayEra ]
mkPayTxOut txout =
  case txOutDatum txout of
    OutputDatum (Datum newDatum) ->
      case fromBuiltinData newDatum of
          Just Holding -> error "Can't pay in holding state"
          Just (Collecting vl pkh _ _) ->
            [ C.TxOut
              ( C.makeShelleyAddressInEra
                  C.shelleyBasedEra
                  testnet
                  (either (error . show) C.PaymentCredentialByKey $ C.toCardanoPaymentKeyHash (Ledger.PaymentPubKeyHash pkh))
                  C.NoStakeAddress
              )
              (toTxOutValue vl)
              C.TxOutDatumNone
              C.ReferenceScriptNone
            ,
              mkPayUpdateTxOut vl txout ]
          Nothing ->
            error "Failed to decode output datum"
    OutputDatumHash _ ->
        error "Expected OutputDatum, got OutputDatumHash"
    NoOutputDatum ->
        error "Expected OutputDatum, got NoOutputDatum"

mkPayTx :: (E.MonadEmulator m)
  => MultiSigParams
  -- ^ Multisig Params
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkPayTx multisig = do
  let multisigAddr = mkMultiSigAddress multisig
  unspentOutputs <- E.utxosAt multisigAddr
  slotConfig <- asks pSlotConfig
  let
    txOuts' = map C.fromCardanoTxOutToPV2TxInfoTxOut' $ Map.elems (C.unUTxO unspentOutputs)
    deadline = getDeadline $ head txOuts'
    validityRange = toValidityRange slotConfig $ Interval.to $ deadline - 1000
    witnessHeader =
      C.toCardanoTxInScriptWitnessHeader
        (Ledger.getValidator <$> Scripts.vValidatorScript (typedValidator multisig))
    redeemer = toHashableScriptData Pay
    witness =
        C.BuildTxWith $
          C.ScriptWitness C.ScriptWitnessForSpending $
            witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits
    txIns = (,witness) <$> Map.keys (C.unUTxO unspentOutputs)
    txOuts = checkEmpty $ mkPayTxOut (head txOuts')
    utx =
      E.emptyTxBodyContent
      { C.txIns = txIns
        , C.txOuts = txOuts
        , C.txValidityLowerBound = fst validityRange
        , C.txValidityUpperBound = snd validityRange
      }
    in pure (C.CardanoBuildTx utx, unspentOutputs)

-- Pay endpoint
pay :: (E.MonadEmulator m)
  => MultiSigParams
  -> Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> m ()
pay multisig wallet privateKey = do
  E.logInfo @String $ "Paying signed multisig"
  (utx, utxoIndex) <- mkPayTx multisig
  void $ E.submitTxConfirmed utxoIndex wallet [Ledger.Address.toWitness privateKey] utx

-- | Build a transaction to cancel the multisig contract.
mkCancelTx :: (E.MonadEmulator m)
  => MultiSigParams
  -- ^ Multisig Params
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkCancelTx multisig = do
  let multisigAddr = mkMultiSigAddress multisig
  unspentOutputs <- E.utxosAt multisigAddr
  slotConfig <- asks pSlotConfig
  let
    txOuts' = map C.fromCardanoTxOutToPV2TxInfoTxOut' $ Map.elems (C.unUTxO unspentOutputs)
    deadline = getDeadline $ head txOuts'
    validityRange = toValidityRange slotConfig $ Interval.from $ deadline
    witnessHeader =
      C.toCardanoTxInScriptWitnessHeader
        (Ledger.getValidator <$> Scripts.vValidatorScript (typedValidator multisig))
    redeemer = toHashableScriptData Cancel
    witness =
        C.BuildTxWith $
          C.ScriptWitness C.ScriptWitnessForSpending $
            witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits
    txIns = (,witness) <$> Map.keys (C.unUTxO unspentOutputs)
    datum = Holding
    txOuts = map (mkDatumUpdateTxOut datum) txOuts'
    utx =
      E.emptyTxBodyContent
      { C.txIns = txIns
        , C.txOuts = txOuts
        , C.txValidityLowerBound = fst validityRange
        , C.txValidityUpperBound = snd validityRange
      }
    in pure (C.CardanoBuildTx utx, unspentOutputs)

-- Cancel endpoint
cancel :: (E.MonadEmulator m)
  => MultiSigParams
  -> Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> m ()
cancel multisig wallet privateKey = do
  E.logInfo @String $ "Adding signature to contract of wallet: " <> show wallet
  (utx, utxoIndex) <- mkCancelTx multisig
  void $ E.submitTxConfirmed utxoIndex wallet [Ledger.Address.toWitness privateKey] utx

-- | Build a transaction to donate to the multisig contract.
-- CURRENTLY UNUSED
-- 
-- mkDonateTx :: SlotConfig
--   -> MultiSigParams
--   -- ^ The multisig contract
--   -> Ledger.CardanoAddress
--   -- ^ Wallet address
--   -> Value
--   -- ^ How much money to pay in
--   -> (C.CardanoBuildTx, Ledger.UtxoIndex)
-- mkDonateTx _slotConfig multisig _wallet vl =
--   let multisigAddr = mkMultiSigAddress multisig
--       txOut = C.TxOut multisigAddr (toTxOutValue vl) C.TxOutDatumNone C.ReferenceScriptNone
--       -- (toTxOutInlineDatum pkh) C.ReferenceScriptNone
--       utx =
--         E.emptyTxBodyContent
--           { C.txOuts = [txOut]
--           }
--       utxoIndex = mempty
--    in (C.CardanoBuildTx utx, utxoIndex)

-- donate :: (E.MonadEmulator m)
--   => MultiSigParams
--   -> Ledger.CardanoAddress
--   -> Ledger.PaymentPrivateKey
--   -> Value
--   -> m ()
-- donate multisig wallet privateKey vl = do
--   E.logInfo @String $ "Donate " <> show vl <> " to the script"
--   slotConfig <- asks pSlotConfig
--   let (utx, utxoIndex) = mkDonateTx slotConfig multisig wallet vl
--   void $ E.submitTxConfirmed utxoIndex wallet [Ledger.Address.toWitness privateKey] utx

-- | Build a transaction to open the multisig contract.
mkOpenTx :: MultiSigParams
  -- ^ The multisig contract
  -> Value
  -- ^ How much money to pay in
  -> (C.CardanoBuildTx, Ledger.UtxoIndex)
mkOpenTx multisig vl =
  let multisigAddr = mkMultiSigAddress multisig
      datum = Holding
      txOut = C.TxOut multisigAddr (toTxOutValue vl) (toTxOutInlineDatum datum) C.ReferenceScriptNone
      utx =
        E.emptyTxBodyContent
          { C.txOuts = [txOut]
          }
      utxoIndex = mempty
   in (C.CardanoBuildTx utx, utxoIndex)

-- Open endpoint
open :: (E.MonadEmulator m)
  => MultiSigParams
  -> Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> Value
  -> m ()
open multisig wallet privateKey vl = do
  E.logInfo @String $ "Open MultiSig with value: " <> show vl
  let (utx, utxoIndex) = mkOpenTx multisig vl
  void $ E.submitTxConfirmed utxoIndex wallet [Ledger.Address.toWitness privateKey] utx

-- To get the coverage 
-- covIdx :: CoverageIndex
-- covIdx = getCovIdx $$(PlutusTx.compile [||multiSigValidator||])
