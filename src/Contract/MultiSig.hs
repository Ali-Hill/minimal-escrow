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
{-# OPTIONS_GHC -g -fplugin-opt PlutusTx.Plugin:coverage-all #-}

module Contract.MultiSig where

import Control.Monad (void)
import Control.Monad.RWS.Class (asks)
import Data.Map qualified as Map

import Cardano.Api qualified as C
import Cardano.Api.Shelley qualified as C
import PlutusTx (ToData)
import PlutusTx qualified
import PlutusTx.Code (getCovIdx)
import PlutusTx.Coverage (CoverageIndex)
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

data MultiSigParams = MultiSigParams
  { signatories :: [Ada.PubKeyHash]
  , minNumSignatures :: Integer
  , minimumValue :: Value
  }

PlutusTx.makeLift ''MultiSigParams

data Label =
        Holding
        | Collecting Value Ada.PubKeyHash POSIXTime [Ada.PubKeyHash]

PlutusTx.unstableMakeIsData ''Label
PlutusTx.makeLift ''Label

data Input =
        Propose Value Ada.PubKeyHash POSIXTime
        | Add Ada.PubKeyHash
        | Pay
        | Cancel

PlutusTx.unstableMakeIsData ''Input
PlutusTx.makeLift ''Input

{-# INLINABLE scriptOutputsAt' #-}
-- | Get the list of 'TxOut' outputs of the pending transaction at
--   a given script address.
scriptOutputsAt' :: Ledger.ScriptHash -> TxInfo -> [(OutputDatum, Value)]
scriptOutputsAt' h p =
    let flt TxOut{txOutDatum=d, txOutAddress=Ledger.Address.Address (ScriptCredential s) _, txOutValue} | s PlutusTx.== h = Just (d, txOutValue)
        flt _ = Nothing
    in PlutusTx.mapMaybe flt (txInfoOutputs p)

{-# INLINABLE valueLockedBy #-}
-- | Get the total value locked by the given validator in this transaction.
valueLockedBy :: TxInfo -> Ledger.ScriptHash  -> Value
valueLockedBy ptx h =
    let outputs = PlutusTx.map snd (scriptOutputsAt' h ptx)
    in mconcat outputs

{-# INLINABLE scriptInputsAt #-}
-- | Get the list of 'TxOut' outputs of the pending transaction at
--   a given script address.
scriptInputsAt :: Ledger.ScriptHash -> TxInfo -> [(OutputDatum, Value)]
scriptInputsAt h p =
    let flt TxOut{txOutDatum=d, txOutAddress=Ledger.Address.Address (ScriptCredential s) _, txOutValue} | s PlutusTx.== h = Just (d, txOutValue)
        flt _ = Nothing
    in PlutusTx.mapMaybe flt (PlutusTx.map txInInfoResolved $ txInfoInputs p)

{-# INLINABLE scriptInputValue #-}
scriptInputValue :: TxInfo -> Ledger.ScriptHash -> Value
scriptInputValue ptx h = mconcat (PlutusTx.map snd (scriptInputsAt h ptx))

{-# INLINABLE ownHashes #-}
-- | Get the validator and datum hashes of the output that is curently being validated
ownHashes :: ScriptContext -> (Ledger.ScriptHash, OutputDatum)
ownHashes (findOwnInput -> Just TxInInfo{txInInfoResolved=TxOut{txOutAddress=Ledger.Address.Address (ScriptCredential s) _, txOutDatum=d}}) = (s,d)
ownHashes _ = PlutusTx.traceError "Lg" -- "Can't get validator and datum hashes"

{-# INLINABLE ownHash' #-}
-- | Get the hash of the validator script that is currently being validated.
ownHash' :: ScriptContext -> Ledger.ScriptHash
ownHash' p = fst (ownHashes p)

{-# INLINABLE getOutputDatum #-}
getOutputDatum :: ScriptContext -> OutputDatum
getOutputDatum s = fst $ PlutusTx.List.head (Plutus.Script.Utils.V2.Contexts.scriptOutputsAt (Plutus.Script.Utils.V2.Contexts.ownHash s) (scriptContextTxInfo s))

-- | Haskell version of the above agda code
{-# INLINABLE multiSigValidator #-}
multiSigValidator :: MultiSigParams -> Label -> Input -> ScriptContext -> Bool
multiSigValidator param lbl inp sc = case (lbl, inp) of
  (Holding, Propose v pkh deadline) ->
    let outDatum = getOutputDatum sc
        oldValue = scriptInputValue (scriptContextTxInfo sc) (ownHash' sc)
        newValue = valueLockedBy (scriptContextTxInfo sc) (ownHash' sc)
    in oldValue PlutusTx.== newValue
       PlutusTx.&& oldValue `geq` v
       PlutusTx.&& v `geq` minimumValue param -- instead of v >= 0
       PlutusTx.&&
        case outDatum of
        OutputDatum (Datum newDatum) -> case PlutusTx.fromBuiltinData newDatum of
            Just Holding -> False
            Just (Collecting v' pkh' deadline' sigs') ->
              v PlutusTx.== v'
              PlutusTx.&& pkh PlutusTx.== pkh'
              PlutusTx.&& deadline PlutusTx.== deadline'
              PlutusTx.&& sigs' PlutusTx.== []
            Nothing ->
              PlutusTx.traceError "Failed to decode output datum"
        OutputDatumHash _ ->
            PlutusTx.traceError "Expected OutputDatum, got OutputDatumHash"
        NoOutputDatum ->
            PlutusTx.traceError "Expected OutputDatum, got NoOutputDatum"

  (Holding, _) -> False

  (Collecting _ _ _ _, Propose _ _ _) -> False

  (Collecting v pkh deadline sigs, Add sig) ->
    let oldValue = scriptInputValue (scriptContextTxInfo sc) (ownHash' sc)
        newValue = valueLockedBy (scriptContextTxInfo sc) (ownHash' sc)
        outDatum = getOutputDatum sc
    in oldValue PlutusTx.== newValue
      PlutusTx.&& txSignedBy (scriptContextTxInfo sc) sig
      PlutusTx.&& PlutusTx.elem sig (signatories param)
      PlutusTx.&& case outDatum of
      OutputDatum (Datum newDatum) -> case PlutusTx.fromBuiltinData newDatum of
          Just Holding -> False
          Just (Collecting v' pkh' deadline' sigs') ->
            v PlutusTx.== v'
            PlutusTx.&& pkh PlutusTx.== pkh'
            PlutusTx.&& deadline PlutusTx.== deadline'
            PlutusTx.&& sigs' PlutusTx.== sig : sigs
          Nothing ->
            PlutusTx.traceError "Failed to decode output datum"
      OutputDatumHash _ ->
          PlutusTx.traceError "Expected OutputDatum, got OutputDatumHash"
      NoOutputDatum ->
          PlutusTx.traceError "Expected OutputDatum, got NoOutputDatum"

  (Collecting v pkh _deadline sigs, Pay) ->
    let outDatum = getOutputDatum sc
        oldValue = scriptInputValue (scriptContextTxInfo sc) (ownHash' sc)
        newValue = valueLockedBy (scriptContextTxInfo sc) (ownHash' sc)
    in PlutusTx.length sigs PlutusTx.>= minNumSignatures param
       PlutusTx.&& case outDatum of
        OutputDatum (Datum newDatum) -> case PlutusTx.fromBuiltinData newDatum of
            Just Holding ->
              valuePaidTo (scriptContextTxInfo sc) pkh PlutusTx.== v
              PlutusTx.&& oldValue PlutusTx.== (v PlutusTx.+ newValue)
            Just (Collecting _ _ _ _) -> False
            Nothing ->
              False
        OutputDatumHash _ ->
            PlutusTx.traceError "Expected OutputDatum, got OutputDatumHash"
        NoOutputDatum ->
            PlutusTx.traceError "Expected OutputDatum, got NoOutputDatum"

  (Collecting _v _pkh deadline _sigs, Cancel) ->
    let outDatum = getOutputDatum sc
        oldValue = scriptInputValue (scriptContextTxInfo sc) (ownHash' sc)
        newValue = valueLockedBy (scriptContextTxInfo sc) (ownHash' sc)
    in oldValue PlutusTx.== newValue
      PlutusTx.&& case outDatum of
      OutputDatum (Datum newDatum) -> case PlutusTx.fromBuiltinData newDatum of
          Just Holding -> (deadline PlutusTx.- 1000) `Interval.before` ((txInfoValidRange (scriptContextTxInfo sc)))
          Just (Collecting _ _ _ _) -> False
          Nothing ->
            PlutusTx.traceError "Failed to decode output datum"
      OutputDatumHash _ ->
          PlutusTx.traceError "Expected OutputDatum, got OutputDatumHash"
      NoOutputDatum ->
          PlutusTx.traceError "Expected OutputDatum, got NoOutputDatum"

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

toValidityRange
  :: SlotConfig
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

-- Simple propose offchain
-- Propose is used to start the process of gathering signatures
-- It moves the datum from holding to collecting state
mkProposeTx
  :: (E.MonadEmulator m)
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

mkAddSigDatum :: Ada.PubKeyHash -> TxOut -> Label
mkAddSigDatum sig txout =
  case txOutDatum txout of
    OutputDatum (Datum newDatum) ->
      case PlutusTx.fromBuiltinData newDatum of
          Just Holding -> error "Can't add signature to holding state"
          Just (Collecting v pkh deadline sigs) ->
            Collecting v pkh deadline (sig : sigs)
          Nothing ->
            error "Failed to decode output datum"
    OutputDatumHash _ ->
        error "Expected OutputDatum, got OutputDatumHash"
    NoOutputDatum ->
        error "Expected OutputDatum, got NoOutputDatum"

getDeadline :: TxOut -> POSIXTime
getDeadline txout =
  case txOutDatum txout of
    OutputDatum (Datum newDatum) ->
      case PlutusTx.fromBuiltinData newDatum of
          Just Holding -> error "Can't get deadline in holding state"
          Just (Collecting _ _ deadline _) -> deadline
          Nothing ->
            error "Failed to decode output datum"
    OutputDatumHash _ ->
        error "Expected OutputDatum, got OutputDatumHash"
    NoOutputDatum ->
        error "Expected OutputDatum, got NoOutputDatum"

-- Add sig to contract
-- Add a signature to the contract, to eventually reach the number of signature required

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

addSig :: (E.MonadEmulator m)
  => MultiSigParams
  -> Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> m ()
addSig multisig wallet privateKey = do
  E.logInfo @String $ "Adding signature to contract of wallet: " <> show wallet
  (utx, utxoIndex) <- mkAddSigTx multisig wallet
  void $ E.submitTxConfirmed utxoIndex wallet [Ledger.Address.toWitness privateKey] utx

mkPayUpdateTxOut :: Value -> TxOut -> C.TxOut C.CtxTx C.ConwayEra
mkPayUpdateTxOut vl txout =
  case C.toCardanoAddressInEra testnet (txOutAddress txout) of
    Left _ -> error "Couldn't decode address"
    Right addr -> C.TxOut
                    addr
                    (toTxOutValue ((txOutValue txout) <> (PlutusTx.inv vl) ))
                    (toTxOutInlineDatum Holding)
                    C.ReferenceScriptNone

mkPayTxOut :: TxOut -> [ C.TxOut C.CtxTx C.ConwayEra ]
mkPayTxOut txout =
  case txOutDatum txout of
    OutputDatum (Datum newDatum) ->
      case PlutusTx.fromBuiltinData newDatum of
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

pay :: (E.MonadEmulator m)
  => MultiSigParams
  -> Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> m ()
pay multisig wallet privateKey = do
  E.logInfo @String $ "Paying signed multisig"
  (utx, utxoIndex) <- mkPayTx multisig
  void $ E.submitTxConfirmed utxoIndex wallet [Ledger.Address.toWitness privateKey] utx

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

cancel :: (E.MonadEmulator m)
  => MultiSigParams
  -> Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> m ()
cancel multisig wallet privateKey = do
  E.logInfo @String $ "Adding signature to contract of wallet: " <> show wallet
  (utx, utxoIndex) <- mkCancelTx multisig
  void $ E.submitTxConfirmed utxoIndex wallet [Ledger.Address.toWitness privateKey] utx

mkDonateTx :: SlotConfig
  -> MultiSigParams
  -- ^ The multisig contract
  -> Ledger.CardanoAddress
  -- ^ Wallet address
  -> Value
  -- ^ How much money to pay in
  -> (C.CardanoBuildTx, Ledger.UtxoIndex)
mkDonateTx _slotConfig multisig _wallet vl =
  let multisigAddr = mkMultiSigAddress multisig
      txOut = C.TxOut multisigAddr (toTxOutValue vl) C.TxOutDatumNone C.ReferenceScriptNone
      -- (toTxOutInlineDatum pkh) C.ReferenceScriptNone
      utx =
        E.emptyTxBodyContent
          { C.txOuts = [txOut]
          }
      utxoIndex = mempty
   in (C.CardanoBuildTx utx, utxoIndex)

donate :: (E.MonadEmulator m)
  => MultiSigParams
  -> Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> Value
  -> m ()
donate multisig wallet privateKey vl = do
  E.logInfo @String $ "Donate " <> show vl <> " to the script"
  slotConfig <- asks pSlotConfig
  let (utx, utxoIndex) = mkDonateTx slotConfig multisig wallet vl
  void $ E.submitTxConfirmed utxoIndex wallet [Ledger.Address.toWitness privateKey] utx

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

covIdx :: CoverageIndex
covIdx = getCovIdx $$(PlutusTx.compile [||multiSigValidator||])
