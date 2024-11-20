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

-- | A general-purpose escrow contract in Plutus
module Contract.MultiSig
{-
  (
  -- $escrow
  Escrow,
  EscrowError (..),
  AsEscrowError (..),
  EscrowParams (..),
  EscrowTarget (..),
  payToScriptTarget,
  payToPaymentPubKeyTarget,
  targetTotal,
  payRedeemRefund,
  typedValidator,

  -- * Actions
  pay,
  redeem,
  refund,
  badRefund,
  RedeemFailReason (..),
  RedeemSuccess (..),
  RefundSuccess (..),

  -- * Exposed for test endpoints
  Action (..),
  Datum,
  validate,

  -- * Coverage
  covIdx,
) -} where

import Control.Lens (makeClassyPrisms)
import Control.Monad (void)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.RWS.Class (asks)
import Data.Map qualified as Map

import Cardano.Api qualified as C
import Cardano.Api.Shelley qualified as C
import PlutusTx (ToData)
import PlutusTx qualified
import PlutusTx.Code (getCovIdx)
import PlutusTx.Coverage (CoverageIndex)
import PlutusTx.Prelude ()
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.TH (loadFromFile)

import Cardano.Node.Emulator qualified as E
import Cardano.Node.Emulator.Internal.Node (
  SlotConfig,
  pSlotConfig,
  posixTimeRangeToContainedSlotRange,
 )
import Cardano.Node.Emulator.Test (testnet)
import Data.Maybe (fromJust)
import Ledger (POSIXTime, PaymentPubKeyHash (unPaymentPubKeyHash), TxId, getCardanoTxId)
import Ledger qualified
import Ledger.Address (toWitness, Address (..))
import Ledger.Tx.CardanoAPI qualified as C
import Ledger.Typed.Scripts (validatorCardanoAddress)
import Ledger.Typed.Scripts qualified as Scripts
import Plutus.Script.Utils.Scripts (ValidatorHash, datumHash, validatorHash)
import Plutus.Script.Utils.V2.Contexts (
  ScriptContext (ScriptContext, scriptContextTxInfo),
  TxInfo,
  scriptOutputsAt,
  txInfoValidRange,
  txSignedBy,
  ownHash,
 )
import Plutus.Script.Utils.V2.Typed.Scripts qualified as V2
import Plutus.Script.Utils.V2.Scripts qualified as V2

import Plutus.Script.Utils.Value (Value, geq, lt)
import PlutusLedgerApi.V1.Interval qualified as Interval
import PlutusLedgerApi.V2 (Datum (Datum), Credential(..), OutputDatum (..))
import PlutusLedgerApi.V2.Contexts (valuePaidTo)
import PlutusLedgerApi.V2.Tx
    ( OutputDatum, TxOut(TxOut, txOutValue, txOutDatum, txOutAddress) )
import PlutusLedgerApi.V2.Contexts
import qualified Plutus.Script.Utils.Value as Ada
import qualified PlutusTx.Builtins as PlutusTx
import qualified Ledger as Ada
import PlutusTx.Prelude (Eq ((==)))
import qualified Data.Aeson.Encoding as Map
import Cardano.Api (ConwayEra)
-- (OutputDatum (OutputDatum))
import Data.Either (fromRight)
import qualified Plutus.Script.Utils.Ada as Ada
import qualified PlutusTx.List

import Debug.Trace qualified as Trace


fromCardanoTxOutDatum' :: C.TxOutDatum C.CtxUTxO era -> OutputDatum
fromCardanoTxOutDatum' C.TxOutDatumNone       =
    NoOutputDatum
fromCardanoTxOutDatum' (C.TxOutDatumHash _ h) =
    OutputDatumHash $ Ada.DatumHash $ PlutusTx.toBuiltin (C.serialiseToRawBytes h)
fromCardanoTxOutDatum' (C.TxOutDatumInline _ d) =
    OutputDatum $ Datum $ C.fromCardanoScriptData d




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
    let flt TxOut{txOutDatum=d, txOutAddress=Address (ScriptCredential s) _, txOutValue} | s PlutusTx.== h = Just (d, txOutValue)
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
    let flt TxOut{txOutDatum=d, txOutAddress=Address (ScriptCredential s) _, txOutValue} | s PlutusTx.== h = Just (d, txOutValue)
        flt _ = Nothing
    in PlutusTx.mapMaybe flt (PlutusTx.map txInInfoResolved $ txInfoInputs p)

{-# INLINABLE scriptInputValue #-}
scriptInputValue :: TxInfo -> Ledger.ScriptHash -> Value
scriptInputValue ptx h = mconcat (PlutusTx.map snd (scriptInputsAt h ptx))

{-# INLINABLE ownHashes #-}
-- | Get the validator and datum hashes of the output that is curently being validated
ownHashes :: ScriptContext -> (Ledger.ScriptHash, OutputDatum)
ownHashes (findOwnInput -> Just TxInInfo{txInInfoResolved=TxOut{txOutAddress=Address (ScriptCredential s) _, txOutDatum=d}}) = (s,d)
ownHashes _ = PlutusTx.traceError "Lg" -- "Can't get validator and datum hashes"

{-# INLINABLE ownHash' #-}
-- | Get the hash of the validator script that is currently being validated.
ownHash' :: ScriptContext -> Ledger.ScriptHash
ownHash' p = fst (ownHashes p)

{-# INLINABLE getOutputDatum #-}
getOutputDatum :: ScriptContext -> OutputDatum
getOutputDatum s = fst $ PlutusTx.List.head (scriptOutputsAt (ownHash s) (scriptContextTxInfo s))

-- scriptOutputsAt

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
         
  (Collecting v pkh deadline sigs, Pay) ->
    let outDatum = getOutputDatum sc
        oldValue = scriptInputValue (scriptContextTxInfo sc) (ownHash' sc)
        newValue = valueLockedBy (scriptContextTxInfo sc) (ownHash' sc)
    in PlutusTx.length sigs PlutusTx.>= minNumSignatures param
       PlutusTx.&& case outDatum of
        OutputDatum (Datum newDatum) -> case PlutusTx.fromBuiltinData newDatum of
            Just Holding -> True
              -- valuePaidTo (scriptContextTxInfo sc) pkh PlutusTx.== v
              -- PlutusTx.&& oldValue PlutusTx.== (v PlutusTx.+ newValue)
            Just (Collecting _ _ _ _) -> True
            Nothing ->
              True
        OutputDatumHash _ ->
            PlutusTx.traceError "Expected OutputDatum, got OutputDatumHash"
        NoOutputDatum ->
            PlutusTx.traceError "Expected OutputDatum, got NoOutputDatum"
           
  (Collecting v pkh deadline sigs, Cancel) ->
    let outDatum = snd (ownHashes sc)
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

{-
mkDatumUpdateTxOut' :: Ledger.CardanoAddress -> Label -> Value -> TxOut -> C.TxOut C.CtxTx C.ConwayEra
mkDatumUpdateTxOut' address datum value txout =
                  C.TxOut
                    address
                    (toTxOutValue (txOutValue txout))
                    -- (toTxOutValue value)
                    -- C.TxOutDatumNone
                    (toTxOutInlineDatum datum)
                    C.ReferenceScriptNone
-}

checkEmpty :: [a] -> [a]
checkEmpty [] = error "empty list"
checkEmpty x = x

-- Simple propose offchain
-- we could check that we are mapping over a single contract here to make this better
-- no error handling for the moment
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
  -- current <- fst <$> E.currentTimeRange
  let
    pkh = Ledger.PaymentPubKeyHash $ fromJust $ Ledger.cardanoPubKeyHash wallet
    uPkh = unPaymentPubKeyHash pkh
    validityRange = toValidityRange slotConfig $ Interval.to $ deadline - 1000
    newLabel = Collecting value uPkh deadline []
    witnessHeader =
      C.toCardanoTxInScriptWitnessHeader
        (Ledger.getValidator <$> Scripts.vValidatorScript (typedValidator multisig))
    redeemer = toHashableScriptData $ Propose value uPkh deadline
    witness =
        C.BuildTxWith $
          C.ScriptWitness C.ScriptWitnessForSpending $
            witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits
            -- (C.ScriptDatumForTxIn (toHashableScriptData newLabel)) redeemer C.zeroExecutionUnits
    txIns = (,witness) <$> Map.keys (C.unUTxO unspentOutputs)
    txOuts' = map C.fromCardanoTxOutToPV2TxInfoTxOut' $ Map.elems (C.unUTxO unspentOutputs)
    txOuts = checkEmpty $ map (mkDatumUpdateTxOut newLabel) txOuts'
   --  txOuts = checkEmpty $ map (mkDatumUpdateTxOut' multisigAddr newLabel value) txOuts'
    utx =
      E.emptyTxBodyContent
      { C.txIns = txIns
        , C.txOuts = txOuts
        , C.txValidityLowerBound = fst validityRange
        , C.txValidityUpperBound = snd validityRange
      }
    -- utxoIndex = mempty
    in pure (C.CardanoBuildTx utx, unspentOutputs)

propose
  :: (E.MonadEmulator m)
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
  void $ E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx

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
-- TODO: I think I need to add signature additionally here
-- TODO: We should get the deadline from the datum
mkAddSigTx
  :: (E.MonadEmulator m)
  => MultiSigParams
  -- ^ Multisig Params
  -> Ledger.CardanoAddress
  -- ^ Wallet Address
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkAddSigTx multisig wallet = do
  let multisigAddr = mkMultiSigAddress multisig
  unspentOutputs <- E.utxosAt multisigAddr
  slotConfig <- asks pSlotConfig
  -- current <- fst <$> E.currentTimeRange
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
--     lst = Trace.trace (show txOuts') txOuts'
--    datum = mkAddSigDatum uPkh (head lst)
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

addSig
  :: (E.MonadEmulator m)
  => MultiSigParams
  -> Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> m ()
addSig multisig wallet privateKey = do
  E.logInfo @String $ "Adding signature to contract of wallet: " <> show wallet
  (utx, utxoIndex) <- mkAddSigTx multisig wallet
  void $ E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx


mkPayTxOut :: TxOut -> C.TxOut C.CtxTx C.ConwayEra
mkPayTxOut txout =
  case txOutDatum txout of
    OutputDatum (Datum newDatum) ->
      case PlutusTx.fromBuiltinData newDatum of
          Just Holding -> error "Can't pay in holding state"
          Just (Collecting vl pkh _ _) ->
            C.TxOut
              ( C.makeShelleyAddressInEra
                  C.shelleyBasedEra
                  testnet
                  (either (error . show) C.PaymentCredentialByKey $ C.toCardanoPaymentKeyHash (Ledger.PaymentPubKeyHash pkh))
                  C.NoStakeAddress
              )
              (toTxOutValue vl)
              (toTxOutInlineDatum Holding)
              C.ReferenceScriptNone
          Nothing ->
            error "Failed to decode output datum"
    OutputDatumHash _ ->
        error "Expected OutputDatum, got OutputDatumHash"
    NoOutputDatum ->
        error "Expected OutputDatum, got NoOutputDatum"


-- TODO: We should get the deadline from the datum
mkPayTx
  :: (E.MonadEmulator m)
  => MultiSigParams
  -- ^ Multisig Params
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkPayTx multisig = do
  let multisigAddr = mkMultiSigAddress multisig
  unspentOutputs <- E.utxosAt multisigAddr
  slotConfig <- asks pSlotConfig
  -- current <- fst <$> E.currentTimeRange
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
    txOuts = checkEmpty $ map mkPayTxOut txOuts'
    --     lst = Trace.trace (show txOuts') txOuts'
--    datum = mkAddSigDatum uPkh (head lst)
    utx =
      E.emptyTxBodyContent
      { C.txIns = txIns
        , C.txOuts = txOuts
        , C.txValidityLowerBound = fst validityRange
        , C.txValidityUpperBound = snd validityRange
      }
    in pure (C.CardanoBuildTx utx, unspentOutputs)

pay
  :: (E.MonadEmulator m)
  => MultiSigParams
  -> Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> m ()
pay multisig wallet privateKey = do
  E.logInfo @String $ "Paying signed multisig"
  (utx, utxoIndex) <- mkPayTx multisig
  void $ E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx

mkCancelTx
  :: (E.MonadEmulator m)
  => MultiSigParams
  -- ^ Multisig Params
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkCancelTx multisig = do
  let multisigAddr = mkMultiSigAddress multisig
  unspentOutputs <- E.utxosAt multisigAddr
  slotConfig <- asks pSlotConfig
  -- current <- fst <$> E.currentTimeRange
  let
    txOuts' = map C.fromCardanoTxOutToPV2TxInfoTxOut' $ Map.elems (C.unUTxO unspentOutputs)
    deadline = getDeadline $ head txOuts'
    validityRange = toValidityRange slotConfig $ Interval.to $ deadline - 1000
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
    utxoIndex = mempty
    in pure (C.CardanoBuildTx utx, utxoIndex)

cancel
  :: (E.MonadEmulator m)
  => MultiSigParams
  -> Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> m ()
cancel multisig wallet privateKey = do
  E.logInfo @String $ "Adding signature to contract of wallet: " <> show wallet
  (utx, utxoIndex) <- mkCancelTx multisig
  void $ E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx

-- TODOL Check inlinedatum here
mkDonateTx
  :: SlotConfig
  -> MultiSigParams
  -- ^ The escrow contract
  -> Ledger.CardanoAddress
  -- ^ Wallet address
  -> Value
  -- ^ How much money to pay in
  -> (C.CardanoBuildTx, Ledger.UtxoIndex)
mkDonateTx slotConfig multisig wallet vl =
  let multisigAddr = mkMultiSigAddress multisig
      pkh = Ledger.PaymentPubKeyHash $ fromJust $ Ledger.cardanoPubKeyHash wallet
      txOut = C.TxOut multisigAddr (toTxOutValue vl) C.TxOutDatumNone C.ReferenceScriptNone
      -- (toTxOutInlineDatum pkh) C.ReferenceScriptNone
      utx =
        E.emptyTxBodyContent
          { C.txOuts = [txOut]
          }
      utxoIndex = mempty
   in (C.CardanoBuildTx utx, utxoIndex)

donate
  :: (E.MonadEmulator m)
  => MultiSigParams
  -> Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> Value
  -> m ()
donate multisig wallet privateKey vl = do
  E.logInfo @String $ "Donate " <> show vl <> " to the script"
  slotConfig <- asks pSlotConfig
  let (utx, utxoIndex) = mkDonateTx slotConfig multisig wallet vl
  void $ E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx


toCardanoPaymentCredential :: Credential -> Either Ada.ToCardanoError C.PaymentCredential
toCardanoPaymentCredential (PubKeyCredential _) = error "Should be script"
toCardanoPaymentCredential (ScriptCredential validatorHash) = C.PaymentCredentialByScript <$> C.toCardanoScriptHash validatorHash




mkOpenTx
  :: MultiSigParams
  -- ^ The escrow contract
  -> Value
  -- ^ How much money to pay in
  -> (C.CardanoBuildTx, Ledger.UtxoIndex)
mkOpenTx multisig vl =
  let multisigAddr = mkMultiSigAddress multisig
      datum = Holding
      txOut = C.TxOut multisigAddr (toTxOutValue vl) (toTxOutInlineDatum datum) C.ReferenceScriptNone
      -- (toTxOutInlineDatum datum)
      --  C.TxOutDatumNone
      utx =
        E.emptyTxBodyContent
          { C.txOuts = [txOut]
          }
      utxoIndex = mempty
   in (C.CardanoBuildTx utx, utxoIndex)


open
  :: (E.MonadEmulator m)
  => MultiSigParams
  -> Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> Value
  -> m ()
open multisig wallet privateKey vl = do
  E.logInfo @String $ "Open MultiSig with value: " <> show vl
  slotConfig <- asks pSlotConfig
  let (utx, utxoIndex) = mkOpenTx multisig vl
  void $ E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx

covIdx :: CoverageIndex
covIdx = getCovIdx $$(PlutusTx.compile [||multiSigValidator||])




-- Collecting Value Ada.PubKeyHash POSIXTime [Ada.PubKeyHash]


{-
mkOpenTx
  :: MultiSigParams
  -- ^ The escrow contract
  -> Value
  -- ^ How much money to pay in
  -> (C.CardanoBuildTx, Ledger.UtxoIndex)
mkOpenTx multisig vl =
  let multisigAddr = mkMultiSigAddress multisig
      datum = Holding
      txOut = C.TxOut
                ( C.makeShelleyAddressInEra
                    C.shelleyBasedEra
                    testnet
                    (fromRight (error "couldn't get script credential") (toCardanoPaymentCredential $ Ada.cardanoAddressCredential multisigAddr))
                    C.NoStakeAddress
                )
                (toTxOutValue vl)
                (toTxOutInlineDatum datum)
                C.ReferenceScriptNone


        -- C.TxOut multisigAddr (toTxOutValue vl) (toTxOutInlineDatum datum) C.ReferenceScriptNone
      utx =
        E.emptyTxBodyContent
          { C.txOuts = [txOut]
          }
      utxoIndex = mempty
   in (C.CardanoBuildTx utx, utxoIndex)
-}
