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
import Plutus.Script.Utils.Scripts (ValidatorHash, datumHash)
import Plutus.Script.Utils.V2.Contexts (
  ScriptContext (ScriptContext, scriptContextTxInfo),
  TxInfo,
  scriptOutputsAt,
  txInfoValidRange,
  txSignedBy,
 )
import Plutus.Script.Utils.V2.Typed.Scripts qualified as V2
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
-- (OutputDatum (OutputDatum))

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

{-# INLINABLE ownHash #-}
-- | Get the hash of the validator script that is currently being validated.
ownHash :: ScriptContext -> Ledger.ScriptHash
ownHash p = fst (ownHashes p)

-- | Haskell version of the above agda code
{-# INLINABLE multiSigValidator #-}
multiSigValidator :: MultiSigParams -> Label -> Input -> ScriptContext -> Bool
multiSigValidator param lbl inp sc = case (lbl, inp) of
  (Holding, Propose v pkh deadline) ->
    let oldValue = scriptInputValue (scriptContextTxInfo sc) (ownHash sc)
        newValue = valueLockedBy (scriptContextTxInfo sc) (ownHash sc)
        outDatum = snd (ownHashes sc)
    in oldValue PlutusTx.== newValue
      PlutusTx.&& oldValue `geq` v
      PlutusTx.&& v `geq` minimumValue param -- instead of v >= 0
      PlutusTx.&& case outDatum of
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
    let oldValue = scriptInputValue (scriptContextTxInfo sc) (ownHash sc)
        newValue = valueLockedBy (scriptContextTxInfo sc) (ownHash sc)
        outDatum = snd (ownHashes sc)
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
    let outDatum = snd (ownHashes sc)
        oldValue = scriptInputValue (scriptContextTxInfo sc) (ownHash sc)
        newValue = valueLockedBy (scriptContextTxInfo sc) (ownHash sc)
    in PlutusTx.length sigs PlutusTx.>= minNumSignatures param
      PlutusTx.&& case outDatum of
      OutputDatum (Datum newDatum) -> case PlutusTx.fromBuiltinData newDatum of
          Just Holding ->
            valuePaidTo (scriptContextTxInfo sc) pkh PlutusTx.== v
            PlutusTx.&& oldValue PlutusTx.== (v PlutusTx.+ newValue)
          Just (Collecting _ _ _ _) -> False
          Nothing ->
            PlutusTx.traceError "Failed to decode output datum"
      OutputDatumHash _ ->
          PlutusTx.traceError "Expected OutputDatum, got OutputDatumHash"
      NoOutputDatum ->
          PlutusTx.traceError "Expected OutputDatum, got NoOutputDatum"

  (Collecting v pkh deadline sigs, Cancel) ->
    let outDatum = snd (ownHashes sc)
        oldValue = scriptInputValue (scriptContextTxInfo sc) (ownHash sc)
        newValue = valueLockedBy (scriptContextTxInfo sc) (ownHash sc)
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
