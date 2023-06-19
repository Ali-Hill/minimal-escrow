{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:debug-context #-}
-- {-# OPTIONS_GHC -g -fplugin-opt PlutusTx.Plugin:coverage-all #-}
-- | A general-purpose escrow contract in Plutus
module Contract.Escrow(
    -- $escrow
    Escrow
    , EscrowError(..)
    , AsEscrowError(..)
    , EscrowParams(..)
    , EscrowTarget(..)
    , payToScriptTarget
    , payToPaymentPubKeyTarget
    , targetTotal
    , typedValidator
    -- * Exposed for test endpoints
    , Action(..)
    -- * Coverage
    -- , covIdx
    ) where

import Control.Lens (_1, has, makeClassyPrisms, only, review)
import Control.Monad (void)
import Control.Monad.Error.Lens (throwing)
import Data.Aeson (FromJSON, ToJSON)
import GHC.Generics (Generic)

import PlutusTx qualified
import PlutusTx.Code
import PlutusTx.Coverage
import PlutusTx.Prelude hiding (Applicative (..), Semigroup (..), check, foldMap)

import Cardano.Node.Emulator.Params (pNetworkId)
import Ledger (POSIXTime, PaymentPubKeyHash (unPaymentPubKeyHash), TxId, getCardanoTxId)
import Ledger qualified as L
import Ledger.Interval (after, before)
import Ledger.Tx qualified as Tx
import Ledger.Tx.Constraints (TxConstraints)
import Ledger.Tx.Constraints qualified as Constraints
import Ledger.Tx.Constraints.ValidityInterval qualified as Interval
import Ledger.Typed.Scripts (TypedValidator)
import Ledger.Typed.Scripts qualified as Scripts
import Plutus.Contract
import Plutus.Script.Utils.Scripts (datumHash)
import Plutus.Script.Utils.V2.Contexts (ScriptContext (..), TxInfo (..), scriptOutputsAt, txInfoValidRange, txSignedBy)
import Plutus.Script.Utils.V2.Typed.Scripts qualified as V2
import Plutus.Script.Utils.Value (Value, geq, lt)
import Plutus.V2.Ledger.Api (Datum (Datum), DatumHash, ValidatorHash)
import Plutus.V2.Ledger.Contexts (valuePaidTo)
import Plutus.V2.Ledger.Tx (OutputDatum (OutputDatumHash))

import Prelude (Semigroup (..), foldMap)
import Prelude qualified as Haskell
import Cooked

import qualified Plutus.V1.Ledger.Interval as IntervalV1


type EscrowSchema =
        Endpoint "pay-escrow" Value
        .\/ Endpoint "redeem-escrow" ()
        .\/ Endpoint "refund-escrow" ()

data RedeemFailReason = DeadlinePassed | NotEnoughFundsAtAddress
    deriving stock (Haskell.Eq, Haskell.Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

data EscrowError =
    RedeemFailed RedeemFailReason
    | RefundFailed
    | EContractError ContractError
    deriving stock (Haskell.Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

makeClassyPrisms ''EscrowError

instance AsContractError EscrowError where
    _ContractError = _EContractError

-- $escrow
-- The escrow contract implements the exchange of value between multiple
-- parties. It is defined by a list of targets (public keys and script
-- addresses, each associated with a value). It works similar to the
-- crowdfunding contract in that the contributions can be made independently,
-- and the funds can be unlocked only by a transaction that pays the correct
-- amount to each target. A refund is possible if the outputs locked by the
-- contract have not been spent by the deadline. (Compared to the crowdfunding
-- contract, the refund policy is simpler because here because there is no
-- "collection period" during which the outputs may be spent after the deadline
-- has passed. This is because we're assuming that the participants in the
-- escrow contract will make their deposits as quickly as possible after
-- agreeing on a deal)
--
-- The contract supports two modes of operation, manual and automatic. In
-- manual mode, all actions are driven by endpoints that exposed via 'payEp'
-- 'redeemEp' and 'refundEp'. In automatic mode, the 'pay', 'redeem' and
-- 'refund'actions start immediately. This mode is useful when the escrow is
-- called from within another contract, for example during setup (collection of
-- the initial deposits).

-- | Defines where the money should go. Usually we have `d = Datum` (when
--   defining `EscrowTarget` values in off-chain code). Sometimes we have
--   `d = DatumHash` (when checking the hashes in on-chain code)
data EscrowTarget d =
    PaymentPubKeyTarget PaymentPubKeyHash Value
    | ScriptTarget ValidatorHash d Value
    deriving (Haskell.Functor)

PlutusTx.makeLift ''EscrowTarget

-- | An 'EscrowTarget' that pays the value to a public key address.
payToPaymentPubKeyTarget :: PaymentPubKeyHash -> Value -> EscrowTarget d
payToPaymentPubKeyTarget = PaymentPubKeyTarget

-- | An 'EscrowTarget' that pays the value to a script address, with the
--   given data script.
payToScriptTarget :: ValidatorHash -> Datum -> Value -> EscrowTarget Datum
payToScriptTarget = ScriptTarget

-- | Definition of an escrow contract, consisting of a deadline and a list of targets
data EscrowParams d =
    EscrowParams
        { escrowDeadline :: POSIXTime
        -- ^ Latest point at which the outputs may be spent.
        , escrowTargets  :: [EscrowTarget d]
        -- ^ Where the money should go. For each target, the contract checks that
        --   the output 'mkTxOutput' of the target is present in the spending
        --   transaction.
        } deriving (Haskell.Functor)

PlutusTx.makeLift ''EscrowParams

-- | The total 'Value' that must be paid into the escrow contract
--   before it can be unlocked
targetTotal :: EscrowParams d -> Value
targetTotal = Haskell.foldl (\vl tgt -> vl + targetValue tgt) mempty . escrowTargets

-- | The 'Value' specified by an 'EscrowTarget'
targetValue :: EscrowTarget d -> Value
targetValue = \case
    PaymentPubKeyTarget _ vl -> vl
    ScriptTarget _ _ vl      -> vl

-- | Create a 'Ledger.TxOut' value for the target
mkTx :: EscrowTarget Datum -> TxConstraints Action PaymentPubKeyHash
mkTx = \case
    PaymentPubKeyTarget pkh vl ->
        Constraints.mustPayToPubKey pkh vl
    ScriptTarget vs ds vl ->
        Constraints.mustPayToOtherScriptWithDatumInTx vs ds vl
        <> Constraints.mustIncludeDatumInTx ds

data Action = Redeem | Refund
  deriving (Haskell.Show)

instance Cooked.PrettyCooked Action where
  prettyCookedOpt _ Redeem = "Redeem"
  prettyCookedOpt _ Refund = "Refund"

instance Eq Action where
  {-# INLINEABLE (==) #-}
  Redeem == Redeem = True
  Refund == Refund = True
  _ == _ = False

data Escrow
instance Scripts.ValidatorTypes Escrow where
    type instance RedeemerType Escrow = Action
    type instance DatumType Escrow = L.PubKeyHash -- PaymentPubKeyHash

PlutusTx.unstableMakeIsData ''Action
PlutusTx.makeLift ''Action

{-# INLINABLE meetsTarget #-}
-- | @ptx `meetsTarget` tgt@ if @ptx@ pays at least @targetValue tgt@ to the
--   target address.
--
--   The reason why this does not require the target amount to be equal
--   to the actual amount is to enable any excess funds consumed by the
--   spending transaction to be paid to target addresses. This may happen if
--   the target address is also used as a change address for the spending
--   transaction, and allowing the target to be exceed prevents outsiders from
--   poisoning the contract by adding arbitrary outputs to the script address.
meetsTarget :: TxInfo -> EscrowTarget DatumHash -> Bool
meetsTarget ptx = \case
    PaymentPubKeyTarget pkh vl ->
        valuePaidTo ptx (unPaymentPubKeyHash pkh) `geq` vl
    ScriptTarget validatorHash dataValue vl ->
        case scriptOutputsAt validatorHash ptx of
            [(dataValue', vl')] ->
                traceIfFalse "dataValue" (dataValue' == (OutputDatumHash dataValue))
                && traceIfFalse "value" (vl' `geq` vl)
            _ -> False

{-# INLINABLE validate #-}
validate :: EscrowParams DatumHash -> L.PubKeyHash -> Action -> ScriptContext -> Bool
validate EscrowParams{escrowDeadline, escrowTargets} contributor action ScriptContext{scriptContextTxInfo} =
    case action of
        Redeem ->
            -- traceIfFalse "escrowDeadline-after" (escrowDeadline `after` txInfoValidRange scriptContextTxInfo)
            traceIfFalse "escrowDeadline-after" (IntervalV1.to escrowDeadline `IntervalV1.contains` txInfoValidRange scriptContextTxInfo)
            && traceIfFalse "meetsTarget" (all (meetsTarget scriptContextTxInfo) escrowTargets)
            -- traceIfFalse "meetsTarget" (all (meetsTarget scriptContextTxInfo) escrowTargets)
        Refund ->
            traceIfFalse "escrowDeadline-before" ((escrowDeadline - 1) `before` txInfoValidRange scriptContextTxInfo)
            && traceIfFalse "txSignedBy" (scriptContextTxInfo `txSignedBy` contributor)

typedValidator :: EscrowParams Datum -> V2.TypedValidator Escrow
typedValidator escrow = go (Haskell.fmap datumHash escrow) where
    go = V2.mkTypedValidatorParam @Escrow
        $$(PlutusTx.compile [|| validate ||])
        $$(PlutusTx.compile [|| wrap ||])
    wrap = Scripts.mkUntypedValidator

-- covIdx :: CoverageIndex
-- covIdx = getCovIdx $$(PlutusTx.compile [|| validate ||])
