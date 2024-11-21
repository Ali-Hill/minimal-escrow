{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Spec.MultiSig where

import Control.Lens (At (at), makeLenses, to, (%=), (.=), (^.))
import Control.Monad (void, when)
import Control.Monad.Trans (lift)
import Data.Default (Default (def))
import Data.Foldable (Foldable (fold, length, null), sequence_)
import Data.Map (Map)
import Data.Map qualified as Map
import GHC.Generics (Generic)

import Cardano.Api.Shelley (toPlutusData)
import Cardano.Node.Emulator qualified as E
import Cardano.Node.Emulator.Internal.Node.Params qualified as Params
import Cardano.Node.Emulator.Internal.Node.TimeSlot qualified as TimeSlot
import Cardano.Node.Emulator.Test (
  checkPredicateOptions,
  hasValidatedTransactionCountOfTotal,
  walletFundsChange,
  (.&&.),
 )
import Cardano.Node.Emulator.Test.Coverage (writeCoverageReport)
import Cardano.Node.Emulator.Test.NoLockedFunds (
  NoLockedFundsProof (nlfpMainStrategy, nlfpWalletStrategy),
  checkNoLockedFundsProofWithOptions,
  defaultNLFP,
 )
import Ledger (Slot, minAdaTxOutEstimated)
import Ledger qualified
import Ledger.Tx.CardanoAPI (fromCardanoSlotNo)
import Ledger.Typed.Scripts qualified as Scripts
import Ledger.Value.CardanoAPI qualified as Value
import Plutus.Script.Utils.Ada qualified as Ada
import Plutus.Script.Utils.Value (Value, geq)
import PlutusLedgerApi.V1.Time (POSIXTime)

import PlutusTx (fromData)
import PlutusTx.Monoid (inv)

import Cardano.Api (
  AddressInEra (AddressInEra),
  AllegraEraOnwards (AllegraEraOnwardsConway),
  IsShelleyBasedEra (shelleyBasedEra),
  TxOut (TxOut),
  TxValidityLowerBound (TxValidityLowerBound, TxValidityNoLowerBound),
  TxValidityUpperBound (TxValidityUpperBound),
  UTxO (unUTxO),
  toAddressAny,
 )
import Test.QuickCheck qualified as QC hiding ((.&&.))
import Test.QuickCheck.ContractModel (
  Action,
  Actions,
  ContractModel,
  DL,
  RunModel,
  action,
  anyActions_,
  assertModel,
  contractState,
  currentSlot,
  deposit,
  forAllDL,
  lockedValue,
  observe,
  symIsZero,
  utxo,
  viewContractState,
  viewModelState,
  wait,
  waitUntilDL,
  withdraw,
 )
import Test.QuickCheck.ContractModel qualified as QCCM
import Test.QuickCheck.ContractModel.ThreatModel (
  IsInputOrOutput (addressOf),
  ThreatModel,
  anyInputSuchThat,
  changeValidityRange,
  getRedeemer,
  shouldNotValidate,
 )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (
  Property,
  choose,
  frequency,
  testProperty,
 )

import Contract.MultiSig (MultiSigParams (..),
                          propose,
                          addSig,
                       --   donate,
                          cancel,
                          pay,
                          open
                         )

import Contract.MultiSig qualified as Impl



import Control.Monad.Except (catchError)

import Plutus.Contract.Test.Certification
import Plutus.Contract.Test.Certification.Run
import Test.QuickCheck.DynamicLogic qualified as QCD
import qualified Ledger
import qualified Plutus.Script.Utils.Value as Ada
import qualified Cardano.Node.Emulator as E

type Wallet = Integer

walletPubKeyHash :: Wallet -> Ledger.PubKeyHash
walletPubKeyHash =
    Ledger.pubKeyHash
    . Ledger.unPaymentPubKey
    . (E.knownPaymentPublicKeys !!)
    . pred
    . fromIntegral

-- We create five wallets for testing purposes
w1, w2, w3, w4, w5 :: Wallet
w1 = 1
w2 = 2
w3 = 3
w4 = 4
w5 = 5

walletAddress :: Wallet -> Ledger.CardanoAddress
walletAddress = (E.knownAddresses !!) . pred . fromIntegral

walletPaymentPubKeyHash :: Wallet -> Ledger.PaymentPubKeyHash
walletPaymentPubKeyHash =
  Ledger.PaymentPubKeyHash
    . Ledger.pubKeyHash
    . Ledger.unPaymentPubKey
    . (E.knownPaymentPublicKeys !!)
    . pred
    . fromIntegral

walletPrivateKey :: Wallet -> Ledger.PaymentPrivateKey
walletPrivateKey = (E.knownPaymentPrivateKeys !!) . pred . fromIntegral

-- Parameters for the multisig contract
modelParams :: MultiSigParams
modelParams = MultiSigParams
  { signatories = map walletPubKeyHash [1 .. 5]
  , minNumSignatures = 2
  , minimumValue = Ada.lovelaceValueOf 1000
  }

data MultiSigModel = MultiSigModel
  { _possible_signatories :: [Wallet],
    _signatures :: [Wallet],
    _minNumSignatures :: Integer,
    _minimumValue :: Integer,
    _target :: Wallet,
    _deadline :: Slot,
    _proposedValue :: Integer,
    _contractValue :: Integer
  }
  deriving (Eq, Show, Generic)

makeLenses ''MultiSigModel

options :: E.Options MultiSigModel
options =
  E.defaultOptions
    { E.params = Params.increaseTransactionLimits def
    -- , E.coverageIndex = Impl.covIdx
    }

instance ContractModel MultiSigModel where
  data Action MultiSigModel
    = Propose Integer Wallet Wallet Slot
    | AddSig Wallet
--    | Donate Wallet Integer
    | Cancel Wallet
    | Pay Wallet
    | Open Wallet Integer
    deriving (Show, Eq, Generic)

  initialState =
    MultiSigModel
      { _possible_signatories = [],
        _signatures = [],
        _minNumSignatures = 0,
        _minimumValue = 2,
        _target = 0,
        _deadline = 0,
        _proposedValue = 0,
        _contractValue = 0
      }

  nextState a = void $ case a of
    Propose v _w t s -> do
      target .= t
      proposedValue .= v
      deadline .= s
      wait 2
    AddSig w -> do
      signatures %= (w :)
      wait 1
{-    Donate w v -> do
      contractValue %= (+ v)
      withdraw (walletAddress w) (Ada.adaValueOf $ fromInteger v) -}
      wait 1
    Cancel _w -> do
      signatures .= []
      wait 1
    Pay _w -> do
      oldContractValue <- viewContractState contractValue
      target <- viewContractState target
      proposedValue <- viewContractState proposedValue
      deposit (walletAddress target) (Ada.adaValueOf $ fromInteger proposedValue)
      contractValue .= (oldContractValue - proposedValue)
      wait 1
    Open w v -> do
      contractValue %= (+ v)
      withdraw (walletAddress w) (Ada.adaValueOf $ fromInteger v)
      wait 1

-- To implement to really use Quickcheck dynamic and contract model
-- It defines when an action can be triggered or not
-- No worries, we'll also try to trigger then if you said it's not possible, sometimes, 👀
  precondition _s a = case a of
    Propose _v _w _t _s -> True
    AddSig _w -> True
 --   Donate w v -> True
    Cancel _w -> True
    Pay _w -> True
    Open _w _v -> True
   
  validFailingAction _ _ = False

instance RunModel MultiSigModel E.EmulatorM where
    perform _ cmd _ = lift $ act cmd


act :: Action MultiSigModel -> E.EmulatorM ()
act = \case
  Propose v w t s ->
    propose
      modelParams
      (walletAddress w)
      (walletAddress t)
      (walletPrivateKey w)
      (Ada.adaValueOf $ fromInteger v)
      (TimeSlot.slotToEndPOSIXTime def s)
  AddSig w ->
    addSig
      modelParams
      (walletAddress w)
      (walletPrivateKey w)
 {- Donate w v ->
    donate
      modelParams
      (walletAddress w)
      (walletPrivateKey w)
      (Ada.adaValueOf $ fromInteger v) -}
  Cancel w ->
    cancel
      modelParams
      (walletAddress w)
      (walletPrivateKey w)
  Pay w ->
    pay
      modelParams
      (walletAddress w)
      (walletPrivateKey w)
  Open w v ->
    open
      modelParams
      (walletAddress w)
      (walletPrivateKey w)
      (Ada.adaValueOf $ fromInteger v)

prop_MultiSig :: Actions MultiSigModel -> Property
prop_MultiSig = E.propRunActionsWithOptions options

unitTest1 :: DL MultiSigModel ()
unitTest1 = do
  action $ Open w1 1000
  waitUntilDL 12
  action $ Propose 10 w1 w2 20
  action $ AddSig w4
  action $ AddSig w5
  action $ Pay w4

prop_Check :: QC.Property
prop_Check = QC.withMaxSuccess 1 $ QC.noShrinking $ forAllDL unitTest1 prop_MultiSig


tests :: TestTree
tests =
  testGroup "Multisig tests"
    [ testGroup "Positive tests"
        [
          -- unit tests
          testProperty "unit test 1" prop_Check
        ],
      testGroup "Negative tests"
        [
        ] 
    ]

