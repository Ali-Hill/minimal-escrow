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
                          donate,
                          cancel,
                          pay,
                         )

import Contract.MultiSig qualified as Impl



import Control.Monad.Except (catchError)

import Plutus.Contract.Test.Certification
import Plutus.Contract.Test.Certification.Run
import Test.QuickCheck.DynamicLogic qualified as QCD
import Plutus.Contract.Test.Certification.Run (certifyWithOptions)
import qualified Ledger
import qualified Plutus.Script.Utils.Value as Ada

type Wallet = Integer

-- Model should be

{-
 possible_signatories :: [Ada.PubKeyHash]
 , signature :: [Ada.PubKey]
 , minNumSignatures :: Integer
 , minimumValue :: Value
 , deadline :: Slot
 , proposedValue :: Value
-}

data MultiSigModel = MultiSigModel
  { _possible_signatories :: [Wallet],
    _signatures :: [Wallet],
    _minNumSignatures :: Integer,
    _minimumValue :: Value,
    _target :: Wallet,
    _deadline :: Slot,
    _proposedValue :: Value,
    _contractValue :: Value
  }
  deriving (Eq, Show, Generic)

makeLenses ''MultiSigModel

options :: E.Options MultiSigModel
options =
  E.defaultOptions
    { E.params = Params.increaseTransactionLimits def
    , E.coverageIndex = Impl.covIdx
    }

instance ContractModel MultiSigModel where
  data Action MultiSigModel
    = Propose Integer Wallet Wallet Slot
    | AddSig Wallet
    | Donate Wallet Integer
    | Cancel Wallet
    | Pay Wallet
    deriving (Show, Eq, Generic)

  initialState =
    MultiSigModel
      { _possible_signatories = [],
        _signatures = [],
        _minNumSignatures = 0,
        _minimumValue = Ada.valueOf Ledger.minAdaTxOutEstimated,
        _target = 0,
        _deadline = 0,
        _proposedValue = Ada.adaValueOf 0,
        _contractValue = Ada.adaValueOf 0
      }

  nextState a = void $ case a of
    Propose v w t s -> do
      target .= t
      proposedValue .= v
      deadline .= s
      wait 1
    AddSig w -> do
      signatures %= (w :)
      wait 1
    Donate w v -> do
      contractValue %= (<> v)
      withdraw (walletAddress w) v -- may have to make it integer
      wait 1
    Cancel w -> do
      -- probably want to set the contract value to 0
      wait 1
    Pay w -> do
      deposit (walletAddress target) proposedValue
      contractValue %= (<> inv proposedValue)
      -- probably also want to set the contract value to 0
      wait 1

  precondition s a = case a of
    Propose v w t s -> True
    AddSig w -> True
    Donate w v -> True
    Cancel w -> True
    Pay w -> True

  validFailingAction _ _ = False

  --TODO: Define arbitraryAction

instance RunModel MultiSigModel E.EmulatorM where
    perform _ cmd _ = lift $ void $ act cmd

-- To catch errors use voidCatch
-- voidCatch m = catchError (void m) (\ _ -> pure ())

act :: Action MultiSigModel -> E.EmulatorM ()
act = \case
  Propose v w t s ->
    propose
      ModelParams
      (walletAddress w)
      (walletAddress t)
      (walletPricateKey w)
      v
      fromCardanoSlotNo s
