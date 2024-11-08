{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE InstanceSigs #-}

module Lib.Types (
    VerificationKeyHash,
    TreasuryDatum(..),
    MultisigDatum(..),
    MultisigRedeemer(..)
)
where


import PlutusLedgerApi.V1.Crypto (PubKeyHash) -- Used as VerificationKeyHash
import PlutusLedgerApi.V1.Address (Address)
import PlutusTx (unstableMakeIsData)
import PlutusTx.Prelude ( Integer )
import Prelude (Show, Eq, (==), (&&), Bool)

-- Type Alias for VerificationKeyHash, as in Aiken
type VerificationKeyHash = PubKeyHash

-- TreasuryDatum Equivalent
data TreasuryDatum = TreasuryDatum
  { value :: Integer
  , owners :: [VerificationKeyHash]
  }
  deriving stock (Show, Eq)

-- MultisigDatum Equivalent
data MultisigDatum = MultisigDatum
  { release_value :: Integer
  , beneficiary :: Address
  , required_signers :: [VerificationKeyHash]
  , signed_users :: [VerificationKeyHash]
  }
  deriving stock (Show)

instance Eq MultisigDatum where
    (==) :: MultisigDatum -> MultisigDatum -> Bool
    MultisigDatum rv1 b1 rs1 su1 == MultisigDatum rv2 b2 rs2 su2 =
        rv1 == rv2 && b1 == b2 && rs1 == rs2 && su1 == su2

-- MultisigRedeemer Equivalent
data MultisigRedeemer = Use | Sign
  deriving stock (Show, Eq)

-- Making Types Compatible with PlutusTx
unstableMakeIsData ''TreasuryDatum
unstableMakeIsData ''MultisigDatum
unstableMakeIsData ''MultisigRedeemer
