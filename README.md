# Dogfooding session: Testing DApps

## Overview 

This example is a multisig one, developed for a Plutus HA meeting dogfooding session.
There are multiple possible goals for this session, including:

- Getting people to challenge a specification, and finds potential loopholes in them
- Learn how to write unit tests using the Contract model
- Learn how to write the contract model
- Learn how to complete the contract model to use QuickCheck-dynamic for Property-based testing

There is no wrong or right way to do this, and the goal is to learn and have fun. You can also use other testing libraries.

There are multiple (a lot?) of vulnerabilities in this contract. Try to come up with ways to exploit them.


## Informal specification

This is a multisig contract. 
Its goal is to allow multiple parties to agree on a transaction before it is executed.

There are 5 different endpoints:
- Open: Open a multisig contract
- Propose: Propose a transaction
- AddSig: Add a signature to a transaction
- Pay: Pay from the contract to the beneficiary
- Cancel: Cancel a transaction

A set number of signatories must be reached before a transaction can be executed.

A "security" requirement is that no transaction can be executed without the required number of signatories.
A "liveness" requirement is that it should not be possible to lock the contract indefinitely.

An instance of the contract model has been provided in /Spec/MultiSig.hs to be able to start writing unit tests.

Useful resources to write it from scratch, or improve the one provided:

- https://plutus-apps.readthedocs.io/en/latest/plutus/tutorials/contract-testing.html
- https://engineering.iog.io/2022-09-28-introduce-q-d/

## Current Build Instructions

1. run `nix develop`
2. `cabal repl multisig-test`

- `import Spec.MultiSig`
- `import Test.QuickCheck`
- `quickCheck prop_Check` (or any other property you want to test or unit test that you want to execute)
