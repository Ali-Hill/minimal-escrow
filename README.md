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

## Current Build Instructions

1. run `nix develop`
2. `cabal repl multisig-test`

- `import Spec.MultiSig`
- `import Test.QuickCheck`
- `quickCheck prop_Check`
