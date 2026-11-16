import Contracts.Common
namespace ReproView
open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
set_option linter.unusedVariables false in
verity_contract ViewLoop where
  storage
    next : Address → Uint256 := slot 0
    count : Uint256 := slot 1
  function view walk () : Uint256 := do
    let c ← getStorage count
    let mut cur ← getMapping next (wordToAddress 1)
    forEach "i" c (do
      cur ← getMapping next (wordToAddress cur))
    return cur
  function view sumIdx () : Uint256 := do
    let c ← getStorage count
    let mut acc := 0
    forEach "i" c (do
      acc := add acc i)
    return acc
end ReproView
