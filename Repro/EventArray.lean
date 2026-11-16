import Contracts.Common
namespace Repro
open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
set_option linter.unusedVariables false in
verity_contract EventArray where
  storage
    x : Uint256 := slot 0
  event_defs
    event Owners(owners : Array Address, t : Uint256)
  function first (owners : Array Address, t : Uint256) : Unit := do
    emit "Owners" [owners, t]
  function second (t : Uint256, owners : Array Address) : Unit := do
    emit "Owners" [owners, t]
end Repro
