import Contracts.Common
namespace ReproMore
open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_intrinsic gasNow (tag : Uint256) : Uint256
  where pure;
        yul := [template (tag) -> g := [ g := gas() ]];
        min_fork := cancun;
        semantics := (fun _ => (0 : Verity.Core.Uint256));
        obligation [g := assumed "GAS"]

set_option linter.unusedVariables false in
verity_contract MoreBugs where
  storage
    x : Uint256 := slot 0
  -- Bug A: calling the intrinsic wrapper by name compiles to its Lean semantics (0), no gas().
  function wrapperCall () : Uint256 := do
    let g := gasNow 1
    return g
  -- Bug B: returnArray of a memory array copies from calldata.
  function memArray ()
    local_obligations [m := assumed "alloc"]
    : Array Uint256 := do
    let arr ← allocArray 2
    setMemoryArrayElement arr 0 7
    setMemoryArrayElement arr 1 8
    returnArray arr
  -- Bug C: both branches of an if-expression are evaluated; the untaken checked read reverts.
  function pick (xs : Array Uint256, i : Uint256) : Uint256 := do
    let v := if i == 0 then 1 else arrayElement xs (sub i 1)
    return v
end ReproMore
