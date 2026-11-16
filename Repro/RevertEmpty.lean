import Contracts.Common
namespace ReproRevert
open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
verity_contract RE where
  storage
    x : Uint256 := slot 0
  function f (a : Uint256) : Unit := do
    if a > 1 then revertEmpty else pure ()
end ReproRevert
