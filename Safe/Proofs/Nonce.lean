import Safe.Spec

/-!
# P2: every execution consumes the nonce it signs

`consumeNonce` is the first thing `execTransaction` does after ABI checks: it reads the nonce `n`,
computes the EIP-712 hashes over `n`, and stores `n + 1`. It always succeeds, writes no other storage,
and the `txHash` that `checkNSignatures` then verifies commits to `n`. So a set of signatures is valid
for exactly one nonce, and that nonce is gone once the transaction lands.
-/

namespace SafeVerity.Proofs
open Verity Contracts

/-! ## One-step meaning of the primitives `consumeNonce` uses -/

theorem mstore_run (o v : Uint256) (s : ContractState) :
    Contracts.mstore o v s =
      .success () { s with memory := fun k => if k = o.val then v else s.memory k } := by
  simp only [Contracts.mstore, Compiler.CompilationModel.DenoteFunctionCalls.writeMemoryWords]
  congr; funext k
  by_cases hk : k = o.val
  · simp only [hk, ↓reduceIte]
    apply Verity.Core.Uint256.ext
    exact Nat.mod_eq_of_lt v.isLt
  · simp [hk]

/-- The memory `copyBytes data d` leaves; only `keccak256(data)` depends on it, kept abstract. -/
def copyMem (data : ByteArray) (d : Uint256) (s : ContractState) : Nat → Uint256 :=
  match Contracts.copyBytes data d s with
  | .success _ s' => s'.memory
  | .revert _ s' => s'.memory

theorem copyBytes_run (data : ByteArray) (d : Uint256) (s : ContractState) :
    Contracts.copyBytes data d s = .success () { s with memory := copyMem data d s } := rfl

/-- The words `keccak256(p, size)` reads, as listed by `MemorySlice.words`, are what it hashes. -/
theorem keccak_eq_keccakWords (mem : Nat → Uint256) (p : Uint256) (size : Nat) (ws : List Nat)
    (h : Compiler.Keccak.MemorySlice.words (fun a => (mem a).val) p.val size = ws) :
    Verity.Core.Uint256.ofNat
        (Compiler.Keccak.MemorySlice.keccak (fun a => (mem a).val) p.val size) =
      Spec.keccakWords ws size := by
  simp only [Compiler.Keccak.MemorySlice.keccak, Compiler.Keccak.MemorySlice.bytesBE, h,
    Spec.keccakWords]
  apply Verity.Core.Uint256.ext
  simp [Compiler.Constants.evmModulus, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]

set_option maxHeartbeats 1000000 in
theorem consumeNonce_spec (ctx : ExecutableCallContext) (target : Address) (value : Uint256)
    (data : ByteArray) (operation safeTxGas baseGas gasPrice : Uint256)
    (gasToken refundReceiver : Address) (s : ContractState) :
    ∃ dataHash mem,
      Safe.consumeNonce_registry ctx target value data operation safeTxGas baseGas gasPrice gasToken
          refundReceiver s =
        .success
          (Spec.txHash (Spec.domainSeparator s.chainId s.thisAddress)
              (Spec.safeTxHash target value dataHash operation safeTxGas baseGas gasPrice gasToken
                refundReceiver (s.storage 5)),
           Spec.safeTxHash target value dataHash operation safeTxGas baseGas gasPrice gasToken
              refundReceiver (s.storage 5))
          { (s.writeSlot 5 (Verity.EVM.Uint256.add (s.storage 5) 1)) with memory := mem } := by
  simp only [Safe.consumeNonce_registry, Safe.domainSeparatorHash_registry, Bind.bind, Pure.pure,
    Verity.bind, Verity.pure, Verity.getStorage, Contracts.chainid, Verity.chainid,
    Contracts.contractAddress, Verity.contractAddress, Contracts.mloadLive, mstore_run,
    Contracts.keccak256Live, copyBytes_run, Verity.setStorage]
  refine ⟨_, _, ?_⟩
  sorry

end SafeVerity.Proofs
