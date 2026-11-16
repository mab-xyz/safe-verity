import Safe.Proofs.Signatures

/-!
# `execTransaction` end to end: P1 ∘ P2

A successful `execTransaction` was authorised by `threshold` distinct owners, all for the EIP-712
hash of exactly this transaction at the nonce the Safe held when it started.
-/

namespace SafeVerity.Proofs
open Verity Contracts

theorem writeSlot_storageWords_map (s : ContractState) (n : Nat) (v : Uint256) (sl : Nat) (k : Address) :
    (s.writeSlot n v).storageWords (.map sl k) = s.storageWords (.map sl k) := by
  simp [ContractState.writeSlot]

theorem writeSlot_storageWords_mapChain (s : ContractState) (n : Nat) (v : Uint256) (sl : Nat)
    (ks : List Nat) (o : Nat) :
    (s.writeSlot n v).storageWords (.mapChain sl ks o) = s.storageWords (.mapChain sl ks o) := by
  simp [ContractState.writeSlot]

/-- **P1 ∘ P2.** If `execTransaction` succeeds from `s`, then `threshold` (as stored in `s`) distinct
owners of `s` each authorised `txHash(domainSeparator, safeTxHash(…, nonce))` for the nonce stored
in `s`, through the signature kind their `v` byte selects. -/
theorem execTransaction_authorized (ctx : ExecutableCallContext) (target : Address) (value : Uint256)
    (data : ByteArray) (operation safeTxGas baseGas gasPrice : Uint256)
    (gasToken refundReceiver : Address) (signatures : ByteArray) (s s' : ContractState) (ok : Bool)
    (h : Safe.execTransaction_registry ctx target value data operation safeTxGas baseGas gasPrice
      gasToken refundReceiver signatures s = .success ok s') :
    ∃ dataHash, ∃ signers : List Uint256,
      signers.length = (s.storage 4).val ∧ signers.Pairwise (· < ·) ∧
      ∀ k (hk : k < signers.length), signers[k] ≠ Safe.sentinel ∧
        Spec.ownerLink s signers[k] ≠ 0 ∧
        Spec.Authorizes s
          (Spec.txHash (Spec.domainSeparator s.chainId s.thisAddress)
            (Spec.safeTxHash target value dataHash operation safeTxGas baseGas gasPrice gasToken
              refundReceiver (s.storage 5)))
          (Verity.Core.Uint256.ofNat k) signers[k] := by
  unfold Safe.execTransaction_registry at h
  dsimp only at h
  by_cases hop : operation > 1
  · rw [if_pos hop] at h; exact absurd h revertEmpty_bind_ne
  rw [if_neg hop] at h
  replace h := pure_bind_success h
  obtain ⟨dataHash, mem, hcn⟩ := consumeNonce_spec ctx target value data operation safeTxGas baseGas
    gasPrice gasToken refundReceiver s
  obtain ⟨_, s1, hc1, h⟩ := bind_success_iff.mp h
  rw [hcn] at hc1; injection hc1 with hc1 hs1; subst hc1 hs1
  dsimp only at h
  obtain ⟨t, s2, ht, h⟩ := bind_success_iff.mp h
  rw [getStorage_run] at ht; injection ht with ht hs2; subst ht hs2
  obtain ⟨hGS001, h⟩ := require_bind_success h
  obtain ⟨_, s3, hcheck, -⟩ := bind_success_iff.mp h
  obtain ⟨_, signers, hlen, hpw, hall⟩ := checkNSignatures_sound _ _ _ _ _ _ _ hcheck
  refine ⟨dataHash, signers, ?_, hpw, ?_⟩
  · rw [hlen]; rfl
  · intro k hk
    obtain ⟨h1, h2, h3⟩ := hall k hk
    refine ⟨h1, ?_, ?_⟩
    · simpa [Spec.ownerLink, withMem, writeSlot_storageWords_map] using h2
    · simpa [Spec.Authorizes, Spec.sigV, Spec.sigR, Spec.sigS, Spec.sigPos, Spec.sigBase, Spec.cdWord,
        Spec.approved, withMem, ContractState.writeSlot, writeSlot_storageWords_mapChain] using h3

end SafeVerity.Proofs
