import Safe.Spec
import Safe.Proofs.Frame
import Safe.Proofs.Nonce

/-!
# P1: a successful signature check names `threshold` distinct owners

`checkNSignatures(txHash, …, t)` succeeds only if it found `t` signers `o₀ < o₁ < … < oₜ₋₁` (so
pairwise distinct), each a current owner (not the list sentinel), each authorising `txHash` through
the kind its `v` byte selects (`Spec.Authorizes`). It changes no storage and reads no other calldata.
-/

namespace SafeVerity.Proofs
open Verity Contracts

theorem calldataloadLive_run (o : Uint256) (s : ContractState) :
    Contracts.calldataloadLive o s = .success (Spec.cdWord s o) s := rfl

theorem cdWord_same {s t : ContractState} (h : Same s t) (o : Uint256) :
    Spec.cdWord t o = Spec.cdWord s o := by
  simp only [Spec.cdWord, h.hCalldata, h.hSelector]

theorem require_bind_success {β : Type} {c : Bool} {msg : String} {f : Unit → Contract β}
    {s t : ContractState} {b : β} (h : (Verity.require c msg >>= f) s = .success b t) :
    c = true ∧ f () s = .success b t := by
  simp only [Bind.bind, Verity.bind, Verity.require] at h
  cases c <;> simp_all

theorem revertEmpty_bind_ne {β : Type} {f : Unit → Contract β} {s t : ContractState} {b : β} :
    (revertEmpty >>= f) s ≠ .success b t := by
  simp [Bind.bind, Verity.bind, revertEmpty]

theorem bind_success_iff {α β : Type} {m : Contract α} {f : α → Contract β} {s t : ContractState}
    {b : β} : (m >>= f) s = .success b t ↔ ∃ a s1, m s = .success a s1 ∧ f a s1 = .success b t := by
  simp only [Bind.bind, Verity.bind]
  constructor
  · intro h; split at h
    · rename_i a s1 hm; exact ⟨a, s1, hm, h⟩
    · cases h
  · rintro ⟨a, s1, hm, hf⟩; rw [hm]; exact hf

theorem ite_success {α : Type} {c : Prop} [Decidable c] {x y : Contract α} {s t : ContractState}
    {b : α} (h : (if c then x else y) s = .success b t) :
    (c ∧ x s = .success b t) ∨ (¬ c ∧ y s = .success b t) := by
  by_cases hc : c
  · left; rw [if_pos hc] at h; exact ⟨hc, h⟩
  · right; rw [if_neg hc] at h; exact ⟨hc, h⟩

theorem pure_bind_success {α β : Type} {a : α} {f : α → Contract β} {s t : ContractState} {b : β}
    (h : (Pure.pure a >>= f) s = .success b t) : f a s = .success b t := by
  obtain ⟨a', s', hp, h⟩ := bind_success_iff.mp h
  simp only [Pure.pure, Verity.pure] at hp
  injection hp with h1 h2

theorem ecrecover_run (h v r sg : Uint256) (st : ContractState) :
    ∃ a, Contracts.ecrecover h v r sg st = .success a st ∧ addressToWord a = Spec.recover h v r sg :=
  ⟨_, rfl, rfl⟩

theorem ecrecover_inv {h v r sg : Uint256} {st st' : ContractState} {a : Address}
    (he : Contracts.ecrecover h v r sg st = .success a st') :
    st' = st ∧ addressToWord a = Spec.recover h v r sg := by
  injection he with ha hst; exact ⟨hst.symm, by rw [← ha]; rfl⟩

/-- The GS026 join point every signature kind ends in. -/
theorem gs026_fact (cur last b : Uint256) (st u : ContractState)
    (h : (Verity.getMapping Safe.owners (wordToAddress cur) >>= fun w =>
      Verity.require (decide (cur > last) && w != 0 && cur != Safe.sentinel) "GS026" >>= fun _ =>
        (Pure.pure cur : Contract Uint256)) st = .success b u) :
    b = cur ∧ u = st ∧ last < cur ∧ st.storageWords (.map Safe.owners.slot (wordToAddress cur)) ≠ 0 ∧
      cur ≠ Safe.sentinel := by
  obtain ⟨w, s1, hw, h⟩ := bind_success_iff.mp h
  injection hw with hw hs1; subst hw hs1
  obtain ⟨hc, h⟩ := require_bind_success h
  simp only [Pure.pure, Verity.pure] at h; injection h with hb hu; subst hb hu
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
  exact ⟨rfl, rfl, hc.1.1, hc.1.2, hc.2⟩

theorem keeps_domainSeparatorHash (ctx : ExecutableCallContext) :
    Keeps (Safe.domainSeparatorHash_registry ctx) := by
  intro s a t h
  obtain ⟨m, hm⟩ := domainSeparatorHash_withMem ctx s
  rw [hm] at h; injection h with _ h; subst h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem same_withMem (s : ContractState) (m : Nat → Uint256) : Same s (withMem s m) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `if c then (do revertReturndata; k) else (do pure (); k)`: both branches continue with `k`
(the EDSL's `revertReturndata` does not revert; see README). -/
theorem ite_continue {β : Type} {c : Prop} [Decidable c] {f : Unit → Contract β} {s t : ContractState}
    {b : β} (h : (if c then (Contracts.revertReturndata >>= f) else (Pure.pure () >>= f)) s =
      .success b t) : f () s = .success b t := by
  rcases ite_success h with ⟨_, h⟩ | ⟨_, h⟩ <;> exact pure_bind_success h

set_option hygiene false in
/-- One primitive that keeps `Same`: peel it off `hb`, extend `hs`. -/
macro "kstep " k:term : tactic =>
  `(tactic| (obtain ⟨_, _, hk, hb⟩ := bind_success_iff.mp hb; replace hs := hs.trans ($k _ _ _ hk)))

set_option hygiene false in
/-- `require c msg; k`: record `c`, continue with `k`. -/
macro "kreq" : tactic => `(tactic| (obtain ⟨_, hb⟩ := require_bind_success hb))

set_option hygiene false in
/-- `if c then (revertEmpty; k) else (pure (); k)`: the first branch cannot succeed. -/
macro "krevif" : tactic =>
  `(tactic| (rcases ite_success hb with ⟨_, hb⟩ | ⟨_, hb⟩
             · exact absurd hb revertEmpty_bind_ne
             replace hb := pure_bind_success hb))

/-- **P1.** If `checkNSignatures` succeeds, it found `t` strictly increasing (hence distinct)
signers, none the sentinel, each an owner and each authorising `txHash`; storage is unchanged. -/
theorem checkNSignatures_sound (ctx : ExecutableCallContext) (txHash safeTxHash sigLen t : Uint256)
    (s0 s1 : ContractState)
    (h : Safe.checkNSignatures_registry ctx txHash safeTxHash sigLen t s0 = .success () s1) :
    Same s0 s1 ∧ ∃ signers : List Uint256,
      signers.length = t.val ∧ signers.Pairwise (· < ·) ∧
      ∀ k (hk : k < signers.length), signers[k] ≠ Safe.sentinel ∧
        Spec.ownerLink s0 signers[k] ≠ 0 ∧
        Spec.Authorizes s0 txHash (Verity.Core.Uint256.ofNat k) signers[k] := by
  unfold Safe.checkNSignatures_registry at h
  dsimp only at h
  by_cases hov : t > Verity.EVM.Uint256.div Safe.maxWord 65
  · rw [if_pos hov] at h; exact absurd h revertEmpty_bind_ne
  rw [if_neg hov] at h
  obtain ⟨_, _, hp, h⟩ := bind_success_iff.mp h
  injection hp with _ hp; subst hp
  obtain ⟨hGS020, h⟩ := require_bind_success h
  obtain ⟨ds, sB, hds, h⟩ := bind_success_iff.mp h
  have hB := keeps_domainSeparatorHash ctx s0 ds sB hds
  obtain ⟨base, sC, hbase, h⟩ := bind_success_iff.mp h
  rw [calldataloadLive_run] at hbase; injection hbase with hbase hC; subst hC hbase
  obtain ⟨last, sD, hloop, h⟩ := bind_success_iff.mp h
  simp only [Pure.pure, Verity.pure] at h
  injection h with _ h; subst h
  have key := loopList_chain s0 _
    (fun i b => b ≠ Safe.sentinel ∧ Spec.ownerLink s0 b ≠ 0 ∧
      Spec.Authorizes s0 txHash (Verity.Core.Uint256.ofNat i) b) (· < ·) ?hstep _ _ _ _ _ hB hloop
  rotate_left
  · intro i a s b u hs hb
    have hs₀ := hs
    obtain ⟨r, s1, hr, hb⟩ := bind_success_iff.mp hb
    rw [calldataloadLive_run] at hr; injection hr with hr h1; subst h1 hr
    obtain ⟨sv, s2, hsv, hb⟩ := bind_success_iff.mp hb
    rw [calldataloadLive_run] at hsv; injection hsv with hsv h2; subst h2 hsv
    obtain ⟨vw, s3, hvw, hb⟩ := bind_success_iff.mp hb
    rw [calldataloadLive_run] at hvw; injection hvw with hvw h3; subst h3 hvw
    rcases ite_success hb with ⟨hv0, hb⟩ | ⟨hv0, hb⟩
    · -- contract signature (EIP-1271): only the claimed signer is pinned down
      kreq; krevif; kreq
      kstep (fun s a t h => keeps_calldataloadLive _ s a t h)
      krevif; kreq; krevif
      kstep (fun s a t h => keeps_mloadLive _ s a t h)
      iterate 10 kstep (fun s a t h => keeps_mstore _ _ s a t h)
      kstep (fun s a t h => keeps_calldatacopyLive _ _ _ s a t h)
      kstep (fun s a t h => keeps_evmStaticCallWords _ _ _ _ _ _ _ s a t h)
      replace hb := ite_continue hb
      kstep (fun s a t h => keeps_returndataSizeLive s a t h)
      krevif
      kstep (fun s a t h => keeps_returndataCopyLive _ _ _ s a t h)
      kstep (fun s a t h => keeps_mloadLive _ s a t h)
      kreq
      obtain ⟨rfl, rfl, hlt, hown, hsent⟩ := gs026_fact _ _ _ _ _ hb
      refine ⟨hs, hlt, hsent, ?_, ?_⟩
      · simp only [Spec.ownerLink]; rw [← hs.hStorage]; exact hown
      · left
        simp only [cdWord_same hs₀, cdWord_same hB] at hv0
        simp only [Spec.sigV, Spec.sigR, Spec.sigPos, Spec.sigBase, cdWord_same hs₀, cdWord_same hB]
        exact ⟨by simpa using hv0, trivial⟩
    rcases ite_success hb with ⟨hv1, hb⟩ | ⟨hv1, hb⟩
    · -- approved hash: msg.sender is the approver, or it approved txHash before
      obtain ⟨snd, s4, hsnd, hb⟩ := bind_success_iff.mp hb
      injection hsnd with hsnd h4; subst hsnd h4
      obtain ⟨apv, s5, hapv, hb⟩ := bind_success_iff.mp hb
      injection hapv with hapv h5; subst hapv h5
      obtain ⟨hc, hb⟩ := require_bind_success hb
      obtain ⟨rfl, rfl, hlt, hown, hsent⟩ := gs026_fact _ _ _ _ _ hb
      refine ⟨hs, hlt, hsent, ?_, ?_⟩
      · simp only [Spec.ownerLink]; rw [← hs.hStorage]; exact hown
      · right; left
        simp only [cdWord_same hs, cdWord_same hB] at hv0 hv1 hc
        simp only [Spec.sigV, Spec.sigR, Spec.sigPos, Spec.sigBase, Spec.approved, cdWord_same hs,
          cdWord_same hB]
        refine ⟨by simpa using hv1, trivial, ?_⟩
        simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
        rcases hc with hc | hc
        · left; rw [← hs.hSender]; exact hc
        · right; rw [← hs.hStorage]; exact hc
    rcases ite_success hb with ⟨hv30, hb⟩ | ⟨hv30, hb⟩
    · -- eth_sign: ecrecover over the "\x19Ethereum Signed Message:\n32" digest, with v - 4
      obtain ⟨q, s4, hq, hb⟩ := bind_success_iff.mp hb
      rw [mloadLive_run] at hq; injection hq with hq h4; subst hq h4
      obtain ⟨_, s5, h5, hb⟩ := bind_success_iff.mp hb
      rw [mstore_withMem] at h5; injection h5 with _ h5; subst h5
      obtain ⟨_, s6, h6, hb⟩ := bind_success_iff.mp hb
      rw [mstore_withMem] at h6; injection h6 with _ h6; subst h6
      obtain ⟨pre, s7, h7, hb⟩ := bind_success_iff.mp hb
      rw [keccak256Live_run] at h7; injection h7 with h7 h8; subst h8
      simp only [withMem_withMem, withMem_memory] at h7
      rw [show (60 : Verity.Core.Uint256).val = 60 from rfl, keccak2 _ _ _ _ 60 rfl] at h7
      subst h7
      obtain ⟨a', s9, hsg, hb⟩ := bind_success_iff.mp hb
      obtain ⟨h9, hrec⟩ := ecrecover_inv hsg; subst h9
      have hb := pure_bind_success hb
      obtain ⟨rfl, rfl, hlt, hown, hsent⟩ := gs026_fact _ _ _ _ _ hb
      refine ⟨hs.trans (same_withMem _ _), hlt, hsent, ?_, ?_⟩
      · simp only [Spec.ownerLink]; rw [← hs.hStorage]; exact hown
      · right; right; left
        simp only [cdWord_same hs, cdWord_same hB] at hv30 hrec
        simp only [Spec.sigV, Spec.sigR, Spec.sigS, Spec.sigPos, Spec.sigBase, Spec.ethSignHash]
        exact ⟨hv30, hrec⟩
    -- plain ECDSA
    obtain ⟨sg, s4, hsg, hb⟩ := bind_success_iff.mp hb
    obtain ⟨a', ha', hrec⟩ := ecrecover_run txHash _ _ _ s
    rw [ha'] at hsg; injection hsg with hsg h4; subst hsg h4
    have hb := pure_bind_success hb
    obtain ⟨rfl, rfl, hlt, hown, hsent⟩ := gs026_fact _ _ _ _ _ hb
    refine ⟨hs, hlt, hsent, ?_, ?_⟩
    · simp only [Spec.ownerLink]; rw [← hs.hStorage]; exact hown
    · right; right; right
      simp only [cdWord_same hs, cdWord_same hB] at hv0 hv1 hv30 hrec
      simp only [Spec.sigV, Spec.sigR, Spec.sigS, Spec.sigPos, Spec.sigBase]
      exact ⟨by simpa using hv0, by simpa using hv1, hv30, hrec⟩
  obtain ⟨hD, outs, hchain, -⟩ := key
  refine ⟨hD, outs, ?_, (StepChain.pairwise_lt hchain).2, ?_⟩
  · rw [StepChain.length hchain, List.length_range]
  · intro k hk
    have hP := StepChain.get hchain k hk
    have hkt : k < t.val := by rw [StepChain.length hchain, List.length_range] at hk; exact hk
    simpa [List.getD_eq_getElem?_getD, List.getElem?_range hkt] using hP

end SafeVerity.Proofs
