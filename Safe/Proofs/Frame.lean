import Safe.Contract

/-!
# Frames: what a contract fragment leaves unchanged

`Keeps c` says a successful run of `c` leaves storage, calldata, the caller and the contract's own
address untouched; only memory, returndata, the call journal and events may change. The signature
loop has this property, so every owner check it makes reads the storage the transaction started
with, and every signature it parses comes from the transaction's own calldata.
-/

namespace SafeVerity.Proofs
open Verity Contracts

/-- The parts of the state a signature check reads and must not change. -/
structure Same (s t : ContractState) : Prop where
  hStorage : t.storageWords = s.storageWords
  hCalldata : t.calldata = s.calldata
  hSelector : t.selector = s.selector
  hSender : t.sender = s.sender
  hThis : t.thisAddress = s.thisAddress
  hChainId : t.chainId = s.chainId

theorem Same.refl (s : ContractState) : Same s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Same.trans {a b c : ContractState} (h1 : Same a b) (h2 : Same b c) : Same a c :=
  ⟨h2.hStorage.trans h1.hStorage, h2.hCalldata.trans h1.hCalldata,
    h2.hSelector.trans h1.hSelector, h2.hSender.trans h1.hSender, h2.hThis.trans h1.hThis,
    h2.hChainId.trans h1.hChainId⟩

/-- A successful run keeps `Same`. -/
def Keeps {α : Type} (c : Contract α) : Prop :=
  ∀ s a t, c s = .success a t → Same s t

theorem keeps_pure {α : Type} (a : α) : Keeps (Pure.pure a : Contract α) := by
  intro s b t h; simp only [Pure.pure, Verity.pure] at h; cases h; exact Same.refl _

theorem keeps_bind {α β : Type} {m : Contract α} {f : α → Contract β}
    (hm : Keeps m) (hf : ∀ a, Keeps (f a)) : Keeps (m >>= f) := by
  intro s b t h
  simp only [Bind.bind, Verity.bind] at h
  split at h
  · rename_i a s1 h1; exact (hm s a s1 h1).trans (hf a s1 b t h)
  · cases h

theorem keeps_ite {α : Type} {c : Prop} [Decidable c] {x y : Contract α}
    (hx : Keeps x) (hy : Keeps y) : Keeps (if c then x else y) := by
  split <;> assumption

/-- A state that only differs in memory, returndata, calls or events is `Same`. -/
theorem same_of_eq_fields {s t : ContractState} (h1 : t.storageWords = s.storageWords)
    (h2 : t.calldata = s.calldata) (h3 : t.selector = s.selector) (h4 : t.sender = s.sender)
    (h5 : t.thisAddress = s.thisAddress) (h6 : t.chainId = s.chainId) : Same s t :=
  ⟨h1, h2, h3, h4, h5, h6⟩

/-- Primitives that return the input state unchanged. -/
theorem keeps_of_state_eq {α : Type} {c : Contract α}
    (h : ∀ s a t, c s = .success a t → t = s) : Keeps c := by
  intro s a t hc; rw [h s a t hc]; exact Same.refl _

/-- A primitive of the form `fun s => .success (f s) s`. -/
theorem keeps_read {α : Type} (f : ContractState → α) :
    Keeps (fun s => ContractResult.success (f s) s) :=
  keeps_of_state_eq (by intro s a t h; injection h with _ h; exact h.symm)

/-- Primitives that only change memory, returndata, calls or events. -/
theorem keeps_of_fields {α : Type} {c : Contract α}
    (h : ∀ s a t, c s = .success a t →
      t.storageWords = s.storageWords ∧ t.calldata = s.calldata ∧ t.selector = s.selector ∧
      t.sender = s.sender ∧ t.thisAddress = s.thisAddress ∧ t.chainId = s.chainId) : Keeps c := by
  intro s a t hc
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h s a t hc
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem keeps_require (b : Bool) (msg : String) : Keeps (Verity.require b msg) :=
  keeps_of_state_eq (by intro s a t h; unfold Verity.require at h; split at h <;> cases h; rfl)

theorem keeps_revertEmpty : Keeps revertEmpty := by
  intro s a t h; cases h

theorem keeps_revertReturndata : Keeps Contracts.revertReturndata :=
  keeps_pure ()

theorem keeps_getStorage (f : StorageSlot Uint256) : Keeps (Verity.getStorage f) := keeps_read _

theorem keeps_getMapping (f : StorageSlot (Address → Uint256)) (k : Address) :
    Keeps (Verity.getMapping f k) := keeps_read _

theorem keeps_getMappingN {α : Type} (f : StorageSlot α) (ks : List MappingKeyWord) :
    Keeps (Contracts.getMappingN f ks) := keeps_read _

theorem keeps_msgSender : Keeps Verity.msgSender := keeps_read _

theorem keeps_calldataloadLive (o : Uint256) : Keeps (Contracts.calldataloadLive o) := keeps_read _

theorem keeps_mloadLive (o : Uint256) : Keeps (Contracts.mloadLive o) := keeps_read _

theorem keeps_keccak256Live (o n : Uint256) : Keeps (Contracts.keccak256Live o n) := keeps_read _

theorem keeps_returndataSizeLive : Keeps Contracts.returndataSizeLive := keeps_read _

theorem keeps_ecrecover (h v r sg : Uint256) : Keeps (Contracts.ecrecover h v r sg) := keeps_read _

theorem keeps_mstore (o v : Uint256) : Keeps (Contracts.mstore o v) :=
  keeps_of_fields (by
    intro s a t h; injection h with _ h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem keeps_calldatacopyLive (d o n : Uint256) : Keeps (Contracts.calldatacopyLive d o n) :=
  keeps_of_fields (by
    intro s a t h; injection h with _ h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem keeps_returndataCopyLive (d o n : Uint256) : Keeps (Contracts.returndataCopyLive d o n) :=
  keeps_of_fields (by
    intro s a t h; unfold Contracts.returndataCopyLive at h
    split at h
    · injection h with _ h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases h)

/-- A `staticcall` cannot change the caller's world (`denoteCall`: `.staticcall` keeps the world). -/
theorem keeps_evmStaticCallWords (adv : Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel)
    (g tgt io isz oo osz : Uint256) : Keeps (Contracts.evmStaticCallWords adv g tgt io isz oo osz) := by
  apply keeps_of_fields
  intro s a t h
  unfold Contracts.evmStaticCallWords at h
  dsimp only at h
  simp only [Contract.run, Contracts.commonExternalCall_apply] at h
  split at h
  all_goals first
    | (rename_i heq; injection heq with _ hp; subst hp; injection h with _ h; subst h
       exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    | cases h

end SafeVerity.Proofs

namespace SafeVerity.Proofs
open Verity Contracts

/-- `outs` are the successive loop states for `idx`, starting from `a`: each step is related to the
previous one by `R` and satisfies `P` at its index. -/
def StepChain {σ : Type} (P : Nat → σ → Prop) (R : σ → σ → Prop) : List Nat → σ → List σ → Prop
  | [], _, [] => True
  | i :: rest, a, b :: bs => R a b ∧ P i b ∧ StepChain P R rest b bs
  | _, _, _ => False

theorem StepChain.length {σ : Type} {P : Nat → σ → Prop} {R : σ → σ → Prop} :
    ∀ {idx : List Nat} {a : σ} {outs : List σ}, StepChain P R idx a outs → outs.length = idx.length
  | [], _, [], _ => rfl
  | _ :: _, _, _ :: _, ⟨_, _, h⟩ => by rw [List.length_cons, List.length_cons, StepChain.length h]
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim

/-- A successful `loopList` whose every step keeps `Same s0` and establishes `R`/`P` yields a
`StepChain` of loop states. -/
theorem loopList_chain {σ : Type} (s0 : ContractState) (body : Nat → σ → Contract σ)
    (P : Nat → σ → Prop) (R : σ → σ → Prop)
    (hbody : ∀ i a s b t, Same s0 s → body i a s = .success b t → Same s0 t ∧ R a b ∧ P i b) :
    ∀ (idx : List Nat) (a : σ) (s t : ContractState) (r : σ), Same s0 s →
      Contracts.loopList idx a body s = .success r t →
      Same s0 t ∧ ∃ outs, StepChain P R idx a outs ∧ r = outs.getLastD a := by
  intro idx
  induction idx with
  | nil =>
      intro a s t r hs h
      simp only [Contracts.loopList, List.foldlM, Pure.pure, Verity.pure] at h
      injection h with hr ht; subst hr ht
      exact ⟨hs, [], by simp [StepChain], rfl⟩
  | cons i rest ih =>
      intro a s t r hs h
      simp only [Contracts.loopList, List.foldlM, Bind.bind, Verity.bind] at h
      split at h
      · rename_i b s1 h1
        obtain ⟨hs1, hR, hP⟩ := hbody i a s b s1 hs h1
        obtain ⟨ht, outs, hc, hr⟩ := ih b s1 t r hs1 h
        refine ⟨ht, b :: outs, ⟨hR, hP, hc⟩, ?_⟩
        rw [hr]; cases outs <;> simp [List.getLastD]
      · cases h

/-- Starting below every element and stepping by `<`, the loop states are strictly increasing. -/
theorem StepChain.pairwise_lt {P : Nat → Uint256 → Prop} :
    ∀ {idx : List Nat} {a : Uint256} {outs : List Uint256},
      StepChain P (· < ·) idx a outs → (∀ x ∈ outs, a < x) ∧ outs.Pairwise (· < ·)
  | [], _, [], _ => by simp
  | _ :: _, a, b :: bs, ⟨hab, _, h⟩ => by
      obtain ⟨hgt, hpw⟩ := StepChain.pairwise_lt h
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hab
        · have h1 := hab; have h2 := hgt x hx
          simp only [Verity.Core.Uint256.lt_def] at h1 h2 ⊢; omega
      · exact List.Pairwise.cons hgt hpw
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim

end SafeVerity.Proofs
