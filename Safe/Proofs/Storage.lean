import Safe.Proofs.ExecTransaction
import Safe.Proofs.Payment

/-!
# P3: `execTransaction` itself writes only the nonce

External calls are the adversary's: a `call` may re-enter, and a `delegatecall` runs foreign code on
the Safe's storage. Leave those effects out (`StorageInert`: no external call changes the Safe's
storage). Then a successful `execTransaction` ends with exactly the storage it started with, except
for nonce := nonce + 1. So every other change — owners, threshold, modules — can only come from the
transaction's own inner call, which the owners signed.
-/

namespace SafeVerity.Proofs
open Verity Contracts
open Compiler.CompilationModel.DenoteExternalCalls

/-- No external call changes the calling Safe's storage. -/
def StorageInert (adv : AdversaryModel) : Prop :=
  ∀ site w, (adv.stateTransition site w).storageWords = w.storageWords

/-- A successful run leaves storage unchanged. -/
def KS {α : Type} (c : Contract α) : Prop :=
  ∀ s a t, c s = .success a t → t.storageWords = s.storageWords

theorem ks_of_keeps {α : Type} {c : Contract α} (h : Keeps c) : KS c :=
  fun s a t hc => (h s a t hc).hStorage

theorem ks_bind {α β : Type} {m : Contract α} {f : α → Contract β} (hm : KS m) (hf : ∀ a, KS (f a)) :
    KS (m >>= f) := by
  intro s b t h
  obtain ⟨a, s1, h1, h2⟩ := bind_success_iff.mp h
  exact (hf a s1 b t h2).trans (hm s a s1 h1)

theorem ks_ite {α : Type} {c : Prop} [Decidable c] {x y : Contract α} (hx : KS x) (hy : KS y) :
    KS (if c then x else y) := by
  split <;> assumption

theorem ks_pure {α : Type} (a : α) : KS (Pure.pure a : Contract α) := ks_of_keeps (keeps_pure a)

theorem ks_prod {α β γ : Type} (p : α × β) {f : α → β → Contract γ} (hf : ∀ a b, KS (f a b)) :
    KS (match p with | (a, b) => f a b) := by
  cases p; exact hf _ _

theorem ks_require (b : Bool) (msg : String) : KS (Verity.require b msg) :=
  ks_of_keeps (keeps_require b msg)
theorem ks_revertEmpty : KS revertEmpty := ks_of_keeps keeps_revertEmpty
theorem ks_mloadLive (o : Uint256) : KS (Contracts.mloadLive o) := ks_of_keeps (keeps_mloadLive o)
theorem ks_mstore (o v : Uint256) : KS (Contracts.mstore o v) := ks_of_keeps (keeps_mstore o v)
theorem ks_returndataSizeLive : KS Contracts.returndataSizeLive := ks_of_keeps keeps_returndataSizeLive

theorem ks_copyBytes (data : ByteArray) (d : Uint256) : KS (Contracts.copyBytes data d) := by
  intro s a t h; rw [copyBytes_withMem] at h; injection h with _ h; subst h; rfl

theorem ks_txOrigin : KS Verity.txOrigin := by
  intro s a t h; injection h with _ h; subst h; rfl

theorem ks_gasPrice : KS Contracts.gasPrice := by
  intro s a t h; injection h with _ h; subst h; rfl

/-- `emit name [x, y]` with plain word arguments, as `ExecutionSuccess`/`ExecutionFailure`. -/
theorem ks_emit2 (name : String) (x y : Uint256) :
    KS (Contracts.emit name [EventArg.word (Pure.pure x), EventArg.word (Pure.pure y)]) := by
  intro s a t h
  simp only [Contracts.emit, List.mapM, List.mapM.loop, EventArg.toWord, Bind.bind, Verity.bind,
    Pure.pure, Verity.pure, Verity.emitEvent, List.reverse_cons, List.reverse_nil] at h
  injection h with _ h; subst h; rfl

theorem ks_requireOutcome (ctx : ExecutableCallContext) (a b c : Uint256) :
    KS (Safe.requireOutcome_registry ctx a b c) := by
  intro s u t h
  have h' : Safe.requireOutcome a b c s = .success u t := h
  exact ((requireOutcome_success_iff a b c s t).mp (by cases u; exact h')).2 ▸ rfl

theorem ks_paymentAmount (ctx : ExecutableCallContext) (g bg gp : Uint256) (tok : Address) (tp : Uint256) :
    KS (Safe.paymentAmount_registry ctx g bg gp tok tp) := by
  intro s a t h
  have h' : Safe.paymentAmount g bg gp tok tp s = .success a t := h
  rw [paymentAmount_eq] at h'
  split at h' <;> cases h'; rfl

theorem ks_evmCallWords (adv : AdversaryModel) (hAdv : StorageInert adv) (g tgt v io isz oo osz : Uint256) :
    KS (Contracts.evmCallWords adv g tgt v io isz oo osz) := by
  intro s a t h
  unfold Contracts.evmCallWords at h
  split at h
  · injection h with _ h; subst h; rfl
  · rename_i paid hpaid
    dsimp only at h
    simp only [Contract.run, Contracts.commonExternalCall_apply] at h
    unfold Compiler.CompilationModel.DenoteFunctionCalls.debitSelfBalance at hpaid
    split at hpaid <;> cases hpaid
    split at h
    all_goals first
      | (rename_i heq; injection heq with _ hp; subst hp; injection h with _ h; subst h
         show (denoteCallJournaled adv _ _).state.world.storageWords = _
         simp only [denoteCallJournaled, denoteCall]
         split <;> simp_all [StorageInert])
      | (injection h with _ h; subst h; rfl)
      | cases h

theorem ks_evmDelegateCallWords (adv : AdversaryModel) (hAdv : StorageInert adv) (g tgt io isz oo osz : Uint256) :
    KS (Contracts.evmDelegateCallWords adv g tgt io isz oo osz) := by
  intro s a t h
  unfold Contracts.evmDelegateCallWords at h
  dsimp only at h
  simp only [Contract.run, Contracts.commonExternalCall_apply] at h
  split at h
  all_goals first
    | (rename_i heq; injection heq with _ hp; subst hp; injection h with _ h; subst h
       show (denoteCallJournaled adv _ _).state.world.storageWords = _
       simp only [denoteCallJournaled, denoteCall]
       split <;> simp_all [StorageInert])
    | (injection h with _ h; subst h; rfl)
    | cases h

attribute [local irreducible] KS in
set_option maxRecDepth 20000 in
/-- **P3.** If no external call touches the Safe's storage, a successful `execTransaction` changes
exactly one storage word: the nonce, from `n` to `n + 1`. -/
theorem execTransaction_writes_only_nonce (ctx : ExecutableCallContext) (hAdv : StorageInert ctx.adversary)
    (target : Address) (value : Uint256) (data : ByteArray)
    (operation safeTxGas baseGas gasPrice : Uint256) (gasToken refundReceiver : Address)
    (signatures : ByteArray) (s s' : ContractState) (ok : Bool)
    (h : Safe.execTransaction_registry ctx target value data operation safeTxGas baseGas gasPrice
      gasToken refundReceiver signatures s = .success ok s') :
    s'.storageWords = (s.writeSlot 5 (Verity.EVM.Uint256.add (s.storage 5) 1)).storageWords := by
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
  obtain ⟨_, h⟩ := require_bind_success h
  obtain ⟨_, s3, hcheck, h⟩ := bind_success_iff.mp h
  have h3 := (checkNSignatures_sound _ _ _ _ _ _ _ hcheck).1.hStorage
  have tail : ∀ c : Contract Bool, KS c → c s3 = .success ok s' → s'.storageWords = s3.storageWords :=
    fun c hc hrun => by unfold KS at hc; exact hc _ _ _ hrun
  rw [tail _ ?_ h, h3]
  · rfl
  repeat' with_reducible first
    | apply ks_bind
    | apply ks_ite
    | apply ks_prod
    | exact ks_pure _
    | exact ks_require _ _
    | exact ks_revertEmpty
    | exact ks_mloadLive _
    | exact ks_mstore _ _
    | exact ks_returndataSizeLive
    | exact ks_copyBytes _ _
    | exact ks_txOrigin
    | exact ks_gasPrice
    | exact ks_emit2 _ _ _
    | exact ks_requireOutcome _ _ _ _
    | exact ks_paymentAmount _ _ _ _ _ _
    | exact ks_evmCallWords _ hAdv _ _ _ _ _ _ _
    | exact ks_evmDelegateCallWords _ hAdv _ _ _ _ _ _
    | intro _

end SafeVerity.Proofs
