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

/-! ## Memory bookkeeping: writes at `p + 32k` read back by `keccak256(p, ·)` -/

/-- One `mstore`'s effect on the word map. -/
def wr (m : Nat → Uint256) (o v : Uint256) : Nat → Uint256 := fun k => if k = o.val then v else m k

theorem mstore_run' (o v : Uint256) (s : ContractState) :
    Contracts.mstore o v s = .success () { s with memory := wr s.memory o v } := mstore_run o v s

local notation "M" => Verity.Core.Uint256.modulus

theorem M_eq : M = 2 ^ 256 := rfl

@[simp] theorem val_lit (n : Nat) : (OfNat.ofNat n : Verity.Core.Uint256).val = n % M := rfl

@[simp] theorem add_val (a b : Uint256) : (Verity.EVM.Uint256.add a b).val = (a.val + b.val) % M := rfl

/-- Reading key `(p + j) mod 2^256` after a write at key `(p + i) mod 2^256`, offsets below 2^256. -/
theorem wr_off (m : Nat → Uint256) (p v : Uint256) (i j : Nat) (hi : i < 2 ^ 256) (hj : j < 2 ^ 256) :
    wr m (Verity.EVM.Uint256.add p (no_index (OfNat.ofNat i))) v ((p.val + j) % M) =
      if i = j then v else m ((p.val + j) % M) := by
  have hp : p.val < 2 ^ 256 := p.isLt
  unfold wr
  simp only [add_val, val_lit, M_eq]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg, if_neg h]
    rw [Nat.mod_eq_of_lt hi]
    omega

theorem wr_off0 (m : Nat → Uint256) (p v : Uint256) (j : Nat) (hj : j < 2 ^ 256) :
    wr m p v ((p.val + j) % M) = if 0 = j then v else m ((p.val + j) % M) := by
  have hp : p.val < 2 ^ 256 := p.isLt
  unfold wr
  simp only [M_eq]
  by_cases h : 0 = j
  · subst h; rw [Nat.add_zero, Nat.mod_eq_of_lt hp]; simp
  · rw [if_neg, if_neg h]; omega

theorem key_eq_iff (a i j : Nat) (ha : a < 2 ^ 256) (hi : i < 2 ^ 256) (hj : j < 2 ^ 256) :
    ((a + i) % 2 ^ 256 = (a + j) % 2 ^ 256) ↔ i = j := by
  constructor
  · intro h; omega
  · intro h; subst h; rfl

theorem key0_iff (a j : Nat) (ha : a < 2 ^ 256) (hj : j < 2 ^ 256) :
    ((a + j) % 2 ^ 256 = a) ↔ j = 0 := by
  constructor
  · intro h; omega
  · intro h; subst h; rw [Nat.add_zero]; exact Nat.mod_eq_of_lt ha

theorem key0_iff' (a j : Nat) (ha : a < 2 ^ 256) (hj : j < 2 ^ 256) :
    (a = (a + j) % 2 ^ 256) ↔ j = 0 := by
  rw [eq_comm]; exact key0_iff a j ha hj

theorem val_lt (x : Uint256) : x.val < 2 ^ 256 := x.isLt

/-- The offsets `consumeNonce` adds to its buffer pointer. -/
theorem lit_vals :
    (Verity.Core.Uint256.val 2 = 2) ∧ (Verity.Core.Uint256.val 32 = 32) ∧
    (Verity.Core.Uint256.val 34 = 34) ∧ (Verity.Core.Uint256.val 64 = 64) ∧
    (Verity.Core.Uint256.val 96 = 96) ∧ (Verity.Core.Uint256.val 128 = 128) ∧
    (Verity.Core.Uint256.val 160 = 160) ∧ (Verity.Core.Uint256.val 192 = 192) ∧
    (Verity.Core.Uint256.val 224 = 224) ∧ (Verity.Core.Uint256.val 256 = 256) ∧
    (Verity.Core.Uint256.val 288 = 288) ∧ (Verity.Core.Uint256.val 320 = 320) ∧
    (Verity.Core.Uint256.val 352 = 352) ∧ (Verity.Core.Uint256.val 66 = 66) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem words_eq (mem : Nat → Uint256) (p : Uint256) (size : Nat) :
    Compiler.Keccak.MemorySlice.words (fun a => (mem a).val) p.val size =
      (List.range ((size + 31) / 32)).map (fun i => (mem ((p.val + i * 32) % M)).val) := by
  simp [Compiler.Keccak.MemorySlice.words, Compiler.Keccak.MemorySlice.byteWordCount,
    Compiler.Constants.evmModulus, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]

/-- `keccak256(p, 96)` over three words written at `p, p + 32, p + 64`. -/
theorem keccak3 (m : Nat → Uint256) (p w0 w1 w2 : Uint256) (size : Nat)
    (hsize : (size + 31) / 32 = 3) :
    Verity.Core.Uint256.ofNat (Compiler.Keccak.MemorySlice.keccak
        (fun x => (wr (wr (wr m p w0) (Verity.EVM.Uint256.add p 32) w1)
          (Verity.EVM.Uint256.add p 64) w2 x).val) p.val size) =
      Spec.keccakWords [w0.val, w1.val, w2.val] size := by
  apply keccak_eq_keccakWords
  rw [words_eq, hsize]
  simp only [show List.range 3 = [0, 1, 2] from rfl, List.map_cons, List.map_nil, Nat.reduceMul,
    Nat.zero_mul, Nat.one_mul]
  simp (disch := first | decide | norm_num) only [wr_off, wr_off0, ↓reduceIte, Nat.reduceEqDiff]

/-- The domain separator: three words at the free pointer, hashed; only memory changes. -/
theorem domainSeparatorHash_spec (ctx : ExecutableCallContext) (s : ContractState) :
    ∃ m, Safe.domainSeparatorHash_registry ctx s =
      .success (Spec.domainSeparator s.chainId s.thisAddress) { s with memory := m } := by
  unfold Safe.domainSeparatorHash_registry
  simp only [Bind.bind, Pure.pure, Verity.bind, Verity.pure,
    Contracts.chainid, Verity.chainid, Contracts.contractAddress, Verity.contractAddress,
    Contracts.mloadLive, mstore_run', Contracts.keccak256Live]
  rw [show (96 : Verity.Core.Uint256).val = 96 from rfl, keccak3 _ _ _ _ _ 96 rfl]
  exact ⟨_, rfl⟩

/-- `keccak256(p, size)` over two words written at `p, p + 32` (size 33..64). -/
theorem keccak2 (m : Nat → Uint256) (p w0 w1 : Uint256) (size : Nat) (hsize : (size + 31) / 32 = 2) :
    Verity.Core.Uint256.ofNat (Compiler.Keccak.MemorySlice.keccak
        (fun x => (wr (wr m p w0) (Verity.EVM.Uint256.add p 32) w1 x).val) p.val size) =
      Spec.keccakWords [w0.val, w1.val] size := by
  apply keccak_eq_keccakWords
  rw [words_eq, hsize]
  simp only [show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_nil, Nat.reduceMul,
    Nat.zero_mul, Nat.one_mul]
  simp (disch := first | decide | norm_num) only [wr_off, wr_off0, ↓reduceIte, Nat.reduceEqDiff]

/-- `keccak256(p, 352)` over eleven words written at `p, p + 32, …, p + 320`. -/
theorem keccak11 (m : Nat → Uint256) (p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : Uint256) :
    Verity.Core.Uint256.ofNat (Compiler.Keccak.MemorySlice.keccak
        (fun x => (wr (wr (wr (wr (wr (wr (wr (wr (wr (wr (wr m p w0)
          (Verity.EVM.Uint256.add p 32) w1) (Verity.EVM.Uint256.add p 64) w2)
          (Verity.EVM.Uint256.add p 96) w3) (Verity.EVM.Uint256.add p 128) w4)
          (Verity.EVM.Uint256.add p 160) w5) (Verity.EVM.Uint256.add p 192) w6)
          (Verity.EVM.Uint256.add p 224) w7) (Verity.EVM.Uint256.add p 256) w8)
          (Verity.EVM.Uint256.add p 288) w9) (Verity.EVM.Uint256.add p 320) w10 x).val) p.val 352) =
      Spec.keccakWords [w0.val, w1.val, w2.val, w3.val, w4.val, w5.val, w6.val, w7.val, w8.val,
        w9.val, w10.val] 352 := by
  apply keccak_eq_keccakWords
  rw [words_eq]
  simp only [Nat.reduceAdd, Nat.reduceDiv,
    show List.range 11 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] from rfl, List.map_cons,
    List.map_nil, Nat.reduceMul, Nat.zero_mul, Nat.one_mul]
  simp (disch := first | decide | norm_num) only [wr_off, wr_off0, ↓reduceIte, Nat.reduceEqDiff]

/-! ## States that differ only in memory, kept small -/

/-- `s` with its memory replaced by `m`. -/
def withMem (s : ContractState) (m : Nat → Uint256) : ContractState := { s with memory := m }

@[simp] theorem withMem_withMem (s : ContractState) (a b : Nat → Uint256) :
    withMem (withMem s a) b = withMem s b := rfl
@[simp] theorem withMem_memory (s : ContractState) (m : Nat → Uint256) : (withMem s m).memory = m := rfl
@[simp] theorem withMem_readSlot (s : ContractState) (m : Nat → Uint256) (k : Nat) :
    (withMem s m).readSlot k = s.readSlot k := rfl
@[simp] theorem withMem_writeSlot (s : ContractState) (m : Nat → Uint256) (k : Nat) (v : Uint256) :
    (withMem s m).writeSlot k v = withMem (s.writeSlot k v) m := rfl

theorem mstore_withMem (o v : Uint256) (s : ContractState) :
    Contracts.mstore o v s = .success () (withMem s (wr s.memory o v)) := mstore_run o v s

/-- The memory `copyBytes data d` leaves, as a function of the memory before. -/
def copyMem' (data : ByteArray) (d : Uint256) (m : Nat → Uint256) : Nat → Uint256 :=
  copyMem data d { Verity.defaultState with memory := m }

theorem copyBytes_withMem (data : ByteArray) (d : Uint256) (s : ContractState) :
    Contracts.copyBytes data d s = .success () (withMem s (copyMem' data d s.memory)) := rfl

theorem keccak256Live_run (o n : Uint256) (s : ContractState) :
    Contracts.keccak256Live o n s =
      .success (Verity.Core.Uint256.ofNat
        (Compiler.Keccak.MemorySlice.keccak (fun a => (s.memory a).val) o.val n.val)) s := rfl

theorem mloadLive_run (o : Uint256) (s : ContractState) :
    Contracts.mloadLive o s = .success (s.memory o.val) s := rfl

theorem getStorage_run (f : StorageSlot Uint256) (s : ContractState) :
    Verity.getStorage f s = .success (s.readSlot f.slot) s := rfl

theorem setStorage_run (f : StorageSlot Uint256) (v : Uint256) (s : ContractState) :
    Verity.setStorage f v s = .success () (s.writeSlot f.slot v) := rfl

theorem domainSeparatorHash_withMem (ctx : ExecutableCallContext) (s : ContractState) :
    ∃ m, Safe.domainSeparatorHash_registry ctx s =
      .success (Spec.domainSeparator s.chainId s.thisAddress) (withMem s m) :=
  domainSeparatorHash_spec ctx s

theorem bind_success_eq {α β : Type} {m : Contract α} {f : α → Contract β} {s s1 : ContractState}
    {a : α} (h : m s = .success a s1) : (m >>= f) s = f a s1 := by
  simp only [Bind.bind, Verity.bind, h]

/-- **P2.** `consumeNonce` always succeeds. It returns the EIP-712 `txHash` (and `safeTxHash`) of the
transaction at the *current* nonce `n`, and its only storage effect is nonce := n + 1
(everything else but memory is unchanged). -/
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
          (withMem (s.writeSlot 5 (Verity.EVM.Uint256.add (s.storage 5) 1)) mem) := by
  obtain ⟨m1, hds⟩ := domainSeparatorHash_withMem ctx s
  unfold Safe.consumeNonce_registry
  rw [bind_success_eq (getStorage_run _ _), bind_success_eq hds, bind_success_eq (mloadLive_run _ _),
    bind_success_eq (copyBytes_withMem _ _ _), bind_success_eq (keccak256Live_run _ _ _)]
  repeat rw [bind_success_eq (mstore_withMem _ _ _)]
  rw [bind_success_eq (keccak256Live_run _ _ _)]
  repeat rw [bind_success_eq (mstore_withMem _ _ _)]
  rw [bind_success_eq (keccak256Live_run _ _ _), bind_success_eq (setStorage_run _ _ _)]
  simp only [withMem_withMem, withMem_memory, withMem_writeSlot, Pure.pure, Verity.pure]
  rw [show (352 : Verity.Core.Uint256).val = 352 from rfl, keccak11,
    show (66 : Verity.Core.Uint256).val = 66 from rfl, keccak3 _ _ _ _ _ 66 rfl]
  exact ⟨_, _, rfl⟩

end SafeVerity.Proofs
