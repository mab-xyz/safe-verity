import Safe.Contract

/-!
# P4: the GS013 rule and the refund amount

`requireOutcome` and `paymentAmount` are the two pieces of `execTransaction` that decide, after the
inner call, whether the transaction stands and how much it pays. Gas itself is not modelled
(`gasleftModel` is opaque), so `gasUsed` is an arbitrary input here.
-/

namespace SafeVerity.Proofs
open Verity Contracts

local notation "M" => Verity.Core.Uint256.modulus

/-- GS013: the post-call check passes iff the inner call succeeded, or the transaction set a
`safeTxGas` or a `gasPrice`; it never changes state. -/
theorem requireOutcome_success_iff (success safeTxGas gasPrice : Uint256) (s s' : ContractState) :
    Safe.requireOutcome success safeTxGas gasPrice s = .success () s' ↔
      (success = 1 ∨ safeTxGas ≠ 0 ∨ gasPrice ≠ 0) ∧ s' = s := by
  unfold Safe.requireOutcome
  by_cases h : success = 1 ∨ safeTxGas ≠ 0 ∨ gasPrice ≠ 0
  · have hb : (success == 1 || safeTxGas != 0 || gasPrice != 0) = true := by
      rcases h with h | h | h <;> simp [h]
    simp [Verity.require, hb, h, eq_comm]
  · have hb : (success == 1 || safeTxGas != 0 || gasPrice != 0) = false := by
      simp only [not_or, ne_eq, not_not] at h
      simp [h.1, h.2.1, h.2.2]
    simp [Verity.require, hb, h]

/-- The price per gas unit the refund uses: capped by `tx.gasprice` for ETH, as signed for a token. -/
def refundPrice (gasPrice txPrice : Uint256) (gasToken : Address) : Uint256 :=
  if gasToken = zeroAddress then Contracts.min gasPrice txPrice else gasPrice

private theorem maxWord_val : Safe.maxWord.val = M - 1 := by
  decide

/-- The refund amount is SafeMath's `gasUsed.add(baseGas).mul(price)`: the exact product when
neither step overflows, otherwise an empty revert; state is never changed. -/
theorem paymentAmount_eq (gasUsed baseGas gasPrice txPrice : Uint256) (gasToken : Address)
    (s : ContractState) :
    Safe.paymentAmount gasUsed baseGas gasPrice gasToken txPrice s =
      if gasUsed.val + baseGas.val < M ∧
          (gasUsed.val + baseGas.val) * (refundPrice gasPrice txPrice gasToken).val < M
      then .success (Verity.Core.Uint256.ofNat ((gasUsed.val + baseGas.val) *
          (refundPrice gasPrice txPrice gasToken).val)) s
      else .revert "" s := by
  have hM2 : 2 ≤ M := by decide
  have hg : gasUsed.val < M := gasUsed.isLt
  have hb : baseGas.val < M := baseGas.isLt
  set price := refundPrice gasPrice txPrice gasToken with hprice
  have hp : price.val < M := price.isLt
  have hsub : (Verity.EVM.Uint256.sub Safe.maxWord baseGas).val = M - 1 - baseGas.val := by
    simp only [Verity.EVM.Uint256.sub, Verity.Core.Uint256.sub, maxWord_val]
    rw [if_pos (by omega)]
    simp only [Verity.Core.Uint256.val_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  unfold Safe.paymentAmount
  by_cases hov : gasUsed.val + baseGas.val < M
  · have hle : ¬ gasUsed > Verity.EVM.Uint256.sub Safe.maxWord baseGas := by
      simp only [gt_iff_lt, Verity.Core.Uint256.lt_def, hsub]; omega
    have hbase : (Verity.EVM.Uint256.add gasUsed baseGas).val = gasUsed.val + baseGas.val := by
      show (Verity.Core.Uint256.add gasUsed baseGas).val = _
      simp only [Verity.Core.Uint256.add, Verity.Core.Uint256.val_ofNat]
      exact Nat.mod_eq_of_lt hov
    simp only [hle, ↓reduceIte, hov, true_and]
    have hpr : (if (gasToken == Verity.zeroAddress) = true then Contracts.min gasPrice txPrice
        else gasPrice) = price := by
      simp [hprice, refundPrice]
    rw [hpr]
    by_cases hmul : (gasUsed.val + baseGas.val) * price.val < M
    · have hno : ¬ ((Verity.EVM.Uint256.add gasUsed baseGas != 0 &&
          decide (price > Verity.EVM.Uint256.div Safe.maxWord (Verity.EVM.Uint256.add gasUsed baseGas)))
          = true) := by
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_and]
        intro hne
        have hpos : 0 < gasUsed.val + baseGas.val := by
          rw [← hbase]; rcases Nat.eq_zero_or_pos (Verity.EVM.Uint256.add gasUsed baseGas).val with h | h
          · exact absurd (Verity.Core.Uint256.ext (by simpa using h)) hne
          · exact h
        simp only [gt_iff_lt, Verity.Core.Uint256.lt_def, not_lt, Verity.EVM.Uint256.div,
          Verity.Core.Uint256.div, hbase, maxWord_val, Nat.pos_iff_ne_zero.mp hpos, ↓reduceIte,
          Verity.Core.Uint256.val_ofNat]
        rw [Nat.mod_eq_of_lt (by have := Nat.div_le_self (M - 1) (gasUsed.val + baseGas.val); omega)]
        rw [Nat.le_div_iff_mul_le hpos]; rw [Nat.mul_comm]; omega
      simp only [hno, Bool.false_eq_true, ↓reduceIte, hmul, Bind.bind, Pure.pure, Verity.bind,
        Verity.pure]
      congr 1
      show Verity.Core.Uint256.mul _ _ = _
      simp [Verity.Core.Uint256.mul, hbase]
    · have hyes : (Verity.EVM.Uint256.add gasUsed baseGas != 0 &&
          decide (price > Verity.EVM.Uint256.div Safe.maxWord (Verity.EVM.Uint256.add gasUsed baseGas)))
          = true := by
        have hpos : 0 < gasUsed.val + baseGas.val := by
          rcases Nat.eq_zero_or_pos (gasUsed.val + baseGas.val) with h | h
          · rw [h] at hmul; simp at hmul; exact absurd (by decide : 0 < M) (by omega)
          · exact h
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
        refine ⟨fun h0 => by have := congrArg Verity.Core.Uint256.val h0; simp [hbase] at this; omega, ?_⟩
        simp only [gt_iff_lt, Verity.Core.Uint256.lt_def, Verity.EVM.Uint256.div,
          Verity.Core.Uint256.div, hbase, maxWord_val, Nat.pos_iff_ne_zero.mp hpos, ↓reduceIte,
          Verity.Core.Uint256.val_ofNat]
        rw [Nat.mod_eq_of_lt (by have := Nat.div_le_self (M - 1) (gasUsed.val + baseGas.val); omega)]
        rw [Nat.div_lt_iff_lt_mul hpos]; rw [Nat.mul_comm]; omega
      simp only [hyes, ↓reduceIte, hmul, Bind.bind, Pure.pure, Verity.bind, Verity.pure, revertEmpty]
  · have hgt : gasUsed > Verity.EVM.Uint256.sub Safe.maxWord baseGas := by
      simp only [gt_iff_lt, Verity.Core.Uint256.lt_def, hsub]; omega
    simp only [hgt, ↓reduceIte, hov, Bind.bind, Verity.bind, revertEmpty, false_and]

end SafeVerity.Proofs
