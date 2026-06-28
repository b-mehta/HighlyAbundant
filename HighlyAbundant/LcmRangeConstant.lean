/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.Basic

/-!
# `lcmRange` is constant between consecutive prime powers

`lcmRange n` only increases when `n` crosses a prime power. If there is no prime power in `(m, n]`
then `lcmRange m = lcmRange n`, and highly-abundant-ness transfers along such a block.
-/

open Nat ArithmeticFunction

/-- For a prime `p`, the `p`-adic valuation of `lcmRange x` is `Nat.log p x`. -/
lemma factorization_lcmRange_eq_log {p x : ℕ} (hp : p.Prime) :
    (lcmRange x).factorization p = Nat.log p x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [lcmRange]
  · apply factorization_lcmRange_eq (Nat.pow_log_le_self p hx.ne')
      (Nat.lt_pow_succ_log_self hp.one_lt x) hp

/-- If no prime power lies in `(m, n]` (with `m ≤ n`), then `lcmRange m = lcmRange n`. -/
theorem lcmRange_eq_of_no_primePow_mem {m n : ℕ} (hmn : m ≤ n)
    (h : ∀ q, IsPrimePow q → m < q → n < q) : lcmRange m = lcmRange n := by
  refine Nat.factorization_inj (by simp) (by simp) ?_
  ext p
  by_cases hp : p.Prime
  · rw [factorization_lcmRange_eq_log hp, factorization_lcmRange_eq_log hp]
    refine le_antisymm (Nat.log_mono_right hmn) ?_
    by_contra! hlt
    have hj : 1 ≤ Nat.log p n := by lia
    have hn : n ≠ 0 := by
      rintro rfl
      simp at hlt
    have hle : p ^ Nat.log p n ≤ n := Nat.pow_log_le_self p hn
    have hgt : m < p ^ Nat.log p n :=
      (Nat.lt_pow_succ_log_self hp.one_lt m).trans_le (Nat.pow_le_pow_right hp.pos hlt)
    have hpp : IsPrimePow (p ^ Nat.log p n) :=
      (isPrimePow_nat_iff _).2 ⟨p, Nat.log p n, hp, hj, rfl⟩
    exact absurd (h _ hpp hgt) (by lia)
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp, Nat.factorization_eq_zero_of_not_prime _ hp]

/-- Highly-abundant-ness transfers across a block with no prime power in `(m, n]`. -/
theorem isHighlyAbundant_lcmRange_of_le {m n : ℕ} (hmn : m ≤ n)
    (h : ∀ q, IsPrimePow q → m < q → n < q) (hm : IsHighlyAbundant (lcmRange m)) :
    IsHighlyAbundant (lcmRange n) := by rwa [lcmRange_eq_of_no_primePow_mem hmn h] at hm

/-- Transfer `IsHighlyAbundant (lcmRange ·)` along a block given as a finite gap condition on
`Finset.Ioc m n`. This form is dischargeable by `decide` for concrete `m`, `n`. -/
theorem isHighlyAbundant_lcmRange_of_no_primePow_Ioc {m n : ℕ} (hmn : m ≤ n)
    (hgap : ∀ x ∈ Finset.Ioc m n, ¬ IsPrimePow x) (hm : IsHighlyAbundant (lcmRange m)) :
    IsHighlyAbundant (lcmRange n) := by
  refine isHighlyAbundant_lcmRange_of_le hmn (fun q hq hmq ↦ ?_) hm
  by_contra hc
  push Not at hc
  exact hgap q (Finset.mem_Ioc.2 ⟨hmq, hc⟩) hq
