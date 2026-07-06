/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev

/-!
# Definitions and basic lemmas about highly abundant numbers and lcm(1..n)

`lcm (1..n)` is mathlib's `Nat.lcmUpto`, re-exported here so it can be named
without qualification.
-/
open Nat

notation "σ₁" => ArithmeticFunction.sigma 1

export Nat (lcmUpto)

/-- Definition of highly abundant number -/
def IsHighlyAbundant (N : ℕ) : Prop :=
  ∀ m > 0, m < N → σ₁ m < σ₁ N

/- a few small examples of lcmUpto -/
example : lcmUpto 1 = 1 := rfl
example : lcmUpto 2 = 2 := rfl
example : lcmUpto 6 = 60 := rfl

open ArithmeticFunction

-- some helper lemmas
lemma sigma_one_apply_prime {p : ℕ} (hp : p.Prime) : σ₁ p = p + 1 := by
  have : σ₁ p = σ₁ (p ^ 1) := by simp
  rw [this, sigma_one_apply_prime_pow hp]
  simp

lemma sigma_one_apply_prime_pow' {p k : ℕ} (hp : p.Prime) :
    σ₁ (p ^ k) = (p ^ (k + 1) - 1) / (p - 1) := by
  rw [sigma_one_apply_prime_pow hp, Nat.geomSum_eq hp.two_le]

lemma cast_sigma_one_apply_prime_pow_aux' {α : Type*} [Field α] [CharZero α] {p k : ℕ}
    (hp : p.Prime) :
    (σ₁ (p ^ k) : α) = (p ^ (k + 1) - 1 : ℕ) / (p - 1 : ℕ) := by
  have : 1 ≤ p := hp.one_le
  rw [sigma_one_apply_prime_pow' hp, Nat.cast_div (Nat.sub_one_dvd_pow_sub_one p (k + 1))]
  simp only [ne_eq, cast_eq_zero]
  have := hp.two_le
  lia

lemma cast_sigma_one_apply_prime_pow' {α : Type*} [Field α] [CharZero α] {p k : ℕ} (hp : p.Prime) :
    (σ₁ (p ^ k) : α) = (p ^ (k + 1) - 1) / (p - 1) := by
  have : 1 ≤ p := hp.one_le
  rw [cast_sigma_one_apply_prime_pow_aux' hp, Nat.cast_sub (one_le_pow _ _ hp.pos),
    Nat.cast_sub this, Nat.cast_one, Nat.cast_pow]

lemma factorization_eq {n p k : ℕ} (h₁ : p ^ k ∣ n) (h₂ : ¬ p ^ (k + 1) ∣ n)
    (hp : p.Prime) :
    n.factorization p = k := by
  have hn : n ≠ 0 := by
    contrapose! h₂
    simp [h₂]
  suffices k ≤ Nat.factorization n p ∧ ¬ (k + 1 ≤ Nat.factorization n p) by lia
  simp [← hp.pow_dvd_iff_le_factorization hn, *]

lemma Nat.factorization_finsetLcm {α : Type*} {p : ℕ} {s : Finset α} {f : α → ℕ}
    (h : ∀ x ∈ s, f x ≠ 0) :
    (s.lcm f).factorization p = s.sup (fun i ↦ (f i).factorization p) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
    simp only [Finset.mem_insert, ne_eq, forall_eq_or_imp] at h
    rw [Finset.lcm_insert, lcm_eq_nat_lcm, Nat.factorization_lcm h.1 (by simpa using h.2)]
    simp only [Finset.sup_insert, Finsupp.sup_apply, ih h.2]

@[simp, grind .] lemma lcmUpto_ne_zero {n : ℕ} : lcmUpto n ≠ 0 := by simp [Nat.lcmUpto]
@[simp, grind .] lemma lcmUpto_pos {n : ℕ} : 0 < lcmUpto n := lcmUpto_ne_zero.bot_lt

lemma dvd_lcmUpto_of_le {p n : ℕ} (hp : p ≠ 0) (hpn : p ≤ n) : p ∣ lcmUpto n := by
  apply Finset.dvd_lcm
  grind

lemma factorization_lcmUpto_sup {p n : ℕ} :
    (lcmUpto n).factorization p = Finset.sup (Finset.Icc 1 n) (fun i ↦ i.factorization p) := by
  apply Nat.factorization_finsetLcm
  grind

lemma factorization_lcmUpto_le {n p k : ℕ} (h' : n < p ^ (k + 1)) (hp : p.Prime) :
    (lcmUpto n).factorization p ≤ k := by
  simp only [factorization_lcmUpto_sup, Finset.sup_le_iff, Finset.mem_Icc, and_imp]
  intro i hi hin
  suffices ¬ (k + 1 ≤ i.factorization p) by lia
  rw [← hp.pow_dvd_iff_le_factorization (by lia)]
  intro h
  have := Nat.le_of_dvd (by lia) h
  lia

lemma factorization_lcmUpto_eq {n p k : ℕ} (h : p ^ k ≤ n) (h' : n < p ^ (k + 1)) (hp : p.Prime) :
    (lcmUpto n).factorization p = k := by
  apply le_antisymm
  · apply factorization_lcmUpto_le h' hp
  · rw [← hp.pow_dvd_iff_le_factorization (by simp)]
    apply dvd_lcmUpto_of_le (pow_ne_zero _ hp.ne_zero) h

lemma factorization_lcmUpto_le_one {p n : ℕ} (hp : p.Prime) (hnp : n < p ^ 2) :
    (lcmUpto n).factorization p ≤ 1 :=
  factorization_lcmUpto_le hnp hp

lemma not_dvd_of_lt {n p k : ℕ} (h' : n < p ^ (k + 1)) (hp : p.Prime) :
    ¬ p ^ (k + 1) ∣ lcmUpto n := by
  rw [hp.pow_dvd_iff_le_factorization (by grind)]
  have := factorization_lcmUpto_le h' hp
  lia

lemma factorization_lcmUpto_eq_one {p n : ℕ} (hp : p.Prime) (hpn : p ≤ n) (hnp : n < p ^ 2) :
    (lcmUpto n).factorization p = 1 := by
  apply le_antisymm
  · apply factorization_lcmUpto_le_one hp hnp
  · rw [← hp.dvd_iff_one_le_factorization]
    · exact dvd_lcmUpto_of_le (by grind) hpn
    simp

lemma sq_not_dvd {p n : ℕ} (hp : p.Prime) (hnp : n < p ^ 2) : ¬ p ^ 2 ∣ lcmUpto n := by
  rw [hp.pow_dvd_iff_le_factorization lcmUpto_ne_zero, not_le]
  have := factorization_lcmUpto_le_one hp hnp
  lia

/-! ### `lcmUpto` is constant between consecutive prime powers

`lcmUpto n` only increases when `n` crosses a prime power. If there is no prime power in `(m, n]`
then `lcmUpto m = lcmUpto n`, and highly-abundant-ness transfers along such a block.
-/

open ArithmeticFunction

/-- For a prime `p`, the `p`-adic valuation of `lcmUpto x` is `Nat.log p x`. -/
lemma factorization_lcmUpto_eq_log {p x : ℕ} (hp : p.Prime) :
    (lcmUpto x).factorization p = Nat.log p x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [Nat.lcmUpto]
  · apply factorization_lcmUpto_eq (Nat.pow_log_le_self p hx.ne')
      (Nat.lt_pow_succ_log_self hp.one_lt x) hp

/-- If no prime power lies in `(m, n]` (with `m ≤ n`), then `lcmUpto m = lcmUpto n`. -/
theorem lcmUpto_eq_of_no_primePow_mem {m n : ℕ} (hmn : m ≤ n)
    (h : ∀ q, IsPrimePow q → m < q → n < q) : lcmUpto m = lcmUpto n := by
  refine Nat.factorization_inj (by simp) (by simp) ?_
  ext p
  by_cases hp : p.Prime
  · rw [factorization_lcmUpto_eq_log hp, factorization_lcmUpto_eq_log hp]
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
theorem isHighlyAbundant_lcmUpto_of_le {m n : ℕ} (hmn : m ≤ n)
    (h : ∀ q, IsPrimePow q → m < q → n < q) (hm : IsHighlyAbundant (lcmUpto m)) :
    IsHighlyAbundant (lcmUpto n) := by rwa [lcmUpto_eq_of_no_primePow_mem hmn h] at hm

/-- Transfer `IsHighlyAbundant (lcmUpto ·)` along a block given as a finite gap condition on
`Finset.Ioc m n`. This form is dischargeable by `decide` for concrete `m`, `n`. -/
theorem isHighlyAbundant_lcmUpto_of_no_primePow_Ioc {m n : ℕ} (hmn : m ≤ n)
    (hgap : ∀ x ∈ Finset.Ioc m n, ¬ IsPrimePow x) (hm : IsHighlyAbundant (lcmUpto m)) :
    IsHighlyAbundant (lcmUpto n) := by
  refine isHighlyAbundant_lcmUpto_of_le hmn (fun q hq hmq ↦ ?_) hm
  by_contra hc
  push Not at hc
  exact hgap q (Finset.mem_Ioc.2 ⟨hmq, hc⟩) hq
