/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Chebyshev

public section

/-!
# Definitions and basic lemmas about highly abundant numbers and lcm(1..n)

`lcm (1..n)` is mathlib's `Nat.lcmUpto`.
-/
open Nat

notation "σ₁" => ArithmeticFunction.sigma 1

/-- Definition of highly abundant number -/
@[expose]
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

/-- `n ^ k` is one of the terms of `sigma k n`, so it bounds the sum below. -/
lemma pow_le_sigma {k n : ℕ} (hn : n ≠ 0) : n ^ k ≤ ArithmeticFunction.sigma k n := by
  rw [sigma_apply]
  exact Finset.single_le_sum (f := fun d ↦ d ^ k) (fun i _ ↦ Nat.zero_le _)
    (Nat.mem_divisors_self _ hn)

lemma le_sigma_one {n : ℕ} (hn : n ≠ 0) : n ≤ σ₁ n := by
  simpa using pow_le_sigma (k := 1) hn


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

attribute [simp, grind .] Nat.lcmUpto_ne_zero Nat.lcmUpto_pos

lemma dvd_lcmUpto_of_le {p n : ℕ} (hp : p ≠ 0) (hpn : p ≤ n) : p ∣ lcmUpto n := by
  apply Finset.dvd_lcm
  grind

/-- For `2 ≤ n` the divisor sum of `lcm (1..n)` is at least `2`. -/
lemma two_le_sigma_lcmUpto {n : ℕ} (hn : 2 ≤ n) : 2 ≤ σ₁ (lcmUpto n) :=
  le_trans (Nat.le_of_dvd (lcmUpto_pos n) (dvd_lcmUpto_of_le two_ne_zero hn))
    (le_sigma_one (lcmUpto_ne_zero n))

lemma factorization_lcmUpto_le {n p k : ℕ} (h' : n < p ^ (k + 1)) (hp : p.Prime) :
    (lcmUpto n).factorization p ≤ k := by
  rw [Nat.factorization_lcmUpto n hp]
  have := Nat.log_lt_of_lt_pow' (Nat.succ_ne_zero k) h'
  lia

lemma factorization_lcmUpto_eq {n p k : ℕ} (h : p ^ k ≤ n) (h' : n < p ^ (k + 1)) (hp : p.Prime) :
    (lcmUpto n).factorization p = k := by
  rw [Nat.factorization_lcmUpto n hp, Nat.log_eq_of_pow_le_of_lt_pow h h']

lemma factorization_lcmUpto_le_one {p n : ℕ} (hp : p.Prime) (hnp : n < p ^ 2) :
    (lcmUpto n).factorization p ≤ 1 :=
  factorization_lcmUpto_le hnp hp

lemma factorization_lcmUpto_eq_one {p n : ℕ} (hp : p.Prime) (hpn : p ≤ n) (hnp : n < p ^ 2) :
    (lcmUpto n).factorization p = 1 := by
  apply le_antisymm
  · apply factorization_lcmUpto_le_one hp hnp
  · rw [← hp.dvd_iff_one_le_factorization]
    · exact dvd_lcmUpto_of_le (by grind) hpn
    simp

lemma sq_not_dvd {p n : ℕ} (hp : p.Prime) (hnp : n < p ^ 2) : ¬ p ^ 2 ∣ lcmUpto n := by
  rw [hp.pow_dvd_iff_le_factorization (lcmUpto_ne_zero _), not_le]
  have := factorization_lcmUpto_le_one hp hnp
  lia

/-! ### `lcmUpto` is constant between consecutive prime powers

`lcmUpto n` only increases when `n` crosses a prime power. If there is no prime power in `(m, n]`
then `lcmUpto m = lcmUpto n`, and highly-abundant-ness transfers along such a block.
-/

/-- If no prime power lies in `(m, n]` (with `m ≤ n`), then `lcmUpto m = lcmUpto n`. -/
theorem lcmUpto_eq_of_le {m n : ℕ} (hmn : m ≤ n)
    (h : ∀ q, IsPrimePow q → m < q → n < q) : lcmUpto m = lcmUpto n := by
  refine Nat.factorization_inj (by simp) (by simp) ?_
  ext p
  by_cases hp : p.Prime
  · rw [Nat.factorization_lcmUpto m hp, Nat.factorization_lcmUpto n hp]
    refine le_antisymm (Nat.log_mono_right hmn) ?_
    by_contra! hlt
    have hpp : IsPrimePow (p ^ Nat.log p n) := hp.isPrimePow.pow (by lia)
    grind [Nat.pow_log_le_self, Nat.lt_pow_of_log_lt, hp.one_lt]
  · simp [hp]

/-- Highly-abundant-ness transfers across a block with no prime power in `(m, n]`. -/
theorem isHighlyAbundant_lcmUpto_of_le {m n : ℕ} (hmn : m ≤ n)
    (h : ∀ q, IsPrimePow q → m < q → n < q) (hm : IsHighlyAbundant (lcmUpto m)) :
    IsHighlyAbundant (lcmUpto n) := by rwa [lcmUpto_eq_of_le hmn h] at hm

/-- Transfer `IsHighlyAbundant (lcmUpto ·)` along a block given as a finite gap condition on
`Finset.Ioc m n`. This form is dischargeable by `decide` for concrete `m`, `n`. -/
theorem isHighlyAbundant_lcmUpto_of_no_primePow_Ioc {m n : ℕ} (hmn : m ≤ n)
    (hgap : ∀ x ∈ Finset.Ioc m n, ¬ IsPrimePow x) (hm : IsHighlyAbundant (lcmUpto m)) :
    IsHighlyAbundant (lcmUpto n) := by
  refine isHighlyAbundant_lcmUpto_of_le hmn (fun q hq hmq ↦ ?_) hm
  by_contra! hc
  exact hgap q (Finset.mem_Ioc.2 ⟨hmq, hc⟩) hq
