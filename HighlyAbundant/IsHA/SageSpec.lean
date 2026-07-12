/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import HighlyAbundant.Basic
public import HighlyAbundant.IsHA.Sage
public import HighlyAbundant.Prime.TrialDivision
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.Prime.Nth
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Algebra.BigOperators.Intervals

public section

/-!
# Correctness of the `lcm (1..n)` highly-abundant decider

Specification and correctness for the search in `HighlyAbundant.Sage`. The witness set
`W B goal cand idx` collects the `t` a node `(goal, cand, idx)` still admits: `t ∈ P idx` with
`cand * t < B` and `goal ≤ σ₁ t`, where `P j` is the naturals all of whose prime factors are at
least the `j`-th prime. The search answers `some true` exactly when the root witness set is empty,
which for `(B, sL) = (lcmUpto n, σ₁ (lcmUpto n))` says `lcmUpto n` is highly abundant.
-/
set_option linter.mathlibStandardSet true

open Nat Finset ArithmeticFunction

attribute [grind .] sigma_pos

namespace Sage

/-! ### Specification: `P`, `W`, `lcmData` -/

/-- `P j`: naturals `≥ 1` whose every prime factor is at least the `j`-th prime. -/
def P (j : ℕ) : Set ℕ :=
  { t | 1 ≤ t ∧ ∀ q : ℕ, q.Prime → q ∣ t → nth Nat.Prime j ≤ q }

@[grind =] lemma mem_P {j t : ℕ} :
    t ∈ P j ↔ 1 ≤ t ∧ ∀ q : ℕ, q.Prime → q ∣ t → nth Nat.Prime j ≤ q :=
  Iff.rfl

/-- The witness set of a node `(goal, cand, idx)` for bound `B`. -/
def W (B goal cand idx : ℕ) : Set ℕ :=
  { t | t ∈ P idx ∧ cand * t < B ∧ goal ≤ σ₁ t }

@[simp, grind =] lemma mem_W {B goal cand idx t : ℕ} :
    t ∈ W B goal cand idx ↔ t ∈ P idx ∧ cand * t < B ∧ goal ≤ σ₁ t :=
  Iff.rfl

/-! ### The `primes` table -/

private lemma primesRArray_get_eq_nth_aux (i : Fin 49) :
    primesRArray.get i.val = nth Nat.Prime i.val := by
  have hp : ∀ i : Fin 49, Nat.Prime (primesRArray.get i.val) := by
    intro i
    refine checkPrime_true ?_
    fin_cases i <;> rfl
  rw [← nth_count (hp i)]
  congr 1
  decide +kernel +revert

/-- The wheel's array lookup gives the `i`-th prime. -/
@[grind <=]
private lemma primesRArray_get_eq_nth {i : ℕ} (hi : i < 49) :
    primesRArray.get i = nth Nat.Prime i :=
  primesRArray_get_eq_nth_aux ⟨i, hi⟩

/-! ### Membership in `P` -/

/-- If `x ≥ 1` and every prime factor of `x` exceeds the `front`-th prime, then
`x ∈ P (front + 1)`. -/
private lemma mem_P_succ_of_factors_gt {x front : ℕ} (hx : 1 ≤ x)
    (h : ∀ q, q.Prime → q ∣ x → nth Nat.Prime front < q) : x ∈ P (front + 1) :=
  ⟨hx, fun q hq hqd => by by_contra! hlt; grind [le_nth_of_lt_nth_succ hlt hq]⟩

/-- If `t ∈ P front`, `p ≥ nth Nat.Prime front` is a prime, `t = p^k * t'` with `t'`
coprime to `p`, and `∀ q ∣ t prime, p ≤ q`, then `t' ∈ P (front + 1)`. -/
private lemma mem_P_succ_of_coprime {t t' p k front : ℕ}
    (hp_prime : p.Prime) (hp_geprimes : nth Nat.Prime front ≤ p)
    (hp_min : ∀ q, q.Prime → q ∣ t → p ≤ q) (hpk_t : p ^ k * t' = t)
    (ht'₀ : 1 ≤ t') (hcoprime : Nat.Coprime p t') : t' ∈ P (front + 1) :=
  mem_P_succ_of_factors_gt ht'₀ fun q hq hqd =>
    hp_geprimes.trans_lt (lt_of_le_of_ne
      (hp_min q hq (hpk_t ▸ dvd_mul_of_dvd_right hqd _))
      fun hqp => hp_prime.coprime_iff_not_dvd.mp hcoprime (hqp ▸ hqd))

open omega

/-- After factoring `t = p^k * t'` with `k ≥ 1`, `p` prime, and `Coprime p t'`, the prime
factors of `t` are those of `t'` plus `{p}`. -/
private lemma card_primeFactors_coprime {t t' p k : ℕ} (hp_prime : p.Prime)
    (hk : 1 ≤ k) (hpk_t : p ^ k * t' = t) (hcoprime : p.Coprime t') :
    #t.primeFactors = #t'.primeFactors + 1 := by
  have hp_not_t' : p ∉ t'.primeFactors := fun h =>
    hp_prime.coprime_iff_not_dvd.mp hcoprime (mem_primeFactors.mp h).2.1
  rw [← hpk_t, (hcoprime.pow_left k).primeFactors_mul,
    primeFactors_pow p (by lia), hp_prime.primeFactors,
    card_union_of_disjoint (disjoint_singleton_left.mpr hp_not_t'),
    card_singleton, Nat.add_comm]

/-- `1 ∈ P j` for any `j` since `1` has no prime factors. -/
@[simp, grind .] private theorem one_mem_P (j : ℕ) : 1 ∈ P j := by
  grind [Nat.not_prime_one, Nat.dvd_one]

/-! ### Multiplicative decomposition -/

/-- Decompose `t` at a prime factor `p`: `t = p ^ k * t'` with `k ≥ 1`, `Coprime p t'`,
`1 ≤ t' < t`. -/
private lemma exists_factor_decomp {t p : ℕ} (hp : p.Prime) (hpt : p ∣ t) (htne : t ≠ 0) :
    ∃ k t' : ℕ, 1 ≤ k ∧ p ^ k * t' = t ∧ 1 ≤ t' ∧ t' < t ∧ Nat.Coprime p t' := by
  set k := t.factorization p
  set t' := ordCompl[p] t
  have hk₀ : 1 ≤ k :=
    (hp.pow_dvd_iff_le_factorization htne).mp (by simpa using hpt)
  have hpk_t : ordProj[p] t * t' = t := ordProj_mul_ordCompl_eq_self t p
  have hpk_ge2 : 2 ≤ ordProj[p] t :=
    hp.two_le.trans (by simpa using Nat.pow_le_pow_right hp.one_lt.le hk₀)
  have ht'₀ : 1 ≤ t' := Nat.ordCompl_pos _ htne
  refine ⟨k, t', hk₀, hpk_t, ht'₀, ?_, coprime_ordCompl hp htne⟩
  nlinarith [hpk_t, hpk_ge2, ht'₀]

/-- For `t ≥ 2`, decompose at the smallest prime factor. -/
private lemma exists_minFac_decomp {t : ℕ} (ht : 2 ≤ t) :
    ∃ p k t' : ℕ, p.Prime ∧ p ∣ t ∧ 1 ≤ k ∧ p ^ k * t' = t ∧
      1 ≤ t' ∧ t' < t ∧ Nat.Coprime p t' ∧
      (∀ q, q.Prime → q ∣ t → p ≤ q) := by
  obtain ⟨k, t', hk, hpkt, ht'p, ht'l, hcop⟩ :=
    exists_factor_decomp (minFac_prime (by omega)) (minFac_dvd t) (by omega)
  exact ⟨_, k, t', minFac_prime (by omega), minFac_dvd t, hk, hpkt, ht'p, ht'l,
    hcop, fun q hq hqd => minFac_le_of_dvd hq.two_le hqd⟩

end Sage
