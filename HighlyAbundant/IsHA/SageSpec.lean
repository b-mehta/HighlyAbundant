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

/-! ### The `primes` table -/

private lemma primesRArray_get_eq_nth_aux (i : Fin 49) :
    primesRArray.get i.val = nth Nat.Prime i.val := by
  have hp : ∀ i : Fin 49, Nat.Prime (primesRArray.get i.val) := by
    intro i
    refine checkPrime_true ?_
    revert i; decide +kernel
  rw [← nth_count (hp i)]
  congr 1
  decide +kernel +revert

/-- The wheel's array lookup gives the `i`-th prime. -/
@[grind <=]
private lemma primesRArray_get_eq_nth {i : ℕ} (hi : i < 49) :
    primesRArray.get i = nth Nat.Prime i :=
  primesRArray_get_eq_nth_aux ⟨i, hi⟩

/-! ### Ceiling division -/

@[grind =]
private theorem ceilDiv_le_iff {a b c : ℕ} (hb : 0 < b) : ceilDiv a b ≤ c ↔ a ≤ c * b := by
  rw [ceilDiv, div_le_iff_le_mul_add_pred hb, mul_comm]; lia

@[grind =]
private theorem lt_ceilDiv_iff {a b c : ℕ} (hb : 0 < b) : c < ceilDiv a b ↔ c * b < a :=
  lt_iff_lt_of_le_iff_le (ceilDiv_le_iff hb)

private theorem le_ceilDiv_mul {a b : ℕ} (hb : 0 < b) : a ≤ ceilDiv a b * b :=
  (ceilDiv_le_iff hb).mp le_rfl

/-! ### Specification: `P` and `W` -/

/-- `P j`: nonzero naturals whose every prime factor is at least the `j`-th prime. -/
def P (j : ℕ) : Set ℕ :=
  {t | t ≠ 0 ∧ ∀ q : ℕ, q.Prime → q ∣ t → nth Nat.Prime j ≤ q}

@[grind =] lemma mem_P {j t : ℕ} :
    t ∈ P j ↔ t ≠ 0 ∧ ∀ q : ℕ, q.Prime → q ∣ t → nth Nat.Prime j ≤ q :=
  Iff.rfl

/-- `1 ∈ P j` for any `j` since `1` has no prime factors. -/
@[simp, grind .] private theorem one_mem_P (j : ℕ) : 1 ∈ P j := by
  grind [Nat.not_prime_one, Nat.dvd_one]

/-- The witness set of a node `(goal, cand, idx)` for bound `B`. -/
def W (B goal cand idx : ℕ) : Set ℕ :=
  {t | t ∈ P idx ∧ cand * t < B ∧ goal ≤ σ₁ t}

@[simp, grind =] lemma mem_W {B goal cand idx t : ℕ} :
    t ∈ W B goal cand idx ↔ t ∈ P idx ∧ cand * t < B ∧ goal ≤ σ₁ t :=
  Iff.rfl

/-! ### Membership in `P` -/

/-- If `x ≠ 0` and every prime factor of `x` exceeds the `front`-th prime, then
`x ∈ P (front + 1)`. -/
private lemma mem_P_succ_of_factors_gt {x front : ℕ} (hx : x ≠ 0)
    (h : ∀ q, q.Prime → q ∣ x → nth Nat.Prime front < q) : x ∈ P (front + 1) :=
  ⟨hx, fun q hq hqd => by by_contra! hlt; grind [le_nth_of_lt_nth_succ hlt hq]⟩

/-- If `p ≥ nth Nat.Prime front` is prime, `t = p^k * t'` with `t'` nonzero and coprime to `p`,
and every prime factor of `t` is `≥ p`, then `t' ∈ P (front + 1)`. -/
private lemma mem_P_succ_of_coprime {t t' p k front : ℕ}
    (hp_prime : p.Prime) (hp_geprimes : nth Nat.Prime front ≤ p)
    (hp_min : ∀ q, q.Prime → q ∣ t → p ≤ q) (hpk_t : p ^ k * t' = t)
    (ht'₀ : t' ≠ 0) (hcoprime : Nat.Coprime p t') : t' ∈ P (front + 1) := by
  grind [mem_P_succ_of_factors_gt, hp_prime.coprime_iff_not_dvd]

/-! ### Multiplicative decomposition -/

/-- Decompose `t` at a prime factor `p`: `t = p ^ k * t'` with `0 < k`, `Coprime p t'`,
`0 < t'`, `t' < t`. -/
private lemma exists_factor_decomp {t p : ℕ} (hp : p.Prime) (hpt : p ∣ t) (htne : t ≠ 0) :
    ∃ k t' : ℕ, 0 < k ∧ p ^ k * t' = t ∧ 0 < t' ∧ t' < t ∧ Nat.Coprime p t' := by
  set k := t.factorization p
  set t' := ordCompl[p] t
  have hk₀ : 0 < k :=
    (hp.pow_dvd_iff_le_factorization htne).mp (by simpa using hpt)
  have hpk_t : ordProj[p] t * t' = t := ordProj_mul_ordCompl_eq_self t p
  have hpk_ge2 : 2 ≤ ordProj[p] t :=
    hp.two_le.trans (by simpa using Nat.pow_le_pow_right hp.one_lt.le hk₀)
  have ht'₀ : 0 < t' := Nat.ordCompl_pos _ htne
  refine ⟨k, t', hk₀, hpk_t, ht'₀, ?_, coprime_ordCompl hp htne⟩
  nlinarith [hpk_t, hpk_ge2, ht'₀]

/-- For `t ≥ 2`, decompose at the smallest prime factor, which is minimal among the prime
divisors of `t`. -/
private lemma exists_minFac_decomp {t : ℕ} (ht : 2 ≤ t) :
    ∃ p k t' : ℕ, 0 < k ∧ p ^ k * t' = t ∧ 0 < t' ∧ t' < t ∧ Nat.Coprime p t' ∧
      Minimal (fun q => q.Prime ∧ q ∣ t) p := by
  obtain ⟨k, t', hk, hpkt, ht'p, ht'l, hcop⟩ :=
    exists_factor_decomp (minFac_prime (by lia)) (minFac_dvd t) (by lia)
  exact ⟨_, k, t', hk, hpkt, ht'p, ht'l, hcop,
    ⟨minFac_prime (by lia), minFac_dvd t⟩, fun q ⟨hq, hqd⟩ _ => minFac_le_of_dvd hq.two_le hqd⟩

/-- After factoring `t = p^k * t'` with `k ≠ 0`, `p` prime, and `Coprime p t'`, the prime
factors of `t` are those of `t'` plus `{p}`. -/
private lemma card_primeFactors_coprime {t t' p k : ℕ} (hp_prime : p.Prime)
    (hk : k ≠ 0) (hpk_t : p ^ k * t' = t) (hcoprime : p.Coprime t') :
    #t.primeFactors = #t'.primeFactors + 1 := by
  have hp_not_t' : p ∉ t'.primeFactors := fun h =>
    hp_prime.coprime_iff_not_dvd.mp hcoprime (mem_primeFactors.mp h).2.1
  rw [← hpk_t, (hcoprime.pow_left k).primeFactors_mul,
    primeFactors_pow p (by lia), hp_prime.primeFactors,
    card_union_of_disjoint (disjoint_singleton_left.mpr hp_not_t'),
    card_singleton, Nat.add_comm]

/-! ### Products over prime windows -/

/-- `primesProd front back = ∏_{i ∈ [front, back]} (i-th prime)`. -/
private noncomputable def primesProd (front back : ℕ) : ℕ :=
  ∏ i ∈ Ico front (back + 1), nth Nat.Prime i

/-- `primesProdM1 front back = ∏_{i ∈ [front, back]} ((i-th prime) - 1)`. -/
private noncomputable def primesProdM1 (front back : ℕ) : ℕ :=
  ∏ i ∈ Ico front (back + 1), (nth Nat.Prime i - 1)

@[grind =] private theorem primesProd_empty {front back : ℕ} (h : back < front) :
    primesProd front back = 1 := by grind [primesProd, Ico_eq_empty]

@[grind =] private theorem primesProdM1_empty {front back : ℕ} (h : back < front) :
    primesProdM1 front back = 1 := by grind [primesProdM1, Ico_eq_empty]

@[grind =] private theorem primesProd_succ {front back : ℕ} (h : front ≤ back + 1) :
    primesProd front (back + 1) = primesProd front back * nth Nat.Prime (back + 1) :=
  prod_Ico_succ_top h _

@[grind =] private theorem primesProdM1_succ {front back : ℕ} (h : front ≤ back + 1) :
    primesProdM1 front (back + 1) = primesProdM1 front back * (nth Nat.Prime (back + 1) - 1) :=
  prod_Ico_succ_top h _

@[grind =] private theorem primesProd_self (i : ℕ) :
    primesProd i i = nth Nat.Prime i := by simp [primesProd]

@[grind =] private theorem primesProdM1_self (i : ℕ) :
    primesProdM1 i i = nth Nat.Prime i - 1 := by simp [primesProdM1]

/-- `primesProdM1 front B ≤ primesProd front B` since each factor `(p-1) ≤ p`. -/
private theorem primesProdM1_le_primesProd {front B : ℕ} :
    primesProdM1 front B ≤ primesProd front B :=
  prod_le_prod' (by simp)

/-- Factoring `primesProd` at the front. -/
@[grind =] private theorem primesProd_succ_front {front B : ℕ} (hB : front ≤ B) :
    primesProd front B = nth Nat.Prime front * primesProd (front + 1) B := by
  grind [primesProd, prod_eq_prod_Ico_succ_bot]

/-- Factoring `primesProdM1` at the front. -/
@[grind =] private theorem primesProdM1_succ_front {front B : ℕ} (hB : front ≤ B) :
    primesProdM1 front B = (nth Nat.Prime front - 1) * primesProdM1 (front + 1) B := by
  grind [primesProdM1, prod_eq_prod_Ico_succ_bot]

/-! ### Sigma at a single prime -/

/-- `σ₁(p ^ k) * (p₀ - 1) ≤ p ^ k * p₀` for `p` prime and `2 ≤ p₀ ≤ p`. -/
private theorem sigma_pow_le_window_factor {p p₀ k : ℕ} (hp : p.Prime) (hp₀ : 2 ≤ p₀)
    (hple : p₀ ≤ p) :
    σ₁ (p ^ k) * (p₀ - 1) ≤ p ^ k * p₀ := by
  refine Nat.le_of_mul_le_mul_right (c := p - 1) ?_ (by lia)
  rw [mul_right_comm, sigma_one_apply_prime_pow' hp,
    Nat.div_mul_cancel (Nat.sub_one_dvd_pow_sub_one p (k + 1))]
  zify [one_le_pow (k+1) _ hp.pos, (by lia : 1 ≤ p₀), (by lia : 1 ≤ p)] at *
  linear_combination hple * p ^ k + hp₀

/-! ### The two main bounds: σ-window and radical -/

/-- `σ₁(t) * Π'(front, B) ≤ t * Π(front, B)` for `t ∈ P front` with at most
`B - front + 1` distinct primes. -/
private theorem sigma_bound_window {t front : ℕ} (B : ℕ) (ht : t ≠ 0) (hP : t ∈ P front)
    (hBsize : B + 1 ≤ 49) (hcard : t.primeFactors.card + front ≤ B + 1) :
    σ₁ t * primesProdM1 front B ≤ t * primesProd front B := by
  induction t using Nat.strongRecOn generalizing front B with
  | ind t ih =>
    obtain rfl | ht1 := eq_or_ne t 1
    · simpa using primesProdM1_le_primesProd
    have ht2 : 2 ≤ t := by lia
    obtain ⟨p, k, t', hk₀, hpk_t, ht'₀, ht'_lt, hcoprime, hmin⟩ := exists_minFac_decomp ht2
    have hp_prime : p.Prime := hmin.prop.1
    have hp_geprimes : nth Nat.Prime front ≤ p := hP.2 p hp_prime hmin.prop.2
    have hcard := card_primeFactors_coprime hp_prime hk₀.ne' hpk_t hcoprime
    have ht'P : t' ∈ P (front + 1) :=
      mem_P_succ_of_coprime hp_prime hp_geprimes (fun q hq hqd => hmin.le ⟨hq, hqd⟩)
        hpk_t ht'₀.ne' hcoprime
    have IH := ih t' ht'_lt B ht'₀.ne' ht'P hBsize (by lia)
    have hcons : σ₁ (p ^ k) * (nth Nat.Prime front - 1) ≤ p ^ k * nth Nat.Prime front :=
      sigma_pow_le_window_factor hp_prime (prime_nth_prime front).two_le hp_geprimes
    calc σ₁ t * primesProdM1 front B
        = σ₁ (p ^ k) * (nth Nat.Prime front - 1) * (σ₁ t' * primesProdM1 (front + 1) B) := by
          rw [← hpk_t, isMultiplicative_sigma.map_mul_of_coprime (hcoprime.pow_left k),
            primesProdM1_succ_front (by lia)]
          ring
      _ ≤ p ^ k * nth Nat.Prime front * (t' * primesProd (front + 1) B) := by gcongr
      _ = t * primesProd front B := by grind

/-- `primesProd front (front + j - 1) ≤ t` for `t ∈ P front` with `j ≥ 1`
distinct primes, and `front + j ≤ 49`. -/
private theorem primesProd_le_t {t front : ℕ} (ht : t ≠ 0) (hP : t ∈ P front) (j : ℕ)
    (hj : j ≠ 0) (hjle : j ≤ t.primeFactors.card) (hsize : front + j ≤ 49) :
    primesProd front (front + j - 1) ≤ t := by
  induction t using Nat.strongRecOn generalizing front j with
  | ind t ih =>
    have ht1 : t ≠ 1 := by grind [primeFactors_one]
    have ht2 : 2 ≤ t := by lia
    obtain ⟨p, k, t', hk₀, hpk_t, ht'₀, ht'_lt, hcoprime, hmin⟩ := exists_minFac_decomp ht2
    have hp_prime : p.Prime := hmin.prop.1
    have hp_dvd : p ∣ t := hpk_t ▸ (dvd_pow_self p (by lia)).mul_right _
    have hp_geprimes : nth Nat.Prime front ≤ p := hP.2 p hp_prime hp_dvd
    have hpk_ge : nth Nat.Prime front ≤ p ^ k := hp_geprimes.trans (le_self_pow (by lia) p)
    rcases lt_or_ge 1 j with hj2 | hj2
    · have ht'P : t' ∈ P (front + 1) :=
        mem_P_succ_of_coprime hp_prime hp_geprimes (fun q hq hqd => hmin.le ⟨hq, hqd⟩)
          hpk_t ht'₀.ne' hcoprime
      have hcard := card_primeFactors_coprime hp_prime hk₀.ne' hpk_t hcoprime
      have IH := ih t' ht'_lt ht'₀.ne' ht'P (j - 1) (by lia) (by lia) (by lia)
      rw [(by lia : (front + 1) + (j - 1) - 1 = front + j - 1)] at IH
      calc primesProd front (front + j - 1)
          = nth Nat.Prime front * primesProd (front + 1) (front + j - 1) :=
            primesProd_succ_front (by lia)
        _ ≤ p ^ k * t' := by gcongr
        _ = t := hpk_t
    · obtain rfl : j = 1 := by lia
      rw [Nat.add_sub_cancel, primesProd_self]
      exact hpk_ge.trans (hpk_t ▸ Nat.le_mul_of_pos_right _ ht'₀)

end Sage
