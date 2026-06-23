/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import HighlyAbundant.Basic
import HighlyAbundant.Sage
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Correctness of the `lcm (1..n)` HA-decider

Spec of the search in `HighlyAbundant.Sage`. Notation:

* `P j := { t ≥ 1 | smallest prime factor of t ≥ nth Nat.Prime j }` (every
  prime factor is at least the `j`-th prime);
* `W B g a minIdx := { t ∈ P minIdx | a * t < B ∧ g ≤ σ₁ t }`
  is the witness set of a node `(g, a, minIdx)` for bound `B`.

## File layout

1. Specification: `P`, `W`, `lcmData`.
2. The `primes` table: bridge to `nth Nat.Prime`.
3. Membership in `P` and factor-count bookkeeping: `mem_P_succ_of_factors_gt`,
   `mem_P_succ_of_coprime`, `card_primeFactors_coprime`, `one_mem_P`.
4. Multiplicative decomposition: `exists_factor_decomp`, `exists_minFac_decomp`.
5. Products over prime windows: `primesProd`, `primesProdM1`, and their `@[grind =]`
   equational lemmas. Used to thread the wheel invariants through `extend`.
6. Sigma at a single prime: `sigma_pow_le_window_factor`, `sigma_pow_expChildren_eq`;
   ceiling-division: `ceilDiv_le_iff`, `le_ceilDiv_mul`.
7. The two main bounds: `sigma_bound_window` and `primesProd_le_t`.
8. Ruling out `.tooLarge` from a witness: `extend_ne_tooLarge`.
9. Window invariants: `extend_window_invariant`.
10. Degenerate case `lhs = 0`: `wheelChildren_zero_eq_none`.
11. `expChildren` analysis: `mem_expChildren`, `expChildren_witness_walk`.
12. `wheelChildren` and `children`: `mem_wheelChildren`, `wheelChildren_acc_subset`,
    `wheelChildren_witness`, `mem_children`, `child_witness_to_parent`,
    `witness_to_child`, `children_spec`.
13. Step correctness and top-level result: `step_true`,
    `highlyAbundantLcm_correct`.

## Partial verification

`step`'s shared fuel does not factor over `++`, so the root evaluation
`step B searchFuel [(sL, 1, 0)]` does not decompose into per-child evaluations.
To prove `lcm (1..n)` highly abundant from per-subtree results, with
`(B, sL) = (lcmRange n, σ₁ (lcmRange n))` and `2 ≤ B`:

1. Evaluate `children B sL 1 0 = some cs` (enlarge `primes` on `none`).
2. For each `c ∈ cs`, obtain `step B searchFuel [c] = some true` separately;
   `step_true` gives `W B c.1 c.2.1 c.2.2 = ∅`.
3. `1 ∉ W B sL 1 0` since `σ₁ 1 = 1 < sL`. Negating `children_spec` gives
   `(∀ t ∈ W B sL 1 0, t = 1) ↔ (∀ c ∈ cs, W B c.1 c.2.1 c.2.2 = ∅)`; the right
   side holds by step 2, so combined with step 3 we get `W B sL 1 0 = ∅`.
4. `W B sL 1 0 = ∅` unfolds to `¬ ∃ m, 1 ≤ m ∧ m < B ∧ sL ≤ σ₁ m`, which with
   `B = lcm (1..n)` and `sL = σ₁ B` is highly-abundance of `lcm (1..n)`.

Only `children_spec` and `step_true` are used; the full root is never evaluated.
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

/-- The witness set of a node `(g, a, minIdx)` for bound `B`. -/
def W (B g a minIdx : ℕ) : Set ℕ :=
  { t | t ∈ P minIdx ∧ a * t < B ∧ g ≤ σ₁ t }

@[simp, grind =] lemma mem_W {B g a minIdx t : ℕ} :
    t ∈ W B g a minIdx ↔ t ∈ P minIdx ∧ a * t < B ∧ g ≤ σ₁ t :=
  Iff.rfl

/-! ### The `primes` table -/

private lemma primesRArray_get_eq_nth_aux (i : Fin 49) :
    primesRArray.get i.val = nth Nat.Prime i.val := by
  have hp : ∀ i : Fin 49, Nat.Prime (primesRArray.get i.val) := by decide +kernel
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

/-- `σ₁(p ^ k) * (p₀ - 1) ≤ p ^ k * p₀` for `p` prime, `2 ≤ p₀ ≤ p`. One step
of the window σ-bound: it lets a prime in the window absorb a `p^k` factor of `t`. -/
private theorem sigma_pow_le_window_factor {p p₀ k : ℕ} (hp : p.Prime) (hp₀ : 2 ≤ p₀)
    (hple : p₀ ≤ p) :
    σ₁ (p ^ k) * (p₀ - 1) ≤ p ^ k * p₀ := by
  have hpk₀ : 1 ≤ p ^ k := one_le_pow _ _ hp.pos
  refine Nat.le_of_mul_le_mul_right (c := p - 1) ?_ (by lia)
  rw [mul_right_comm, sigma_one_apply_prime_pow' hp,
    Nat.div_mul_cancel (Nat.sub_one_dvd_pow_sub_one p (k + 1))]
  zify [one_le_pow (k+1) _ hp.pos, (by omega : (1 : ℕ) ≤ p₀), (by omega : (1 : ℕ) ≤ p)]
  nlinarith [pow_succ p k]

/-- σ formula in `expChildren`'s loop: `(p ^ k * p - 1) / (p - 1) = σ₁ (p ^ k)` for prime `p`. -/
@[grind =] private theorem sigma_pow_expChildren_eq {p k : ℕ} (hp : p.Prime) :
    (p ^ k * p - 1) / (p - 1) = σ₁ (p ^ k) := by rw [← pow_succ, ← sigma_one_apply_prime_pow' hp]

@[grind =]
private theorem ceilDiv_le_iff {a b c : ℕ} (hb : 0 < b) : ceilDiv a b ≤ c ↔ a ≤ c * b := by
  rw [ceilDiv, div_le_iff_le_mul_add_pred hb, mul_comm]; omega

@[grind =]
private theorem lt_ceilDiv_iff {a b c : ℕ} (hb : 0 < b) : c < ceilDiv a b ↔ c * b < a :=
  lt_iff_lt_of_le_iff_le (ceilDiv_le_iff hb)

private theorem le_ceilDiv_mul {a b : ℕ} (hb : 0 < b) : a ≤ ceilDiv a b * b :=
  (ceilDiv_le_iff hb).mp le_rfl

/-! ### The two main bounds: σ-window and radical -/

/-- `σ₁(t) * Π'(front, B) ≤ t * Π(front, B)` for `t ∈ P front` with at most
`B - front + 1` distinct primes. -/
private theorem sigma_bound_window {t front : ℕ} (B : ℕ) (ht : 1 ≤ t) (hP : t ∈ P front)
    (hBsize : B + 1 ≤ 49) (hcard : t.primeFactors.card + front ≤ B + 1) :
    σ₁ t * primesProdM1 front B ≤ t * primesProd front B := by
  induction t using Nat.strongRecOn generalizing front B with
  | ind t ih =>
    obtain rfl | ht1 := eq_or_ne t 1
    · simpa using primesProdM1_le_primesProd
    have ht2 : 2 ≤ t := by lia
    obtain ⟨p, k, t', hp_prime, hp_dvd, hk₀, hpk_t, ht'₀, ht'_lt,
        hcoprime, hp_min⟩ := exists_minFac_decomp ht2
    have hp_geprimes : nth Nat.Prime front ≤ p := hP.2 p hp_prime hp_dvd
    have hcard := card_primeFactors_coprime hp_prime hk₀ hpk_t hcoprime
    have ht'P : t' ∈ P (front + 1) :=
      mem_P_succ_of_coprime hp_prime hp_geprimes hp_min hpk_t ht'₀ hcoprime
    have IH := ih t' ht'_lt B ht'₀ ht'P hBsize (by lia)
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
private theorem primesProd_le_t {t front : ℕ} (ht : 1 ≤ t) (hP : t ∈ P front) (j : ℕ)
    (hj : 1 ≤ j) (hjle : j ≤ t.primeFactors.card) (hsize : front + j ≤ 49) :
    primesProd front (front + j - 1) ≤ t := by
  induction t using Nat.strongRecOn generalizing front j with
  | ind t ih =>
    have ht1 : t ≠ 1 := by grind [primeFactors_one]
    have ht2 : 2 ≤ t := by omega
    obtain ⟨p, k, t', hp_prime, _, hk₀, hpk_t, ht'₀, ht'_lt, hcoprime, hp_min⟩ :=
      exists_minFac_decomp ht2
    have hp_dvd : p ∣ t := hpk_t ▸ (dvd_pow_self p (by omega)).mul_right _
    have hp_geprimes : nth Nat.Prime front ≤ p := hP.2 p hp_prime hp_dvd
    have hpk_ge : nth Nat.Prime front ≤ p ^ k := hp_geprimes.trans (le_self_pow (by omega) p)
    rcases lt_or_ge 1 j with hj2 | hj2
    · have ht'P : t' ∈ P (front + 1) :=
        mem_P_succ_of_coprime hp_prime hp_geprimes hp_min hpk_t ht'₀ hcoprime
      have hcard := card_primeFactors_coprime hp_prime hk₀ hpk_t hcoprime
      have IH := ih t' ht'_lt ht'₀ ht'P (j - 1) (by omega) (by omega) (by omega)
      rw [(by omega : (front + 1) + (j - 1) - 1 = front + j - 1)] at IH
      calc primesProd front (front + j - 1)
          = nth Nat.Prime front * primesProd (front + 1) (front + j - 1) :=
            primesProd_succ_front (by omega)
        _ ≤ p ^ k * t' := by gcongr
        _ = t := hpk_t
    · obtain rfl : j = 1 := by omega
      rw [Nat.add_sub_cancel, primesProd_self]
      exact hpk_ge.trans (hpk_t ▸ Nat.le_mul_of_pos_right _ ht'₀)

/-! ### Ruling out `.tooLarge` from a witness -/

/-- At a wheel `.tooLarge` state with `back + 1 < 49`, the witness `t` with
`t ≤ m`, `t ∈ P front`, `g ≤ σ₁ t` gives `False`. -/
@[grind .] private theorem extend_tooLarge_contra
    {m g front back lhs rhs t : ℕ}
    (hlhs : lhs = m * primesProd front back)
    (hrhs : rhs = g * primesProdM1 front back)
    (hfront : front ≤ back + 1)
    (hback_lt : back + 1 < 49)
    (hsmall : lhs < rhs)
    (hbig : m * m < lhs * primesRArray.get (back + 1))
    (ht2 : 2 ≤ t) (htP : t ∈ P front) (htm : t ≤ m) (htσ : g ≤ σ₁ t) : False := by
  rw [primesRArray_get_eq_nth hback_lt] at hbig
  rcases lt_or_ge t.primeFactors.card (back + 2 - front) with hcard | hcard
  · have hbound := sigma_bound_window back (by omega) htP (by omega) (by omega)
    have h_chain : σ₁ t * primesProdM1 front back < g * primesProdM1 front back := by
      nlinarith [Nat.mul_le_mul_right (primesProd front back) htm]
    exact absurd htσ (not_le.mpr (Nat.lt_of_mul_lt_mul_right h_chain))
  · have hrad := primesProd_le_t (by omega) htP (back + 2 - front) (by omega) hcard (by omega)
    rw [(by omega : front + (back + 2 - front) - 1 = back + 1)] at hrad
    have hppsm : m < primesProd front (back + 1) := Nat.lt_of_mul_lt_mul_left (a := m)
      (by rwa [primesProd_succ (by omega : front ≤ back + 1), ← mul_assoc, ← hlhs])
    lia

/-- At a wheel `.tooLarge` empty-window state with `front < 49`, the witness `t`
with `t ≤ m`, `t ∈ P front`, `t ≥ 2` gives `False`. -/
@[grind .] private theorem extend_tooLarge_empty_contra
    {m front back lhs : ℕ} {t : ℕ}
    (hlhs : lhs = m * primesProd front back) (hfront_lt : front < 49)
    (hempty : back + 1 = front)
    (hbig : m * m < lhs * primesRArray.get front)
    (ht2 : 2 ≤ t) (htP : t ∈ P front) (htm : t ≤ m) : False := by
  rw [primesProd_empty (by omega : back < front), mul_one] at hlhs
  rw [primesRArray_get_eq_nth hfront_lt, hlhs] at hbig
  have h1 : nth Nat.Prime front ≤ t.minFac := htP.2 _ (minFac_prime (by omega)) (minFac_dvd t)
  grind [Nat.lt_of_mul_lt_mul_left hbig, minFac_le]

/-- If `t` is a witness, `extend` cannot return `.tooLarge`. -/
@[grind .] private theorem extend_ne_tooLarge {fuel m g front t : ℕ} (ht2 : 2 ≤ t)
    (htP : t ∈ P front) (htm : t ≤ m) (htσ : g ≤ σ₁ t)
    {back lhs rhs : ℕ} (hlhs : lhs = m * primesProd front back)
    (hrhs : rhs = g * primesProdM1 front back) (hfront : front ≤ back + 1) :
    extend fuel (m * m) front back lhs rhs ≠ .tooLarge := by
  fun_induction extend fuel (m * m) front back lhs rhs with grind

/-! ### Window invariants -/

/-- When `extend` returns `.window`, the new `(b, lhs', rhs')` satisfy the wheel invariants
shifted to `b`, and `b ≥ back`. -/
private theorem extend_window_invariant {fuel m g front back lhs rhs b lhs' rhs' : ℕ}
    (hlhs : lhs = m * primesProd front back) (hrhs : rhs = g * primesProdM1 front back)
    (hfront : front ≤ back + 1)
    (heq : extend fuel (m * m) front back lhs rhs = Wheel.window b lhs' rhs') :
    lhs' = m * primesProd front b ∧ rhs' = g * primesProdM1 front b ∧
    back ≤ b ∧ front ≤ b := by
  fun_induction extend with grind

/-! ### Degenerate case: `lhs = 0` -/

/-- For `m2 = 0` and `lhs = 0`: `extend` returns either `.exhaustedTable` or
`.window b 0 rhs'` (so never `.tooLarge`, and any `.window` has `lhs' = 0`). -/
@[grind .]
private lemma extend_zero_lhs {fuel front back lhs rhs : ℕ} (hlhs : lhs = 0) :
    extend fuel 0 front back lhs rhs = Wheel.exhaustedTable ∨
    ∃ b rhs', extend fuel 0 front back lhs rhs = Wheel.window b 0 rhs' := by
  fun_induction extend fuel 0 front back lhs rhs with
  | case2 => simp [hlhs]
  | _ => grind

/-- For `m2 = 0` and `lhs = 0`, `wheelChildren` returns `none`. -/
@[grind =]
private theorem wheelChildren_zero_eq_none {fuel g a front back lhs rhs : ℕ}
    {acc : List (ℕ × ℕ × ℕ)} (hlhs : lhs = 0) :
    wheelChildren fuel 0 0 g a front back lhs rhs acc = none := by
  fun_induction wheelChildren with grind [Nat.zero_div]

/-! ### `expChildren` analysis -/

section
variable {fuel g a next m p pk : ℕ}

/-- One step of `expChildren` when `pk ≤ m` and `σ(pk) < g`. -/
private theorem expChildren_step (hfuel : 1 ≤ fuel) (hpkm : pk ≤ m)
    (hsig_lt : (pk * p - 1) / (p - 1) < g) :
    expChildren fuel g a next m p pk =
      (ceilDiv g ((pk * p - 1) / (p - 1)), a * pk, next) ::
      expChildren (fuel - 1) g a next m p (pk * p) := by
  fun_induction expChildren with grind

/-- One step of `expChildren` when `pk ≤ m` and `σ(pk) ≥ g` (final child). -/
private theorem expChildren_stop (hfuel : 1 ≤ fuel) (hpkm : pk ≤ m)
    (hsig_le : g ≤ (pk * p - 1) / (p - 1)) :
    expChildren fuel g a next m p pk =
      [(ceilDiv g ((pk * p - 1) / (p - 1)), a * pk, next)] := by
  fun_induction expChildren with grind

end

/-- Every entry of `expChildren ... (p ^ k₀)` (for prime `p`, `k₀ ≥ 1`) has the form
`(⌈g / σ₁(p^k)⌉, a * p^k, next)` for some `k ≥ k₀` with `p ^ k ≤ m`. -/
private theorem mem_expChildren {fuel g a next m p k₀ : ℕ}
    (hp : p.Prime) (hk₀ : 1 ≤ k₀) {c : ℕ × ℕ × ℕ}
    (hc : c ∈ expChildren fuel g a next m p (p ^ k₀)) :
    ∃ k, k₀ ≤ k ∧ p ^ k ≤ m ∧ c = (ceilDiv g (σ₁ (p ^ k)), a * p ^ k, next) := by
  induction fuel generalizing k₀ with grind [expChildren, =_ pow_succ]

/-- Witness `1` for the stop arm of `expChildren_witness_walk`: when `σ(p ^ j₀) ≥ g`,
the child `(ceilDiv g σ(p ^ j₀), a*p ^ j₀, next)` has `1` as a witness. -/
private lemma one_witnesses_stop {B a g next p k j₀ s : ℕ}
    (hp : p.Prime) (hjk : j₀ ≤ k) (hs₀ : 1 ≤ s)
    (hat : a * p ^ k * s < B) (hσg : g ≤ σ₁ (p ^ j₀)) :
    1 ∈ W B (ceilDiv g (σ₁ (p ^ j₀))) (a * p ^ j₀) next := by
  simp only [mem_W, one_mem_P, mul_one, sigma_one, true_and]
  constructor
  · grind [Nat.mul_le_mul_left a (Nat.pow_le_pow_right hp.one_lt.le hjk),
      Nat.le_mul_of_pos_right (a * p ^ k) hs₀]
  · grind [pow_ne_zero, hp.pos]

/-- Walk `expChildren` from `pk₀ = p ^ j₀` looking for a child with a witness, given
a parent witness `t = p ^ k * s` (factored at `p` with `s` coprime to `p`). -/
private theorem expChildren_witness_walk {B a g m p : ℕ} (hp : p.Prime) (next : ℕ)
    (n k j₀ : ℕ) (hn : k - j₀ = n) (hj₀ : 1 ≤ j₀) (hj₀_k : j₀ ≤ k) (hpkm : p ^ k ≤ m)
    {s : ℕ} (hs₀ : 1 ≤ s) (hsP : s ∈ P next) (hat : a * p ^ k * s < B)
    (htσ : g ≤ σ₁ (p ^ k) * σ₁ s) (fuel : ℕ) (hfuel : n + 1 ≤ fuel) :
    ∃ c ∈ expChildren fuel g a next m p (p ^ j₀), (W B c.1 c.2.1 c.2.2).Nonempty := by
  induction n generalizing j₀ fuel with
  | zero =>
    obtain rfl : j₀ = k := by omega
    have h_sig_eq : (p ^ j₀ * p - 1) / (p - 1) = σ₁ (p ^ j₀) := sigma_pow_expChildren_eq hp
    by_cases hσg : g ≤ σ₁ (p ^ j₀)
    · rw [expChildren_stop (by omega) hpkm (h_sig_eq ▸ hσg), h_sig_eq]
      exact ⟨_, List.mem_singleton.mpr rfl, ⟨_, one_witnesses_stop hp hj₀_k hs₀ hat hσg⟩⟩
    push Not at hσg
    rw [expChildren_step (by omega) hpkm (h_sig_eq.symm ▸ hσg), h_sig_eq]
    refine ⟨_, List.mem_cons_self, ⟨s, hsP, hat, ?_⟩⟩
    grind [hp.pos]
  | succ n ih =>
    have hpjm : p ^ j₀ ≤ m := (Nat.pow_le_pow_right hp.one_lt.le hj₀_k).trans hpkm
    have h_sig_eq : (p ^ j₀ * p - 1) / (p - 1) = σ₁ (p ^ j₀) := sigma_pow_expChildren_eq hp
    by_cases hσg : g ≤ σ₁ (p ^ j₀)
    · rw [expChildren_stop (by omega) hpjm (h_sig_eq.symm ▸ hσg), h_sig_eq]
      exact ⟨_, List.mem_singleton.mpr rfl, ⟨_, one_witnesses_stop hp hj₀_k hs₀ hat hσg⟩⟩
    push Not at hσg
    rw [expChildren_step (by omega) hpjm (h_sig_eq.symm ▸ hσg), h_sig_eq, ← pow_succ]
    obtain ⟨c, hc, hwit⟩ := ih (j₀ + 1) (by omega) (by omega) (by omega) (fuel - 1) (by omega)
    grind

/-! ### `wheelChildren` and `children` -/

/-- Each entry of `wheelChildren`'s output is either from `acc` or of the form
`(⌈g / σ₁(p^k)⌉, a * p^k, i + 1)` for some `i ≥ front`, `k ≥ 1` with
`p = nth Nat.Prime i` and `p^k ≤ m`. -/
private theorem mem_wheelChildren {fuel m2 m g a front back lhs rhs : ℕ}
    {acc : List (ℕ × ℕ × ℕ)} {L : List (ℕ × ℕ × ℕ)}
    (h : wheelChildren fuel m2 m g a front back lhs rhs acc = some L)
    {c : ℕ × ℕ × ℕ} (hc : c ∈ L) :
    c ∈ acc ∨ ∃ i k, front ≤ i ∧ 1 ≤ k ∧ nth Nat.Prime i ^ k ≤ m ∧
      c = (ceilDiv g (σ₁ (nth Nat.Prime i ^ k)), a * nth Nat.Prime i ^ k, i + 1) := by
  fun_induction wheelChildren generalizing L with
  | case4 front _ _ _ acc _ _ _ _ _ hp p =>
    rename_i hrec
    have hp : p = nth Nat.Prime front := primesRArray_get_eq_nth hp
    rcases hrec h hc with hcacc | ⟨i, k, hi, hk, hpkm, hceq⟩
    · rcases List.mem_append.mp hcacc with hcexp | hcorig
      · obtain ⟨k, hk, hpkm, hceq⟩ := mem_expChildren (prime_nth_prime front) le_rfl
          (by rwa [pow_one, ← hp])
        grind
      · exact Or.inl hcorig
    · exact Or.inr ⟨i, k, by grind⟩
  | _ => grind

/-- Anything in `acc` going in is still in the output `L` coming out, since `wheelChildren`
only ever prepends to `acc`. -/
private lemma wheelChildren_acc_subset {fuel m2 m g a front back lhs rhs : ℕ}
    {acc L : List (ℕ × ℕ × ℕ)}
    (h : wheelChildren fuel m2 m g a front back lhs rhs acc = some L) : acc ⊆ L := by
  fun_induction wheelChildren generalizing L with grind [List.mem_append_right]

/-- Given the wheel invariants and a viable witness `t`, some child in
`wheelChildren`'s output `L` has a non-empty witness set. -/
private theorem wheelChildren_witness {B a m g : ℕ} (hmdef : m = B / a)
    (ha₀ : 1 ≤ a) {fuel front back lhs rhs : ℕ} {acc L : List (ℕ × ℕ × ℕ)}
    (hfuel : 49 + 1 - front ≤ fuel)
    (hlhs : lhs = m * primesProd front back) (hrhs : rhs = g * primesProdM1 front back)
    (hfront_le : front ≤ back + 1)
    (hwc : wheelChildren fuel (m * m) m g a front back lhs rhs acc = some L)
    {t : ℕ} (ht2 : 2 ≤ t) (htP : t ∈ P front) (hat : a * t < B) (htσ : g ≤ σ₁ t) :
    ∃ c ∈ L, (W B c.1 c.2.1 c.2.2).Nonempty := by
  have htm : t ≤ m := hmdef ▸ (le_div_iff_mul_le ha₀).mpr (by linarith)
  fun_induction wheelChildren generalizing L with
  | case1 | case2 | case5 => cases hwc
  | case3 => grind
  | case4 front back lhs rhs acc _ b lhs' rhs' hext hp p =>
    rename_i hrec
    have hp : p = nth Nat.Prime front := primesRArray_get_eq_nth hp
    have hp_prime : (nth Nat.Prime front).Prime := prime_nth_prime front
    obtain ⟨hlhs', hrhs', _, hfront_b⟩ := extend_window_invariant hlhs hrhs hfront_le hext
    replace hlhs : lhs' / p = m * primesProd (front + 1) b := by
      rw [hp, hlhs', primesProd_succ_front hfront_b, mul_left_comm,
        Nat.mul_div_cancel_left _ hp_prime.pos]
    replace hrhs : rhs' / (p - 1) = g * primesProdM1 (front + 1) b := by
      rw [hp, hrhs', primesProdM1_succ_front hfront_b, mul_left_comm,
        Nat.mul_div_cancel_left _ (Nat.sub_pos_of_lt hp_prime.one_lt)]
    by_cases hdvd : nth Nat.Prime front ∣ t
    · obtain ⟨k, s, hk₀, hpk_t, hs₀, _, hcoprime⟩ :=
        exists_factor_decomp hp_prime hdvd (by omega)
      have hpkm : nth Nat.Prime front ^ k ≤ m :=
        (le_of_dvd (by omega) ⟨s, hpk_t.symm⟩).trans htm
      have htσ' : g ≤ σ₁ (nth Nat.Prime front ^ k) * σ₁ s := by
        rwa [← isMultiplicative_sigma.map_mul_of_coprime (hcoprime.pow_left k), hpk_t]
      have hsP : s ∈ P (front + 1) :=
        mem_P_succ_of_coprime hp_prime le_rfl htP.2 hpk_t hs₀ hcoprime
      obtain ⟨c, hc, hwit⟩ := expChildren_witness_walk hp_prime (front + 1) (k - 1) k 1
        (by omega) (by omega) hk₀ hpkm hs₀ hsP
        (by rwa [mul_assoc, hpk_t]) htσ' (m + 1)
        (by have : k ≤ m := (Nat.lt_pow_self hp_prime.one_lt).le.trans hpkm; omega)
      exact ⟨c, wheelChildren_acc_subset hwc (List.mem_append_left _ (by grind)), hwit⟩
    · exact hrec (by omega) hlhs hrhs (by omega) hwc
        (mem_P_succ_of_factors_gt (by omega) fun q' hq'_prime hq'_dvd =>
          lt_of_le_of_ne (htP.2 q' hq'_prime hq'_dvd) (by grind))

/-- Every `c` in `children`'s output has the form
`(⌈g / σ₁(p^k)⌉, a * p^k, i + 1)` for some `i ≥ minIdx`, `k ≥ 1` with
`p = nth Nat.Prime i` and `p^k ≤ B / a`. -/
private theorem mem_children {B g a minIdx : ℕ} {cs : List (ℕ × ℕ × ℕ)}
    (h : children B g a minIdx = some cs) {c : ℕ × ℕ × ℕ} (hc : c ∈ cs) :
    ∃ i k, minIdx ≤ i ∧ 1 ≤ k ∧ nth Nat.Prime i ^ k ≤ B / a ∧
      c = (ceilDiv g (σ₁ (nth Nat.Prime i ^ k)),
        a * nth Nat.Prime i ^ k, i + 1) := by
  rw [children] at h
  split at h <;> [grind [mem_wheelChildren h hc]; grind]

/-- If `t'` is a witness of the child `(⌈g / σ₁(p ^ k)⌉, a * p ^ k, i+1)`
where `p = nth Nat.Prime i`, then `p ^ k * t'` is a non-trivial witness of the
parent `(g, a, minIdx)`. -/
private theorem child_witness_to_parent {B g a minIdx i k : ℕ}
    (hmi : minIdx ≤ i) (hk : 1 ≤ k) {t' : ℕ}
    (ht' : t' ∈ W B (ceilDiv g (σ₁ (nth Nat.Prime i ^ k)))
      (a * nth Nat.Prime i ^ k) (i + 1)) :
    nth Nat.Prime i ^ k * t' ∈ W B g a minIdx ∧
      nth Nat.Prime i ^ k * t' ≠ 1 := by
  set p := nth Nat.Prime i
  obtain ⟨⟨ht'1, ht'P⟩, ht'lt, ht'σ⟩ := ht'
  have hpPrime : p.Prime := prime_nth_prime i
  have hpk_ge2 : 2 ≤ p ^ k := hpPrime.two_le.trans (le_self_pow (by omega) p)
  have hpkt'_ge2 : 2 ≤ p ^ k * t' := hpk_ge2.trans (Nat.le_mul_of_pos_right _ ht'1)
  have hcop : Nat.Coprime (p ^ k) t' := by
    refine (hpPrime.coprime_iff_not_dvd.mpr fun hpdvd => ?_).pow_left _
    linarith [ht'P p hpPrime hpdvd, nth_strictMono infinite_setOf_prime (lt_succ_self i)]
  refine ⟨⟨⟨by omega, fun q hqPrime hqDvd => ?_⟩, by rwa [← mul_assoc], ?_⟩, by omega⟩
  · rcases hqPrime.dvd_mul.mp hqDvd with h1 | h2
    · obtain rfl : q = p :=
        (prime_dvd_prime_iff_eq hqPrime hpPrime).mp (hqPrime.dvd_of_dvd_pow h1)
      exact (nth_strictMono infinite_setOf_prime).monotone hmi
    · exact ((nth_strictMono infinite_setOf_prime).monotone (by omega)).trans (ht'P q hqPrime h2)
  · grind [isMultiplicative_sigma.map_mul_of_coprime, le_ceilDiv_mul]

/-- A non-trivial witness of the parent gives a witness for some child in `cs`. -/
private theorem witness_to_child {B g a minIdx : ℕ} {cs : List (ℕ × ℕ × ℕ)}
    (h : children B g a minIdx = some cs) {t : ℕ}
    (ht : t ∈ W B g a minIdx) (h1 : t ≠ 1) :
    ∃ c ∈ cs, (W B c.1 c.2.1 c.2.2).Nonempty := by
  rcases Nat.eq_zero_or_pos a with rfl | ha₀
  · grind [children]
  · simp only [children] at h
    split at h
    · rename_i hminIdx_lt
      obtain ⟨⟨ht₀, htP⟩, htlt, htσ⟩ := ht
      rw [primesRArray_get_eq_nth hminIdx_lt, ← primesProdM1_self minIdx,
        mul_comm (nth Nat.Prime minIdx) (B / a), ← primesProd_self minIdx] at h
      exact wheelChildren_witness rfl ha₀ (by omega) rfl rfl (by omega) h
        (by omega) ⟨ht₀, htP⟩ htlt htσ
    · cases h

/-- `children` reduces nontrivial witnesses of a node to witnesses of its children. -/
theorem children_spec {B g a minIdx : ℕ} {cs : List (ℕ × ℕ × ℕ)}
    (h : children B g a minIdx = some cs) :
    (∃ t ∈ W B g a minIdx, t ≠ 1) ↔
      ∃ c ∈ cs, (W B c.1 c.2.1 c.2.2).Nonempty := by
  refine ⟨fun ⟨t, ht, h1⟩ => witness_to_child h ht h1, ?_⟩
  rintro ⟨c, hc, t', ht'⟩
  obtain ⟨i, k, hmi, hk, _, hceq⟩ := mem_children h hc
  rw [hceq] at ht'
  obtain ⟨hw, hne⟩ := child_witness_to_parent hmi hk ht'
  exact ⟨_, hw, hne⟩

/-! ### Step correctness and top-level result -/

/-- `step = some true` ⟹ every node on the stack has an empty witness set. -/
theorem step_true {B fuel : ℕ} {stack : List (ℕ × ℕ × ℕ)}
    (h : step B fuel stack = some true) :
    ∀ node ∈ stack, W B node.1 node.2.1 node.2.2 = ∅ := by
  fun_induction step with
  | case1 | case2 | case3 | case5 => grind
  | case4 _ _ a _ _ _ _ ih =>
    simp only [List.mem_cons, forall_eq_or_imp, Prod.forall]
    refine ⟨?_, fun a b c hm => ih h (a, b, c) hm⟩
    rw [Set.eq_empty_iff_forall_notMem]
    rintro t ⟨⟨ht1, _⟩, htlt, _⟩
    linarith [Nat.le_mul_of_pos_right a ht1]
  | case6 _ _ _ _ _ _ _ hch ih1 =>
    intro node hnode
    rcases List.mem_cons.mp hnode with rfl | hnode
    · rw [Set.eq_empty_iff_forall_notMem]
      intro t htW
      obtain rfl | h1 := eq_or_ne t 1
      · grind [sigma_one]
      obtain ⟨c, hc, hwc⟩ := (children_spec hch).mp ⟨t, htW, h1⟩
      grind [Set.not_nonempty_iff_eq_empty]
    · exact ih1 h _ (List.mem_append.mpr (Or.inr hnode))

/- `step_false` (the dual of `step_true`) is currently unused and only `sorry`-proved;
commented out until something needs it.
/-- `step = some false` ⟹ some node on the stack has a nonempty witness set. -/
theorem step_false {B fuel : ℕ} {stack : List (ℕ × ℕ × ℕ)}
    (h : step B fuel stack = some false) :
    ∃ node ∈ stack, (W B node.1 node.2.1 node.2.2).Nonempty := sorry
-/

/-- A `some true` answer of `highlyAbundantLcm?` on `(lcmRange n, σ₁ (lcmRange n))`
certifies that `lcm (1..n)` is highly abundant. -/
theorem highlyAbundantLcm_correct {n : ℕ}
    (h : highlyAbundantLcm? (lcmRange n) (σ₁ (lcmRange n)) = some true) :
    IsHighlyAbundant (lcmRange n) := by
  intro m hm₀ hm_lt
  rw [highlyAbundantLcm?] at h
  by_cases hB : lcmRange n ≤ 1
  · omega
  simp only [hB, if_false] at h
  have hW : W (lcmRange n) (σ₁ (lcmRange n)) 1 0 = ∅ :=
    step_true h (σ₁ (lcmRange n), 1, 0) List.mem_cons_self
  by_contra! hcontra
  have h2 : nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have hmW : m ∈ W (lcmRange n) (σ₁ (lcmRange n)) 1 0 := by grind [Nat.Prime.two_le]
  rwa [hW] at hmW

/-- Recursive partial step: a non-trivial node's witness set is empty if all its
children's witness sets are empty. Used to bottom-up build `W = ∅` proofs for nodes
whose direct `step` evaluation would be too expensive. -/
theorem W_eq_empty_of_partial {B g a minIdx : ℕ} {cs : List (ℕ × ℕ × ℕ)}
    (hg : 2 ≤ g)
    (hch : children B g a minIdx = some cs)
    (hcs : ∀ c ∈ cs, W B c.1 c.2.1 c.2.2 = ∅) :
    W B g a minIdx = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro t ht
  obtain rfl | h1 := eq_or_ne t 1
  · obtain ⟨_, _, hle⟩ := ht
    simp at hle
    omega
  · obtain ⟨c, hc, hwc⟩ := (children_spec hch).mp ⟨t, ht, h1⟩
    rw [hcs c hc] at hwc
    exact hwc.ne_empty rfl

/-- If the root witness set is empty, `lcm(1..n)` is highly abundant. -/
theorem isHighlyAbundant_of_root_W_eq_empty {n : ℕ}
    (hW : W (lcmRange n) (σ₁ (lcmRange n)) 1 0 = ∅) :
    IsHighlyAbundant (lcmRange n) := by
  intro m hm₀ hm_lt
  by_contra! hcontra
  have h2 : nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have hmW : m ∈ W (lcmRange n) (σ₁ (lcmRange n)) 1 0 := by grind [Nat.Prime.two_le]
  rwa [hW] at hmW

/-- Partial-verification entry point taking `W = ∅` for each root child. Used
when individual subtrees are evaluated recursively rather than via `step`. -/
theorem highlyAbundantLcm_correct_partial_W {n : ℕ} {cs : List (ℕ × ℕ × ℕ)}
    (hsL : 2 ≤ σ₁ (lcmRange n))
    (hch : children (lcmRange n) (σ₁ (lcmRange n)) 1 0 = some cs)
    (hcs : ∀ c ∈ cs, W (lcmRange n) c.1 c.2.1 c.2.2 = ∅) :
    IsHighlyAbundant (lcmRange n) :=
  isHighlyAbundant_of_root_W_eq_empty (W_eq_empty_of_partial hsL hch hcs)

/-- Partial-verification entry point: certify `lcm (1..n)` is highly abundant from
per-child kernel evaluations. The root `step` is never evaluated; instead, expand the
root via `children` and check each child's subtree separately with its own `step`. -/
theorem highlyAbundantLcm_correct_partial {n : ℕ} {cs : List (ℕ × ℕ × ℕ)}
    (hsL : 2 ≤ σ₁ (lcmRange n))
    (hch : children (lcmRange n) (σ₁ (lcmRange n)) 1 0 = some cs)
    (hcs : ∀ c ∈ cs, step (lcmRange n) searchFuel [c] = some true) :
    IsHighlyAbundant (lcmRange n) :=
  highlyAbundantLcm_correct_partial_W hsL hch
    (fun c hc => step_true (hcs c hc) c List.mem_cons_self)

end Sage
