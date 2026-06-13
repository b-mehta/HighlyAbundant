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
* `W B target num minIdx := { t ∈ P minIdx | num * t < B ∧ target ≤ σ₁ t }`
  is the witness set of a node `(target, num, minIdx)` for bound `B`.

## File layout

1. Specification: `P`, `W`, `lcmData`.
2. The `primes` table: bridge to `nth Nat.Prime`.
3. Membership in `P` and factor-count bookkeeping: `mem_P_succ_of_factors_gt`,
   `mem_P_succ_of_coprime_decomp`, `card_primeFactors_of_coprime_decomp`, `one_mem_P`.
4. Multiplicative decomposition: `exists_factor_decomp`, `exists_minFac_decomp`.
5. Products over prime windows: `primesProd`, `primesProdM1`, and the wheel
   invariant updates fed to cases 4 and 7 of `extend`'s recursion.
6. Sigma at a single prime: `sigma_pow_le_window_factor`, `sigma_pow_expChildren_eq`;
   ceiling-division: `ceilDiv_le_iff`, `le_ceilDiv_mul`.
7. The two main bounds: `sigma_bound_window` and `primesProd_le_t`.
8. Ruling out `.tooLarge` from a witness: `extend_ne_tooLarge_of_witness`.
9. Window invariants: `extend_window_invariant`.
10. Degenerate case `lhs = 0`: `wheelChildren_zero_no_some`.
11. `expChildren` analysis: `mem_expChildren`, `expChildren_witness_walk`.
12. `wheelChildren` and `children`: `mem_wheelChildren`, `wheelChildren_acc_subset`,
    `wheelChildren_witness`, `mem_children`, `child_witness_to_parent`,
    `witness_to_child`, `children_spec`.
13. Step correctness and top-level result: `step_true`, `step_false`,
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

open Nat

namespace Sage

/-! ### Specification: `P`, `W`, `lcmData` -/

/-- `P j`: naturals `≥ 1` whose every prime factor is at least the `j`-th prime. -/
def P (j : Nat) : Set Nat :=
  { t | 1 ≤ t ∧ ∀ q : Nat, q.Prime → q ∣ t → nth Nat.Prime j ≤ q }

@[grind =] lemma mem_P {j t : ℕ} :
    t ∈ P j ↔ 1 ≤ t ∧ ∀ q : Nat, q.Prime → q ∣ t → nth Nat.Prime j ≤ q :=
  Iff.rfl

/-- The witness set of a node `(target, num, minIdx)` for bound `B`. -/
def W (B target num minIdx : Nat) : Set Nat :=
  { t | t ∈ P minIdx ∧ num * t < B ∧ target ≤ σ₁ t }

@[grind =] lemma mem_W {B target num minIdx t : ℕ} :
    t ∈ W B target num minIdx ↔ t ∈ P minIdx ∧ num * t < B ∧ target ≤ σ₁ t :=
  Iff.rfl

/-- `(lcmRange n, σ₁ (lcmRange n))` computed as
`(∏ p^{⌊log_p n⌋}, ∏ σ(p^{⌊log_p n⌋}))` over the primes `p ≤ n` in the table.
For `#eval` use to supply `(B, sL)` to `highlyAbundantLcm?`; the formal proof
goes through `lcmRange` directly, so this equivalence is not used. -/
def lcmData (n : Nat) : Nat × Nat :=
  (primes.toList.takeWhile (· ≤ n)).foldl
    (fun (acc : Nat × Nat) p =>
      let e := log p n
      (acc.1 * p ^ e, acc.2 * ((p ^ (e + 1) - 1) / (p - 1)))) (1, 1)

/-! ### The `primes` table -/

private lemma primesRArray_get_eq_nth_aux : ∀ i : Fin 49,
    primesRArray.get i.val = nth Nat.Prime i.val := by
  intro i
  have hp : ∀ i : Fin 49, Nat.Prime (primesRArray.get i.val) := by decide +kernel
  rw [← nth_count (hp i)]
  congr 1
  decide +kernel +revert

/-- The wheel's array lookup gives the `i`-th prime. -/
@[grind <=]
private lemma primesRArray_get_eq_nth (i : Nat) (hi : i < 49) :
    primesRArray.get i = nth Nat.Prime i :=
  primesRArray_get_eq_nth_aux ⟨i, hi⟩

/-! ### Membership in `P` -/

/-- If `x ≥ 1` and every prime factor of `x` exceeds the `front`-th prime, then
`x ∈ P (front + 1)`. -/
private lemma mem_P_succ_of_factors_gt {x front : Nat} (hx : 1 ≤ x)
    (h : ∀ q, q.Prime → q ∣ x → nth Nat.Prime front < q) : x ∈ P (front + 1) :=
  ⟨hx, fun q hq hqd => by
    by_contra! hlt
    linarith [le_nth_of_lt_nth_succ hlt hq, h q hq hqd]⟩

/-- If `t ∈ P front`, `p ≥ nth Nat.Prime front` is a prime, `t = p^k * t'` with `t'`
coprime to `p`, and `∀ q ∣ t prime, p ≤ q`, then `t' ∈ P (front + 1)`. -/
private lemma mem_P_succ_of_coprime_decomp {t t' p k front : Nat}
    (hp_prime : p.Prime) (hp_geprimes : nth Nat.Prime front ≤ p)
    (hp_min : ∀ q, q.Prime → q ∣ t → p ≤ q) (hpk_t : p ^ k * t' = t)
    (ht'_pos : 1 ≤ t') (hcoprime : Nat.Coprime p t') : t' ∈ P (front + 1) :=
  mem_P_succ_of_factors_gt ht'_pos fun q hq hqd =>
    hp_geprimes.trans_lt (lt_of_le_of_ne
      (hp_min q hq (hpk_t ▸ dvd_mul_of_dvd_right hqd _))
      fun hqp => hp_prime.coprime_iff_not_dvd.mp hcoprime (hqp ▸ hqd))

/-- After factoring `t = p^k * t'` with `k ≥ 1`, `p` prime, and `Coprime p t'`, the prime
factors of `t` are those of `t'` plus `{p}`. -/
private lemma card_primeFactors_of_coprime_decomp {t t' p k : Nat} (hp_prime : p.Prime)
    (hk : 1 ≤ k) (hpk_t : p ^ k * t' = t) (hcoprime : Nat.Coprime p t') :
    t.primeFactors.card = t'.primeFactors.card + 1 := by
  have hp_not_t' : p ∉ t'.primeFactors := fun h =>
    hp_prime.coprime_iff_not_dvd.mp hcoprime (mem_primeFactors.mp h).2.1
  rw [← hpk_t, Nat.Coprime.primeFactors_mul (hcoprime.pow_left k),
    primeFactors_pow p (by omega : k ≠ 0), hp_prime.primeFactors,
    Finset.card_union_of_disjoint (Finset.disjoint_singleton_left.mpr hp_not_t'),
    Finset.card_singleton, Nat.add_comm]

/-- `1 ∈ P j` for any `j` since `1` has no prime factors. -/
private theorem one_mem_P (j : Nat) : 1 ∈ P j := by grind [Nat.not_prime_one, Nat.dvd_one]

/-! ### Multiplicative decomposition -/

/-- Decompose `t` at a prime factor `p`: `t = p ^ k * t'` with `k ≥ 1`, `Coprime p t'`,
`2 ≤ p ^ k`, `1 ≤ t' < t`. -/
private lemma exists_factor_decomp {t p : Nat} (hp : p.Prime) (hpt : p ∣ t) (htne : t ≠ 0) :
    ∃ k t' : Nat, 1 ≤ k ∧ p ^ k * t' = t ∧ 2 ≤ p ^ k ∧ 1 ≤ t' ∧ t' < t ∧
      Nat.Coprime p t' := by
  set k := t.factorization p
  set t' := ordCompl[p] t -- t / p ^ k
  have hk_pos : 1 ≤ k :=
    (hp.pow_dvd_iff_le_factorization htne).mp (by simpa using hpt)
  have hpk_t : ordProj[p] t * t' = t := ordProj_mul_ordCompl_eq_self t p
  have hpk_ge2 : 2 ≤ ordProj[p] t :=
    hp.two_le.trans (by simpa using Nat.pow_le_pow_right hp.one_lt.le hk_pos)
  have ht'_pos : 1 ≤ t' := Nat.ordCompl_pos _ htne
  refine ⟨k, t', hk_pos, hpk_t, hpk_ge2, ht'_pos, ?_, coprime_ordCompl hp htne⟩
  nlinarith [hpk_t, hpk_ge2, ht'_pos]

/-- For `t ≥ 2`, decompose at the smallest prime factor. -/
private lemma exists_minFac_decomp {t : Nat} (ht : 2 ≤ t) :
    ∃ p k t' : Nat, p.Prime ∧ p ∣ t ∧ 1 ≤ k ∧ p ^ k * t' = t ∧
      2 ≤ p ^ k ∧ 1 ≤ t' ∧ t' < t ∧ Nat.Coprime p t' ∧
      (∀ q, q.Prime → q ∣ t → p ≤ q) := by
  obtain ⟨k, t', hk, hpkt, hpk2, ht'p, ht'l, hcop⟩ :=
    exists_factor_decomp (minFac_prime (by omega)) (minFac_dvd t) (by omega)
  exact ⟨_, k, t', minFac_prime (by omega), minFac_dvd t, hk, hpkt, hpk2, ht'p, ht'l,
    hcop, fun q hq hqd => minFac_le_of_dvd hq.two_le hqd⟩

/-! ### Products over prime windows -/

/-- `primesProd front back = ∏_{i ∈ [front, back]} (i-th prime)`. -/
private noncomputable def primesProd (front back : Nat) : Nat :=
  ∏ i ∈ Finset.Ico front (back + 1), nth Nat.Prime i

/-- `primesProdM1 front back = ∏_{i ∈ [front, back]} ((i-th prime) - 1)`. -/
private noncomputable def primesProdM1 (front back : Nat) : Nat :=
  ∏ i ∈ Finset.Ico front (back + 1), (nth Nat.Prime i - 1)

@[grind =] private theorem primesProd_empty {front back : Nat} (h : back < front) :
    primesProd front back = 1 := by grind [primesProd, Finset.Ico_eq_empty]

@[grind =] private theorem primesProdM1_empty {front back : Nat} (h : back < front) :
    primesProdM1 front back = 1 := by grind [primesProdM1, Finset.Ico_eq_empty]

@[grind =] private theorem primesProd_succ {front back : Nat} (h : front ≤ back + 1) :
    primesProd front (back + 1) = primesProd front back * nth Nat.Prime (back + 1) :=
  Finset.prod_Ico_succ_top h _

@[grind =] private theorem primesProdM1_succ {front back : Nat} (h : front ≤ back + 1) :
    primesProdM1 front (back + 1) = primesProdM1 front back * (nth Nat.Prime (back + 1) - 1) :=
  Finset.prod_Ico_succ_top h _

@[grind =] private theorem primesProd_self (i : Nat) :
    primesProd i i = nth Nat.Prime i := by simp [primesProd]

@[grind =] private theorem primesProdM1_self (i : Nat) :
    primesProdM1 i i = nth Nat.Prime i - 1 := by simp [primesProdM1]

/-- `primesProdM1 front B ≤ primesProd front B` since each factor `(p-1) ≤ p`. -/
private theorem primesProdM1_le_primesProd (front B : Nat) :
    primesProdM1 front B ≤ primesProd front B :=
  Finset.prod_le_prod (fun _ _ => zero_le _) (fun _ _ => by omega)

/-- Factoring `primesProd` at the front. -/
@[grind =] private theorem primesProd_succ_front {front B : Nat} (hB : front ≤ B) :
    primesProd front B = nth Nat.Prime front * primesProd (front + 1) B := by
  simp [primesProd, Finset.prod_eq_prod_Ico_succ_bot (by omega : front < B + 1)]

/-- Factoring `primesProdM1` at the front. -/
@[grind =] private theorem primesProdM1_succ_front {front B : Nat} (hB : front ≤ B) :
    primesProdM1 front B = (nth Nat.Prime front - 1) * primesProdM1 (front + 1) B := by
  grind [primesProdM1, Finset.prod_eq_prod_Ico_succ_bot]

/-- Wheel invariant after extending the window by one prime (the recursive arm
on a non-empty window). -/
private lemma extend_case3_invariants {m target front back lhs rhs : Nat}
    (hlhs : lhs = m * primesProd front back) (hrhs : rhs = target * primesProdM1 front back)
    (hf : front ≤ back) (hb : back + 1 < 49) :
    lhs * primesRArray.get (back + 1) = m * primesProd front (back + 1) ∧
    rhs * (primesRArray.get (back + 1) - 1) = target * primesProdM1 front (back + 1) := by grind

/-- Wheel invariant when seeding an empty window at `front` (the recursive arm
on an empty window). -/
private lemma extend_case6_invariants {m target front back lhs rhs : Nat}
    (hlhs : lhs = m * primesProd front back) (hrhs : rhs = target * primesProdM1 front back)
    (hback : back < front) (hf : front < 49) :
    lhs * primesRArray.get front = m * primesProd front front ∧
    rhs * (primesRArray.get front - 1) = target * primesProdM1 front front := by grind

/-! ### Sigma at a single prime -/

/-- `σ₁(p ^ k) * (p₀ - 1) ≤ p ^ k * p₀` for `p` prime, `2 ≤ p₀ ≤ p`. One step
of the window σ-bound: it lets a prime in the window absorb a `p^k` factor of `t`. -/
private theorem sigma_pow_le_window_factor {p p₀ k : Nat} (hp : p.Prime) (hp₀ : 2 ≤ p₀)
    (hple : p₀ ≤ p) :
    σ₁ (p ^ k) * (p₀ - 1) ≤ p ^ k * p₀ := by
  have hpk_pos : 1 ≤ p ^ k := one_le_pow _ _ hp.pos
  refine Nat.le_of_mul_le_mul_right ?_ (by omega : 0 < p - 1)
  rw [mul_right_comm, sigma_one_apply_prime_pow' hp,
    Nat.div_mul_cancel (Nat.sub_one_dvd_pow_sub_one p (k + 1))]
  zify [one_le_pow (k+1) _ hp.pos, (by omega : (1 : Nat) ≤ p₀), (by omega : (1 : Nat) ≤ p)]
  nlinarith [hpk_pos, hple, hp₀, hp.two_le, pow_succ p k]

/-- σ formula in `expChildren`'s loop: `(p ^ k * p - 1) / (p - 1) = σ₁ (p ^ k)` for prime `p`. -/
@[grind =] private theorem sigma_pow_expChildren_eq {p k : Nat} (hp : p.Prime) :
    (p ^ k * p - 1) / (p - 1) = σ₁ (p ^ k) := by rw [← pow_succ, ← sigma_one_apply_prime_pow' hp]

private theorem ceilDiv_le_iff {a b c : Nat} (hb : 0 < b) : ceilDiv a b ≤ c ↔ a ≤ c * b := by
  rw [ceilDiv, div_le_iff_le_mul_add_pred hb, mul_comm]; omega

private theorem le_ceilDiv_mul {a b : Nat} (hb : 0 < b) : a ≤ ceilDiv a b * b :=
  (ceilDiv_le_iff hb).mp le_rfl

/-! ### The two main bounds: σ-window and radical -/

/-- `σ₁(t) * Π'(front, B) ≤ t * Π(front, B)` for `t ∈ P front` with at most
`B - front + 1` distinct primes. -/
private theorem sigma_bound_window (t front B : Nat) (ht : 1 ≤ t) (hP : t ∈ P front)
    (hBsize : B + 1 ≤ 49) (hcard : t.primeFactors.card + front ≤ B + 1) :
    σ₁ t * primesProdM1 front B ≤ t * primesProd front B := by
  induction t using Nat.strongRecOn generalizing front B with
  | _ t ih =>
    by_cases ht1 : t = 1
    · subst ht1
      simpa using primesProdM1_le_primesProd front B
    have ht2 : 2 ≤ t := by omega
    obtain ⟨p, k, t', hp_prime, hp_dvd, hk_pos, hpk_t, _, ht'_pos, ht'_lt,
        hcoprime, hp_min⟩ := exists_minFac_decomp ht2
    have hp_geprimes : nth Nat.Prime front ≤ p := hP.2 p hp_prime hp_dvd
    have hcard := card_primeFactors_of_coprime_decomp hp_prime hk_pos hpk_t hcoprime
    have ht'_P : t' ∈ P (front + 1) :=
      mem_P_succ_of_coprime_decomp hp_prime hp_geprimes hp_min hpk_t ht'_pos hcoprime
    have IH := ih t' ht'_lt _ _ ht'_pos ht'_P hBsize (by omega)
    have hcons : σ₁ (p ^ k) * (nth Nat.Prime front - 1) ≤ p ^ k * nth Nat.Prime front :=
      sigma_pow_le_window_factor hp_prime (prime_nth_prime front).two_le hp_geprimes
    calc σ₁ t * primesProdM1 front B
        = σ₁ (p ^ k) * (nth Nat.Prime front - 1) *
            (σ₁ t' * primesProdM1 (front + 1) B) := by
          rw [← hpk_t, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
            (hcoprime.pow_left k), primesProdM1_succ_front (by omega)]
          ring
      _ ≤ p ^ k * nth Nat.Prime front * (t' * primesProd (front + 1) B) := by gcongr
      _ = t * primesProd front B := by grind

/-- `primesProd front (front + j - 1) ≤ t` for `t ∈ P front` with `j ≥ 1`
distinct primes, and `front + j ≤ 49`. -/
private theorem primesProd_le_t (t front : Nat) (ht : 1 ≤ t) (hP : t ∈ P front) (j : Nat)
    (hj : 1 ≤ j) (hjle : j ≤ t.primeFactors.card) (hsize : front + j ≤ 49) :
    primesProd front (front + j - 1) ≤ t := by
  induction t using Nat.strongRecOn generalizing front j with
  | _ t ih =>
    have ht1 : t ≠ 1 := by grind [primeFactors_one]
    have ht2 : 2 ≤ t := by omega
    obtain ⟨p, k, t', hp_prime, _, hk_pos, hpk_t, _, ht'_pos, ht'_lt, hcoprime, hp_min⟩ :=
      exists_minFac_decomp ht2
    have hp_dvd : p ∣ t := hpk_t ▸ (dvd_pow_self p (by omega)).mul_right _
    have hp_geprimes : nth Nat.Prime front ≤ p := hP.2 p hp_prime hp_dvd
    have hpk_ge : nth Nat.Prime front ≤ p ^ k := hp_geprimes.trans (le_self_pow (by omega) p)
    rcases lt_or_ge 1 j with hj2 | hj2
    · have ht'_in_P : t' ∈ P (front + 1) :=
        mem_P_succ_of_coprime_decomp hp_prime hp_geprimes hp_min hpk_t ht'_pos hcoprime
      have hcard := card_primeFactors_of_coprime_decomp hp_prime hk_pos hpk_t hcoprime
      have IH := ih t' ht'_lt _ ht'_pos ht'_in_P (j - 1) (by omega) (by omega) (by omega)
      rw [(by omega : (front + 1) + (j - 1) - 1 = front + j - 1)] at IH
      calc primesProd front (front + j - 1)
          = nth Nat.Prime front * primesProd (front + 1) (front + j - 1) :=
            primesProd_succ_front (by omega)
        _ ≤ p ^ k * t' := by gcongr
        _ = t := hpk_t
    · obtain rfl : j = 1 := by omega
      rw [Nat.add_sub_cancel, primesProd_self]
      exact hpk_ge.trans (hpk_t ▸ Nat.le_mul_of_pos_right _ ht'_pos)

/-! ### Ruling out `.tooLarge` from a witness -/

/-- At a wheel `.tooLarge` state with `back + 1 < 49`, the witness `t` with
`t ≤ m`, `t ∈ P front`, `target ≤ σ₁ t` gives `False`. -/
private theorem extend_tooLarge_contradiction
    {m target front back lhs rhs : Nat} {t : Nat}
    (hlhs : lhs = m * primesProd front back)
    (hrhs : rhs = target * primesProdM1 front back)
    (hfront : front ≤ back + 1)
    (hback_lt : back + 1 < 49)
    (hsmall : lhs < rhs)
    (hbig : lhs * primesRArray.get (back + 1) > m * m)
    (ht2 : 2 ≤ t) (htP : t ∈ P front) (htm : t ≤ m) (htσ : target ≤ σ₁ t) : False := by
  rw [primesRArray_get_eq_nth _ hback_lt] at hbig
  rcases lt_or_ge t.primeFactors.card (back + 2 - front) with hcard | hcard
  · have hbound := sigma_bound_window t front back (by omega) htP (by omega) (by omega)
    have h_chain : σ₁ t * primesProdM1 front back < target * primesProdM1 front back := by
      nlinarith [Nat.mul_le_mul_right (primesProd front back) htm, hlhs, hrhs, hsmall]
    exact absurd htσ (not_le.mpr (Nat.lt_of_mul_lt_mul_right h_chain))
  · have hrad := primesProd_le_t t front (by omega) htP (back + 2 - front) (by omega) hcard
      (by omega)
    rw [(by omega : front + (back + 2 - front) - 1 = back + 1)] at hrad
    have hppsm : m < primesProd front (back + 1) := Nat.lt_of_mul_lt_mul_left (a := m)
      (by rw [primesProd_succ (by omega : front ≤ back + 1), ← mul_assoc, ← hlhs]; exact hbig)
    omega

/-- At a wheel `.tooLarge` empty-window state with `front < 49`, the witness `t`
with `t ≤ m`, `t ∈ P front`, `t ≥ 2` gives `False`. -/
private theorem extend_tooLarge_empty_contradiction
    {m front back lhs : Nat} {t : Nat}
    (hlhs : lhs = m * primesProd front back) (hfront_lt : front < 49)
    (hempty : back + 1 = front)
    (hbig : lhs * primesRArray.get front > m * m)
    (ht2 : 2 ≤ t) (htP : t ∈ P front) (htm : t ≤ m) : False := by
  rw [primesProd_empty (by omega : back < front), mul_one] at hlhs
  rw [primesRArray_get_eq_nth _ hfront_lt, hlhs, mul_comm m m] at hbig
  have h1 : nth Nat.Prime front ≤ t.minFac := htP.2 _ (minFac_prime (by omega)) (minFac_dvd t)
  linarith [Nat.lt_of_mul_lt_mul_left hbig, minFac_le (by omega : 0 < t)]

/-- If `t` is a witness, `extend` cannot return `.tooLarge`. -/
private theorem extend_ne_tooLarge_of_witness (fuel m target front t : Nat) (ht2 : 2 ≤ t)
    (htP : t ∈ P front) (htm : t ≤ m) (htσ : target ≤ σ₁ t)
    (back lhs rhs : Nat) (hlhs : lhs = m * primesProd front back)
    (hrhs : rhs = target * primesProdM1 front back) (hfront : front ≤ back + 1) :
    extend fuel (m * m) front back lhs rhs ≠ .tooLarge := by
  fun_induction extend fuel (m * m) front back lhs rhs with
  | case1 | case2 | case5 | case8 => simp
  | case3 _ _ _ _ _ _ hb1 _ _ hbig =>
    exact fun _ =>
      extend_tooLarge_contradiction hlhs hrhs hfront hb1 (by omega) hbig ht2 htP htm htσ
  | case4 _ _ _ _ hf _ hb1 _ _ _ ih => grind [extend_case3_invariants]
  | case6 _ _ _ _ _ hf1 _ _ hbig =>
    exact fun _ => extend_tooLarge_empty_contradiction hlhs hf1 (by omega) hbig ht2 htP htm
  | case7 _ _ _ _ _ hf1 _ _ _ ih => grind [extend_case6_invariants]

/-! ### Window invariants -/

/-- When `extend` returns `.window`, the new `(b, lhs', rhs')` satisfy the wheel invariants
shifted to `b`, and `b ≥ back`. -/
private theorem extend_window_invariant (fuel m target front back lhs rhs b lhs' rhs' : Nat)
    (hlhs : lhs = m * primesProd front back) (hrhs : rhs = target * primesProdM1 front back)
    (hfront : front ≤ back + 1)
    (heq : extend fuel (m * m) front back lhs rhs = Wheel.window b lhs' rhs') :
    lhs' = m * primesProd front b ∧ rhs' = target * primesProdM1 front b ∧
    back ≤ b ∧ front ≤ b := by
  fun_induction extend fuel (m * m) front back lhs rhs with
  | case1 | case5 | case8 => simp at heq
  | case2 _ _ _ _ hf _ => obtain ⟨rfl, rfl, rfl⟩ := heq; exact ⟨hlhs, hrhs, le_refl _, hf⟩
  | case3 | case6 => cases heq
  | case4 _ _ _ _ hf _ hb1 _ _ _ ih => grind [extend_case3_invariants]
  | case7 _ _ _ _ _ hf1 _ _ _ ih => grind [extend_case6_invariants]

/-! ### Degenerate case: `lhs = 0` -/

/-- For `m2 = 0` and `lhs = 0`: `extend` returns either `.exhaustedTable` or
`.window b 0 rhs'` (so never `.tooLarge`, and any `.window` has `lhs' = 0`). -/
@[grind .]
private lemma extend_zero_lhs_combined (fuel front back lhs rhs : Nat) (hlhs : lhs = 0) :
    extend fuel 0 front back lhs rhs = Wheel.exhaustedTable ∨
    ∃ b rhs', extend fuel 0 front back lhs rhs = Wheel.window b 0 rhs' := by
  fun_induction extend fuel 0 front back lhs rhs with
  | case2 back _ rhs => exact Or.inr ⟨back, rhs, by grind⟩
  | _ => grind

/-- For `m2 = 0` and `lhs = 0`, `wheelChildren` returns `none`. -/
private theorem wheelChildren_zero_no_some (fuel target num front back lhs rhs : Nat)
    (acc : List (Nat × Nat × Nat)) (hlhs : lhs = 0) :
    wheelChildren fuel 0 0 target num front back lhs rhs acc = none := by
  fun_induction wheelChildren with grind [Nat.zero_div]

/-! ### `expChildren` analysis -/

/-- One step of `expChildren` when `pk ≤ m` and `σ(pk) < target`. -/
private theorem expChildren_step
    {fuel target num next m p pk : Nat}
    (hfuel : 1 ≤ fuel) (hpk_le_m : pk ≤ m)
    (hsig_lt : (pk * p - 1) / (p - 1) < target) :
    expChildren fuel target num next m p pk =
      (ceilDiv target ((pk * p - 1) / (p - 1)), num * pk, next) ::
      expChildren (fuel - 1) target num next m p (pk * p) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    simp only [expChildren, if_neg (by omega : ¬ pk > m),
      if_neg (by omega : ¬ (pk * p - 1) / (p - 1) ≥ target), Nat.add_sub_cancel]

/-- One step of `expChildren` when `pk ≤ m` and `σ(pk) ≥ target` (final child). -/
private theorem expChildren_stop
    {fuel target num next m p pk : Nat}
    (hfuel : 1 ≤ fuel) (hpk_le_m : pk ≤ m)
    (hsig_ge : (pk * p - 1) / (p - 1) ≥ target) :
    expChildren fuel target num next m p pk =
      [(ceilDiv target ((pk * p - 1) / (p - 1)), num * pk, next)] := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    simp only [expChildren, if_neg (by omega : ¬ pk > m), if_pos hsig_ge]

/-- Every entry of `expChildren ... (p ^ k₀)` (for prime `p`, `k₀ ≥ 1`) has the
prime-power form for some `k ≥ k₀` with `p ^ k ≤ m`. -/
private theorem mem_expChildren {fuel target num nextMinIdx m p k₀ : Nat}
    (hp : p.Prime) (hk₀ : 1 ≤ k₀) {c : Nat × Nat × Nat}
    (hc : c ∈ expChildren fuel target num nextMinIdx m p (p ^ k₀)) :
    ∃ k, k₀ ≤ k ∧ p ^ k ≤ m ∧
      c = (ceilDiv target (σ₁ (p ^ k)), num * p ^ k, nextMinIdx) := by
  induction fuel generalizing k₀ with
  | zero => simp only [expChildren, List.not_mem_nil] at hc
  | succ fuel ih =>
    rw [expChildren] at hc
    have hspk_eq : (p ^ k₀ * p - 1) / (p - 1) = σ₁ (p ^ k₀) := sigma_pow_expChildren_eq hp
    by_cases hpm : p ^ k₀ > m
    · grind
    by_cases hge : (p ^ k₀ * p - 1) / (p - 1) ≥ target
    · grind
    simp only [if_neg hpm, if_neg hge, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨k₀, le_refl _, by omega, by rw [hspk_eq]⟩
    · rw [← pow_succ] at hc
      have ⟨k, hk, hpkm, hceq⟩ := ih (by omega) hc
      exact ⟨k, by omega, hpkm, hceq⟩

/-- Witness `1` for the stop arm of `expChildren_witness_walk`: when `σ(p ^ j₀) ≥ target`,
the child `(ceilDiv target σ(p ^ j₀), num*p ^ j₀, next)` has `1` as a witness. -/
private lemma one_witnesses_stop {B num target next p k j₀ t'' : Nat}
    (hp : p.Prime) (hjk : j₀ ≤ k) (ht''_pos : 1 ≤ t'')
    (hnumt : num * p ^ k * t'' < B) (hσ_target : σ₁ (p ^ j₀) ≥ target) :
    W B (ceilDiv target (σ₁ (p ^ j₀))) (num * p ^ j₀) next ≠ ∅ := by
  refine Set.nonempty_iff_ne_empty.mp ⟨1, one_mem_P _, ?_, ?_⟩
  · linarith [Nat.mul_le_mul_left num (Nat.pow_le_pow_right hp.one_lt.le hjk),
      Nat.le_mul_of_pos_right (num * p ^ k) ht''_pos]
  · have hσpj_pos : 0 < σ₁ (p ^ j₀) := ArithmeticFunction.sigma_pos _ _ (pow_ne_zero _ hp.pos.ne')
    simp [ceilDiv, div_le_iff_le_mul_add_pred hσpj_pos]
    omega

/-- Walk `expChildren` from `pk₀ = p ^ j₀` looking for a child with a witness, given
a parent witness `t = p ^ k * t''` (factored at `p` with `t''` coprime to `p`). -/
private theorem expChildren_witness_walk {B num target m p : Nat} (hp : p.Prime) (next : Nat)
    (n k j₀ : Nat) (hn : k - j₀ = n) (hj₀ : 1 ≤ j₀) (hj₀_k : j₀ ≤ k) (hpk_le_m : p ^ k ≤ m)
    {t'' : Nat} (ht''_pos : 1 ≤ t'') (ht''_P : t'' ∈ P next) (hnumt : num * p ^ k * t'' < B)
    (htσ : target ≤ σ₁ (p ^ k) * σ₁ t'') {fuel : Nat} (hfuel : n + 1 ≤ fuel) :
    ∃ c ∈ expChildren fuel target num next m p (p ^ j₀), W B c.1 c.2.1 c.2.2 ≠ ∅ := by
  induction n generalizing j₀ fuel with
  | zero =>
    obtain rfl : j₀ = k := by omega
    have h_sig_eq : (p ^ j₀ * p - 1) / (p - 1) = σ₁ (p ^ j₀) := sigma_pow_expChildren_eq hp
    by_cases hσ_target : σ₁ (p ^ j₀) ≥ target
    · rw [expChildren_stop (by omega) hpk_le_m (h_sig_eq.symm ▸ hσ_target), h_sig_eq]
      exact ⟨_, List.mem_singleton.mpr rfl,
        one_witnesses_stop hp hj₀_k ht''_pos hnumt hσ_target⟩
    push Not at hσ_target
    rw [expChildren_step (by omega) hpk_le_m (h_sig_eq.symm ▸ hσ_target), h_sig_eq]
    refine ⟨_, List.mem_cons_self, Set.nonempty_iff_ne_empty.mp ⟨t'', ht''_P, hnumt, ?_⟩⟩
    exact (ceilDiv_le_iff (ArithmeticFunction.sigma_pos _ _ (pow_ne_zero _ hp.pos.ne'))).mpr
      (by linarith [mul_comm (σ₁ (p ^ j₀)) (σ₁ t'')])
  | succ n ih =>
    have hpj_le_m : p ^ j₀ ≤ m := (Nat.pow_le_pow_right hp.one_lt.le hj₀_k).trans hpk_le_m
    have h_sig_eq : (p ^ j₀ * p - 1) / (p - 1) = σ₁ (p ^ j₀) := sigma_pow_expChildren_eq hp
    by_cases hσ_target : σ₁ (p ^ j₀) ≥ target
    · rw [expChildren_stop (by omega) hpj_le_m (h_sig_eq.symm ▸ hσ_target), h_sig_eq]
      exact ⟨_, List.mem_singleton.mpr rfl,
        one_witnesses_stop hp hj₀_k ht''_pos hnumt hσ_target⟩
    push Not at hσ_target
    rw [expChildren_step (by omega) hpj_le_m (h_sig_eq.symm ▸ hσ_target), h_sig_eq, ← pow_succ]
    obtain ⟨c, hc, hwit⟩ := ih (j₀ + 1) (by omega) (by omega) (by omega)
      (fuel := fuel - 1) (by omega)
    exact ⟨c, List.mem_cons_of_mem _ hc, hwit⟩

/-! ### `wheelChildren` and `children` -/

/-- Each entry of `wheelChildren`'s output is either from `acc` or has the prime-power form. -/
private theorem mem_wheelChildren {fuel m2 m target num front back lhs rhs : Nat}
    {acc : List (Nat × Nat × Nat)} {L : List (Nat × Nat × Nat)}
    (h : wheelChildren fuel m2 m target num front back lhs rhs acc = some L)
    {c : Nat × Nat × Nat} (hc : c ∈ L) :
    c ∈ acc ∨ ∃ i k, front ≤ i ∧ 1 ≤ k ∧ (nth Nat.Prime i) ^ k ≤ m ∧
      c = (ceilDiv target (σ₁ ((nth Nat.Prime i) ^ k)),
        num * (nth Nat.Prime i) ^ k, i + 1) := by
  fun_induction wheelChildren fuel m2 m target num front back lhs rhs acc generalizing L with
  | case1 | case2 | case5 => cases h
  | case3 => grind
  | case4 front _ _ _ _ _ _ _ _ _ hp _ =>
    rename_i hrec
    have hq : primesRArray.get front = nth Nat.Prime front := primesRArray_get_eq_nth front hp
    rcases hrec h hc with hcacc | ⟨i, k, hi, hk, hpkm, hceq⟩
    · rcases List.mem_append.mp hcacc with hcexp | hcorig
      · obtain ⟨k, hk, hpkm, hceq⟩ := mem_expChildren (prime_nth_prime front) le_rfl
          (by rw [pow_one, ← hq]; exact hcexp)
        exact Or.inr ⟨front, k, le_rfl, hk, hpkm, hceq⟩
      · exact Or.inl hcorig
    · exact Or.inr ⟨i, k, by omega, hk, hpkm, hceq⟩

/-- Anything in `acc` going in is still in the output `L` coming out, since `wheelChildren`
only ever prepends to `acc`. -/
private lemma wheelChildren_acc_subset (fuel m2 m target num front back lhs rhs : Nat)
    (acc L : List (Nat × Nat × Nat))
    (h : wheelChildren fuel m2 m target num front back lhs rhs acc = some L) : acc ⊆ L := by
  fun_induction wheelChildren fuel m2 m target num front back lhs rhs acc generalizing L with
  | case1 | case2 | case5 => cases h
  | case3 => grind
  | case4 => grind [List.mem_append_right]

/-- Given the wheel invariants and a viable witness `t`, some child in
`wheelChildren`'s output `L` has a non-empty witness set. -/
private theorem wheelChildren_witness {B num m target : Nat} (hmdef : m = B / num)
    (hnum_pos : 1 ≤ num) (fuel front back lhs rhs : Nat) (acc L : List (Nat × Nat × Nat))
    (hfuel : 49 + 1 - front ≤ fuel)
    (hlhs : lhs = m * primesProd front back) (hrhs : rhs = target * primesProdM1 front back)
    (hfront_le : front ≤ back + 1)
    (hwc : wheelChildren fuel (m * m) m target num front back lhs rhs acc = some L)
    (t : Nat) (ht2 : 2 ≤ t) (htP : t ∈ P front) (hnumt : num * t < B) (htσ : target ≤ σ₁ t) :
    ∃ c ∈ L, W B c.1 c.2.1 c.2.2 ≠ ∅ := by
  have htm : t ≤ m := hmdef ▸ (le_div_iff_mul_le hnum_pos).mpr (by linarith)
  fun_induction wheelChildren fuel (m * m) m target num front back lhs rhs acc generalizing L with
  | case1 | case2 | case5 => cases hwc
  | case3 front _ _ _ _ _ hext =>
    exact absurd hext (extend_ne_tooLarge_of_witness 50 m target front t ht2 htP htm htσ
      _ _ _ hlhs hrhs hfront_le)
  | case4 front back lhs rhs acc _ b lhs' rhs' hext hp _ =>
    rename_i hrec
    have hq : primesRArray.get front = nth Nat.Prime front := primesRArray_get_eq_nth front hp
    have hp_prime : (nth Nat.Prime front).Prime := prime_nth_prime front
    obtain ⟨hlhs', hrhs', _, hfront_b⟩ := extend_window_invariant 50 m target front back lhs rhs
      b lhs' rhs' hlhs hrhs hfront_le hext
    have hlhs_new : lhs' / primesRArray.get front = m * primesProd (front + 1) b := by
      rw [hq, hlhs', primesProd_succ_front hfront_b, mul_left_comm,
        Nat.mul_div_cancel_left _ hp_prime.pos]
    have hrhs_new : rhs' / (primesRArray.get front - 1) =
        target * primesProdM1 (front + 1) b := by
      rw [hq, hrhs', primesProdM1_succ_front hfront_b, mul_left_comm,
        Nat.mul_div_cancel_left _ (Nat.sub_pos_of_lt hp_prime.one_lt)]
    by_cases hdvd : nth Nat.Prime front ∣ t
    · obtain ⟨k, t'', hk_pos, hpk_t, _, ht''_pos, _, hcoprime⟩ :=
        exists_factor_decomp hp_prime hdvd (by omega)
      have hpk_le_m : nth Nat.Prime front ^ k ≤ m :=
        (le_of_dvd (by omega) ⟨t'', hpk_t.symm⟩).trans htm
      have htσ' : target ≤ σ₁ ((nth Nat.Prime front) ^ k) * σ₁ t'' := by
        rwa [← ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
          (hcoprime.pow_left k), hpk_t]
      have ht''_P : t'' ∈ P (front + 1) :=
        mem_P_succ_of_coprime_decomp hp_prime le_rfl htP.2 hpk_t ht''_pos hcoprime
      obtain ⟨c, hc, hwit⟩ := expChildren_witness_walk hp_prime (front + 1) (k - 1) k 1
        (by omega) (by omega) hk_pos hpk_le_m ht''_pos ht''_P
        (by rwa [mul_assoc, hpk_t]) htσ' (fuel := m + 1)
        (by have : k ≤ m := (Nat.lt_pow_self hp_prime.one_lt).le.trans hpk_le_m; omega)
      exact ⟨c, wheelChildren_acc_subset _ _ _ _ _ _ _ _ _ _ _ hwc
        (List.mem_append_left _ (by grind)), hwit⟩
    · exact hrec L (by omega) hlhs_new hrhs_new (by omega) hwc
        (mem_P_succ_of_factors_gt (by omega) fun q' hq'_prime hq'_dvd =>
          lt_of_le_of_ne (htP.2 q' hq'_prime hq'_dvd) (Ne.symm fun h => hdvd (h ▸ hq'_dvd)))

/-- Every `c` in `children`'s output is a prime-power child of the form
`(⌈target / σ₁(p ^ k)⌉, num * p ^ k, i + 1)` for some prime index `i ≥ minIdx`
with `p = nth Nat.Prime i` and some `k ≥ 1`, `p ^ k ≤ B/num`. -/
private theorem mem_children {B target num minIdx : Nat} {cs : List (Nat × Nat × Nat)}
    (h : children B target num minIdx = some cs) {c : Nat × Nat × Nat} (hc : c ∈ cs) :
    ∃ i k, minIdx ≤ i ∧ 1 ≤ k ∧ (nth Nat.Prime i) ^ k ≤ B / num ∧
      c = (ceilDiv target (σ₁ ((nth Nat.Prime i) ^ k)),
        num * (nth Nat.Prime i) ^ k, i + 1) := by
  rw [children] at h
  split at h
  · exact (mem_wheelChildren h hc).resolve_left (by simp)
  · cases h

/-- If `t'` is a witness of the child `(⌈target / σ₁(p ^ k)⌉, num * p ^ k, i+1)`
where `p = nth Nat.Prime i`, then `p ^ k * t'` is a non-trivial witness of the
parent `(target, num, minIdx)`. -/
private theorem child_witness_to_parent {B target num minIdx i k : Nat}
    (hmi : minIdx ≤ i) (hk : 1 ≤ k) {t' : Nat}
    (ht' : t' ∈ W B (ceilDiv target (σ₁ ((nth Nat.Prime i) ^ k)))
      (num * (nth Nat.Prime i) ^ k) (i + 1)) :
    (nth Nat.Prime i) ^ k * t' ∈ W B target num minIdx ∧
      (nth Nat.Prime i) ^ k * t' ≠ 1 := by
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
  · rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, mul_comm]
    exact (le_ceilDiv_mul (ArithmeticFunction.sigma_pos _ _ (pow_ne_zero _ hpPrime.pos.ne'))).trans
      (Nat.mul_le_mul_right _ ht'σ)

/-- A non-trivial witness of the parent gives a witness for some child in `cs`. -/
private theorem witness_to_child {B target num minIdx : Nat} {cs : List (Nat × Nat × Nat)}
    (h : children B target num minIdx = some cs) {t : Nat}
    (ht : t ∈ W B target num minIdx) (h1 : t ≠ 1) :
    ∃ c ∈ cs, W B c.1 c.2.1 c.2.2 ≠ ∅ := by
  rcases Nat.eq_zero_or_pos num with rfl | hnum_pos
  · grind [children, wheelChildren_zero_no_some]
  · rw [children] at h
    split at h
    · rename_i hminIdx_lt
      dsimp only at h
      obtain ⟨⟨ht_pos, htP⟩, htlt, htσ⟩ := ht
      rw [primesRArray_get_eq_nth minIdx hminIdx_lt, ← primesProdM1_self minIdx,
        mul_comm (nth Nat.Prime minIdx) (B / num), ← primesProd_self minIdx] at h
      exact wheelChildren_witness rfl hnum_pos _ minIdx minIdx _ _ [] cs (by omega) rfl rfl
        (by omega) h t (by omega) ⟨ht_pos, htP⟩ htlt htσ
    · cases h

/-- `children` reduces nontrivial witnesses of a node to witnesses of its children. -/
theorem children_spec {B target num minIdx : Nat} {cs : List (Nat × Nat × Nat)}
    (h : children B target num minIdx = some cs) :
    (∃ t ∈ W B target num minIdx, t ≠ 1) ↔
      ∃ c ∈ cs, W B c.1 c.2.1 c.2.2 ≠ ∅ := by
  refine ⟨fun ⟨t, ht, h1⟩ => witness_to_child h ht h1, ?_⟩
  rintro ⟨c, hc, hwit⟩
  obtain ⟨i, k, hmi, hk, _, hceq⟩ := mem_children h hc
  obtain ⟨t', ht'⟩ := Set.nonempty_iff_ne_empty.mpr hwit
  rw [hceq] at ht'
  obtain ⟨hw, hne⟩ := child_witness_to_parent hmi hk ht'
  exact ⟨_, hw, hne⟩

/-! ### Step correctness and top-level result -/

/-- `step = some true` ⟹ every node on the stack has an empty witness set. -/
theorem step_true {B fuel : Nat} {stack : List (Nat × Nat × Nat)}
    (h : step B fuel stack = some true) :
    ∀ node ∈ stack, W B node.1 node.2.1 node.2.2 = ∅ := by
  fun_induction step with
  | case1 | case2 | case3 | case5 => grind
  | case4 _ _ num _ _ _ _ ih =>
    simp only [List.mem_cons, forall_eq_or_imp, Prod.forall]
    refine ⟨?_, fun a b c hm => ih h (a, b, c) hm⟩
    rw [Set.eq_empty_iff_forall_notMem]
    rintro t ⟨⟨ht1, _⟩, htlt, _⟩
    linarith [Nat.le_mul_of_pos_right num ht1]
  | case6 _ _ _ _ _ _ _ hch ih1 =>
    intro node hnode
    rcases List.mem_cons.mp hnode with rfl | hnode
    · rw [Set.eq_empty_iff_forall_notMem]
      intro t htW
      by_cases h1 : t = 1
      · grind [ArithmeticFunction.sigma_one]
      obtain ⟨c, hc, hwc⟩ := (children_spec hch).mp ⟨t, htW, h1⟩
      grind
    · exact ih1 h _ (List.mem_append.mpr (Or.inr hnode))

/-- `step = some false` ⟹ some node on the stack has a nonempty witness set. -/
theorem step_false {B fuel : Nat} {stack : List (Nat × Nat × Nat)}
    (h : step B fuel stack = some false) :
    ∃ node ∈ stack, W B node.1 node.2.1 node.2.2 ≠ ∅ := sorry

/-- A `some true` answer of `highlyAbundantLcm?` on `(lcmRange n, σ₁ (lcmRange n))`
certifies that `lcm (1..n)` is highly abundant. -/
theorem highlyAbundantLcm_correct {n : Nat}
    (h : highlyAbundantLcm? (lcmRange n) (σ₁ (lcmRange n)) = some true) :
    IsHighlyAbundant (lcmRange n) := by
  intro m hm_pos hm_lt
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

end Sage
