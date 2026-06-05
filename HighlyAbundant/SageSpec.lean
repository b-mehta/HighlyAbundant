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
3. Membership in `P`: `mem_P_succ_of_factors_gt`, `one_mem_P`.
4. Multiplicative decomposition: `exists_factor_decomp`, `exists_minFac_decomp`.
5. Products over prime windows: `primesProd`, `primesProdM1`, and the wheel
   invariant updates in cases 3 and 6 of `extend`'s recursion.
6. Sigma at a single prime: `sigma_pow_le_window_factor`, `sigma_pow_expChildren_eq`.
7. The two main bounds: `sigma_bound_window` and `primesProd_le_t`.
8. Ruling out `.tooLarge` from a witness: `extend_ne_tooLarge_of_witness`.
9. Window invariants: `extend_window_invariant`.
10. Degenerate case `lhs = 0`: `wheelChildren_zero_no_some`.
11. `expChildren` analysis: `mem_expChildren`, `expChildren_witness_walk`.
12. `wheelChildren` and `children`: `mem_wheelChildren`, `wheelChildren_witness`,
    `mem_children`, `child_witness_to_parent`, `witness_to_child`, `children_spec`.
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

/-- Fast computation of `(lcmRange n, σ₁ (lcmRange n))` as
`(∏ p^{⌊log_p n⌋}, ∏ σ(p^{⌊log_p n⌋}))` over the primes `p ≤ n` in the table.
Intended for `#eval`-style use to supply `(B, sL)` to `highlyAbundantLcm?`;
the proof in `highlyAbundantLcm_correct` is stated in terms of `lcmRange` so
this equivalence is not needed formally. -/
def lcmData (n : Nat) : Nat × Nat :=
  (primes.toList.takeWhile (· ≤ n)).foldl
    (fun (acc : Nat × Nat) p =>
      let e := log p n
      (acc.1 * p ^ e, acc.2 * ((p ^ (e + 1) - 1) / (p - 1)))) (1, 1)

/-! ### The `primes` table -/

private lemma primesRArray_get_eq_nth_aux : ∀ i : Fin primes.size,
    primesRArray.get i.val = nth Nat.Prime i.val := by
  intro i
  have hp : ∀ i : Fin primes.size, Nat.Prime (primesRArray.get i.val) := by
    decide +kernel
  rw [← nth_count (hp i)]
  congr 1
  decide +kernel +revert

/-- The wheel's array lookup gives the `i`-th prime. -/
private lemma primesRArray_get_eq_nth (i : Nat) (hi : i < primes.size) :
    primesRArray.get i = nth Nat.Prime i :=
  primesRArray_get_eq_nth_aux ⟨i, hi⟩

/-! ### Membership in `P` -/

/-- If `x ≥ 1` and every prime factor of `x` exceeds the `front`-th prime, then
`x ∈ P (front + 1)`. -/
private lemma mem_P_succ_of_factors_gt {x front : Nat} (hx : 1 ≤ x)
    (h : ∀ q, q.Prime → q ∣ x → nth Nat.Prime front < q) : x ∈ P (front + 1) :=
  ⟨hx, fun q hq hqd => by
    by_contra! hlt
    have := le_nth_of_lt_nth_succ hlt hq
    have := h q hq hqd
    omega⟩

/-- `1 ∈ P j` for any `j` since `1` has no prime factors. -/
private theorem one_mem_P (j : Nat) : 1 ∈ P j :=
  ⟨le_rfl, fun _ hq hd => absurd (dvd_one.mp hd) hq.one_lt.ne'⟩

/-! ### Multiplicative decomposition -/

/-- Decompose `t` at a prime factor `p`: `t = p ^ k * t'` with `k ≥ 1`, `Coprime p t'`,
`2 ≤ p ^ k`, `1 ≤ t' < t`. -/
private lemma exists_factor_decomp {t p : Nat} (hp : p.Prime) (hpt : p ∣ t) (htne : t ≠ 0) :
    ∃ k t' : Nat, 1 ≤ k ∧ p ^ k * t' = t ∧ 2 ≤ p ^ k ∧ 1 ≤ t' ∧ t' < t ∧
      Nat.Coprime p t' := by
  set k := t.factorization p
  set t' := t / p ^ k
  have hk_pos : 1 ≤ k := by
    rw [← hp.pow_dvd_iff_le_factorization htne]
    simpa using hpt
  have hpk_t : p ^ k * t' = t := Nat.mul_div_cancel_left' (ordProj_dvd t p)
  have hpk_ge2 : 2 ≤ p ^ k :=
    hp.two_le.trans (by simpa using Nat.pow_le_pow_right hp.one_lt.le hk_pos)
  have ht'_pos : 1 ≤ t' := Nat.pos_of_mul_pos_left (by rw [hpk_t]; omega)
  refine ⟨k, t', hk_pos, hpk_t, hpk_ge2, ht'_pos, ?_, coprime_ordCompl hp htne⟩
  nlinarith [hpk_t, hpk_ge2, ht'_pos]

/-- For `t ≥ 2`, decompose at the smallest prime factor. -/
private lemma exists_minFac_decomp {t : Nat} (ht : 2 ≤ t) :
    ∃ p k t' : Nat, p.Prime ∧ p ∣ t ∧ 1 ≤ k ∧ p ^ k * t' = t ∧
      2 ≤ p ^ k ∧ 1 ≤ t' ∧ t' < t ∧ Nat.Coprime p t' ∧
      (∀ q, q.Prime → q ∣ t → p ≤ q) := by
  have ht1 : t ≠ 1 := by omega
  have htne : t ≠ 0 := by omega
  obtain ⟨k, t', hk, hpkt, hpk2, ht'p, ht'l, hcop⟩ :=
    exists_factor_decomp (minFac_prime ht1) (minFac_dvd t) htne
  exact ⟨_, k, t', minFac_prime ht1, minFac_dvd t, hk, hpkt, hpk2, ht'p, ht'l,
    hcop, fun q hq hqd => minFac_le_of_dvd hq.two_le hqd⟩

/-! ### Products over prime windows -/

/-- `primesProd front back = ∏_{i ∈ [front, back]} (i-th prime)`. -/
private noncomputable def primesProd (front back : Nat) : Nat :=
  ∏ i ∈ Finset.Ico front (back + 1), nth Nat.Prime i

/-- `primesProdM1 front back = ∏_{i ∈ [front, back]} ((i-th prime) - 1)`. -/
private noncomputable def primesProdM1 (front back : Nat) : Nat :=
  ∏ i ∈ Finset.Ico front (back + 1), (nth Nat.Prime i - 1)

private theorem primesProd_empty {front back : Nat} (h : back < front) :
    primesProd front back = 1 := by grind [primesProd, Finset.Ico_eq_empty]

private theorem primesProdM1_empty {front back : Nat} (h : back < front) :
    primesProdM1 front back = 1 := by grind [primesProdM1, Finset.Ico_eq_empty]

private theorem primesProd_succ {front back : Nat} (h : front ≤ back + 1) :
    primesProd front (back + 1) = primesProd front back * nth Nat.Prime (back + 1) :=
  Finset.prod_Ico_succ_top h _

private theorem primesProdM1_succ {front back : Nat} (h : front ≤ back + 1) :
    primesProdM1 front (back + 1) =
      primesProdM1 front back * (nth Nat.Prime (back + 1) - 1) :=
  Finset.prod_Ico_succ_top h _

private theorem primesProd_self (i : Nat) : primesProd i i = nth Nat.Prime i := by
  simp [primesProd]

private theorem primesProdM1_self (i : Nat) : primesProdM1 i i = nth Nat.Prime i - 1 := by
  simp [primesProdM1]

/-- `primesProdM1 front B ≤ primesProd front B` since each factor `(p-1) ≤ p`. -/
private theorem primesProdM1_le_primesProd (front B : Nat) :
    primesProdM1 front B ≤ primesProd front B :=
  Finset.prod_le_prod (fun _ _ => zero_le _) (fun _ _ => by omega)

/-- Factoring `primesProd` at the front. -/
private theorem primesProd_succ_front {front B : Nat} (hB : front ≤ B) :
    primesProd front B = nth Nat.Prime front * primesProd (front + 1) B := by
  simp [primesProd, Finset.prod_eq_prod_Ico_succ_bot (by omega : front < B + 1)]

/-- Factoring `primesProdM1` at the front. -/
private theorem primesProdM1_succ_front {front B : Nat} (hB : front ≤ B) :
    primesProdM1 front B = (nth Nat.Prime front - 1) * primesProdM1 (front + 1) B := by
  simp [primesProdM1, Finset.prod_eq_prod_Ico_succ_bot (by omega : front < B + 1)]

/-- Wheel invariant update in the `case3` step (extending the window by one prime). -/
private lemma extend_case3_invariants {m target front back lhs rhs : Nat}
    (hlhs : lhs = m * primesProd front back) (hrhs : rhs = target * primesProdM1 front back)
    (hf : front ≤ back) (hb : back + 1 < primes.size) :
    lhs * primesRArray.get (back + 1) = m * primesProd front (back + 1) ∧
    rhs * (primesRArray.get (back + 1) - 1) = target * primesProdM1 front (back + 1) := by
  grind [primesRArray_get_eq_nth, primesProd_succ, primesProdM1_succ]

/-- Wheel invariant update in the `case6` step (seeding an empty window at `front`). -/
private lemma extend_case6_invariants {m target front back lhs rhs : Nat}
    (hlhs : lhs = m * primesProd front back) (hrhs : rhs = target * primesProdM1 front back)
    (hback : back < front) (hf : front < primes.size) :
    lhs * primesRArray.get front = m * primesProd front front ∧
    rhs * (primesRArray.get front - 1) = target * primesProdM1 front front := by
  grind [primesRArray_get_eq_nth, primesProd_self, primesProdM1_self,
    primesProd_empty, primesProdM1_empty]

/-! ### Sigma at a single prime -/

/-- Core arithmetic bound: for `p₀ ≤ p` both primes (or `p₀ ≥ 2`),
`σ₁(p ^ k) * (p₀ - 1) ≤ p ^ k * p₀`. Used to "consume" one prime in the window step. -/
private theorem sigma_pow_le_window_factor {p p₀ k : Nat} (hp : p.Prime) (hp₀ : 2 ≤ p₀)
    (hple : p₀ ≤ p) :
    σ₁ (p ^ k) * (p₀ - 1) ≤ p ^ k * p₀ := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpk_pos : 1 ≤ p ^ k := one_le_pow _ _ hp.pos
  have h_eq : σ₁ (p ^ k) * (p - 1) = p ^ (k + 1) - 1 := by
    rw [sigma_one_apply_prime_pow' hp,
      Nat.div_mul_cancel (Nat.sub_one_dvd_pow_sub_one p (k + 1))]
  refine Nat.le_of_mul_le_mul_right ?_ (by omega : 0 < p - 1)
  have hpk1 : 1 ≤ p ^ (k + 1) := one_le_pow _ _ hp.pos
  rw [mul_right_comm, h_eq]
  zify [hpk1, show 1 ≤ p₀ by omega, show 1 ≤ p by omega]
  nlinarith [hpk_pos, hple, hp₀, hp2, pow_succ p k]

/-- σ formula in `expChildren`'s loop: `(p ^ k * p - 1) / (p - 1) = σ₁ (p ^ k)` for prime `p`. -/
private theorem sigma_pow_expChildren_eq {p k : Nat} (hp : p.Prime) :
    (p ^ k * p - 1) / (p - 1) = σ₁ (p ^ k) := by
  rw [← pow_succ, ← sigma_one_apply_prime_pow' hp]

/-! ### The two main bounds: σ-window and radical -/

/-- Main sigma window bound: `σ₁(t) * Π'(front, B) ≤ t * Π(front, B)` for `t ∈ P front`
with at most `B - front + 1` distinct primes. -/
private theorem sigma_bound_window (t front B : Nat) (ht : 1 ≤ t) (hP : t ∈ P front)
    (hBsize : B + 1 ≤ primes.size) (hcard : t.primeFactors.card + front ≤ B + 1) :
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
    have hpf : t.primeFactors = insert p t'.primeFactors := by
      rw [← hpk_t, Nat.Coprime.primeFactors_mul (hcoprime.pow_left k),
        primeFactors_pow p (by omega : k ≠ 0), hp_prime.primeFactors, Finset.insert_eq]
    have hp_not_t' : p ∉ t'.primeFactors := fun h =>
      hp_prime.coprime_iff_not_dvd.mp hcoprime (mem_primeFactors.mp h).2.1
    have hcard' : t'.primeFactors.card + (front + 1) ≤ B + 1 := by
      rw [hpf, Finset.card_insert_of_notMem hp_not_t'] at hcard
      omega
    have ht'_P : t' ∈ P (front + 1) :=
      mem_P_succ_of_factors_gt ht'_pos fun q hq hqd =>
        hp_geprimes.trans_lt (lt_of_le_of_ne
          (hp_min q hq (hpk_t ▸ dvd_mul_of_dvd_right hqd _))
          fun hqp => hp_prime.coprime_iff_not_dvd.mp hcoprime (hqp ▸ hqd))
    have IH := ih t' ht'_lt _ _ ht'_pos ht'_P hBsize hcard'
    have hcons : σ₁ (p ^ k) * (nth Nat.Prime front - 1) ≤ p ^ k * nth Nat.Prime front :=
      sigma_pow_le_window_factor hp_prime (prime_nth_prime front).two_le hp_geprimes
    calc σ₁ t * primesProdM1 front B
        = σ₁ (p ^ k) * (nth Nat.Prime front - 1) *
            (σ₁ t' * primesProdM1 (front + 1) B) := by
          rw [← hpk_t, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
            (hcoprime.pow_left k), primesProdM1_succ_front (by omega)]
          ring
      _ ≤ p ^ k * nth Nat.Prime front * (t' * primesProd (front + 1) B) := by gcongr
      _ = t * primesProd front B := by
          rw [← hpk_t, primesProd_succ_front (by omega : front ≤ B)]
          ring

/-- Radical bound: `primesProd front (front + j - 1) ≤ t` for `t ∈ P front` with at least `j ≥ 1`
distinct primes, and `front + j ≤ primes.size`. Used in the wheel's `.tooLarge` case. -/
private theorem primesProd_le_t (t front : Nat) (ht : 1 ≤ t) (hP : t ∈ P front) (j : Nat)
    (hj : 1 ≤ j) (hjle : j ≤ t.primeFactors.card) (hsize : front + j ≤ primes.size) :
    primesProd front (front + j - 1) ≤ t := by
  induction t using Nat.strongRecOn generalizing front j with
  | _ t ih =>
    have ht1 : t ≠ 1 := by
      intro h; subst h; simp [primeFactors_one] at hjle; omega
    have ht2 : 2 ≤ t := by omega
    obtain ⟨p, k, t', hp_prime, _, hk_pos, hpk_t, _, ht'_pos, ht'_lt, hcoprime, hp_min⟩ :=
      exists_minFac_decomp ht2
    have hp_dvd : p ∣ t := hpk_t ▸ (dvd_pow_self p (by omega)).mul_right _
    have hp_geprimes : nth Nat.Prime front ≤ p := hP.2 p hp_prime hp_dvd
    have hpk_ge : nth Nat.Prime front ≤ p ^ k :=
      hp_geprimes.trans (le_self_pow (by omega) p)
    rcases lt_or_ge 1 j with hj2 | hj2
    · have hp_not_t' : p ∉ t'.primeFactors := fun h =>
        hp_prime.coprime_iff_not_dvd.mp hcoprime (mem_primeFactors.mp h).2.1
      have h_pf_eq : t.primeFactors = {p} ∪ t'.primeFactors := by
        rw [← hpk_t, Nat.Coprime.primeFactors_mul (hcoprime.pow_left k),
          primeFactors_pow p (by omega : k ≠ 0), hp_prime.primeFactors]
      have ht'_card_eq : t'.primeFactors.card = t.primeFactors.card - 1 := by
        rw [h_pf_eq, Finset.card_union_of_disjoint (Finset.disjoint_singleton_left.mpr hp_not_t'),
            Finset.card_singleton]; omega
      have ht'_in_P : t' ∈ P (front + 1) :=
        mem_P_succ_of_factors_gt ht'_pos fun q hq_prime hq_dvd =>
          hp_geprimes.trans_lt (lt_of_le_of_ne
            (hp_min q hq_prime (hpk_t ▸ dvd_mul_of_dvd_right hq_dvd _))
            fun hqp => hp_prime.coprime_iff_not_dvd.mp hcoprime (hqp ▸ hq_dvd))
      have IH := ih t' ht'_lt _ ht'_pos ht'_in_P (j - 1) (by omega) (by rw [ht'_card_eq]; omega)
        (by omega)
      rw [(by omega : (front + 1) + (j - 1) - 1 = front + j - 1)] at IH
      calc primesProd front (front + j - 1)
          = nth Nat.Prime front * primesProd (front + 1) (front + j - 1) :=
            primesProd_succ_front (by omega)
        _ ≤ p ^ k * t' := by gcongr
        _ = t := hpk_t
    · obtain rfl : j = 1 := by omega
      rw [Nat.add_sub_cancel, primesProd_self]
      calc nth Nat.Prime front ≤ p ^ k := hpk_ge
        _ ≤ p ^ k * t' := Nat.le_mul_of_pos_right _ ht'_pos
        _ = t := hpk_t

/-! ### Ruling out `.tooLarge` from a witness -/

/-- At a wheel `.tooLarge` state with `back + 1 < primes.size`, the witness `t` with
`t ≤ m`, `t ∈ P front`, `target ≤ σ₁ t` gives `False`. -/
private theorem extend_tooLarge_contradiction
    {m target front back lhs rhs : Nat} {t : Nat}
    (hlhs : lhs = m * primesProd front back)
    (hrhs : rhs = target * primesProdM1 front back)
    (hfront : front ≤ back + 1)
    (hback_lt : back + 1 < primes.size)
    (hsmall : lhs < rhs)
    (hbig : lhs * primesRArray.get (back + 1) > m * m)
    (ht2 : 2 ≤ t) (htP : t ∈ P front) (htm : t ≤ m) (htσ : target ≤ σ₁ t) : False := by
  rw [primesRArray_get_eq_nth _ hback_lt] at hbig
  have hpsucc : primesProd front (back + 1) = primesProd front back * nth Nat.Prime (back+1) :=
    primesProd_succ (by omega)
  rcases lt_or_ge t.primeFactors.card (back + 2 - front) with hcard | hcard
  · have h_chain : σ₁ t * primesProdM1 front back < target * primesProdM1 front back :=
      calc σ₁ t * primesProdM1 front back
          ≤ t * primesProd front back :=
            sigma_bound_window t front back (by omega) htP (by omega) (by omega)
        _ ≤ m * primesProd front back := Nat.mul_le_mul_right _ htm
        _ < target * primesProdM1 front back := by rw [← hlhs, ← hrhs]; exact hsmall
    exact absurd htσ (not_le.mpr (Nat.lt_of_mul_lt_mul_right h_chain))
  · have hrad := primesProd_le_t t front (by omega) htP (back + 2 - front) (by omega) hcard
      (by omega)
    have h_idx : front + (back + 2 - front) - 1 = back + 1 := by omega
    rw [h_idx] at hrad
    have hppsm : m < primesProd front (back + 1) :=
      Nat.lt_of_mul_lt_mul_left (a := m) (by rw [hpsucc, ← mul_assoc, ← hlhs]; exact hbig)
    omega

/-- At a wheel `.tooLarge` empty-window state with `front < primes.size`, the witness `t`
with `t ≤ m`, `t ∈ P front`, `t ≥ 2` gives `False`. The condition
`lhs * (front-th prime) > m*m` with `lhs = m` implies `(front-th prime) > m`, but `t` is
at least the `front`-th prime. -/
private theorem extend_tooLarge_empty_contradiction
    {m front back lhs : Nat} {t : Nat}
    (hlhs : lhs = m * primesProd front back) (hfront_lt : front < primes.size)
    (hempty : back + 1 = front)
    (hbig : lhs * primesRArray.get front > m * m)
    (ht2 : 2 ≤ t) (htP : t ∈ P front) (htm : t ≤ m) : False := by
  rw [primesRArray_get_eq_nth _ hfront_lt] at hbig
  rw [primesProd_empty (by omega : back < front), mul_one] at hlhs
  rw [hlhs] at hbig
  have hpf_gt : nth Nat.Prime front > m :=
    Nat.lt_of_mul_lt_mul_left (a := m) (by rwa [mul_comm m m] at hbig)
  have hp0_le : nth Nat.Prime front ≤ t.minFac :=
    htP.2 _ (minFac_prime (by omega)) (minFac_dvd t)
  have : t.minFac ≤ t := minFac_le (by omega)
  omega

/-- If `t` is a witness, `extend` cannot return `.tooLarge`. -/
private theorem extend_ne_tooLarge_of_witness (fuel m target front t : Nat) (ht2 : 2 ≤ t)
    (htP : t ∈ P front) (htm : t ≤ m) (htσ : target ≤ σ₁ t)
    (back lhs rhs : Nat) (hlhs : lhs = m * primesProd front back)
    (hrhs : rhs = target * primesProdM1 front back) (hfront : front ≤ back + 1) :
    extend fuel (m * m) front back lhs rhs ≠ .tooLarge := by
  fun_induction extend fuel (m * m) front back lhs rhs with
  | case1 | case2 | case5 | case8 => simp
  | case3 _ _ _ _ _ _ hb1 _ _ hbig =>
    intro _
    exact extend_tooLarge_contradiction hlhs hrhs hfront hb1 (by omega) hbig ht2 htP htm htσ
  | case4 _ _ _ _ hf _ hb1 _ _ _ ih =>
    obtain ⟨hlhs', hrhs'⟩ := extend_case3_invariants hlhs hrhs hf hb1
    exact ih hlhs' hrhs' (by omega)
  | case6 _ _ _ _ _ hf1 _ _ hbig =>
    intro _
    exact extend_tooLarge_empty_contradiction hlhs hf1 (by omega) hbig ht2 htP htm
  | case7 _ _ _ _ _ hf1 _ _ _ ih =>
    obtain ⟨hlhs_new, hrhs_new⟩ := extend_case6_invariants hlhs hrhs (by omega) hf1
    exact ih hlhs_new hrhs_new (by omega)

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
  | case2 _ _ _ _ hf _ =>
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨hlhs, hrhs, le_refl _, hf⟩
  | case3 | case6 => cases heq
  | case4 _ _ _ _ hf _ hb1 _ _ _ ih =>
    obtain ⟨hlhs_new, hrhs_new⟩ := extend_case3_invariants hlhs hrhs hf hb1
    obtain ⟨h1, h2, _, h4⟩ := ih hlhs_new hrhs_new (by omega) heq
    exact ⟨h1, h2, by omega, h4⟩
  | case7 _ _ _ _ _ hf1 _ _ _ ih =>
    obtain ⟨hlhs_new, hrhs_new⟩ := extend_case6_invariants hlhs hrhs (by omega) hf1
    obtain ⟨h1, h2, _, h4⟩ := ih hlhs_new hrhs_new (by omega) heq
    exact ⟨h1, h2, by omega, h4⟩

/-! ### Degenerate case: `lhs = 0` -/

/-- For `m2 = 0` and `lhs = 0`: `extend` returns either `.exhaustedTable` or
`.window b 0 rhs'` (so never `.tooLarge`, and any `.window` has `lhs' = 0`). -/
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
  fun_induction wheelChildren fuel 0 0 target num front back lhs rhs acc with
  | case1 | case2 | case5 => rfl
  | case3 front back lhs rhs _ _ hext =>
    rcases extend_zero_lhs_combined 50 front back lhs rhs hlhs with h' | ⟨_, _, h'⟩
    · simp [h'] at hext
    · rw [h'] at hext; cases hext
  | case4 front back lhs rhs _ _ _ _ _ hext _ _ ih =>
    rcases extend_zero_lhs_combined 50 front back lhs rhs hlhs with h' | ⟨_, _, h'⟩
    · simp [h'] at hext
    · rw [h'] at hext
      obtain ⟨rfl, rfl, rfl⟩ := hext
      exact ih (by simp)

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
    · simp only [if_pos hpm, List.not_mem_nil] at hc
    by_cases hge : (p ^ k₀ * p - 1) / (p - 1) ≥ target
    · simp only [if_neg hpm, if_pos hge, List.mem_singleton] at hc
      exact ⟨k₀, le_refl _, by omega, by rw [hc, hspk_eq]⟩
    simp only [if_neg hpm, if_neg hge, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨k₀, le_refl _, by omega, by rw [hspk_eq]⟩
    · rw [← pow_succ] at hc
      obtain ⟨k, hk, hpkm, hceq⟩ := ih (by omega) hc
      exact ⟨k, by omega, hpkm, hceq⟩

/-- Witness `1` for the stop arm of `expChildren_witness_walk`: when `σ(p ^ j₀) ≥ target`,
the child `(ceilDiv target σ(p ^ j₀), num*p ^ j₀, next)` has `1` as a witness. -/
private lemma one_witnesses_stop {B num target next p k j₀ t'' : Nat}
    (hp : p.Prime) (hjk : j₀ ≤ k) (ht''_pos : 1 ≤ t'')
    (hnumt : num * p ^ k * t'' < B) (hσ_target : σ₁ (p ^ j₀) ≥ target) :
    W B (ceilDiv target (σ₁ (p ^ j₀))) (num * p ^ j₀) next ≠ ∅ := by
  refine Set.nonempty_iff_ne_empty.mp ⟨1, one_mem_P _, ?_, ?_⟩
  · have : num * p ^ j₀ ≤ num * p ^ k :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp.one_lt.le hjk)
    have := Nat.le_mul_of_pos_right (num * p ^ k) ht''_pos; omega
  · have hσpj_pos : 0 < σ₁ (p ^ j₀) :=
      ArithmeticFunction.sigma_pos _ _ (pow_ne_zero _ hp.pos.ne')
    simp [ceilDiv, div_le_iff_le_mul_add_pred hσpj_pos]; omega

/-- Walk `expChildren` from `pk₀ = p ^ j₀` looking for a child with a witness, given a parent
witness `t = p ^ k * t''` (factored at `p` with `t''` coprime to `p`). The proof iterates by
strong induction on `k - j₀`: at each step either σ(p^{j₀}) ≥ target (stop with witness `1`)
or σ < target (emit and recurse), bottoming out at `j₀ = k` with witness `t''`. -/
private theorem expChildren_witness_walk {B num target m p : Nat} (hp : p.Prime) (next : Nat)
    (n k j₀ : Nat) (hn : k - j₀ = n) (hj₀ : 1 ≤ j₀) (hj₀_k : j₀ ≤ k) (hpk_le_m : p ^ k ≤ m)
    {t'' : Nat} (ht''_pos : 1 ≤ t'') (ht''_P : t'' ∈ P next) (hnumt : num * p ^ k * t'' < B)
    (htσ : target ≤ σ₁ (p ^ k) * σ₁ t'') {fuel : Nat} (hfuel : n + 1 ≤ fuel) :
    ∃ c ∈ expChildren fuel target num next m p (p ^ j₀), W B c.1 c.2.1 c.2.2 ≠ ∅ := by
  induction n generalizing j₀ fuel with
  | zero =>
    have hjk : j₀ = k := by omega
    subst hjk
    have h_sig_eq : (p ^ j₀ * p - 1) / (p - 1) = σ₁ (p ^ j₀) := sigma_pow_expChildren_eq hp
    by_cases hσ_target : σ₁ (p ^ j₀) ≥ target
    · have h_exp : expChildren fuel target num next m p (p ^ j₀) =
          [(ceilDiv target (σ₁ (p ^ j₀)), num * p ^ j₀, next)] := by
        rw [← h_sig_eq]
        exact expChildren_stop (by omega) hpk_le_m (by rw [h_sig_eq]; exact hσ_target)
      rw [h_exp]
      exact ⟨_, List.mem_singleton.mpr rfl, one_witnesses_stop hp le_rfl ht''_pos hnumt hσ_target⟩
    · push Not at hσ_target
      have h_exp : expChildren fuel target num next m p (p ^ j₀) =
          (ceilDiv target (σ₁ (p ^ j₀)), num * p ^ j₀, next) ::
          expChildren (fuel - 1) target num next m p (p ^ j₀ * p) := by
        rw [← h_sig_eq]
        exact expChildren_step (by omega) hpk_le_m (by rw [h_sig_eq]; exact hσ_target)
      rw [h_exp]
      refine ⟨_, List.mem_cons_self, Set.nonempty_iff_ne_empty.mp ⟨t'', ht''_P, hnumt, ?_⟩⟩
      have hσpk_pos : 0 < σ₁ (p ^ j₀) := ArithmeticFunction.sigma_pos _ _ (pow_ne_zero _ hp.pos.ne')
      simp [ceilDiv, div_le_iff_le_mul_add_pred hσpk_pos]
      omega
  | succ n ih =>
    have hpj_le_m : p ^ j₀ ≤ m := (Nat.pow_le_pow_right hp.one_lt.le hj₀_k).trans hpk_le_m
    have h_sig_eq : (p ^ j₀ * p - 1) / (p - 1) = σ₁ (p ^ j₀) := sigma_pow_expChildren_eq hp
    by_cases hσ_target : σ₁ (p ^ j₀) ≥ target
    · have h_exp : expChildren fuel target num next m p (p ^ j₀) =
          [(ceilDiv target (σ₁ (p ^ j₀)), num * p ^ j₀, next)] := by
        rw [← h_sig_eq]
        exact expChildren_stop (by omega) hpj_le_m (by rw [h_sig_eq]; exact hσ_target)
      rw [h_exp]
      exact ⟨_, List.mem_singleton.mpr rfl, one_witnesses_stop hp hj₀_k ht''_pos hnumt hσ_target⟩
    · push Not at hσ_target
      have h_exp : expChildren fuel target num next m p (p ^ j₀) =
          (ceilDiv target (σ₁ (p ^ j₀)), num * p ^ j₀, next) ::
          expChildren (fuel - 1) target num next m p (p ^ j₀ * p) := by
        rw [← h_sig_eq]
        exact expChildren_step (by omega) hpj_le_m (by rw [h_sig_eq]; exact hσ_target)
      rw [h_exp, ← pow_succ]
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
  | case3 => obtain rfl := Option.some.inj h; exact Or.inl hc
  | case4 front _ _ _ _ _ _ _ _ _ hp _ =>
    rename_i hrec
    have hq : primesRArray.get front = nth Nat.Prime front :=
      primesRArray_get_eq_nth front hp
    rcases hrec h hc with hcacc | ⟨i, k, hi, hk, hpkm, hceq⟩
    · rcases List.mem_append.mp hcacc with hcexp | hcorig
      · have hcexp' : c ∈ expChildren (m + 1) target num (front + 1) m
            (nth Nat.Prime front) (nth Nat.Prime front) := hq ▸ hcexp
        obtain ⟨k, hk, hpkm, hceq⟩ :=
          mem_expChildren (prime_nth_prime front) le_rfl
            (by rw [pow_one]; exact hcexp')
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
  | case3 => obtain rfl := Option.some.inj h; exact fun _ hx => hx
  | case4 =>
    rename_i hrec
    exact fun x hx => hrec _ h (List.mem_append_right _ hx)

/-- At any state of `wheelChildren`
with the wheel invariants and a viable witness `t`, some child in the output `L` has a non-empty
witness set. -/
private theorem wheelChildren_witness {B num m target : Nat} (hmdef : m = B / num)
    (hnum_pos : 1 ≤ num) (fuel front back lhs rhs : Nat) (acc L : List (Nat × Nat × Nat))
    (hfuel : primes.size + 1 - front ≤ fuel)
    (hlhs : lhs = m * primesProd front back) (hrhs : rhs = target * primesProdM1 front back)
    (hfront_le : front ≤ back + 1)
    (hwc : wheelChildren fuel (m * m) m target num front back lhs rhs acc = some L)
    (t : Nat) (ht2 : 2 ≤ t) (htP : t ∈ P front) (hnumt : num * t < B) (htσ : target ≤ σ₁ t) :
    ∃ c ∈ L, W B c.1 c.2.1 c.2.2 ≠ ∅ := by
  fun_induction wheelChildren fuel (m * m) m target num front back lhs rhs acc generalizing L with
  | case1 | case2 | case5 => cases hwc
  | case3 front _ _ _ _ _ hext =>
    exfalso
    have htm : t ≤ m := hmdef ▸ (le_div_iff_mul_le hnum_pos).mpr (by linarith)
    exact extend_ne_tooLarge_of_witness 50 m target front t ht2 htP htm htσ
      _ _ _ hlhs hrhs hfront_le hext
  | case4 front back lhs rhs acc _ b lhs' rhs' hext hp _ =>
    rename_i hrec
    have hq : primesRArray.get front = nth Nat.Prime front :=
      primesRArray_get_eq_nth front hp
    have hp_prime : (nth Nat.Prime front).Prime := prime_nth_prime front
    have htm : t ≤ m := hmdef ▸ (le_div_iff_mul_le hnum_pos).mpr (by linarith)
    obtain ⟨hlhs', hrhs', _, hfront_b⟩ :=
      extend_window_invariant 50 m target front back lhs rhs b lhs' rhs'
        hlhs hrhs hfront_le hext
    have hlhs_new : lhs' / primesRArray.get front = m * primesProd (front + 1) b := by
      rw [hq, hlhs', primesProd_succ_front hfront_b,
        mul_left_comm, Nat.mul_div_cancel_left _ hp_prime.pos]
    have hrhs_new : rhs' / (primesRArray.get front - 1) =
        target * primesProdM1 (front + 1) b := by
      rw [hq, hrhs', primesProdM1_succ_front hfront_b, mul_left_comm,
        Nat.mul_div_cancel_left _ (Nat.sub_pos_of_lt hp_prime.one_lt)]
    by_cases hdvd : nth Nat.Prime front ∣ t
    · obtain ⟨k, t'', hk_pos, hpk_t, _, ht''_pos, _, hcoprime⟩ :=
        exists_factor_decomp hp_prime hdvd (by omega)
      have hpk_le_m : (nth Nat.Prime front) ^ k ≤ m :=
        le_trans (le_of_dvd (by omega) ⟨t'', hpk_t.symm⟩) htm
      have htσ' : target ≤ σ₁ ((nth Nat.Prime front) ^ k) * σ₁ t'' := by
        rwa [← ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
          (hcoprime.pow_left k), hpk_t]
      have ht''_P : t'' ∈ P (front + 1) :=
        mem_P_succ_of_factors_gt ht''_pos fun q' hq'_prime hq'_dvd => by
          refine lt_of_le_of_ne
            (htP.2 q' hq'_prime (hpk_t ▸ dvd_mul_of_dvd_right hq'_dvd _)) ?_
          rintro rfl
          exact hp_prime.coprime_iff_not_dvd.mp hcoprime hq'_dvd
      obtain ⟨c, hc, hwit⟩ := expChildren_witness_walk hp_prime (front + 1) (k - 1) k 1
        (by omega) (by omega) hk_pos hpk_le_m ht''_pos ht''_P
        (by rw [mul_assoc, hpk_t]; exact hnumt) htσ' (fuel := m + 1)
        (by have : k ≤ m := (Nat.lt_pow_self hp_prime.one_lt).le.trans hpk_le_m; omega)
      have hcget : c ∈ expChildren (m + 1) target num (front + 1) m
          (primesRArray.get front) (primesRArray.get front) := by
        rw [hq]; rwa [pow_one] at hc
      exact ⟨c, wheelChildren_acc_subset _ _ _ _ _ _ _ _ _ _ _ hwc
        (List.mem_append_left _ hcget), hwit⟩
    · have ht_in_P_next : t ∈ P (front + 1) :=
        mem_P_succ_of_factors_gt (by omega) fun q' hq'_prime hq'_dvd =>
          lt_of_le_of_ne (htP.2 q' hq'_prime hq'_dvd)
            (Ne.symm fun h => hdvd (h ▸ hq'_dvd))
      exact hrec L (by omega) hlhs_new hrhs_new (by omega) hwc ht_in_P_next

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
  have hp_not_dvd : ¬ p ∣ t' := fun hpdvd => by
    have hple : nth Nat.Prime (i + 1) ≤ p := ht'P p hpPrime hpdvd
    have hlt : nth Nat.Prime i < nth Nat.Prime (i + 1) :=
      nth_strictMono infinite_setOf_prime (lt_succ_self i)
    omega
  have hcop : Nat.Coprime (p ^ k) t' :=
    (hpPrime.coprime_iff_not_dvd.mpr hp_not_dvd).pow_left _
  refine ⟨⟨⟨by omega, fun q hqPrime hqDvd => ?_⟩, by rwa [← mul_assoc], ?_⟩, by omega⟩
  · rcases hqPrime.dvd_mul.mp hqDvd with h1 | h2
    · obtain rfl : q = p :=
        (prime_dvd_prime_iff_eq hqPrime hpPrime).mp (hqPrime.dvd_of_dvd_pow h1)
      exact (nth_strictMono infinite_setOf_prime).monotone hmi
    · exact ((nth_strictMono infinite_setOf_prime).monotone (by omega)).trans
        (ht'P q hqPrime h2)
  · rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop]
    have hσpk_pos : 0 < σ₁ (p ^ k) := ArithmeticFunction.sigma_pos _ _ (by positivity)
    refine le_trans ?_ (Nat.mul_le_mul_left _ ht'σ)
    simp [ceilDiv]
    have := div_add_mod (target + σ₁ (p ^ k) - 1) (σ₁ (p ^ k))
    have := mod_lt (target + σ₁ (p ^ k) - 1) hσpk_pos
    omega

/-- A non-trivial witness of the parent gives a witness for some child in `cs`.
Two cases: if `t`'s smallest prime is in the table (`= nth Nat.Prime i`), decompose
and find the corresponding child via the wheel-correctness of `extend`. If
`t`'s smallest prime exceeds the table, the wheel's geometric `.tooLarge`
argument rules `t` out — any prime in `t` could be replaced by a smaller
in-table prime to give a strictly better witness, so off-table witnesses can
never arise where the in-table search succeeded. -/
private theorem witness_to_child {B target num minIdx : Nat} {cs : List (Nat × Nat × Nat)}
    (h : children B target num minIdx = some cs) {t : Nat}
    (ht : t ∈ W B target num minIdx) (h1 : t ≠ 1) :
    ∃ c ∈ cs, W B c.1 c.2.1 c.2.2 ≠ ∅ := by
  rcases Nat.eq_zero_or_pos num with rfl | hnum_pos
  · rw [children] at h
    split at h
    · simp only [Nat.div_zero, Nat.mul_zero] at h
      rw [wheelChildren_zero_no_some _ target 0 _ _ 0 _ [] rfl] at h
      cases h
    · cases h
  · rw [children] at h
    split at h
    · rename_i hminIdx_lt
      dsimp only at h
      obtain ⟨⟨ht_pos, htP⟩, htlt, htσ⟩ := ht
      have hpeq : primesRArray.get minIdx = nth Nat.Prime minIdx :=
        primesRArray_get_eq_nth minIdx hminIdx_lt
      rw [hpeq] at h
      have hL : nth Nat.Prime minIdx * (B / num) =
          B / num * primesProd minIdx minIdx := by rw [primesProd_self]; ring
      have hR : target * (nth Nat.Prime minIdx - 1) =
          target * primesProdM1 minIdx minIdx := by rw [primesProdM1_self]
      rw [hL, hR] at h
      have hps : (primes.size : Nat) = 49 := rfl
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
  induction fuel generalizing stack with
  | zero => simp [step] at h
  | succ fuel ih =>
    rcases stack with _ | ⟨⟨target, num, minIdx⟩, rest⟩
    · simp
    rw [step] at h
    by_cases ht : target ≤ 1
    · simp only [ht, if_true] at h
      by_cases hn : num < B
      · simp [hn] at h
      simp only [hn, if_false] at h
      intro node hnode
      simp only [List.mem_cons] at hnode
      rcases hnode with rfl | hnode
      · rw [Set.eq_empty_iff_forall_notMem]
        rintro t ⟨⟨ht1, _⟩, htlt, _⟩
        have := Nat.le_mul_of_pos_right num ht1
        simp at htlt; omega
      · exact ih h _ hnode
    · simp only [ht, if_false] at h
      match hch : children B target num minIdx, h with
      | some cs, h =>
        have ih_all := ih h
        intro node hnode
        simp only [List.mem_cons] at hnode
        rcases hnode with rfl | hnode
        · rw [Set.eq_empty_iff_forall_notMem]
          rintro t htW
          by_cases h1 : t = 1
          · grind [ArithmeticFunction.sigma_one]
          obtain ⟨c, hc, hwc⟩ := (children_spec hch).mp ⟨t, htW, h1⟩
          grind
        · exact ih_all _ (List.mem_append.mpr (Or.inr hnode))

/-- `step = some false` ⟹ some node on the stack has a nonempty witness set. -/
theorem step_false {B fuel : Nat} {stack : List (Nat × Nat × Nat)}
    (h : step B fuel stack = some false) :
    ∃ node ∈ stack, W B node.1 node.2.1 node.2.2 ≠ ∅ := sorry

/-- Top-level correctness: a `some true` answer of `highlyAbundantLcm?` on
`(lcmRange n, σ₁ (lcmRange n))` certifies that `lcm (1..n)` is highly abundant.

With `P j` defined as "smallest prime factor `≥ nth Nat.Prime j`",
`step_true` at the root directly gives `W (lcmRange n) (σ₁ (lcmRange n)) 1 0 = ∅`,
which unfolds to "no `m ≥ 2 < B` has `σ₁ m ≥ σ₁ B`"; combined with `σ₁ 1 = 1 < σ₁ B`
this is `IsHighlyAbundant`. -/
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
  have hmW : m ∈ W (lcmRange n) (σ₁ (lcmRange n)) 1 0 := by
    grind [Nat.Prime.two_le]
  rwa [hW] at hmW

end Sage
