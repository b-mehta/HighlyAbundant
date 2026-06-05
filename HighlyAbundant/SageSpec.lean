/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import HighlyAbundant.Basic
import HighlyAbundant.Sage
import Mathlib.Data.Nat.Log

/-!
# Correctness of the `lcm (1..n)` HA-decider

Spec of the search in `HighlyAbundant.Sage`. Notation:

* `P j := { t ≥ 1 | smallest prime factor of t ≥ primes[j] }` (off-table primes
  are allowed: any `q > primes[primes.size-1]` trivially satisfies the bound);
* `W B target num minIdx := { t ∈ P minIdx | num * t < B ∧ target ≤ σ₁ t }`
  is the witness set of a node `(target, num, minIdx)` for bound `B`.

## File layout

1. Specification: `P`, `W`, `lcmData`.
2. The `primes` table: monotonicity, injectivity, the "consecutive primes" property.
3. Membership in `P`: `P_le_factor`, `mem_P_succ_of_factors_gt`, `one_mem_P`.
4. Multiplicative decomposition: `exists_factor_decomp`, `exists_minFac_decomp`.
5. Fuel-free wheel: `extend ↔ extendWF` and `wheelChildren ↔ wheelChildrenWF`.
6. Products over prime windows: `primesProd`, `primesProdM1`, and the wheel
   invariant updates in cases 3 and 6 of `extendWF.induct`.
7. Sigma at a single prime: `sigma_pow_le_window_factor`, `sigma_pow_expChildren_eq`.
8. The two main bounds: `sigma_bound_window` and `primesProd_le_t`.
9. Ruling out `.tooLarge` from a witness: `extendWF_ne_tooLarge_of_witness`.
10. Window invariants: `extendWF_window_invariant`.
11. Degenerate case `lhs = 0`: `wheelChildrenWF_zero_no_some`.
12. `expChildren` analysis: `mem_expChildren`, `expChildren_witness_walk`.
13. `wheelChildrenWF` and `children`: `mem_wheelChildrenWF`, `wheelChildrenWF_witness`,
    `mem_children`, `child_witness_to_parent`, `witness_to_child`, `children_spec`.
14. Step correctness and top-level result: `step_true`, `step_false`,
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

namespace Sage

/-! ### Specification: `P`, `W`, `lcmData` -/

/-- `P j`: naturals `≥ 1` whose smallest prime factor is `≥ primes[j]`. When
`j ≥ primes.size`, no prime satisfies the bound, so `P j = {1}` (only the empty
product). Off-table primes are allowed: a prime factor `q > primes[primes.size-1]`
trivially satisfies `primes[j] ≤ q` for any `j < primes.size`. -/
def P (j : Nat) : Set Nat :=
  { t | 1 ≤ t ∧ ∀ q : Nat, q.Prime → q ∣ t → ∃ p, primes[j]? = some p ∧ p ≤ q }

/-- The witness set of a node `(target, num, minIdx)` for bound `B`. -/
def W (B target num minIdx : Nat) : Set Nat :=
  { t | t ∈ P minIdx ∧ num * t < B ∧ target ≤ σ₁ t }

/-- Fast computation of `(lcmRange n, σ₁ (lcmRange n))` as
`(∏ p^{⌊log_p n⌋}, ∏ σ(p^{⌊log_p n⌋}))` over the primes `p ≤ n` in the table.
Intended for `#eval`-style use to supply `(B, sL)` to `highlyAbundantLcm?`;
the proof in `highlyAbundantLcm_correct` is stated in terms of `lcmRange` so
this equivalence is not needed formally. -/
def lcmData (n : Nat) : Nat × Nat :=
  (primes.toList.takeWhile (· ≤ n)).foldl
    (fun (acc : Nat × Nat) p =>
      let e := Nat.log p n
      (acc.1 * p ^ e, acc.2 * ((p ^ (e + 1) - 1) / (p - 1)))) (1, 1)

/-! ### The `primes` table -/

/-- `primes` is strictly increasing (verified by `decide` on the explicit table). -/
private theorem primes_pairwise : primes.toList.Pairwise (· < ·) := by decide

/-- Every entry of `primes` is a prime. -/
private theorem primes_prime_of_mem : ∀ p ∈ primes, p.Prime := by
  decide +kernel

/-- If `primes[i]? = some p`, then `p` is prime. -/
private theorem primes_prime {i p : Nat} (h : primes[i]? = some p) : p.Prime :=
  primes_prime_of_mem _ (Array.mem_of_getElem? h)

/-- Every prime ≤ 227 is in the `primes` table. -/
private theorem prime_in_primes (q : Nat) (hq : q ≤ 227) (hp : q.Prime) : q ∈ primes.toList := by
  decide +kernel +revert

/-- `primes` is strictly monotone on indices in bounds. -/
private theorem primes_lt_of_lt {i j : Nat} (hij : i < j) (hj : j < primes.size) :
    primes[i]'(by omega) < primes[j] := by
  have := List.pairwise_iff_getElem.mp primes_pairwise i j
    (by simpa using Nat.lt_of_lt_of_le hij hj.le) (by simpa) hij
  rwa [Array.getElem_toList, Array.getElem_toList] at this

/-- `primes` is weakly monotone on indices in bounds. -/
private theorem primes_le_of_le {i j : Nat} (hij : i ≤ j) (hj : j < primes.size) :
    primes[i]'(by omega) ≤ primes[j] := by
  obtain rfl | hij := eq_or_lt_of_le hij
  exacts [le_rfl, (primes_lt_of_lt hij hj).le]

/-- The `primes` indexing function is injective on its domain. -/
private theorem primes_eq_iff {i j : Nat} {p : Nat}
    (hi : primes[i]? = some p) (hj : primes[j]? = some p) : i = j := by
  obtain ⟨hilt, rfl⟩ := Array.getElem?_eq_some_iff.mp hi
  obtain ⟨hjlt, heq⟩ := Array.getElem?_eq_some_iff.mp hj
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact absurd heq (primes_lt_of_lt hij hjlt).ne'
  · rfl
  · exact absurd heq (primes_lt_of_lt hij hilt).ne

/-- A prime exceeding the last table entry is at least 229 (the next prime after 227). -/
private theorem prime_ge_229_of_gt {q : Nat} (hp : q.Prime) (hq : 227 < q) : 229 ≤ q := by
  by_contra! hlt
  obtain rfl : q = 228 := by omega
  exact absurd hp (by rw [Nat.prime_def]; push Not; exact fun _ =>
    ⟨2, by decide, by decide, by decide⟩)

/-- The largest entry of `primes` is 227. -/
private theorem primes_last : primes[primes.size - 1]'(by decide) = 227 := by decide

/-- "Consecutive primes" property: any prime `q > primes[i]` with `i + 1 < primes.size`,
`primes[i+1] ≤ q`. -/
private theorem primes_consecutive {i : Nat} (hi : i < primes.size) {q : Nat}
    (hp : q.Prime) (hq : primes[i] < q) (hi1 : i + 1 < primes.size) :
    primes[i + 1] ≤ q := by
  by_cases h : q ≤ 227
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (prime_in_primes q h hp)
    simp only [Array.length_toList] at hj
    rw [Array.getElem_toList] at hq ⊢
    have hji : i + 1 ≤ j := by
      by_contra! hji
      exact absurd (primes_le_of_le (Nat.le_of_lt_succ hji) hi) (by omega)
    exact primes_le_of_le hji hj
  · push Not at h
    have hi1_le := primes_le_of_le (by omega : i + 1 ≤ primes.size - 1) (by decide)
    rw [primes_last] at hi1_le
    have := prime_ge_229_of_gt hp h
    omega

/-! ### Membership in `P` -/

/-- If `t ∈ P front` with `front < primes.size`, then `primes[front]` bounds every prime
factor of `t` from below. -/
private lemma P_le_factor {t front q : Nat} (hP : t ∈ P front) (hq : q.Prime) (hqd : q ∣ t)
    (hfront_lt : front < primes.size) : primes[front] ≤ q := by
  obtain ⟨_, hp0_eq, hp0_le⟩ := hP.2 q hq hqd
  obtain ⟨_, rfl⟩ := Array.getElem?_eq_some_iff.mp hp0_eq; exact hp0_le

/-- If `x ≥ 1` and every prime factor of `x` exceeds `primes[front]`, then `x ∈ P (front + 1)`. -/
private lemma mem_P_succ_of_factors_gt {x front : Nat} (hx : 1 ≤ x)
    (hfront : front < primes.size) (hf1 : front + 1 < primes.size)
    (h : ∀ q, q.Prime → q ∣ x → primes[front] < q) : x ∈ P (front + 1) :=
  ⟨hx, fun q hq hqd => ⟨primes[front + 1], Array.getElem?_eq_getElem hf1,
    primes_consecutive hfront hq (h q hq hqd) hf1⟩⟩

/-- `1 ∈ P j` for any `j` since `1` has no prime factors. -/
private theorem one_mem_P (j : Nat) : 1 ∈ P j :=
  ⟨le_rfl, fun _ hq hd => absurd (Nat.dvd_one.mp hd) hq.one_lt.ne'⟩

/-! ### Multiplicative decomposition -/

/-- Decompose `t` at a prime factor `p`: `t = p^k * t'` with `k ≥ 1`, `Coprime p t'`,
`2 ≤ p^k`, `1 ≤ t' < t`. -/
private lemma exists_factor_decomp {t p : Nat} (hp : p.Prime) (hpt : p ∣ t) (htne : t ≠ 0) :
    ∃ k t' : Nat, 1 ≤ k ∧ p ^ k * t' = t ∧ 2 ≤ p ^ k ∧ 1 ≤ t' ∧ t' < t ∧
      Nat.Coprime p t' := by
  set k := t.factorization p
  set t' := t / p ^ k
  have hk_pos : 1 ≤ k := by
    rw [← hp.pow_dvd_iff_le_factorization htne]
    simpa using hpt
  have hpk_t : p ^ k * t' = t := Nat.mul_div_cancel_left' (Nat.ordProj_dvd t p)
  have hpk_ge2 : 2 ≤ p ^ k :=
    hp.two_le.trans (by simpa using Nat.pow_le_pow_right hp.one_lt.le hk_pos)
  have ht'_pos : 1 ≤ t' := Nat.pos_of_mul_pos_left (by rw [hpk_t]; omega)
  refine ⟨k, t', hk_pos, hpk_t, hpk_ge2, ht'_pos, ?_, Nat.coprime_ordCompl hp htne⟩
  nlinarith [hpk_t, hpk_ge2, ht'_pos]

/-- For `t ≥ 2`, decompose at the smallest prime factor. -/
private lemma exists_minFac_decomp {t : Nat} (ht : 2 ≤ t) :
    ∃ p k t' : Nat, p.Prime ∧ p ∣ t ∧ 1 ≤ k ∧ p ^ k * t' = t ∧
      2 ≤ p ^ k ∧ 1 ≤ t' ∧ t' < t ∧ Nat.Coprime p t' ∧
      (∀ q, q.Prime → q ∣ t → p ≤ q) := by
  have ht1 : t ≠ 1 := by omega
  have htne : t ≠ 0 := by omega
  obtain ⟨k, t', hk, hpkt, hpk2, ht'p, ht'l, hcop⟩ :=
    exists_factor_decomp (Nat.minFac_prime ht1) (Nat.minFac_dvd t) htne
  exact ⟨_, k, t', Nat.minFac_prime ht1, Nat.minFac_dvd t, hk, hpkt, hpk2, ht'p, ht'l,
    hcop, fun q hq hqd => Nat.minFac_le_of_dvd hq.two_le hqd⟩

/-! ### Fuel-free wheel: `extend ↔ extendWF` and `wheelChildren ↔ wheelChildrenWF` -/

/-- The fuel-based and well-founded forms of `extend` agree once fuel is large
enough. The hypothesis `primes.size - back < fuel` is equivalent to
`fuel ≥ max 1 (primes.size + 1 - back)` (the truncated `primes.size + 1 - back`
underflows for `back > primes.size`, so we need the extra `1 ≤ fuel`). -/
theorem extend_eq_extendWF {fuel m2 front back lhs rhs : Nat}
    (h : primes.size - back < fuel) :
    extend fuel m2 front back lhs rhs = extendWF m2 front back lhs rhs := by
  induction fuel generalizing back lhs rhs with
  | zero => omega
  | succ fuel ih =>
    rw [extend, extendWF]
    split_ifs with h1 h2 h3 h4
    · rfl
    · rw [Array.getElem?_eq_getElem h3]
      dsimp only
      split_ifs
      · rfl
      · exact ih (by omega)
    · rw [Array.getElem?_eq_none (by omega : primes.size ≤ back + 1)]
    · rw [Array.getElem?_eq_getElem h4]
      dsimp only
      split_ifs
      · rfl
      · exact ih (by omega)
    · rw [Array.getElem?_eq_none (by omega : primes.size ≤ front)]

/-- The fuel-based and well-founded forms of `wheelChildren` agree once fuel is large
enough. `wheelChildrenWF` returns `some []` where `wheelChildren` returns `some acc`. -/
theorem wheelChildren_eq_wheelChildrenWF
    {fuel m2 m target num front back lhs rhs : Nat}
    (h : primes.size + 1 - front ≤ fuel) (acc : List (Nat × Nat × Nat)) :
    wheelChildren fuel m2 m target num front back lhs rhs acc =
      (wheelChildrenWF m2 m target num front back lhs rhs).map (· ++ acc) := by
  induction fuel generalizing front back lhs rhs acc with
  | zero =>
    rw [wheelChildren, wheelChildrenWF]
    have : front ≥ primes.size := by omega
    simp [this]
  | succ fuel ih =>
    rw [wheelChildren, wheelChildrenWF, extend_eq_extendWF (by omega)]
    by_cases hfront : front ≥ primes.size
    · simp only [hfront, dif_pos, Option.map_none]
      rw [extendWF, Array.getElem?_eq_none hfront]
      split_ifs <;> simp <;> omega
    · simp only [hfront, dif_neg, not_false_eq_true]
      rw [Array.getElem?_eq_getElem (by omega : front < primes.size)]
      generalize extendWF m2 front back lhs rhs = w
      cases w with
      | exhaustedTable => rfl
      | tooLarge => rfl
      | window b lhs' rhs' =>
        dsimp only
        rw [ih (by omega)]
        cases wheelChildrenWF m2 m target num (front + 1) b
            (lhs' / primes[front]) (rhs' / (primes[front] - 1)) with
        | none => rfl
        | some rest => simp [List.append_assoc]

/-- A successful `wheelChildrenWF` recursion at `front + 1` requires `front + 1 < primes.size`. -/
private lemma wheelChildrenWF_some_imp_succ_lt {m2 m target num front b lhs' rhs' : Nat}
    {rest : List (Nat × Nat × Nat)}
    (hrec : wheelChildrenWF m2 m target num (front + 1) b lhs' rhs' = some rest) :
    front + 1 < primes.size := by
  by_contra h; push Not at h
  rw [wheelChildrenWF] at hrec; simp [h] at hrec

/-! ### Products over prime windows -/

/-- `primesProd front back = ∏_{i ∈ [front, back]} primes[i]` (out-of-range indices contribute 1). -/
private def primesProd (front back : Nat) : Nat :=
  ∏ i ∈ Finset.Ico front (back + 1), (primes[i]?).getD 1

/-- `primesProdM1 front back = ∏_{i ∈ [front, back]} (primes[i] - 1)` (out-of-range: contributes 1). -/
private def primesProdM1 (front back : Nat) : Nat :=
  ∏ i ∈ Finset.Ico front (back + 1), ((primes[i]?).getD 2 - 1)

private theorem primesProd_empty {front back : Nat} (h : back < front) :
    primesProd front back = 1 := by
  simp [primesProd, Finset.Ico_eq_empty (by omega : ¬ front < back + 1)]

private theorem primesProdM1_empty {front back : Nat} (h : back < front) :
    primesProdM1 front back = 1 := by
  simp [primesProdM1, Finset.Ico_eq_empty (by omega : ¬ front < back + 1)]

private theorem primesProd_succ {front back : Nat} (h : front ≤ back + 1) :
    primesProd front (back + 1) = primesProd front back * (primes[back + 1]?).getD 1 :=
  Finset.prod_Ico_succ_top h _

private theorem primesProdM1_succ {front back : Nat} (h : front ≤ back + 1) :
    primesProdM1 front (back + 1) =
      primesProdM1 front back * ((primes[back + 1]?).getD 2 - 1) :=
  Finset.prod_Ico_succ_top h _

private theorem primesProd_succ_lt {front back : Nat} (h : front ≤ back + 1)
    (hb : back + 1 < primes.size) :
    primesProd front (back + 1) = primesProd front back * primes[back + 1] := by
  rw [primesProd_succ h, Array.getElem?_eq_getElem hb, Option.getD_some]

private theorem primesProdM1_succ_lt {front back : Nat} (h : front ≤ back + 1)
    (hb : back + 1 < primes.size) :
    primesProdM1 front (back + 1) = primesProdM1 front back * (primes[back + 1] - 1) := by
  rw [primesProdM1_succ h, Array.getElem?_eq_getElem hb, Option.getD_some]

private theorem primesProd_self {i : Nat} (hi : i < primes.size) :
    primesProd i i = primes[i] := by
  simp [primesProd, Array.getElem?_eq_getElem hi]

private theorem primesProdM1_self {i : Nat} (hi : i < primes.size) :
    primesProdM1 i i = primes[i] - 1 := by
  simp [primesProdM1, Array.getElem?_eq_getElem hi]

/-- `primesProdM1 front B ≤ primesProd front B` since each factor `(p-1) ≤ p`. -/
private theorem primesProdM1_le_primesProd (front B : Nat) :
    primesProdM1 front B ≤ primesProd front B := by
  refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => ?_)
  rcases lt_or_ge i primes.size with hi | hi
  · simp [Array.getElem?_eq_getElem hi]
  · simp [Array.getElem?_eq_none hi]

/-- `primesProd` is positive: each factor is at least `1`. -/
private theorem primesProd_pos (front B : Nat) : 1 ≤ primesProd front B := by
  refine Finset.one_le_prod' (fun i _ => ?_)
  rcases lt_or_ge i primes.size with hi | hi
  · simpa [Array.getElem?_eq_getElem hi] using
      (primes_prime_of_mem _ (Array.getElem_mem hi)).one_le
  · simp [Array.getElem?_eq_none hi]

/-- `primesProdM1` is positive when each factor is in range. For out-of-range indices the
factor is `1`. For in-range indices `primes[i] - 1 ≥ 1` since primes are `≥ 2`. -/
private theorem primesProdM1_pos (front B : Nat) : 1 ≤ primesProdM1 front B := by
  refine Finset.one_le_prod' (fun i _ => ?_)
  rcases lt_or_ge i primes.size with hi | hi
  · have := (primes_prime_of_mem _ (Array.getElem_mem hi)).two_le
    simp [Array.getElem?_eq_getElem hi]; omega
  · simp [Array.getElem?_eq_none hi]

/-- Factoring `primesProd` at a valid index `front`. -/
private theorem primesProd_succ_front {front B : Nat} (h : front < primes.size)
    (hB : front ≤ B) :
    primesProd front B = primes[front] * primesProd (front + 1) B := by
  simp [primesProd, Finset.prod_eq_prod_Ico_succ_bot (by omega : front < B + 1),
    Array.getElem?_eq_getElem h]

/-- Factoring `primesProdM1` at a valid index `front`. -/
private theorem primesProdM1_succ_front {front B : Nat} (h : front < primes.size)
    (hB : front ≤ B) :
    primesProdM1 front B = (primes[front] - 1) * primesProdM1 (front + 1) B := by
  simp [primesProdM1, Finset.prod_eq_prod_Ico_succ_bot (by omega : front < B + 1),
    Array.getElem?_eq_getElem h]

/-- Wheel invariant update in the `case3` step (extending the window by one prime). -/
private lemma extendWF_case3_invariants {m target front back lhs rhs : Nat}
    (hlhs : lhs = m * primesProd front back) (hrhs : rhs = target * primesProdM1 front back)
    (hf : front ≤ back) (hb : back + 1 < primes.size) :
    lhs * primes[back + 1] = m * primesProd front (back + 1) ∧
    rhs * (primes[back + 1] - 1) = target * primesProdM1 front (back + 1) :=
  ⟨by rw [primesProd_succ_lt (Nat.le_succ_of_le hf) hb, hlhs]; ring,
   by rw [primesProdM1_succ_lt (Nat.le_succ_of_le hf) hb, hrhs]; ring⟩

/-- Wheel invariant update in the `case6` step (seeding an empty window at `front`). -/
private lemma extendWF_case6_invariants {m target front back lhs rhs : Nat}
    (hlhs : lhs = m * primesProd front back) (hrhs : rhs = target * primesProdM1 front back)
    (hback : back < front) (hf : front < primes.size) :
    lhs * primes[front] = m * primesProd front front ∧
    rhs * (primes[front] - 1) = target * primesProdM1 front front :=
  ⟨by rw [primesProd_self hf, hlhs, primesProd_empty hback, mul_one],
   by rw [primesProdM1_self hf, hrhs, primesProdM1_empty hback, mul_one]⟩

/-! ### Sigma at a single prime -/

/-- Core arithmetic bound: for `p₀ ≤ p` both primes (or `p₀ ≥ 2`),
`σ₁(p^k) * (p₀ - 1) ≤ p^k * p₀`. Used to "consume" one prime in the window step. -/
private theorem sigma_pow_le_window_factor {p p₀ k : Nat} (hp : p.Prime) (hp₀ : 2 ≤ p₀)
    (hple : p₀ ≤ p) :
    σ₁ (p ^ k) * (p₀ - 1) ≤ p ^ k * p₀ := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpk_pos : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
  have h_eq : σ₁ (p ^ k) * (p - 1) = p ^ (k + 1) - 1 := by
    rw [sigma_one_apply_prime_pow' hp,
      Nat.div_mul_cancel (Nat.sub_one_dvd_pow_sub_one p (k + 1))]
  refine Nat.le_of_mul_le_mul_right ?_ (by omega : 0 < p - 1)
  have hpk1 : 1 ≤ p ^ (k + 1) := Nat.one_le_pow _ _ hp.pos
  rw [mul_right_comm, h_eq]
  zify [hpk1, show 1 ≤ p₀ by omega, show 1 ≤ p by omega]
  nlinarith [hpk_pos, hple, hp₀, hp2, pow_succ p k]

/-- σ formula in `expChildren`'s loop: `(p^k * p - 1) / (p - 1) = σ₁ (p^k)` for prime `p`. -/
private theorem sigma_pow_expChildren_eq {p k : Nat} (hp : p.Prime) :
    (p^k * p - 1) / (p - 1) = σ₁ (p^k) := by
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
    obtain ⟨_, hp0_eq, hp_geprimes⟩ := hP.2 p hp_prime hp_dvd
    obtain ⟨hfront_lt, rfl⟩ := Array.getElem?_eq_some_iff.mp hp0_eq
    have hpf : t.primeFactors = insert p t'.primeFactors := by
      rw [← hpk_t, Nat.Coprime.primeFactors_mul (hcoprime.pow_left k),
        Nat.primeFactors_pow p (by omega : k ≠ 0), hp_prime.primeFactors, Finset.insert_eq]
    have hp_not_t' : p ∉ t'.primeFactors := fun h =>
      hp_prime.coprime_iff_not_dvd.mp hcoprime (Nat.mem_primeFactors.mp h).2.1
    have hcard' : t'.primeFactors.card + (front + 1) ≤ B + 1 := by
      rw [hpf, Finset.card_insert_of_notMem hp_not_t'] at hcard
      omega
    have ht'_P : t' ∈ P (front + 1) := by
      refine ⟨ht'_pos, fun q hq hqd => ?_⟩
      have hq_in : q ∈ t'.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hq, hqd, by omega⟩
      have h_two : 2 ≤ t.primeFactors.card := by
        rw [hpf, Finset.card_insert_of_notMem hp_not_t']
        exact Nat.succ_le_succ (Finset.card_pos.mpr ⟨q, hq_in⟩)
      exact ⟨primes[front + 1], Array.getElem?_eq_getElem (by omega),
        primes_consecutive hfront_lt hq (hp_geprimes.trans_lt <| lt_of_le_of_ne
          (hp_min q hq (hpk_t ▸ dvd_mul_of_dvd_right hqd _))
          (Ne.symm fun hqp => hp_prime.coprime_iff_not_dvd.mp hcoprime
            (hqp ▸ hqd))) (by omega)⟩
    have IH := ih t' ht'_lt _ _ ht'_pos ht'_P hBsize hcard'
    have hcons : σ₁ (p^k) * (primes[front] - 1) ≤ p^k * primes[front] :=
      sigma_pow_le_window_factor hp_prime
        (primes_prime_of_mem _ (Array.getElem_mem hfront_lt)).two_le hp_geprimes
    calc σ₁ t * primesProdM1 front B
        = σ₁ (p^k) * (primes[front] - 1) * (σ₁ t' * primesProdM1 (front + 1) B) := by
          rw [← hpk_t, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
            (hcoprime.pow_left k), primesProdM1_succ_front hfront_lt (by omega)]
          ring
      _ ≤ p^k * primes[front] * (t' * primesProd (front + 1) B) := by gcongr
      _ = t * primesProd front B := by
          rw [← hpk_t, primesProd_succ_front hfront_lt (by omega)]
          ring

/-- Radical bound: `primesProd front (front + j - 1) ≤ t` for `t ∈ P front` with at least `j ≥ 1`
distinct primes, and `front + j ≤ primes.size`. Used in the wheel's `.tooLarge` case. -/
private theorem primesProd_le_t (t front : Nat) (ht : 1 ≤ t) (hP : t ∈ P front) (j : Nat)
    (hj : 1 ≤ j) (hjle : j ≤ t.primeFactors.card) (hsize : front + j ≤ primes.size) :
    primesProd front (front + j - 1) ≤ t := by
  induction t using Nat.strongRecOn generalizing front j with
  | _ t ih =>
    have ht1 : t ≠ 1 := by
      intro h; subst h; simp [Nat.primeFactors_one] at hjle; omega
    have ht2 : 2 ≤ t := by omega
    obtain ⟨p, k, t', hp_prime, _, hk_pos, hpk_t, _, ht'_pos, ht'_lt, hcoprime, hp_min⟩ :=
      exists_minFac_decomp ht2
    have hp_dvd : p ∣ t := hpk_t ▸ (dvd_pow_self p (by omega)).mul_right _
    obtain ⟨_, hp0_eq, hp_geprimes⟩ := hP.2 p hp_prime hp_dvd
    obtain ⟨hfront_lt, rfl⟩ := Array.getElem?_eq_some_iff.mp hp0_eq
    have hpk_ge : primes[front] ≤ p^k := hp_geprimes.trans (Nat.le_self_pow (by omega) p)
    rcases Nat.lt_or_ge 1 j with hj2 | hj2
    · have hp_not_t' : p ∉ t'.primeFactors := fun h =>
        hp_prime.coprime_iff_not_dvd.mp hcoprime (Nat.mem_primeFactors.mp h).2.1
      have h_pf_eq : t.primeFactors = {p} ∪ t'.primeFactors := by
        rw [← hpk_t, Nat.Coprime.primeFactors_mul (hcoprime.pow_left k),
          Nat.primeFactors_pow p (by omega : k ≠ 0), hp_prime.primeFactors]
      have ht'_card_eq : t'.primeFactors.card = t.primeFactors.card - 1 := by
        rw [h_pf_eq, Finset.card_union_of_disjoint (Finset.disjoint_singleton_left.mpr hp_not_t'),
            Finset.card_singleton]; omega
      have ht'_in_P : t' ∈ P (front + 1) :=
        mem_P_succ_of_factors_gt ht'_pos hfront_lt (by omega) fun q hq_prime hq_dvd =>
          hp_geprimes.trans_lt (lt_of_le_of_ne
            (hp_min q hq_prime (hpk_t ▸ dvd_mul_of_dvd_right hq_dvd _))
            fun hqp => hp_prime.coprime_iff_not_dvd.mp hcoprime (hqp ▸ hq_dvd))
      have IH := ih t' ht'_lt _ ht'_pos ht'_in_P (j - 1) (by omega) (by rw [ht'_card_eq]; omega)
        (by omega)
      rw [(by omega : (front + 1) + (j - 1) - 1 = front + j - 1)] at IH
      calc primesProd front (front + j - 1)
          = primes[front] * primesProd (front + 1) (front + j - 1) :=
            primesProd_succ_front hfront_lt (by omega)
        _ ≤ p^k * t' := by gcongr
        _ = t := hpk_t
    · obtain rfl : j = 1 := by omega
      rw [Nat.add_sub_cancel, primesProd_self hfront_lt]
      calc primes[front] ≤ p^k := hpk_ge
        _ ≤ p^k * t' := Nat.le_mul_of_pos_right _ ht'_pos
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
    (hbig : lhs * primes[back + 1] > m * m)
    (ht2 : 2 ≤ t) (htP : t ∈ P front) (htm : t ≤ m) (htσ : target ≤ σ₁ t) : False := by
  have hpsucc : primesProd front (back + 1) = primesProd front back * primes[back+1] :=
    primesProd_succ_lt (by omega) hback_lt
  rcases Nat.lt_or_ge t.primeFactors.card (back + 2 - front) with hcard | hcard
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
with `t ≤ m`, `t ∈ P front`, `t ≥ 2` gives `False`. The condition `lhs * primes[front] > m*m`
with `lhs = m` implies `primes[front] > m`, but `t ≥ primes[front]`. -/
private theorem extend_tooLarge_empty_contradiction
    {m front back lhs : Nat} {t : Nat}
    (hlhs : lhs = m * primesProd front back) (hfront_lt : front < primes.size)
    (hempty : back + 1 = front)
    (hbig : lhs * primes[front] > m * m)
    (ht2 : 2 ≤ t) (htP : t ∈ P front) (htm : t ≤ m) : False := by
  rw [primesProd_empty (by omega : back < front), mul_one] at hlhs
  rw [hlhs] at hbig
  have hpf_gt : primes[front] > m := Nat.lt_of_mul_lt_mul_left (a := m) (by rwa [mul_comm m m] at hbig)
  obtain ⟨_, hp0_eq, hp0_le⟩ := htP.2 _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd t)
  obtain ⟨_, rfl⟩ := Array.getElem?_eq_some_iff.mp hp0_eq
  have : t.minFac ≤ t := Nat.minFac_le (by omega)
  omega

/-- The main `.tooLarge` invariant: if `t` is a witness, `extendWF` cannot return `.tooLarge`.
Proved by induction over `extendWF`'s structure. -/
private theorem extendWF_ne_tooLarge_of_witness (m target front t : Nat) (ht2 : 2 ≤ t)
    (htP : t ∈ P front) (htm : t ≤ m) (htσ : target ≤ σ₁ t)
    (back lhs rhs : Nat) (hlhs : lhs = m * primesProd front back)
    (hrhs : rhs = target * primesProdM1 front back) (hfront : front ≤ back + 1) :
    extendWF (m * m) front back lhs rhs ≠ .tooLarge := by
  induction back, lhs, rhs using extendWF.induct (m2 := m * m) (front := front) with
  | case1 _ _ _ hf hge => simp [extendWF, hf, hge]
  | case2 _ _ _ hf hlt hb1 _ _ hbig =>
    intro _
    exact extend_tooLarge_contradiction hlhs hrhs hfront hb1 (by omega) hbig ht2 htP htm htσ
  | case3 back lhs rhs hf hlt hb1 _ _ hle ih =>
    rw [extendWF, if_pos hf, if_neg hlt, dif_pos hb1, if_neg hle]
    obtain ⟨hlhs', hrhs'⟩ := extendWF_case3_invariants hlhs hrhs hf hb1
    exact ih hlhs' hrhs' (by omega)
  | case4 _ _ _ hf hlt hb1 => simp [extendWF, hf, hlt, hb1]
  | case5 _ _ _ hf hf1 _ _ hbig =>
    intro _
    exact extend_tooLarge_empty_contradiction hlhs hf1 (by omega) hbig ht2 htP htm
  | case6 back lhs rhs hf hf1 _ _ hle ih =>
    rw [extendWF, if_neg hf, dif_pos hf1, if_neg hle]
    obtain ⟨hlhs_new, hrhs_new⟩ := extendWF_case6_invariants hlhs hrhs (by omega) hf1
    exact ih hlhs_new hrhs_new (by omega)
  | case7 _ _ _ hf hf1 =>
    simp [extendWF, hf, hf1]

/-! ### Window invariants -/

/-- When `extendWF` returns `.window`, the new `(b, lhs', rhs')` satisfy the wheel invariants
shifted to `b`, and `b ≥ back`. -/
private theorem extendWF_window_invariant (m target front back lhs rhs b lhs' rhs' : Nat)
    (hlhs : lhs = m * primesProd front back) (hrhs : rhs = target * primesProdM1 front back)
    (hfront : front ≤ back + 1)
    (heq : extendWF (m * m) front back lhs rhs = Wheel.window b lhs' rhs') :
    lhs' = m * primesProd front b ∧ rhs' = target * primesProdM1 front b ∧
    back ≤ b ∧ front ≤ b := by
  induction back, lhs, rhs using extendWF.induct (m2 := m * m) (front := front) with
  | case1 back lhs rhs hf hge =>
    rw [extendWF] at heq
    simp [hf, hge] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨hlhs, hrhs, le_refl _, hf⟩
  | case2 _ _ _ hf hlt hb1 _ _ hbig =>
    rw [extendWF, if_pos hf, if_neg hlt, dif_pos hb1, if_pos hbig] at heq
    cases heq
  | case3 back lhs rhs hf hlt hb1 _ _ hle ih =>
    rw [extendWF, if_pos hf, if_neg hlt, dif_pos hb1, if_neg hle] at heq
    obtain ⟨hlhs_new, hrhs_new⟩ := extendWF_case3_invariants hlhs hrhs hf hb1
    obtain ⟨h1, h2, _, h4⟩ := ih hlhs_new hrhs_new (by omega) heq
    exact ⟨h1, h2, by omega, h4⟩
  | case4 _ _ _ hf hlt hb1 =>
    rw [extendWF, if_pos hf, if_neg hlt, dif_neg hb1] at heq
    cases heq
  | case5 _ _ _ hf hf1 _ _ hbig =>
    rw [extendWF, if_neg hf, dif_pos hf1, if_pos hbig] at heq
    cases heq
  | case6 back lhs rhs hf hf1 _ _ hle ih =>
    rw [extendWF, if_neg hf, dif_pos hf1, if_neg hle] at heq
    obtain ⟨hlhs_new, hrhs_new⟩ := extendWF_case6_invariants hlhs hrhs (by omega) hf1
    obtain ⟨h1, h2, _, h4⟩ := ih hlhs_new hrhs_new (by omega) heq
    exact ⟨h1, h2, by omega, h4⟩
  | case7 back _ _ hf hf1 =>
    push Not at hf1
    rw [extendWF, if_neg hf, dif_neg (by omega)] at heq
    cases heq

/-! ### Degenerate case: `lhs = 0` -/

/-- For `m2 = 0` and `lhs = 0`: `extendWF` returns either `.exhaustedTable` or
`.window b 0 rhs'` (so never `.tooLarge`, and any `.window` has `lhs' = 0`). -/
private lemma extendWF_zero_lhs_combined (front back lhs rhs : Nat) (hlhs : lhs = 0) :
    extendWF 0 front back lhs rhs = Wheel.exhaustedTable ∨
    ∃ b rhs', extendWF 0 front back lhs rhs = Wheel.window b 0 rhs' := by
  induction back, lhs, rhs using extendWF.induct (m2 := 0) (front := front) with
  | case1 back lhs rhs hf hge =>
    exact Or.inr ⟨back, rhs, by rw [extendWF, if_pos hf, if_pos hge, hlhs]⟩
  | case2 _ _ _ _ _ _ _ _ hbig => subst hlhs; omega
  | case3 _ _ _ hf hlt hb1 _ _ hle ih =>
    rw [extendWF, if_pos hf, if_neg hlt, dif_pos hb1, if_neg hle]
    exact ih (by omega)
  | case4 _ _ _ hf hlt hb1 =>
    rw [extendWF, if_pos hf, if_neg hlt, dif_neg hb1]
    exact Or.inl rfl
  | case5 _ _ _ _ _ _ _ hbig => subst hlhs; omega
  | case6 _ _ _ hf hf1 _ _ hle ih =>
    rw [extendWF, if_neg hf, dif_pos hf1, if_neg hle]
    exact ih (by omega)
  | case7 back _ _ hf hf1 =>
    push Not at hf1
    rw [extendWF, if_neg hf, dif_neg (by omega)]
    exact Or.inl rfl

/-- For `m2 = 0` and `lhs = 0`, `wheelChildrenWF` returns `none`. -/
private theorem wheelChildrenWF_zero_no_some (target num front back lhs rhs : Nat)
    (hlhs : lhs = 0) : wheelChildrenWF 0 0 target num front back lhs rhs = none := by
  induction front, back, lhs, rhs using wheelChildrenWF.induct
    (m2 := 0) (m := 0) (target := target) (num := num) with
  | case1 _ _ _ _ hfront => rw [wheelChildrenWF]; simp [hfront]
  | case2 _ _ _ _ hfront hext => rw [wheelChildrenWF]; simp [hfront, hext]
  | case3 front back lhs rhs _ hext =>
    rcases extendWF_zero_lhs_combined front back lhs rhs hlhs with h' | ⟨_, _, h'⟩ <;>
      rw [h'] at hext <;> cases hext
  | case4 _ _ _ _ hfront _ _ _ hext _ hrec =>
    rw [wheelChildrenWF]
    simp only [hfront, dif_neg, not_false_eq_true, hext]
    rw [hrec]
  | case5 front back lhs rhs _ b lhs' rhs' hext _ _ hrec =>
    rename_i ih
    exfalso
    have hlhs' : lhs' / primes[front] = 0 := by
      rcases extendWF_zero_lhs_combined front back lhs rhs hlhs with h' | ⟨_, _, h'⟩
      · rw [h'] at hext; cases hext
      · rw [h'] at hext; injection hext with _ hl' _; simp [← hl']
    rw [ih hlhs'] at hrec; cases hrec

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
  | zero => simp [expChildren] at hc
  | succ fuel ih =>
    rw [expChildren] at hc
    have hspk_eq : (p ^ k₀ * p - 1) / (p - 1) = σ₁ (p ^ k₀) := sigma_pow_expChildren_eq hp
    by_cases hpm : p ^ k₀ > m
    · simp [hpm] at hc
    by_cases hge : (p ^ k₀ * p - 1) / (p - 1) ≥ target
    · simp [hpm, hge] at hc
      exact ⟨k₀, le_refl _, by omega, by rw [hc, hspk_eq]⟩
    simp [hpm, hge] at hc
    rcases hc with rfl | hc
    · exact ⟨k₀, le_refl _, by omega, by rw [hspk_eq]⟩
    · rw [← pow_succ] at hc
      obtain ⟨k, hk, hpkm, hceq⟩ := ih (by omega) hc
      exact ⟨k, by omega, hpkm, hceq⟩

/-- Witness `1` for the stop arm of `expChildren_witness_walk`: when `σ(p^j₀) ≥ target`,
the child `(ceilDiv target σ(p^j₀), num*p^j₀, next)` has `1` as a witness. -/
private lemma one_witnesses_stop {B num target next p k j₀ t'' : Nat}
    (hp : p.Prime) (hjk : j₀ ≤ k) (ht''_pos : 1 ≤ t'')
    (hnumt : num * p^k * t'' < B) (hσ_target : σ₁ (p^j₀) ≥ target) :
    W B (ceilDiv target (σ₁ (p^j₀))) (num * p^j₀) next ≠ ∅ := by
  refine Set.nonempty_iff_ne_empty.mp ⟨1, one_mem_P _, ?_, ?_⟩
  · rw [mul_one]
    calc num * p^j₀ ≤ num * p^k :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp.one_lt.le hjk)
      _ ≤ num * p^k * t'' := Nat.le_mul_of_pos_right _ ht''_pos
      _ < B := hnumt
  · have hσpj_pos : 0 < σ₁ (p^j₀) :=
      ArithmeticFunction.sigma_pos _ _ (pow_ne_zero _ hp.pos.ne')
    have hσ1 : σ₁ 1 = 1 := by simp
    rw [hσ1]
    unfold ceilDiv
    rw [Nat.div_le_iff_le_mul_add_pred hσpj_pos]
    omega

/-- Walk `expChildren` from `pk₀ = p^j₀` looking for a child with a witness, given a parent
witness `t = p^k * t''` (factored at `p` with `t''` coprime to `p`). The proof iterates by
strong induction on `k - j₀`: at each step either σ(p^{j₀}) ≥ target (stop with witness `1`)
or σ < target (emit and recurse), bottoming out at `j₀ = k` with witness `t''`. -/
private theorem expChildren_witness_walk {B num target m p : Nat} (hp : p.Prime) (next : Nat)
    (n k j₀ : Nat) (hn : k - j₀ = n) (hj₀ : 1 ≤ j₀) (hj₀_k : j₀ ≤ k) (hpk_le_m : p^k ≤ m)
    {t'' : Nat} (ht''_pos : 1 ≤ t'') (ht''_P : t'' ∈ P next) (hnumt : num * p^k * t'' < B)
    (htσ : target ≤ σ₁ (p^k) * σ₁ t'') {fuel : Nat} (hfuel : n + 1 ≤ fuel) :
    ∃ c ∈ expChildren fuel target num next m p (p^j₀), W B c.1 c.2.1 c.2.2 ≠ ∅ := by
  induction n generalizing j₀ fuel with
  | zero =>
    have hjk : j₀ = k := by omega
    subst hjk
    have h_sig_eq : (p^j₀ * p - 1) / (p - 1) = σ₁ (p^j₀) := sigma_pow_expChildren_eq hp
    by_cases hσ_target : σ₁ (p^j₀) ≥ target
    · have h_exp : expChildren fuel target num next m p (p^j₀) =
          [(ceilDiv target (σ₁ (p^j₀)), num * p^j₀, next)] := by
        rw [← h_sig_eq]
        exact expChildren_stop (by omega) hpk_le_m (by rw [h_sig_eq]; exact hσ_target)
      rw [h_exp]
      exact ⟨_, List.mem_singleton.mpr rfl, one_witnesses_stop hp le_rfl ht''_pos hnumt hσ_target⟩
    · push Not at hσ_target
      have h_exp : expChildren fuel target num next m p (p^j₀) =
          (ceilDiv target (σ₁ (p^j₀)), num * p^j₀, next) ::
          expChildren (fuel - 1) target num next m p (p^j₀ * p) := by
        rw [← h_sig_eq]
        exact expChildren_step (by omega) hpk_le_m (by rw [h_sig_eq]; exact hσ_target)
      rw [h_exp]
      refine ⟨_, List.mem_cons_self, Set.nonempty_iff_ne_empty.mp ⟨t'', ht''_P, hnumt, ?_⟩⟩
      have hσpk_pos : 0 < σ₁ (p^j₀) := ArithmeticFunction.sigma_pos _ _ (pow_ne_zero _ hp.pos.ne')
      unfold ceilDiv
      rw [Nat.div_le_iff_le_mul_add_pred hσpk_pos]
      omega
  | succ n ih =>
    have hpj_le_m : p^j₀ ≤ m := (Nat.pow_le_pow_right hp.one_lt.le hj₀_k).trans hpk_le_m
    have h_sig_eq : (p^j₀ * p - 1) / (p - 1) = σ₁ (p^j₀) := sigma_pow_expChildren_eq hp
    by_cases hσ_target : σ₁ (p^j₀) ≥ target
    · have h_exp : expChildren fuel target num next m p (p^j₀) =
          [(ceilDiv target (σ₁ (p^j₀)), num * p^j₀, next)] := by
        rw [← h_sig_eq]
        exact expChildren_stop (by omega) hpj_le_m (by rw [h_sig_eq]; exact hσ_target)
      rw [h_exp]
      exact ⟨_, List.mem_singleton.mpr rfl, one_witnesses_stop hp hj₀_k ht''_pos hnumt hσ_target⟩
    · push Not at hσ_target
      have h_exp : expChildren fuel target num next m p (p^j₀) =
          (ceilDiv target (σ₁ (p^j₀)), num * p^j₀, next) ::
          expChildren (fuel - 1) target num next m p (p^j₀ * p) := by
        rw [← h_sig_eq]
        exact expChildren_step (by omega) hpj_le_m (by rw [h_sig_eq]; exact hσ_target)
      rw [h_exp, ← pow_succ]
      obtain ⟨c, hc, hwit⟩ := ih (j₀ + 1) (by omega) (by omega) (by omega)
        (fuel := fuel - 1) (by omega)
      exact ⟨c, List.mem_cons_of_mem _ hc, hwit⟩

/-! ### `wheelChildrenWF` and `children` -/

/-- Every entry of `wheelChildrenWF`'s output has the prime-power form. -/
private theorem mem_wheelChildrenWF {m2 m target num front back lhs rhs : Nat}
    {L : List (Nat × Nat × Nat)} (h : wheelChildrenWF m2 m target num front back lhs rhs = some L)
    {c : Nat × Nat × Nat} (hc : c ∈ L) :
    ∃ i p k, front ≤ i ∧ primes[i]? = some p ∧ 1 ≤ k ∧
      p ^ k ≤ m ∧ c = (ceilDiv target (σ₁ (p ^ k)), num * p ^ k, i + 1) := by
  induction front, back, lhs, rhs using wheelChildrenWF.induct
    (m2 := m2) (m := m) (target := target) (num := num) generalizing L with
  | case1 _ _ _ _ hfront => rw [wheelChildrenWF] at h; simp [hfront] at h
  | case2 _ _ _ _ hfront hext => rw [wheelChildrenWF] at h; simp [hfront, hext] at h
  | case3 _ _ _ _ hfront hext =>
    rw [wheelChildrenWF] at h
    simp [hfront, hext] at h
    subst h; cases hc
  | case4 _ _ _ _ hfront _ _ _ hext _ hrec =>
    rw [wheelChildrenWF] at h
    simp only [hfront, dif_neg, not_false_eq_true, hext] at h
    rw [hrec] at h
    cases h
  | case5 front _ _ _ hfront _ _ _ hext _ rest hrec =>
    rename_i ih
    rw [wheelChildrenWF] at h
    simp only [hfront, dif_neg, not_false_eq_true, hext] at h
    rw [hrec] at h
    obtain rfl : rest ++ expChildren (m + 1) target num (front + 1) m
        primes[front] primes[front] = L := Option.some.inj h
    rcases List.mem_append.mp hc with hcrest | hcexp
    · obtain ⟨i, p, k, hi, hpi, hk, hpkm, hceq⟩ := ih hrec hcrest
      exact ⟨i, p, k, by omega, hpi, hk, hpkm, hceq⟩
    · have hpf : front < primes.size := Nat.lt_of_not_ge hfront
      have hp : primes[front].Prime := primes_prime_of_mem _ (Array.getElem_mem hpf)
      obtain ⟨k, hk, hpkm, hceq⟩ := mem_expChildren hp le_rfl (by rw [pow_one]; exact hcexp)
      exact ⟨front, primes[front], k, le_rfl, Array.getElem?_eq_getElem hpf, hk, hpkm, hceq⟩

/-- The inductive lemma: at any state of `wheelChildrenWF` with the wheel invariants and a
viable witness `t`, some child in the output `L` has a non-empty witness set. -/
private theorem wheelChildrenWF_witness {B num m target : Nat} (hmdef : m = B / num)
    (hnum_pos : 1 ≤ num) (front back lhs rhs : Nat) (L : List (Nat × Nat × Nat))
    (hlhs : lhs = m * primesProd front back) (hrhs : rhs = target * primesProdM1 front back)
    (hfront_le : front ≤ back + 1)
    (hwf : wheelChildrenWF (m * m) m target num front back lhs rhs = some L)
    (t : Nat) (ht2 : 2 ≤ t) (htP : t ∈ P front) (hnumt : num * t < B) (htσ : target ≤ σ₁ t) :
    ∃ c ∈ L, W B c.1 c.2.1 c.2.2 ≠ ∅ := by
  induction front, back, lhs, rhs using wheelChildrenWF.induct
    (m2 := m * m) (m := m) (target := target) (num := num)
    generalizing L with
  | case1 _ _ _ _ hfront =>
    simp [wheelChildrenWF, hfront] at hwf
  | case2 _ _ _ _ hfront hext =>
    simp [wheelChildrenWF, hfront, hext] at hwf
  | case3 front _ _ _ hfront hext =>
    exfalso
    have htm : t ≤ m := hmdef ▸ (Nat.le_div_iff_mul_le hnum_pos).mpr (by linarith)
    exact extendWF_ne_tooLarge_of_witness m target front t ht2 htP htm htσ
      _ _ _ hlhs hrhs hfront_le hext
  | case4 _ _ _ _ hfront _ _ _ hext _ hrec =>
    rw [wheelChildrenWF] at hwf
    simp only [hfront, dif_neg, not_false_eq_true, hext] at hwf
    rw [hrec] at hwf
    cases hwf
  | case5 front back lhs rhs hfront b lhs' rhs' hext _ rest hrec =>
    rename_i ih
    rw [wheelChildrenWF] at hwf
    simp only [hfront, dif_neg, not_false_eq_true, hext] at hwf
    rw [hrec] at hwf
    obtain rfl : rest ++ expChildren (m + 1) target num (front + 1) m
        primes[front] primes[front] = L := Option.some.inj hwf
    have hfront_lt : front < primes.size := Nat.lt_of_not_ge hfront
    have hp_prime : (primes[front]).Prime := primes_prime_of_mem _ (Array.getElem_mem hfront_lt)
    have hp2 : 2 ≤ primes[front] := hp_prime.two_le
    have htm : t ≤ m := hmdef ▸ (Nat.le_div_iff_mul_le hnum_pos).mpr (by linarith)
    have hf1 := wheelChildrenWF_some_imp_succ_lt hrec
    by_cases hdvd : primes[front] ∣ t
    · set p := primes[front]
      obtain ⟨k, t'', hk_pos, hpk_t, _, ht''_pos, _, hcoprime⟩ :=
        exists_factor_decomp hp_prime hdvd (by omega)
      have hpk_le_m : p^k ≤ m := le_trans (Nat.le_of_dvd (by omega) ⟨t'', hpk_t.symm⟩) htm
      have htσ' : target ≤ σ₁ (p^k) * σ₁ t'' := by
        rw [← ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
          (hcoprime.pow_left k), hpk_t]; exact htσ
      have ht''_P : t'' ∈ P (front + 1) :=
        mem_P_succ_of_factors_gt ht''_pos hfront_lt hf1 fun q hq_prime hq_dvd => by
          refine lt_of_le_of_ne
            (P_le_factor htP hq_prime (hpk_t ▸ dvd_mul_of_dvd_right hq_dvd _) hfront_lt) ?_
          rintro rfl
          exact hp_prime.coprime_iff_not_dvd.mp hcoprime hq_dvd
      obtain ⟨c, hc, hwit⟩ := expChildren_witness_walk hp_prime (front + 1) (k - 1) k 1
        (by omega) (by omega) hk_pos hpk_le_m ht''_pos ht''_P
        (by rw [mul_assoc, hpk_t]; exact hnumt) htσ' (fuel := m + 1)
        (by have : k ≤ m := (Nat.lt_pow_self hp_prime.one_lt).le.trans hpk_le_m; omega)
      exact ⟨c, List.mem_append_right _ (by rwa [pow_one] at hc), hwit⟩
    · have ht_in_P_next : t ∈ P (front + 1) :=
        mem_P_succ_of_factors_gt (by omega) hfront_lt hf1 fun q hq_prime hq_dvd =>
          lt_of_le_of_ne (P_le_factor htP hq_prime hq_dvd hfront_lt)
            (Ne.symm fun h => hdvd (h ▸ hq_dvd))
      obtain ⟨hlhs', hrhs', _, hfront_b⟩ :=
        extendWF_window_invariant m target front back lhs rhs b lhs' rhs' hlhs hrhs hfront_le hext
      have hlhs_new : lhs' / primes[front] = m * primesProd (front + 1) b := by
        rw [hlhs', primesProd_succ_front hfront_lt hfront_b, mul_left_comm,
          Nat.mul_div_cancel_left _ hp_prime.pos]
      have hrhs_new : rhs' / (primes[front] - 1) = target * primesProdM1 (front + 1) b := by
        rw [hrhs', primesProdM1_succ_front hfront_lt hfront_b, mul_left_comm,
          Nat.mul_div_cancel_left _ (by omega : 0 < primes[front] - 1)]
      obtain ⟨c, hc_rest, hwit⟩ :=
        ih rest hlhs_new hrhs_new (by omega) hrec ht_in_P_next
      exact ⟨c, List.mem_append_left _ hc_rest, hwit⟩

/-- Every `c` in `children`'s output is a prime-power child of the form
`(⌈target / σ₁(p^k)⌉, num * p^k, i + 1)` for some prime index `i ≥ minIdx`
(with `primes[i]? = some p`) and some `k ≥ 1` with `p^k ≤ B/num`. -/
private theorem mem_children {B target num minIdx : Nat} {cs : List (Nat × Nat × Nat)}
    (h : children B target num minIdx = some cs) {c : Nat × Nat × Nat} (hc : c ∈ cs) :
    ∃ i p k, minIdx ≤ i ∧ primes[i]? = some p ∧ 1 ≤ k ∧
      p ^ k ≤ B / num ∧
      c = (ceilDiv target (σ₁ (p ^ k)), num * p ^ k, i + 1) := by
  rw [children] at h
  split at h
  · cases h
  · rw [wheelChildren_eq_wheelChildrenWF (by omega), Option.map_eq_some_iff] at h
    obtain ⟨L, hWF, rfl⟩ := h
    exact mem_wheelChildrenWF hWF (by simpa using hc)

/-- If `t'` is a witness of the child `(⌈target / σ₁(p^k)⌉, num * p^k, i+1)`
where `primes[i]? = some p`, then `p^k * t'` is a non-trivial witness of the
parent `(target, num, minIdx)`. -/
private theorem child_witness_to_parent {B target num minIdx i p k : Nat}
    (hmi : minIdx ≤ i) (hp : primes[i]? = some p) (hk : 1 ≤ k) {t' : Nat}
    (ht' : t' ∈ W B (ceilDiv target (σ₁ (p ^ k))) (num * p ^ k) (i + 1)) :
    p ^ k * t' ∈ W B target num minIdx ∧ p ^ k * t' ≠ 1 := by
  obtain ⟨⟨ht'1, ht'P⟩, ht'lt, ht'σ⟩ := ht'
  have hpPrime : p.Prime := primes_prime hp
  have hpk_ge2 : 2 ≤ p ^ k := hpPrime.two_le.trans (Nat.le_self_pow (by omega) p)
  have hpkt'_ge2 : 2 ≤ p ^ k * t' := hpk_ge2.trans (Nat.le_mul_of_pos_right _ ht'1)
  obtain ⟨hi, hp_eq⟩ := Array.getElem?_eq_some_iff.mp hp
  have hmi_lt : minIdx < primes.size := by omega
  have hp_not_dvd : ¬ p ∣ t' := fun hpdvd => by
    obtain ⟨p', hp', hple⟩ := ht'P p hpPrime hpdvd
    obtain ⟨hip1, hp'_eq⟩ := Array.getElem?_eq_some_iff.mp hp'
    have hlt : primes[i] < primes[i + 1] := primes_lt_of_lt (Nat.lt_succ_self i) hip1
    omega
  have hcop : Nat.Coprime (p ^ k) t' :=
    (hpPrime.coprime_iff_not_dvd.mpr hp_not_dvd).pow_left _
  refine ⟨⟨⟨by omega, fun q hqPrime hqDvd => ?_⟩, ?_, ?_⟩, by omega⟩
  · refine ⟨primes[minIdx], Array.getElem?_eq_getElem hmi_lt, ?_⟩
    rcases hqPrime.dvd_mul.mp hqDvd with h1 | h2
    · obtain rfl : q = p :=
        (Nat.prime_dvd_prime_iff_eq hqPrime hpPrime).mp (hqPrime.dvd_of_dvd_pow h1)
      rw [← hp_eq]; exact primes_le_of_le hmi hi
    · obtain ⟨_, hp', hple⟩ := ht'P q hqPrime h2
      obtain ⟨hip1, rfl⟩ := Array.getElem?_eq_some_iff.mp hp'
      have : primes[minIdx] ≤ primes[i + 1] := primes_le_of_le (by omega) hip1
      omega
  · rw [← Nat.mul_assoc]; exact ht'lt
  · rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop]
    have hσpk_pos : 0 < σ₁ (p ^ k) := ArithmeticFunction.sigma_pos _ _ (by positivity)
    refine le_trans ?_ (Nat.mul_le_mul_left _ ht'σ)
    simp [ceilDiv]
    have := Nat.div_add_mod (target + σ₁ (p ^ k) - 1) (σ₁ (p ^ k))
    have := Nat.mod_lt (target + σ₁ (p ^ k) - 1) hσpk_pos
    omega

/-- A non-trivial witness of the parent gives a witness for some child in `cs`.
Two cases: if `t`'s smallest prime is in the table (`= primes[i]`), decompose
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
    · cases h
    · simp only [Nat.div_zero, Nat.mul_zero] at h
      rw [wheelChildren_eq_wheelChildrenWF (by omega),
        wheelChildrenWF_zero_no_some target 0 _ _ 0 _ rfl] at h
      simp at h
  · rw [children] at h
    split at h
    · cases h
    · rename_i p0 hp0
      set m := B / num with hmdef
      rw [wheelChildren_eq_wheelChildrenWF (by omega), Option.map_eq_some_iff] at h
      obtain ⟨L, hwf, rfl⟩ := h
      obtain ⟨⟨ht_pos, htP⟩, htlt, htσ⟩ := ht
      obtain ⟨hminIdx_lt, rfl⟩ := Array.getElem?_eq_some_iff.mp hp0
      have hL : primes[minIdx] * m = m * primesProd minIdx minIdx := by
        rw [primesProd_self hminIdx_lt]; ring
      have hR : target * (primes[minIdx] - 1) = target * primesProdM1 minIdx minIdx := by
        rw [primesProdM1_self hminIdx_lt]
      rw [hL, hR] at hwf
      obtain ⟨c, hc, hwit⟩ := wheelChildrenWF_witness hmdef hnum_pos minIdx minIdx _ _ L rfl rfl
        (by omega) hwf t (by omega) ⟨ht_pos, htP⟩ htlt htσ
      exact ⟨c, by simpa using hc, hwit⟩

/-- `children` reduces nontrivial witnesses of a node to witnesses of its children. -/
theorem children_spec {B target num minIdx : Nat} {cs : List (Nat × Nat × Nat)}
    (h : children B target num minIdx = some cs) :
    (∃ t ∈ W B target num minIdx, t ≠ 1) ↔
      ∃ c ∈ cs, W B c.1 c.2.1 c.2.2 ≠ ∅ := by
  refine ⟨fun ⟨t, ht, h1⟩ => witness_to_child h ht h1, ?_⟩
  rintro ⟨c, hc, hwit⟩
  obtain ⟨i, p, k, hmi, hp, hk, _, hceq⟩ := mem_children h hc
  obtain ⟨t', ht'⟩ := Set.nonempty_iff_ne_empty.mpr hwit
  rw [hceq] at ht'
  obtain ⟨hw, hne⟩ := child_witness_to_parent hmi hp hk ht'
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
      · ext t
        simp only [W, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨ht1, _⟩, htlt, _⟩
        push Not at hn
        have := Nat.le_mul_of_pos_right num ht1
        omega
      · exact ih h _ hnode
    · simp only [ht, if_false] at h
      match hch : children B target num minIdx, h with
      | some cs, h =>
        have hstep : step B fuel (cs ++ rest) = some true := h
        have ih_all := ih hstep
        intro node hnode
        simp only [List.mem_cons] at hnode
        rcases hnode with rfl | hnode
        · ext t
          simp only [W, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro htW
          push Not at ht
          by_cases h1 : t = 1
          · subst h1
            have : σ₁ 1 = 1 := by simp
            have := htW.2.2
            omega
          obtain ⟨c, hc, hwc⟩ := (children_spec hch).mp ⟨t, htW, h1⟩
          exact hwc (ih_all c (List.mem_append.mpr (Or.inl hc)))
        · exact ih_all _ (List.mem_append.mpr (Or.inr hnode))

/-- `step = some false` ⟹ some node on the stack has a nonempty witness set. -/
theorem step_false {B fuel : Nat} {stack : List (Nat × Nat × Nat)}
    (h : step B fuel stack = some false) :
    ∃ node ∈ stack, W B node.1 node.2.1 node.2.2 ≠ ∅ := sorry

/-- Top-level correctness: a `some true` answer of `highlyAbundantLcm?` on
`(lcmRange n, σ₁ (lcmRange n))` certifies that `lcm (1..n)` is highly abundant.

With `P j` defined as "smallest prime factor `≥ primes[j]`" (off-table primes
allowed), `step_true` at the root directly gives `W (lcmRange n) (σ₁ (lcmRange n)) 1 0 = ∅`,
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
  by_contra hcontra
  push Not at hcontra
  have hmW : m ∈ W (lcmRange n) (σ₁ (lcmRange n)) 1 0 :=
    ⟨⟨hm_pos, fun q hqPrime _ => ⟨2, by decide, hqPrime.two_le⟩⟩, by simpa using hm_lt, hcontra⟩
  rwa [hW] at hmW

end Sage
