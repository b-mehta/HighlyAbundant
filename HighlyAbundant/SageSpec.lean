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

/-! ### Auxiliary facts about the `primes` table -/

/-- `primes` is strictly increasing (verified by `decide` on the explicit table). -/
private theorem primes_pairwise : primes.toList.Pairwise (· < ·) := by decide

/-- Every entry of `primes` is a prime. -/
private theorem primes_prime_of_mem : ∀ p ∈ primes, p.Prime := by
  decide +kernel

/-- If `primes[i]? = some p`, then `p` is prime. -/
private theorem primes_prime {i p : Nat} (h : primes[i]? = some p) : p.Prime := by
  have hi : i < primes.size := by
    by_contra hi
    rw [Array.getElem?_eq_none (Nat.not_lt.mp hi)] at h
    injection h
  rw [Array.getElem?_eq_getElem hi] at h
  obtain rfl : primes[i] = p := Option.some.inj h
  exact primes_prime_of_mem _ (Array.getElem_mem hi)

/-- Every prime ≤ 227 is in the `primes` table. -/
private theorem prime_in_primes (q : Nat) (hq : q ≤ 227) (hp : q.Prime) : q ∈ primes.toList := by
  decide +kernel +revert

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

/-! ### Auxiliary facts about the `primes` table -/

/-- `primes` is strictly monotone on indices in bounds. -/
private theorem primes_lt_of_lt {i j : Nat} (hij : i < j) (hj : j < primes.size) :
    primes[i]'(by omega) < primes[j] := by
  have hi : i < primes.size := by omega
  have hpw := primes_pairwise
  rw [List.pairwise_iff_get] at hpw
  have ha' : i < primes.toList.length := by simp [hi]
  have hb' : j < primes.toList.length := by simp [hj]
  have := hpw ⟨i, ha'⟩ ⟨j, hb'⟩ hij
  simpa using this

/-- `primes` is weakly monotone on indices in bounds. -/
private theorem primes_le_of_le {i j : Nat} (hij : i ≤ j) (hj : j < primes.size) :
    primes[i]'(by omega) ≤ primes[j] := by
  rcases eq_or_lt_of_le hij with rfl | hij
  · exact le_refl _
  · exact (primes_lt_of_lt hij hj).le

/-- The `primes` indexing function is injective on its domain. -/
private theorem primes_eq_iff {i j : Nat} {p : Nat}
    (hi : primes[i]? = some p) (hj : primes[j]? = some p) : i = j := by
  have hilt : i < primes.size := by
    by_contra h
    rw [Array.getElem?_eq_none (Nat.not_lt.mp h)] at hi
    injection hi
  have hjlt : j < primes.size := by
    by_contra h
    rw [Array.getElem?_eq_none (Nat.not_lt.mp h)] at hj
    injection hj
  rw [Array.getElem?_eq_getElem hilt] at hi
  rw [Array.getElem?_eq_getElem hjlt] at hj
  obtain rfl : primes[i] = p := Option.some.inj hi
  obtain heq : primes[j] = primes[i] := Option.some.inj hj
  -- Use Pairwise on toList to extract monotonicity
  have hne : ∀ i j, i < j → ∀ (hi : i < primes.size) (hj : j < primes.size),
      primes[i] < primes[j] := by
    intro a b hab ha hb
    have := primes_pairwise
    rw [List.pairwise_iff_get] at this
    have ha' : a < primes.toList.length := by simp [ha]
    have hb' : b < primes.toList.length := by simp [hb]
    have := this ⟨a, ha'⟩ ⟨b, hb'⟩ hab
    simpa using this
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact absurd heq.symm (hne i j hij hilt hjlt).ne
  · rfl
  · exact absurd heq (hne j i hij hjlt hilt).ne

/-! ### Products over prime windows -/

/-- `primesProd front back = ∏_{i ∈ [front, back]} primes[i]` (out-of-range indices contribute 1). -/
private def primesProd (front back : Nat) : Nat :=
  ∏ i ∈ Finset.Ico front (back + 1), (primes[i]?).getD 1

/-- `primesProdM1 front back = ∏_{i ∈ [front, back]} (primes[i] - 1)` (out-of-range: contributes 1). -/
private def primesProdM1 (front back : Nat) : Nat :=
  ∏ i ∈ Finset.Ico front (back + 1), ((primes[i]?).getD 2 - 1)

private theorem primesProd_empty {front back : Nat} (h : back < front) :
    primesProd front back = 1 := by
  unfold primesProd
  rw [Finset.Ico_eq_empty (by omega), Finset.prod_empty]

private theorem primesProdM1_empty {front back : Nat} (h : back < front) :
    primesProdM1 front back = 1 := by
  unfold primesProdM1
  rw [Finset.Ico_eq_empty (by omega), Finset.prod_empty]

private theorem primesProd_succ {front back : Nat} (h : front ≤ back + 1) :
    primesProd front (back + 1) = primesProd front back * (primes[back + 1]?).getD 1 := by
  unfold primesProd
  rw [show back + 1 + 1 = back + 2 by rfl, Finset.prod_Ico_succ_top h]

private theorem primesProdM1_succ {front back : Nat} (h : front ≤ back + 1) :
    primesProdM1 front (back + 1) =
      primesProdM1 front back * ((primes[back + 1]?).getD 2 - 1) := by
  unfold primesProdM1
  rw [show back + 1 + 1 = back + 2 by rfl]
  exact Finset.prod_Ico_succ_top h _

private theorem primesProd_self {i : Nat} (hi : i < primes.size) :
    primesProd i i = primes[i] := by
  unfold primesProd
  rw [show i + 1 = i + 1 by rfl, Finset.prod_Ico_succ_top (le_refl _), Finset.Ico_self,
    Finset.prod_empty, one_mul, Array.getElem?_eq_getElem hi, Option.getD_some]

private theorem primesProdM1_self {i : Nat} (hi : i < primes.size) :
    primesProdM1 i i = primes[i] - 1 := by
  unfold primesProdM1
  rw [show i + 1 = i + 1 by rfl, Finset.prod_Ico_succ_top (le_refl _), Finset.Ico_self,
    Finset.prod_empty, one_mul, Array.getElem?_eq_getElem hi, Option.getD_some]

/-! ### Sigma bound -/

/-- Core arithmetic bound: for `p₀ ≤ p` both primes (or `p₀ ≥ 2`),
`σ₁(p^k) * (p₀ - 1) ≤ p^k * p₀`. Used to "consume" one prime in the window step. -/
private theorem sigma_pow_le_window_factor {p p₀ k : Nat} (hp : p.Prime) (hp₀ : 2 ≤ p₀)
    (hple : p₀ ≤ p) :
    σ₁ (p ^ k) * (p₀ - 1) ≤ p ^ k * p₀ := by
  have hp2 : 2 ≤ p := hp.two_le
  have h_pdvd : (p - 1) ∣ (p ^ (k + 1) - 1) := Nat.sub_one_dvd_pow_sub_one p (k + 1)
  have h_eq : σ₁ (p^k) * (p - 1) = p^(k+1) - 1 := by
    rw [sigma_one_apply_prime_pow' hp, Nat.div_mul_cancel h_pdvd]
  have hpk_pos : 1 ≤ p^k := Nat.one_le_pow _ _ hp.pos
  have hpk1_pos : 1 ≤ p^(k+1) := Nat.one_le_pow _ _ hp.pos
  have hk : p^(k+1) = p * p^k := by rw [pow_succ, mul_comm]
  refine Nat.le_of_mul_le_mul_right ?_ (by omega : 0 < p - 1)
  rw [mul_assoc, mul_comm (p₀ - 1) (p - 1), ← mul_assoc, h_eq, hk]
  -- Goal: (p * p^k - 1) * (p₀ - 1) ≤ p^k * p₀ * (p - 1)
  set x := p^k with hx
  have hpx_ge_p₀ : p₀ ≤ p * x :=
    le_trans hple (Nat.le_mul_of_pos_right _ (by omega))
  zify [show 1 ≤ p * x from by nlinarith, show 1 ≤ p₀ from by omega,
        show 1 ≤ p from by omega]
  nlinarith [hpk_pos, hple, hp₀, hp2]

/-- `primesProdM1 front B ≤ primesProd front B` since each factor `(p-1) ≤ p`. -/
private theorem primesProdM1_le_primesProd (front B : Nat) :
    primesProdM1 front B ≤ primesProd front B := by
  unfold primesProdM1 primesProd
  apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
  intros i _
  rcases lt_or_ge i primes.size with hi | hi
  · rw [Array.getElem?_eq_getElem hi, Option.getD_some, Option.getD_some]; omega
  · rw [Array.getElem?_eq_none hi, Option.getD_none, Option.getD_none]

/-- `primesProd` is positive: each factor is at least `1`. -/
private theorem primesProd_pos (front B : Nat) : 1 ≤ primesProd front B := by
  unfold primesProd
  apply Finset.one_le_prod'
  intros i _
  rcases lt_or_ge i primes.size with hi | hi
  · rw [Array.getElem?_eq_getElem hi, Option.getD_some]
    exact (primes_prime_of_mem _ (Array.getElem_mem hi)).one_le
  · rw [Array.getElem?_eq_none hi, Option.getD_none]

/-- `primesProdM1` is positive when each factor is in range. For out-of-range indices the
factor is `1`. For in-range indices `primes[i] - 1 ≥ 1` since primes are `≥ 2`. -/
private theorem primesProdM1_pos (front B : Nat) : 1 ≤ primesProdM1 front B := by
  unfold primesProdM1
  apply Finset.one_le_prod'
  intros i _
  rcases lt_or_ge i primes.size with hi | hi
  · rw [Array.getElem?_eq_getElem hi, Option.getD_some]
    have := (primes_prime_of_mem _ (Array.getElem_mem hi)).two_le
    omega
  · rw [Array.getElem?_eq_none hi, Option.getD_none]; omega

/-- Factoring `primesProd` at a valid index `front`. -/
private theorem primesProd_succ_front {front B : Nat} (h : front < primes.size)
    (hB : front ≤ B) :
    primesProd front B = primes[front] * primesProd (front + 1) B := by
  unfold primesProd
  rw [← Finset.prod_Ico_consecutive _ (Nat.le_succ front) (by omega : front + 1 ≤ B + 1)]
  rw [show Finset.Ico front (front + 1) = {front} from by
    ext x; rw [Finset.mem_Ico, Finset.mem_singleton]; omega]
  rw [Finset.prod_singleton, Array.getElem?_eq_getElem h, Option.getD_some]

/-- Factoring `primesProdM1` at a valid index `front`. -/
private theorem primesProdM1_succ_front {front B : Nat} (h : front < primes.size)
    (hB : front ≤ B) :
    primesProdM1 front B = (primes[front] - 1) * primesProdM1 (front + 1) B := by
  unfold primesProdM1
  rw [← Finset.prod_Ico_consecutive _ (Nat.le_succ front) (by omega : front + 1 ≤ B + 1)]
  rw [show Finset.Ico front (front + 1) = {front} from by
    ext x; rw [Finset.mem_Ico, Finset.mem_singleton]; omega]
  rw [Finset.prod_singleton, Array.getElem?_eq_getElem h, Option.getD_some]

/-- A prime exceeding the last table entry is at least 229 (the next prime after 227). -/
private theorem prime_ge_229_of_gt {q : Nat} (hp : q.Prime) (hq : 227 < q) : 229 ≤ q := by
  have h228 : ¬ Nat.Prime 228 := by
    rw [Nat.prime_def]; push Not; intro hge; refine ⟨2, ?_, ?_, ?_⟩ <;> decide
  by_contra hlt
  push Not at hlt
  -- 228 ≤ q < 229, so q = 228.
  have : q = 228 := by omega
  rw [this] at hp
  exact h228 hp

/-- The largest entry of `primes` is 227. -/
private theorem primes_last : primes[primes.size - 1]'(by decide) = 227 := by decide

/-- "Consecutive primes" property: any prime `q > primes[i]` with `i + 1 < primes.size`,
`primes[i+1] ≤ q`. -/
private theorem primes_consecutive {i : Nat} (hi : i < primes.size) {q : Nat}
    (hp : q.Prime) (hq : primes[i] < q) (hi1 : i + 1 < primes.size) :
    primes[i + 1] ≤ q := by
  by_cases h : q ≤ 227
  · have hq_in : q ∈ primes.toList := prime_in_primes q h hp
    rw [List.mem_iff_getElem] at hq_in
    obtain ⟨j, hj, hjeq⟩ := hq_in
    simp only [Array.length_toList] at hj
    rw [Array.getElem_toList] at hjeq
    have hji : i < j := by
      by_contra hji
      push Not at hji
      have : primes[j] ≤ primes[i] := primes_le_of_le hji hi
      omega
    have hji1 : i + 1 ≤ j := hji
    have : primes[i + 1] ≤ primes[j] := primes_le_of_le hji1 hj
    omega
  · push Not at h
    have hq229 : 229 ≤ q := prime_ge_229_of_gt hp h
    have hi1_le : primes[i + 1] ≤ primes[primes.size - 1]'(by decide) :=
      primes_le_of_le (by omega) (by decide)
    rw [primes_last] at hi1_le
    omega

/-- Main sigma window bound: `σ₁(t) * Π'(front, B) ≤ t * Π(front, B)` for `t ∈ P front`
with at most `B - front + 1` distinct primes. -/
private theorem sigma_bound_window :
    ∀ (t : Nat) (front B : Nat),
      1 ≤ t → t ∈ P front → B + 1 ≤ primes.size →
      t.primeFactors.card + front ≤ B + 1 →
      σ₁ t * primesProdM1 front B ≤ t * primesProd front B := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intros front B ht hP hBsize hcard
    by_cases ht1 : t = 1
    · subst ht1
      have hσ : σ₁ 1 = 1 := by simp
      rw [hσ, one_mul, one_mul]
      exact primesProdM1_le_primesProd _ _
    have ht2 : 2 ≤ t := by omega
    have htne : t ≠ 0 := by omega
    -- Get smallest prime p of t
    set p := t.minFac with hp_def
    have hp_prime : p.Prime := Nat.minFac_prime ht1
    have hp_dvd : p ∣ t := Nat.minFac_dvd t
    have hp_two_le : 2 ≤ p := hp_prime.two_le
    -- Get k = factorization of t at p
    set k := t.factorization p with hk_def
    have hpk_dvd : p^k ∣ t := Nat.ordProj_dvd t p
    have hpk_t : p^k * (t / p^k) = t := Nat.mul_div_cancel_left' hpk_dvd
    set t' := t / p^k with ht'_def
    have hcoprime : Nat.Coprime p t' := Nat.coprime_ordCompl hp_prime htne
    -- From hP: primes[front]? = some p0 with p0 ≤ p
    obtain ⟨p0, hp0_eq, hp0_le_p⟩ := hP.2 p hp_prime hp_dvd
    have hfront_lt : front < primes.size := by
      by_contra h
      rw [Array.getElem?_eq_none (Nat.not_lt.mp h)] at hp0_eq
      injection hp0_eq
    rw [Array.getElem?_eq_getElem hfront_lt] at hp0_eq
    have hp0_val : p0 = primes[front] := Option.some.inj hp0_eq.symm
    rw [hp0_val] at hp0_le_p
    have hp_geprimes : primes[front] ≤ p := hp0_le_p
    have hpf_prime : (primes[front]).Prime :=
      primes_prime_of_mem _ (Array.getElem_mem hfront_lt)
    have hpf_two_le : 2 ≤ primes[front] := hpf_prime.two_le
    -- k ≥ 1
    have hk_pos : 1 ≤ k := by
      rw [hk_def, ← (hp_prime.pow_dvd_iff_le_factorization htne)]
      simpa using hp_dvd
    have hpk_ge2 : 2 ≤ p^k := by
      calc 2 ≤ p := hp_two_le
        _ = p^1 := (pow_one p).symm
        _ ≤ p^k := Nat.pow_le_pow_right hp_prime.one_lt.le hk_pos
    -- t' ≥ 1, t' < t
    have ht'_pos : 1 ≤ t' := by
      rcases Nat.eq_zero_or_pos t' with h | h
      · rw [h, mul_zero] at hpk_t; omega
      · exact h
    have ht'_lt : t' < t := by
      have ht_eq : t = p^k * t' := hpk_t.symm
      have : t' * 1 < t' * p^k := Nat.mul_lt_mul_of_pos_left hpk_ge2 ht'_pos
      rw [mul_one] at this
      calc t' = t' * 1 := (mul_one t').symm
        _ < t' * p^k := Nat.mul_lt_mul_of_pos_left hpk_ge2 ht'_pos
        _ = p^k * t' := mul_comm _ _
        _ = t := hpk_t
    -- B ≥ front (since t has ≥ 1 prime, card ≥ 1, so B + 1 ≥ front + 1)
    have h_card_pos : 1 ≤ t.primeFactors.card := by
      rw [Nat.one_le_iff_ne_zero, Finset.card_ne_zero]
      exact ⟨p, by rw [Nat.mem_primeFactors]; exact ⟨hp_prime, hp_dvd, htne⟩⟩
    have hBfront : front ≤ B := by omega
    -- Apply IH to t' at (front + 1, B)
    -- First show t' ∈ P (front + 1)
    have ht'_P : t' ∈ P (front + 1) := by
      refine ⟨ht'_pos, ?_⟩
      intros q hq_prime hq_dvd
      have hq_dvd_t : q ∣ t := by
        rw [← hpk_t]
        exact dvd_mul_of_dvd_right hq_dvd _
      have hq_ne_p : q ≠ p := by
        intro h
        subst h
        -- p ∣ t', but gcd(p, t') = 1, so p = 1, contradicting prime.
        have hp1 : p ∣ 1 := hcoprime.dvd_of_dvd_mul_left (by rw [mul_one]; exact hq_dvd)
        exact hq_prime.one_lt.ne' (Nat.dvd_one.mp hp1)
      have hq_ge_p : q ≥ p := Nat.minFac_le_of_dvd hq_prime.two_le hq_dvd_t
      have hq_gt_p : q > p := lt_of_le_of_ne hq_ge_p (Ne.symm hq_ne_p)
      have hq_gt_pf : q > primes[front] := lt_of_le_of_lt hp_geprimes hq_gt_p
      by_cases hf1 : front + 1 < primes.size
      · refine ⟨primes[front + 1], ?_, ?_⟩
        · rw [Array.getElem?_eq_getElem hf1]
        · exact primes_consecutive hfront_lt hq_prime hq_gt_pf hf1
      · push Not at hf1
        -- front + 1 ≥ primes.size, derive contradiction from #primes ≥ 2 vs window size
        exfalso
        have h_two_primes : 2 ≤ t.primeFactors.card := by
          have hp_in : p ∈ t.primeFactors := by
            rw [Nat.mem_primeFactors]; exact ⟨hp_prime, hp_dvd, htne⟩
          have hq_in : q ∈ t.primeFactors := by
            rw [Nat.mem_primeFactors]; exact ⟨hq_prime, hq_dvd_t, htne⟩
          have hpq_subset : ({p, q} : Finset Nat) ⊆ t.primeFactors := by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact hp_in
            · rw [Finset.mem_singleton] at hx; subst hx; exact hq_in
          have := Finset.card_le_card hpq_subset
          rw [Finset.card_insert_of_notMem (by simp [Ne.symm hq_ne_p]),
              Finset.card_singleton] at this
          omega
        omega
    -- Now show #primeFactors of t' is bounded
    have hcard' : t'.primeFactors.card + (front + 1) ≤ B + 1 := by
      have ht'_dvd_t : t' ∣ t := by
        rw [← hpk_t]; exact dvd_mul_left _ _
      have ht'_pf_subset : t'.primeFactors ⊆ t.primeFactors :=
        Nat.primeFactors_mono ht'_dvd_t htne
      have hp_not_t' : p ∉ t'.primeFactors := by
        rw [Nat.mem_primeFactors]
        intro ⟨_, hpdvd, _⟩
        have : p ∣ 1 := hcoprime.dvd_of_dvd_mul_left (by rw [mul_one]; exact hpdvd)
        exact hp_prime.one_lt.ne' (Nat.dvd_one.mp this)
      have hp_in_t : p ∈ t.primeFactors := by
        rw [Nat.mem_primeFactors]; exact ⟨hp_prime, hp_dvd, htne⟩
      have ht'_pf_card : t'.primeFactors.card ≤ t.primeFactors.card - 1 := by
        have : t'.primeFactors ⊆ t.primeFactors.erase p := by
          intro x hx
          rw [Finset.mem_erase]
          refine ⟨?_, ht'_pf_subset hx⟩
          intro hxp; subst hxp; exact hp_not_t' hx
        have := Finset.card_le_card this
        rw [Finset.card_erase_of_mem hp_in_t] at this
        exact this
      omega
    have IH := ih t' ht'_lt _ _ ht'_pos ht'_P hBsize hcard'
    -- Combine: σ(t) = σ(p^k) * σ(t')
    have hσmul : σ₁ t = σ₁ (p^k) * σ₁ t' := by
      rw [← hpk_t]
      exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcoprime.pow_left k)
    -- Factor Π and Π' at front
    have h_pi : primesProd front B = primes[front] * primesProd (front + 1) B :=
      primesProd_succ_front hfront_lt hBfront
    have h_pi_M1 : primesProdM1 front B = (primes[front] - 1) * primesProdM1 (front + 1) B :=
      primesProdM1_succ_front hfront_lt hBfront
    -- Sigma bound at the consumed prime
    have hcons : σ₁ (p^k) * (primes[front] - 1) ≤ p^k * primes[front] :=
      sigma_pow_le_window_factor hp_prime hpf_two_le hp_geprimes
    -- Combine: σ(t) * Π'(front, B) = σ(p^k) * σ(t') * (primes[front] - 1) * Π'(front+1, B)
    --        ≤ p^k * primes[front] * σ(t') * Π'(front+1, B)  (by sigma_pow bound)
    --        ≤ p^k * primes[front] * t' * Π(front+1, B)  (by IH)
    --        = p^k * t' * primes[front] * Π(front+1, B)
    --        = t * Π(front, B).
    calc σ₁ t * primesProdM1 front B
        = σ₁ (p^k) * σ₁ t' * ((primes[front] - 1) * primesProdM1 (front + 1) B) := by
          rw [hσmul, h_pi_M1]
      _ = (σ₁ (p^k) * (primes[front] - 1)) * (σ₁ t' * primesProdM1 (front + 1) B) := by ring
      _ ≤ (p^k * primes[front]) * (σ₁ t' * primesProdM1 (front + 1) B) :=
          Nat.mul_le_mul_right _ hcons
      _ ≤ (p^k * primes[front]) * (t' * primesProd (front + 1) B) := by
          apply Nat.mul_le_mul_left
          exact IH
      _ = (p^k * t') * (primes[front] * primesProd (front + 1) B) := by ring
      _ = t * primesProd front B := by rw [hpk_t, ← h_pi]

/-- Radical bound: `primesProd front (front + j - 1) ≤ t` for `t ∈ P front` with at least `j ≥ 1`
distinct primes, and `front + j ≤ primes.size`. Used in the wheel's `.tooLarge` case. -/
private theorem primesProd_le_t :
    ∀ (t : Nat) (front : Nat),
      1 ≤ t → t ∈ P front → ∀ j : Nat, 1 ≤ j → j ≤ t.primeFactors.card →
      front + j ≤ primes.size →
      primesProd front (front + j - 1) ≤ t := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intros front ht hP j hj hjle hsize
    have ht1 : t ≠ 1 := by
      intro h; subst h
      simp [Nat.primeFactors_one] at hjle; omega
    have ht2 : 2 ≤ t := by omega
    have htne : t ≠ 0 := by omega
    set p := t.minFac with hp_def
    have hp_prime : p.Prime := Nat.minFac_prime ht1
    have hp_dvd : p ∣ t := Nat.minFac_dvd t
    have hp_two_le : 2 ≤ p := hp_prime.two_le
    set k := t.factorization p with hk_def
    have hpk_dvd : p^k ∣ t := Nat.ordProj_dvd t p
    have hpk_t : p^k * (t / p^k) = t := Nat.mul_div_cancel_left' hpk_dvd
    set t' := t / p^k with ht'_def
    have hcoprime : Nat.Coprime p t' := Nat.coprime_ordCompl hp_prime htne
    have hk_pos : 1 ≤ k := by
      rw [hk_def, ← (hp_prime.pow_dvd_iff_le_factorization htne)]
      simpa using hp_dvd
    have hpk_ge2 : 2 ≤ p^k := by
      calc 2 ≤ p := hp_two_le
        _ = p^1 := (pow_one p).symm
        _ ≤ p^k := Nat.pow_le_pow_right hp_prime.one_lt.le hk_pos
    have ht'_pos : 1 ≤ t' := by
      rcases Nat.eq_zero_or_pos t' with h | h
      · rw [h, mul_zero] at hpk_t; omega
      · exact h
    have ht'_lt : t' < t := by
      calc t' = t' * 1 := (mul_one t').symm
        _ < t' * p^k := Nat.mul_lt_mul_of_pos_left hpk_ge2 ht'_pos
        _ = p^k * t' := mul_comm _ _
        _ = t := hpk_t
    obtain ⟨p0, hp0_eq, hp0_le_p⟩ := hP.2 p hp_prime hp_dvd
    have hfront_lt : front < primes.size := by
      by_contra h
      rw [Array.getElem?_eq_none (Nat.not_lt.mp h)] at hp0_eq
      injection hp0_eq
    rw [Array.getElem?_eq_getElem hfront_lt] at hp0_eq
    have hp0_val : p0 = primes[front] := Option.some.inj hp0_eq.symm
    rw [hp0_val] at hp0_le_p
    have hp_geprimes : primes[front] ≤ p := hp0_le_p
    have hp_in_t : p ∈ t.primeFactors := by
      rw [Nat.mem_primeFactors]; exact ⟨hp_prime, hp_dvd, htne⟩
    have hp_not_t' : p ∉ t'.primeFactors := by
      rw [Nat.mem_primeFactors]
      intro ⟨_, hpdvd, _⟩
      have : p ∣ 1 := hcoprime.dvd_of_dvd_mul_left (by rw [mul_one]; exact hpdvd)
      exact hp_prime.one_lt.ne' (Nat.dvd_one.mp this)
    have ht'_dvd_t : t' ∣ t := by
      rw [← hpk_t]; exact dvd_mul_left _ _
    have ht'_pf_subset : t'.primeFactors ⊆ t.primeFactors :=
      Nat.primeFactors_mono ht'_dvd_t htne
    rcases Nat.lt_or_ge 1 j with hj2 | hj2
    · -- j ≥ 2. Apply IH to t' at (front+1) with j' = j - 1.
      -- Show t' has ≥ j - 1 distinct primes (since t.card ≥ j ≥ 2).
      have hcard2 : 2 ≤ t.primeFactors.card := by omega
      -- t'.primeFactors = t.primeFactors \ {p}.
      have h_supeq : t.primeFactors.erase p ⊆ t'.primeFactors := by
        intro x hx
        rw [Finset.mem_erase] at hx
        obtain ⟨hxnp, hxin⟩ := hx
        rw [Nat.mem_primeFactors] at hxin ⊢
        obtain ⟨hxp, hxd, _⟩ := hxin
        refine ⟨hxp, ?_, ?_⟩
        · rw [← hpk_t] at hxd
          rcases (Nat.Prime.dvd_mul hxp).mp hxd with h | h
          · exfalso
            have : x = p := (Nat.Prime.eq_one_or_self_of_dvd hp_prime _
              (hxp.dvd_of_dvd_pow h)).elim (fun h => absurd h hxp.one_lt.ne') id
            exact hxnp this
          · exact h
        · intro h; rw [h, mul_zero] at hpk_t; omega
      have hsubeq : t'.primeFactors ⊆ t.primeFactors.erase p := by
        intro x hx
        rw [Finset.mem_erase]
        refine ⟨?_, ht'_pf_subset hx⟩
        intro hxp; subst hxp; exact hp_not_t' hx
      have ht'_card_eq : t'.primeFactors.card = t.primeFactors.card - 1 := by
        have := Finset.Subset.antisymm h_supeq hsubeq
        rw [← this, Finset.card_erase_of_mem hp_in_t]
      have ht'_in_P : t' ∈ P (front + 1) := by
        refine ⟨ht'_pos, ?_⟩
        intros q hq_prime hq_dvd
        have hq_dvd_t : q ∣ t := by
          rw [← hpk_t]; exact dvd_mul_of_dvd_right hq_dvd _
        have hq_ne_p : q ≠ p := by
          intro h; subst h
          have hp1 : p ∣ 1 := hcoprime.dvd_of_dvd_mul_left (by rw [mul_one]; exact hq_dvd)
          exact hq_prime.one_lt.ne' (Nat.dvd_one.mp hp1)
        have hq_ge_p : q ≥ p := Nat.minFac_le_of_dvd hq_prime.two_le hq_dvd_t
        have hq_gt_pf : q > primes[front] := lt_of_le_of_lt hp_geprimes
          (lt_of_le_of_ne hq_ge_p (Ne.symm hq_ne_p))
        have hf1 : front + 1 < primes.size := by omega
        refine ⟨primes[front + 1], ?_, primes_consecutive hfront_lt hq_prime hq_gt_pf hf1⟩
        rw [Array.getElem?_eq_getElem hf1]
      have hj' : 1 ≤ j - 1 := by omega
      have hjle' : j - 1 ≤ t'.primeFactors.card := by
        rw [ht'_card_eq]; omega
      have hsize' : (front + 1) + (j - 1) ≤ primes.size := by omega
      have IH := ih t' ht'_lt _ ht'_pos ht'_in_P (j - 1) hj' hjle' hsize'
      have h_idx : (front + 1) + (j - 1) - 1 = front + j - 1 := by omega
      rw [h_idx] at IH
      have hpk_ge : primes[front] ≤ p^k := by
        calc primes[front] ≤ p := hp_geprimes
          _ = p^1 := (pow_one p).symm
          _ ≤ p^k := Nat.pow_le_pow_right hp_prime.one_lt.le hk_pos
      have h_pp : primesProd front (front + j - 1) =
                  primes[front] * primesProd (front + 1) (front + j - 1) :=
        primesProd_succ_front hfront_lt (by omega : front ≤ front + j - 1)
      calc primesProd front (front + j - 1)
          = primes[front] * primesProd (front + 1) (front + j - 1) := h_pp
        _ ≤ p^k * primesProd (front + 1) (front + j - 1) :=
            Nat.mul_le_mul_right _ hpk_ge
        _ ≤ p^k * t' := Nat.mul_le_mul_left _ IH
        _ = t := hpk_t
    · -- j = 1
      have hj1 : j = 1 := by omega
      rw [hj1]
      simp only [Nat.add_sub_cancel]
      rw [primesProd_self hfront_lt]
      calc primes[front] ≤ p := hp_geprimes
        _ = p^1 := (pow_one p).symm
        _ ≤ p^k := Nat.pow_le_pow_right hp_prime.one_lt.le hk_pos
        _ ≤ p^k * t' := Nat.le_mul_of_pos_right _ ht'_pos
        _ = t := hpk_t

/-- Helper: from `lhs < rhs` at the wheel state (front ≤ back, with invariants),
derive `m * primesProd front back < target * primesProdM1 front back`. -/
private theorem wheel_strict_inequality {m target front back lhs rhs : Nat}
    (hlhs : lhs = m * primesProd front back) (hrhs : rhs = target * primesProdM1 front back)
    (h : lhs < rhs) :
    m * primesProd front back < target * primesProdM1 front back := by
  rw [hlhs, hrhs] at h; exact h

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
  have hm_pos : 1 ≤ m := by
    have ht_pos : 0 < t := by omega
    omega
  have hpsucc : primesProd front (back + 1) = primesProd front back * primes[back+1] := by
    rw [primesProd_succ (by omega : front ≤ back + 1),
        Array.getElem?_eq_getElem hback_lt, Option.getD_some]
  have hppsm : m < primesProd front (back + 1) := by
    have h1 : m * primesProd front (back + 1) > m * m := by
      rw [hpsucc, ← mul_assoc, ← hlhs]; exact hbig
    exact (Nat.mul_lt_mul_left (by omega : 0 < m)).mp (by rw [mul_comm m m] at h1; exact h1)
  rcases Nat.lt_or_ge t.primeFactors.card (back + 2 - front) with hcard | hcard
  · have hcard_le : t.primeFactors.card + front ≤ back + 1 := by omega
    have hBsize : back + 1 ≤ primes.size := by omega
    have hsigma := sigma_bound_window t front back (by omega) htP hBsize hcard_le
    have h_wheel := wheel_strict_inequality hlhs hrhs hsmall
    -- σ(t) * primesProdM1 ≤ t * primesProd ≤ m * primesProd < target * primesProdM1
    have h_chain : σ₁ t * primesProdM1 front back < target * primesProdM1 front back := by
      calc σ₁ t * primesProdM1 front back
          ≤ t * primesProd front back := hsigma
        _ ≤ m * primesProd front back := Nat.mul_le_mul_right _ htm
        _ < target * primesProdM1 front back := h_wheel
    have hppm_pos : 0 < primesProdM1 front back := primesProdM1_pos _ _
    have := Nat.lt_of_mul_lt_mul_right h_chain
    omega
  · have hj : 1 ≤ back + 2 - front := by omega
    have hjle : back + 2 - front ≤ t.primeFactors.card := hcard
    have hsize : front + (back + 2 - front) ≤ primes.size := by omega
    have hrad := primesProd_le_t t front (by omega) htP (back + 2 - front) hj hjle hsize
    have h_idx : front + (back + 2 - front) - 1 = back + 1 := by omega
    rw [h_idx] at hrad
    omega

/-- At a wheel `.tooLarge` empty-window state with `front < primes.size`, the witness `t`
with `t ≤ m`, `t ∈ P front`, `t ≥ 2` gives `False`. The condition `lhs * primes[front] > m*m`
with `lhs = m` implies `primes[front] > m`, but `t ≥ primes[front]`. -/
private theorem extend_tooLarge_empty_contradiction
    {m front back lhs : Nat} {t : Nat}
    (hlhs : lhs = m * primesProd front back) (hfront : front ≤ back + 1)
    (hfront_lt : front < primes.size)
    (hempty : back + 1 = front)
    (hbig : lhs * primes[front] > m * m)
    (ht2 : 2 ≤ t) (htP : t ∈ P front) (htm : t ≤ m) : False := by
  have hp_empty : primesProd front back = 1 := primesProd_empty (by omega)
  rw [hp_empty, mul_one] at hlhs
  rw [hlhs] at hbig
  have hm_pos : 1 ≤ m := by omega
  have hpf_gt : primes[front] > m :=
    (Nat.mul_lt_mul_left (by omega : 0 < m)).mp (by rw [mul_comm m m] at hbig; exact hbig)
  obtain ⟨p0, hp0_eq, hp0_le⟩ := htP.2 _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd t)
  rw [Array.getElem?_eq_getElem hfront_lt] at hp0_eq
  have hp0v : p0 = primes[front] := Option.some.inj hp0_eq.symm
  rw [hp0v] at hp0_le
  have hmf_le_t : t.minFac ≤ t := Nat.minFac_le (by omega : 0 < t)
  omega

/-- The main `.tooLarge` invariant: if `t` is a witness, `extendWF` cannot return `.tooLarge`.
Proved by induction over `extendWF`'s structure. -/
private theorem extendWF_ne_tooLarge_of_witness
    (m target front t : Nat)
    (ht2 : 2 ≤ t) (htP : t ∈ P front) (htm : t ≤ m) (htσ : target ≤ σ₁ t)
    (hfront_lt : front < primes.size) :
    ∀ (back lhs rhs : Nat),
      lhs = m * primesProd front back →
      rhs = target * primesProdM1 front back →
      front ≤ back + 1 →
      extendWF (m * m) front back lhs rhs ≠ .tooLarge := by
  intro back lhs rhs
  induction back, lhs, rhs using extendWF.induct (m2 := m * m) (front := front) with
  | case1 back lhs rhs hf hge =>
    intros _ _ _
    rw [extendWF]; simp [hf, hge]
  | case2 back lhs rhs hf hlt hb1 _ _ hbig =>
    intros hlhs hrhs hfront _
    exact extend_tooLarge_contradiction hlhs hrhs hfront hb1
      (by omega) hbig ht2 htP htm htσ
  | case3 back lhs rhs hf hlt hb1 _ _ hle ih =>
    intros hlhs hrhs hfront
    have heq : extendWF (m * m) front back lhs rhs =
        extendWF (m * m) front (back + 1) (lhs * primes[back + 1])
          (rhs * (primes[back + 1] - 1)) := by
      conv_lhs => rw [extendWF]
      rw [if_pos hf, if_neg hlt, dif_pos hb1]
      rw [if_neg hle]
    rw [heq]
    have hlhs' : lhs * primes[back + 1] = m * primesProd front (back + 1) := by
      have hpsucc : primesProd front (back + 1) = primesProd front back * primes[back+1] := by
        rw [primesProd_succ (by omega : front ≤ back + 1),
            Array.getElem?_eq_getElem hb1, Option.getD_some]
      rw [hpsucc, hlhs]; ring
    have hrhs' : rhs * (primes[back + 1] - 1) = target * primesProdM1 front (back + 1) := by
      have hpsucc' : primesProdM1 front (back + 1) =
                     primesProdM1 front back * (primes[back+1] - 1) := by
        rw [primesProdM1_succ (by omega : front ≤ back + 1),
            Array.getElem?_eq_getElem hb1, Option.getD_some]
      rw [hpsucc', hrhs]; ring
    exact ih hlhs' hrhs' (by omega)
  | case4 back lhs rhs hf hlt hb1 =>
    intros _ _ _
    have heq : extendWF (m * m) front back lhs rhs = .exhaustedTable := by
      conv_lhs => rw [extendWF]
      simp [hf, hlt, hb1]
    rw [heq]; intro h; injection h
  | case5 back lhs rhs hf hf1 _ _ hbig =>
    intros hlhs _ hfront
    push Not at hf
    have hbsz : back + 1 = front := by omega
    intro _
    exact extend_tooLarge_empty_contradiction hlhs hfront hf1 hbsz hbig ht2 htP htm
  | case6 back lhs rhs hf hf1 _ _ hle ih =>
    intros hlhs hrhs hfront
    push Not at hf
    have heq : extendWF (m * m) front back lhs rhs =
        extendWF (m * m) front front (lhs * primes[front]) (rhs * (primes[front] - 1)) := by
      conv_lhs => rw [extendWF]
      rw [if_neg (show ¬ front ≤ back from by omega), dif_pos hf1]
      rw [if_neg hle]
    rw [heq]
    have hlhs_new : lhs * primes[front] = m * primesProd front front := by
      rw [primesProd_self hf1]
      have hpe : primesProd front back = 1 := primesProd_empty (by omega)
      rw [hpe, mul_one] at hlhs
      rw [hlhs]
    have hrhs_new : rhs * (primes[front] - 1) = target * primesProdM1 front front := by
      rw [primesProdM1_self hf1]
      have hpe : primesProdM1 front back = 1 := primesProdM1_empty (by omega)
      rw [hpe, mul_one] at hrhs
      rw [hrhs]
    exact ih hlhs_new hrhs_new (by omega)
  | case7 back lhs rhs hf hf1 =>
    intros _ _ _
    push Not at hf
    push Not at hf1
    have heq : extendWF (m * m) front back lhs rhs = .exhaustedTable := by
      conv_lhs => rw [extendWF]
      simp [show ¬ front ≤ back from by omega, show ¬ front < primes.size from by omega]
    rw [heq]; intro h; injection h

/-! ### Skeleton for `children_spec`

* `mem_children`: structural characterization of `cs` — every `c ∈ cs` has the
  form `(⌈target / σ₁(p^k)⌉, num * p^k, i+1)` for some `i ≥ minIdx`, `k ≥ 1`,
  `p^k ≤ B/num`. Proved.
* `child_witness_to_parent`: lifts a child's witness `t'` to the parent's
  witness `primes[i]^k * t'`. Proved.
* `witness_to_child`: the harder direction — given a non-trivial parent
  witness `t`, some child in `cs` has a witness. Proved via the inductive
  `wheelChildrenWF_witness` (off-table primes are handled by the σ/radical
  bounds in `extendWF_ne_tooLarge_of_witness`). -/

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
    by_cases hpm : p ^ k₀ > m
    · simp [hpm] at hc
    · simp only [hpm, if_false] at hc
      have hspk_eq : (p ^ k₀ * p - 1) / (p - 1) = σ₁ (p ^ k₀) := by
        rw [← pow_succ, ← sigma_one_apply_prime_pow' hp]
      by_cases hge : (p ^ k₀ * p - 1) / (p - 1) ≥ target
      · simp only [hge, if_true, List.mem_singleton] at hc
        refine ⟨k₀, le_refl _, by omega, ?_⟩
        rw [hc, hspk_eq]
      · simp only [hge, if_false, List.mem_cons] at hc
        rcases hc with rfl | hc
        · refine ⟨k₀, le_refl _, by omega, ?_⟩
          rw [hspk_eq]
        · have hpow : p ^ k₀ * p = p ^ (k₀ + 1) := (pow_succ p k₀).symm
          rw [hpow] at hc
          obtain ⟨k, hk, hpkm, hceq⟩ := ih (by omega : 1 ≤ k₀ + 1) hc
          exact ⟨k, by omega, hpkm, hceq⟩

/-- Every entry of `wheelChildrenWF`'s output has the prime-power form. -/
private theorem mem_wheelChildrenWF
    {m2 m target num : Nat} {front back lhs rhs : Nat}
    {L : List (Nat × Nat × Nat)}
    (h : wheelChildrenWF m2 m target num front back lhs rhs = some L)
    {c : Nat × Nat × Nat} (hc : c ∈ L) :
    ∃ i p k, front ≤ i ∧ primes[i]? = some p ∧ 1 ≤ k ∧
      p ^ k ≤ m ∧
      c = (ceilDiv target (σ₁ (p ^ k)), num * p ^ k, i + 1) := by
  revert L c
  induction front, back, lhs, rhs using wheelChildrenWF.induct
    (m2 := m2) (m := m) (target := target) (num := num) with
  | case1 front back lhs rhs hfront =>
    intro L h c hc
    rw [wheelChildrenWF] at h
    simp [hfront] at h
  | case2 front back lhs rhs hfront hext =>
    intro L h c hc
    rw [wheelChildrenWF] at h
    simp [hfront, hext] at h
  | case3 front back lhs rhs hfront hext =>
    intro L h c hc
    rw [wheelChildrenWF] at h
    simp only [hfront, dif_neg, not_false_eq_true, hext] at h
    obtain rfl : ([] : List (Nat × Nat × Nat)) = L := Option.some.inj h
    cases hc
  | case4 front back lhs rhs hfront b lhs' rhs' hext _ hrec =>
    intro L h c hc
    rw [wheelChildrenWF] at h
    simp only [hfront, dif_neg, not_false_eq_true, hext] at h
    rw [hrec] at h
    cases h
  | case5 front back lhs rhs hfront b lhs' rhs' hext _ rest hrec =>
    rename_i ih
    intro L h c hc
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
      have hc' : c ∈ expChildren (m + 1) target num (front + 1) m primes[front]
          (primes[front] ^ 1) := by rw [pow_one]; exact hcexp
      obtain ⟨k, hk, hpkm, hceq⟩ := mem_expChildren hp (le_refl 1) hc'
      refine ⟨front, primes[front], k, le_refl _, ?_, hk, hpkm, hceq⟩
      rw [Array.getElem?_eq_getElem hpf]

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
  · rename_i p0 hp0
    -- h is now the (reduced) wheelChildren call = some cs
    have hfuel : primes.size + 1 - minIdx ≤ primes.size + 1 := by omega
    rw [wheelChildren_eq_wheelChildrenWF hfuel] at h
    -- h : (wheelChildrenWF ...).map (· ++ []) = some cs
    generalize hWF :
      wheelChildrenWF (B / num * (B / num)) (B / num) target num minIdx minIdx
        (p0 * (B / num)) (target * (p0 - 1)) = wf at h
    match wf, hWF, h with
    | some L, hWF, h =>
      simp at h
      subst h
      exact mem_wheelChildrenWF hWF hc

/-- If `t'` is a witness of the child `(⌈target / σ₁(p^k)⌉, num * p^k, i+1)`
where `primes[i]? = some p`, then `p^k * t'` is a non-trivial witness of the
parent `(target, num, minIdx)`. -/
private theorem child_witness_to_parent {B target num minIdx i p k : Nat}
    (hmi : minIdx ≤ i) (hp : primes[i]? = some p) (hk : 1 ≤ k) {t' : Nat}
    (ht' : t' ∈ W B (ceilDiv target (σ₁ (p ^ k))) (num * p ^ k) (i + 1)) :
    p ^ k * t' ∈ W B target num minIdx ∧ p ^ k * t' ≠ 1 := by
  obtain ⟨⟨ht'1, ht'P⟩, ht'lt, ht'σ⟩ := ht'
  have hpPrime : p.Prime := primes_prime hp
  have hp2 : 2 ≤ p := hpPrime.two_le
  have hpk_ge2 : 2 ≤ p ^ k := by
    calc 2 ≤ p := hp2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk
  have hne1 : p ^ k * t' ≠ 1 := by
    have : 2 ≤ p ^ k * t' :=
      calc 2 ≤ p ^ k := hpk_ge2
        _ ≤ p ^ k * t' := Nat.le_mul_of_pos_right _ ht'1
    omega
  -- Extract i < primes.size and primes[i] = p.
  have hi : i < primes.size := by
    by_contra h
    rw [Array.getElem?_eq_none (Nat.not_lt.mp h)] at hp
    injection hp
  have hp_eq : primes[i] = p := by
    rw [Array.getElem?_eq_getElem hi] at hp; exact Option.some.inj hp
  have hmi_lt : minIdx < primes.size := by omega
  -- For the coprime argument: any prime factor of t' is ≥ primes[i+1] > p, so p ∤ t'.
  have hp_not_dvd : ¬ p ∣ t' := by
    intro hpdvd
    obtain ⟨p', hp', hple⟩ := ht'P p hpPrime hpdvd
    have hip1 : i + 1 < primes.size := by
      by_contra h
      rw [Array.getElem?_eq_none (Nat.not_lt.mp h)] at hp'
      injection hp'
    rw [Array.getElem?_eq_getElem hip1] at hp'
    have hp'_eq : primes[i + 1] = p' := Option.some.inj hp'
    have hlt : primes[i] < primes[i + 1] := primes_lt_of_lt (Nat.lt_succ_self i) hip1
    omega
  have hcop : Nat.Coprime (p ^ k) t' :=
    (hpPrime.coprime_iff_not_dvd.mpr hp_not_dvd).pow_left _
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, hne1⟩
  · -- 1 ≤ p^k * t'
    have : 2 ≤ p ^ k * t' :=
      calc 2 ≤ p ^ k := hpk_ge2
        _ ≤ p ^ k * t' := Nat.le_mul_of_pos_right _ ht'1
    omega
  · -- ∀ q prime, q ∣ p^k * t' → ∃ p'', primes[minIdx]? = some p'' ∧ p'' ≤ q
    intro q hqPrime hqDvd
    refine ⟨primes[minIdx], Array.getElem?_eq_getElem hmi_lt, ?_⟩
    rcases hqPrime.dvd_mul.mp hqDvd with h1 | h2
    · -- q ∣ p^k, so q = p. Need primes[minIdx] ≤ p = primes[i].
      have hqeqp : q = p :=
        (Nat.prime_dvd_prime_iff_eq hqPrime hpPrime).mp (hqPrime.dvd_of_dvd_pow h1)
      subst hqeqp
      rw [← hp_eq]; exact primes_le_of_le hmi hi
    · -- q ∣ t': by ht'P, q ≥ primes[i+1] > primes[minIdx].
      obtain ⟨p', hp', hple⟩ := ht'P q hqPrime h2
      by_cases hip1 : i + 1 < primes.size
      · rw [Array.getElem?_eq_getElem hip1] at hp'
        have hp'_eq : primes[i + 1] = p' := Option.some.inj hp'
        have : primes[minIdx] ≤ primes[i + 1] := primes_le_of_le (by omega) hip1
        omega
      · rw [Array.getElem?_eq_none (Nat.not_lt.mp hip1)] at hp'; injection hp'
  · -- num * (p^k * t') < B
    rw [← Nat.mul_assoc]
    exact ht'lt
  · -- target ≤ σ₁ (p^k * t')
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop]
    have hσpk_pos : 0 < σ₁ (p ^ k) := ArithmeticFunction.sigma_pos _ _ (by positivity)
    have hceil : target ≤ σ₁ (p ^ k) * ceilDiv target (σ₁ (p ^ k)) := by
      simp [ceilDiv]
      have := Nat.div_add_mod (target + σ₁ (p ^ k) - 1) (σ₁ (p ^ k))
      have := Nat.mod_lt (target + σ₁ (p ^ k) - 1) hσpk_pos
      omega
    calc target ≤ σ₁ (p ^ k) * ceilDiv target (σ₁ (p ^ k)) := hceil
      _ ≤ σ₁ (p ^ k) * σ₁ t' := Nat.mul_le_mul_left _ ht'σ

/-- When `extendWF` returns `.window`, the new `(b, lhs', rhs')` satisfy the wheel invariants
shifted to `b`, and `b ≥ back`. -/
private theorem extendWF_window_invariant
    (m target front : Nat) :
    ∀ (back lhs rhs : Nat) (b lhs' rhs' : Nat),
      lhs = m * primesProd front back →
      rhs = target * primesProdM1 front back →
      front ≤ back + 1 →
      extendWF (m * m) front back lhs rhs = Wheel.window b lhs' rhs' →
      lhs' = m * primesProd front b ∧
      rhs' = target * primesProdM1 front b ∧
      back ≤ b ∧ front ≤ b := by
  intro back lhs rhs b lhs' rhs'
  induction back, lhs, rhs using extendWF.induct (m2 := m * m) (front := front) with
  | case1 back lhs rhs hf hge =>
    intros hlhs hrhs _ heq
    rw [extendWF] at heq
    simp [hf, hge] at heq
    obtain ⟨hb, hl, hr⟩ := heq
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hl, hlhs, hb]
    · rw [← hr, hrhs, hb]
    · omega
    · omega
  | case2 _ _ _ hf hlt hb1 _ _ hbig =>
    intros _ _ _ heq
    rw [extendWF] at heq
    rw [if_pos hf, if_neg hlt, dif_pos hb1, if_pos hbig] at heq
    cases heq
  | case3 back lhs rhs hf hlt hb1 _ _ hle ih =>
    intros hlhs hrhs hfront heq
    have heq2 : extendWF (m * m) front (back + 1) (lhs * primes[back + 1])
        (rhs * (primes[back + 1] - 1)) = Wheel.window b lhs' rhs' := by
      conv_lhs at heq => rw [extendWF]
      rw [if_pos hf, if_neg hlt, dif_pos hb1, if_neg hle] at heq
      exact heq
    have hlhs_new : lhs * primes[back + 1] = m * primesProd front (back + 1) := by
      have hpsucc : primesProd front (back + 1) = primesProd front back * primes[back+1] := by
        rw [primesProd_succ (by omega : front ≤ back + 1),
            Array.getElem?_eq_getElem hb1, Option.getD_some]
      rw [hpsucc, hlhs]; ring
    have hrhs_new : rhs * (primes[back + 1] - 1) = target * primesProdM1 front (back + 1) := by
      have hpsucc' : primesProdM1 front (back + 1) =
                     primesProdM1 front back * (primes[back+1] - 1) := by
        rw [primesProdM1_succ (by omega : front ≤ back + 1),
            Array.getElem?_eq_getElem hb1, Option.getD_some]
      rw [hpsucc', hrhs]; ring
    have IH := ih hlhs_new hrhs_new (by omega) heq2
    refine ⟨IH.1, IH.2.1, ?_, IH.2.2.2⟩
    omega
  | case4 _ _ _ hf hlt hb1 =>
    intros _ _ _ heq
    rw [extendWF] at heq
    push Not at hb1
    rw [if_pos hf, if_neg hlt, dif_neg (by omega)] at heq
    cases heq
  | case5 _ _ _ hf hf1 _ _ hbig =>
    intros _ _ _ heq
    rw [extendWF] at heq
    rw [if_neg hf, dif_pos hf1, if_pos hbig] at heq
    cases heq
  | case6 back lhs rhs hf hf1 _ _ hle ih =>
    intros hlhs hrhs hfront heq
    push Not at hf
    have heq2 : extendWF (m * m) front front (lhs * primes[front]) (rhs * (primes[front] - 1)) =
        Wheel.window b lhs' rhs' := by
      conv_lhs at heq => rw [extendWF]
      rw [if_neg (show ¬ front ≤ back from by omega), dif_pos hf1, if_neg hle] at heq
      exact heq
    have hlhs_new : lhs * primes[front] = m * primesProd front front := by
      rw [primesProd_self hf1]
      have hpe : primesProd front back = 1 := primesProd_empty (by omega)
      rw [hpe, mul_one] at hlhs
      rw [hlhs]
    have hrhs_new : rhs * (primes[front] - 1) = target * primesProdM1 front front := by
      rw [primesProdM1_self hf1]
      have hpe : primesProdM1 front back = 1 := primesProdM1_empty (by omega)
      rw [hpe, mul_one] at hrhs
      rw [hrhs]
    have IH := ih hlhs_new hrhs_new (by omega) heq2
    refine ⟨IH.1, IH.2.1, ?_, IH.2.2.2⟩
    omega
  | case7 _ _ _ hf hf1 =>
    intros _ _ _ heq
    rw [extendWF] at heq
    push Not at hf; push Not at hf1
    rw [if_neg (show ¬ front ≤ _ from by omega), dif_neg (by omega)] at heq
    cases heq
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
    simp only [expChildren]
    rw [if_neg (by omega : ¬ pk > m)]
    rw [if_neg (by omega : ¬ (pk * p - 1) / (p - 1) ≥ target)]
    rfl

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
    simp only [expChildren]
    rw [if_neg (by omega : ¬ pk > m)]
    rw [if_pos hsig_ge]

/-- When `m = 0` (so `m2 = 0`) and `lhs = 0`, `extendWF` cannot return `.tooLarge`. -/
private theorem extendWF_zero_lhs_no_tooLarge (front : Nat) :
    ∀ (back lhs rhs : Nat), lhs = 0 →
      extendWF 0 front back lhs rhs ≠ Wheel.tooLarge := by
  intro back lhs rhs
  induction back, lhs, rhs using extendWF.induct (m2 := 0) (front := front) with
  | case1 back lhs rhs hf hge =>
    intros _ heq; rw [extendWF] at heq; simp [hf, hge] at heq
  | case2 _ _ _ hf hlt hb1 _ _ hbig =>
    intros hlhs _
    subst hlhs
    omega
  | case3 back lhs rhs hf hlt hb1 _ _ hle ih =>
    intros hlhs heq
    have heq2 : extendWF 0 front (back + 1) (lhs * primes[back + 1])
        (rhs * (primes[back + 1] - 1)) = Wheel.tooLarge := by
      conv_lhs at heq => rw [extendWF]
      rw [if_pos hf, if_neg hlt, dif_pos hb1, if_neg hle] at heq
      exact heq
    have hlhs' : lhs * primes[back + 1] = 0 := by rw [hlhs]; ring
    exact ih hlhs' heq2
  | case4 _ _ _ hf hlt hb1 =>
    intros _ heq
    conv_lhs at heq => rw [extendWF]
    push Not at hb1
    rw [if_pos hf, if_neg hlt, dif_neg (by omega)] at heq
    cases heq
  | case5 _ _ _ _ hf1 _ _ hbig =>
    intros hlhs _
    subst hlhs
    omega
  | case6 back lhs rhs hf hf1 _ _ hle ih =>
    intros hlhs heq
    push Not at hf
    have heq2 : extendWF 0 front front (lhs * primes[front]) (rhs * (primes[front] - 1)) =
        Wheel.tooLarge := by
      conv_lhs at heq => rw [extendWF]
      rw [if_neg (show ¬ front ≤ back from by omega), dif_pos hf1, if_neg hle] at heq
      exact heq
    have hlhs' : lhs * primes[front] = 0 := by rw [hlhs]; ring
    exact ih hlhs' heq2
  | case7 _ _ _ hf hf1 =>
    intros _ heq
    push Not at hf; push Not at hf1
    conv_lhs at heq => rw [extendWF]
    rw [if_neg (show ¬ front ≤ _ from by omega), dif_neg (by omega)] at heq
    cases heq

/-- Helper: σ formula in expChildren's loop. -/
private theorem sigma_pow_expChildren_eq {p k : Nat} (hp : p.Prime) :
    (p^k * p - 1) / (p - 1) = σ₁ (p^k) := by
  rw [show p^k * p = p^(k+1) from by ring]
  exact (sigma_one_apply_prime_pow' hp).symm

/-- Helper: `1 ∈ P j` for any `j` since `1` has no prime factors. -/
private theorem one_mem_P (j : Nat) : 1 ∈ P j := by
  refine ⟨le_refl _, ?_⟩
  intros q hq_prime hq_dvd
  exfalso
  exact hq_prime.one_lt.ne' (Nat.dvd_one.mp hq_dvd)

/-- Walk `expChildren` from `pk₀ = p^j₀` looking for a child with a witness, given a parent
witness `t = p^k * t''` (factored at `p` with `t''` coprime to `p`). The proof iterates by
strong induction on `k - j₀`: at each step either σ(p^{j₀}) ≥ target (stop with witness `1`)
or σ < target (emit and recurse), bottoming out at `j₀ = k` with witness `t''`. -/
private theorem expChildren_witness_walk
    {B num target m p : Nat} (hp : p.Prime) (next : Nat) :
    ∀ (n : Nat), ∀ (k j₀ : Nat), k - j₀ = n → 1 ≤ j₀ → j₀ ≤ k → p^k ≤ m →
      ∀ {t'' : Nat}, 1 ≤ t'' → t'' ∈ P next → num * p^k * t'' < B →
      target ≤ σ₁ (p^k) * σ₁ t'' →
      ∀ {fuel : Nat}, n + 1 ≤ fuel →
      ∃ c ∈ expChildren fuel target num next m p (p^j₀), W B c.1 c.2.1 c.2.2 ≠ ∅ := by
  intro n
  induction n with
  | zero =>
    -- j₀ = k, base case.
    intros k j₀ hn hj₀ hj₀_k hpk_le_m t'' ht''_pos ht''_P hnumt htσ fuel hfuel
    -- j₀ = k from hn : k - j₀ = 0 and hj₀_k : j₀ ≤ k.
    have hjk : j₀ = k := by omega
    -- Rewrite j₀ to k everywhere.
    rw [hjk]
    -- expChildren emits child for j = k.
    have hp_pos : 0 < p := hp.pos
    have hp2 : 2 ≤ p := hp.two_le
    have hpk_pos : 1 ≤ p^k := Nat.one_le_pow _ _ hp_pos
    have hpk_ne_zero : p^k ≠ 0 := Nat.pos_iff_ne_zero.mp hpk_pos
    have h_sig_eq : (p^k * p - 1) / (p - 1) = σ₁ (p^k) := sigma_pow_expChildren_eq hp
    by_cases hσ_target : σ₁ (p^k) ≥ target
    · -- σ(p^k) ≥ target: only emit child for k, with witness 1.
      have h_exp : expChildren fuel target num next m p (p^k) =
          [(ceilDiv target (σ₁ (p^k)), num * p^k, next)] := by
        rw [show (ceilDiv target (σ₁ (p^k)), num * p^k, next) =
             (ceilDiv target ((p^k * p - 1) / (p - 1)), num * p^k, next) from by rw [h_sig_eq]]
        exact expChildren_stop (by omega) hpk_le_m (by rw [h_sig_eq]; exact hσ_target)
      rw [h_exp]
      refine ⟨_, List.mem_singleton.mpr rfl, Set.nonempty_iff_ne_empty.mp ⟨1, ?_⟩⟩
      refine ⟨one_mem_P _, ?_, ?_⟩
      · rw [mul_one]
        calc num * p^k ≤ num * p^k * t'' := Nat.le_mul_of_pos_right _ ht''_pos
          _ < B := hnumt
      · have hσ1 : σ₁ 1 = 1 := by simp
        rw [hσ1]
        unfold ceilDiv
        have hσpk_pos : 0 < σ₁ (p^k) := ArithmeticFunction.sigma_pos _ _ hpk_ne_zero
        rw [Nat.div_le_iff_le_mul_add_pred hσpk_pos]
        omega
    · push Not at hσ_target
      have h_exp : expChildren fuel target num next m p (p^k) =
          (ceilDiv target (σ₁ (p^k)), num * p^k, next) ::
          expChildren (fuel - 1) target num next m p (p^k * p) := by
        rw [show (ceilDiv target (σ₁ (p^k)), num * p^k, next) =
             (ceilDiv target ((p^k * p - 1) / (p - 1)), num * p^k, next) from by rw [h_sig_eq]]
        exact expChildren_step (by omega) hpk_le_m (by rw [h_sig_eq]; exact hσ_target)
      rw [h_exp]
      refine ⟨_, List.mem_cons_self, Set.nonempty_iff_ne_empty.mp ⟨t'', ?_⟩⟩
      refine ⟨ht''_P, ?_, ?_⟩
      · exact hnumt
      · have hσpk_pos : 0 < σ₁ (p^k) := ArithmeticFunction.sigma_pos _ _ hpk_ne_zero
        unfold ceilDiv
        rw [Nat.div_le_iff_le_mul_add_pred hσpk_pos]
        have hcom : σ₁ t'' * σ₁ (p^k) = σ₁ (p^k) * σ₁ t'' := mul_comm _ _
        omega
  | succ n ih =>
    intros k j₀ hn hj₀ hj₀_k hpk_le_m t'' ht''_pos ht''_P hnumt htσ fuel hfuel
    -- j₀ < k. We have σ(p^j₀) vs target.
    have hp_pos : 0 < p := hp.pos
    have hp2 : 2 ≤ p := hp.two_le
    have hpj_pos : 1 ≤ p^j₀ := Nat.one_le_pow _ _ hp_pos
    have hpj_le_m : p^j₀ ≤ m := by
      calc p^j₀ ≤ p^k := Nat.pow_le_pow_right hp.one_lt.le hj₀_k
        _ ≤ m := hpk_le_m
    have h_sig_eq : (p^j₀ * p - 1) / (p - 1) = σ₁ (p^j₀) := sigma_pow_expChildren_eq hp
    by_cases hσ_target : σ₁ (p^j₀) ≥ target
    · -- σ(p^j₀) ≥ target: emit child for j₀ with witness 1.
      have h_exp : expChildren fuel target num next m p (p^j₀) =
          [(ceilDiv target (σ₁ (p^j₀)), num * p^j₀, next)] := by
        rw [show (ceilDiv target (σ₁ (p^j₀)), num * p^j₀, next) =
             (ceilDiv target ((p^j₀ * p - 1) / (p - 1)), num * p^j₀, next) from by rw [h_sig_eq]]
        exact expChildren_stop (by omega) hpj_le_m (by rw [h_sig_eq]; exact hσ_target)
      rw [h_exp]
      refine ⟨_, List.mem_singleton.mpr rfl, Set.nonempty_iff_ne_empty.mp ⟨1, ?_⟩⟩
      refine ⟨one_mem_P _, ?_, ?_⟩
      · rw [mul_one]
        calc num * p^j₀ ≤ num * p^k := by
                exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp.one_lt.le hj₀_k)
          _ ≤ num * p^k * t'' := Nat.le_mul_of_pos_right _ ht''_pos
          _ < B := hnumt
      · have hσ1 : σ₁ 1 = 1 := by simp
        rw [hσ1]
        have hpj_ne_zero : p^j₀ ≠ 0 := Nat.one_le_iff_ne_zero.mp hpj_pos
        have hσpj_pos : 0 < σ₁ (p^j₀) := ArithmeticFunction.sigma_pos _ _ hpj_ne_zero
        unfold ceilDiv
        rw [Nat.div_le_iff_le_mul_add_pred hσpj_pos]
        omega
    · -- σ(p^j₀) < target: emit child and recurse.
      push Not at hσ_target
      have h_exp : expChildren fuel target num next m p (p^j₀) =
          (ceilDiv target (σ₁ (p^j₀)), num * p^j₀, next) ::
          expChildren (fuel - 1) target num next m p (p^j₀ * p) := by
        rw [show (ceilDiv target (σ₁ (p^j₀)), num * p^j₀, next) =
             (ceilDiv target ((p^j₀ * p - 1) / (p - 1)), num * p^j₀, next) from by rw [h_sig_eq]]
        exact expChildren_step (by omega) hpj_le_m (by rw [h_sig_eq]; exact hσ_target)
      rw [h_exp]
      have hjnew : k - (j₀ + 1) = n := by omega
      have hjnew_le : j₀ + 1 ≤ k := by omega
      have hpj1 : p^j₀ * p = p^(j₀ + 1) := by ring
      rw [hpj1]
      have IH := ih k (j₀ + 1) hjnew (by omega) hjnew_le hpk_le_m
        ht''_pos ht''_P hnumt htσ (fuel := fuel - 1) (by omega)
      obtain ⟨c, hc, hwit⟩ := IH
      refine ⟨c, List.mem_cons.mpr (Or.inr hc), hwit⟩

/-- The inductive lemma: at any state of `wheelChildrenWF` with the wheel invariants and a
viable witness `t`, some child in the output `L` has a non-empty witness set. -/
private theorem wheelChildrenWF_witness
    {B num m target : Nat} (hmdef : m = B / num) (hnum_pos : 1 ≤ num) :
    ∀ (front back lhs rhs : Nat),
      ∀ (L : List (Nat × Nat × Nat)),
        lhs = m * primesProd front back →
        rhs = target * primesProdM1 front back →
        front ≤ back + 1 →
        wheelChildrenWF (m * m) m target num front back lhs rhs = some L →
        ∀ (t : Nat), 2 ≤ t → t ∈ P front → num * t < B → target ≤ σ₁ t →
          ∃ c ∈ L, W B c.1 c.2.1 c.2.2 ≠ ∅ := by
  intro front back lhs rhs
  induction front, back, lhs, rhs using wheelChildrenWF.induct
    (m2 := m * m) (m := m) (target := target) (num := num) with
  | case1 front back lhs rhs hfront =>
    intros L _ _ _ hwf _ _ _ _ _
    rw [wheelChildrenWF] at hwf; simp [hfront] at hwf
  | case2 front back lhs rhs hfront hext =>
    intros L _ _ _ hwf _ _ _ _ _
    rw [wheelChildrenWF] at hwf; simp [hfront, hext] at hwf
  | case3 front back lhs rhs hfront hext =>
    intros L hlhs hrhs hfront_le _ t ht2 htP hnumt htσ
    exfalso
    have hfront_lt : front < primes.size := Nat.lt_of_not_ge hfront
    have htm : t ≤ m := by
      rw [hmdef]
      exact (Nat.le_div_iff_mul_le hnum_pos).mpr (by linarith)
    exact extendWF_ne_tooLarge_of_witness m target front t ht2 htP htm htσ hfront_lt
      back lhs rhs hlhs hrhs hfront_le hext
  | case4 front back lhs rhs hfront b lhs' rhs' hext _ hrec =>
    intros L _ _ _ hwf _ _ _ _ _
    rw [wheelChildrenWF] at hwf
    simp only [hfront, dif_neg, not_false_eq_true, hext] at hwf
    rw [hrec] at hwf
    cases hwf
  | case5 front back lhs rhs hfront b lhs' rhs' hext _ rest hrec =>
    rename_i ih
    intros L hlhs hrhs hfront_le hwf t ht2 htP hnumt htσ
    rw [wheelChildrenWF] at hwf
    simp only [hfront, dif_neg, not_false_eq_true, hext] at hwf
    rw [hrec] at hwf
    obtain rfl : rest ++ expChildren (m + 1) target num (front + 1) m
        primes[front] primes[front] = L := Option.some.inj hwf
    have hfront_lt : front < primes.size := Nat.lt_of_not_ge hfront
    have hp_prime : (primes[front]).Prime := primes_prime_of_mem _ (Array.getElem_mem hfront_lt)
    have hp2 : 2 ≤ primes[front] := hp_prime.two_le
    have htm : t ≤ m := by
      rw [hmdef]
      exact (Nat.le_div_iff_mul_le hnum_pos).mpr (by linarith)
    by_cases hdvd : primes[front] ∣ t
    · -- Sub-case A: primes[front] ∣ t. Use expChildren_witness_walk.
      set p := primes[front] with hp_def
      have htne : t ≠ 0 := by omega
      set k := t.factorization p with hk_def
      have hk_pos : 1 ≤ k := by
        rw [hk_def, ← (hp_prime.pow_dvd_iff_le_factorization htne)]
        simpa using hdvd
      have hpk_dvd : p^k ∣ t := Nat.ordProj_dvd t p
      have hpk_t : p^k * (t / p^k) = t := Nat.mul_div_cancel_left' hpk_dvd
      set t'' := t / p^k with ht''_def
      have hcoprime : Nat.Coprime p t'' := Nat.coprime_ordCompl hp_prime htne
      have hpk_ge2 : 2 ≤ p^k := by
        calc 2 ≤ p := hp2
          _ = p^1 := (pow_one _).symm
          _ ≤ p^k := Nat.pow_le_pow_right hp_prime.one_lt.le hk_pos
      have ht''_pos : 1 ≤ t'' := by
        rcases Nat.eq_zero_or_pos t'' with h | h
        · rw [h, mul_zero] at hpk_t; omega
        · exact h
      have hpk_le_t : p^k ≤ t := Nat.le_of_dvd (by omega) hpk_dvd
      have hpk_le_m : p^k ≤ m := le_trans hpk_le_t htm
      have hnumt_eq : num * p^k * t'' = num * t := by
        rw [mul_assoc, hpk_t]
      have hnumt' : num * p^k * t'' < B := by rw [hnumt_eq]; exact hnumt
      have hσmul : σ₁ t = σ₁ (p^k) * σ₁ t'' := by
        rw [← hpk_t]
        exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
          (hcoprime.pow_left k)
      have htσ' : target ≤ σ₁ (p^k) * σ₁ t'' := by rw [← hσmul]; exact htσ
      have ht''_P : t'' ∈ P (front + 1) := by
        refine ⟨ht''_pos, ?_⟩
        intros q hq_prime hq_dvd
        have hq_dvd_t : q ∣ t := by
          rw [← hpk_t]; exact dvd_mul_of_dvd_right hq_dvd _
        have hq_ne_p : q ≠ p := by
          intro h
          subst h
          have h1 : p ∣ 1 :=
            hcoprime.dvd_of_dvd_mul_left (by rw [mul_one]; exact hq_dvd)
          exact hq_prime.one_lt.ne' (Nat.dvd_one.mp h1)
        have ⟨p0, hp0_eq, hp0_le⟩ := htP.2 q hq_prime hq_dvd_t
        rw [Array.getElem?_eq_getElem hfront_lt] at hp0_eq
        have hp0v : p0 = p := Option.some.inj hp0_eq.symm
        rw [hp0v] at hp0_le
        have hq_gt_p : q > p := lt_of_le_of_ne hp0_le (Ne.symm hq_ne_p)
        have hf1 : front + 1 < primes.size := by
          by_contra h
          push Not at h
          have hrec_none : wheelChildrenWF (m * m) m target num (front + 1) b
              (lhs' / p) (rhs' / (p - 1)) = none := by
            rw [wheelChildrenWF]; simp [h]
          rw [hrec_none] at hrec; cases hrec
        refine ⟨primes[front + 1], ?_, primes_consecutive hfront_lt hq_prime hq_gt_p hf1⟩
        rw [Array.getElem?_eq_getElem hf1]
      have hfuel : k - 1 + 1 ≤ m + 1 := by
        have hk_le_pk : k ≤ p^k := Nat.lt_pow_self hp_prime.one_lt |>.le
        omega
      have := expChildren_witness_walk hp_prime (front + 1) (k - 1) k 1 (by omega) (by omega)
        hk_pos hpk_le_m ht''_pos ht''_P hnumt' htσ' (fuel := m + 1) hfuel
      obtain ⟨c, hc, hwit⟩ := this
      refine ⟨c, ?_, hwit⟩
      apply List.mem_append.mpr
      right
      rw [pow_one] at hc
      exact hc
    · -- Sub-case B: primes[front] ∤ t. Apply IH.
      have ht_in_P_next : t ∈ P (front + 1) := by
        refine ⟨by omega, ?_⟩
        intros q hq_prime hq_dvd
        have hq_ne_p : q ≠ primes[front] := by
          intro h; rw [h] at hq_dvd; exact hdvd hq_dvd
        have ⟨p0, hp0_eq, hp0_le⟩ := htP.2 q hq_prime hq_dvd
        rw [Array.getElem?_eq_getElem hfront_lt] at hp0_eq
        have hp0v : p0 = primes[front] := Option.some.inj hp0_eq.symm
        rw [hp0v] at hp0_le
        have hq_gt_pf : q > primes[front] := lt_of_le_of_ne hp0_le (Ne.symm hq_ne_p)
        have hf1 : front + 1 < primes.size := by
          by_contra h
          push Not at h
          have hrec_none : wheelChildrenWF (m * m) m target num (front + 1) b
              (lhs' / primes[front]) (rhs' / (primes[front] - 1)) = none := by
            rw [wheelChildrenWF]; simp [h]
          rw [hrec_none] at hrec; cases hrec
        refine ⟨primes[front + 1], ?_, primes_consecutive hfront_lt hq_prime hq_gt_pf hf1⟩
        rw [Array.getElem?_eq_getElem hf1]
      obtain ⟨hlhs', hrhs', _, hfront_b⟩ :=
        extendWF_window_invariant m target front back lhs rhs b lhs' rhs' hlhs hrhs hfront_le hext
      have hp_pos : 0 < primes[front] := hp_prime.pos
      have hpm1_pos : 0 < primes[front] - 1 := by omega
      have hlhs_new : lhs' / primes[front] = m * primesProd (front + 1) b := by
        rw [hlhs', primesProd_succ_front hfront_lt hfront_b,
            show m * (primes[front] * primesProd (front + 1) b) =
                 primes[front] * (m * primesProd (front + 1) b) from by ring]
        exact Nat.mul_div_cancel_left _ hp_pos
      have hrhs_new : rhs' / (primes[front] - 1) = target * primesProdM1 (front + 1) b := by
        rw [hrhs', primesProdM1_succ_front hfront_lt hfront_b,
            show target * ((primes[front] - 1) * primesProdM1 (front + 1) b) =
                 (primes[front] - 1) * (target * primesProdM1 (front + 1) b) from by ring]
        exact Nat.mul_div_cancel_left _ hpm1_pos
      have IH := ih rest hlhs_new hrhs_new (by omega) hrec t ht2 ht_in_P_next hnumt htσ
      obtain ⟨c, hc_rest, hwit⟩ := IH
      refine ⟨c, ?_, hwit⟩
      exact List.mem_append.mpr (Or.inl hc_rest)

/-- For `m2 = 0` and `lhs = 0`, `extendWF.window` produces `lhs' = 0`. -/
private theorem extendWF_zero_lhs_window_zero (front : Nat) :
    ∀ (back lhs rhs b lhs' rhs' : Nat), lhs = 0 →
      extendWF 0 front back lhs rhs = Wheel.window b lhs' rhs' → lhs' = 0 := by
  intro back lhs rhs b lhs' rhs'
  induction back, lhs, rhs using extendWF.induct (m2 := 0) (front := front) with
  | case1 back lhs rhs hf hge =>
    intros hlhs heq
    rw [extendWF] at heq; simp [hf, hge] at heq
    obtain ⟨_, hl, _⟩ := heq
    rw [← hl, hlhs]
  | case2 _ _ _ hf hlt hb1 _ _ hbig =>
    intros hlhs heq
    subst hlhs; omega
  | case3 back lhs rhs hf hlt hb1 _ _ hle ih =>
    intros hlhs heq
    have heq2 : extendWF 0 front (back + 1) (lhs * primes[back + 1])
        (rhs * (primes[back + 1] - 1)) = Wheel.window b lhs' rhs' := by
      conv_lhs at heq => rw [extendWF]
      rw [if_pos hf, if_neg hlt, dif_pos hb1, if_neg hle] at heq
      exact heq
    have hlhs' : lhs * primes[back + 1] = 0 := by rw [hlhs]; ring
    exact ih hlhs' heq2
  | case4 _ _ _ hf hlt hb1 =>
    intros _ heq
    push Not at hb1
    rw [extendWF] at heq
    rw [if_pos hf, if_neg hlt, dif_neg (by omega)] at heq
    cases heq
  | case5 _ _ _ hf hf1 _ _ hbig =>
    intros hlhs heq
    subst hlhs; omega
  | case6 back lhs rhs hf hf1 _ _ hle ih =>
    intros hlhs heq
    push Not at hf
    have heq2 : extendWF 0 front front (lhs * primes[front]) (rhs * (primes[front] - 1)) =
        Wheel.window b lhs' rhs' := by
      conv_lhs at heq => rw [extendWF]
      rw [if_neg (show ¬ front ≤ back from by omega), dif_pos hf1, if_neg hle] at heq
      exact heq
    have hlhs' : lhs * primes[front] = 0 := by rw [hlhs]; ring
    exact ih hlhs' heq2
  | case7 _ _ _ hf hf1 =>
    intros _ heq
    push Not at hf; push Not at hf1
    rw [extendWF] at heq
    rw [if_neg (show ¬ front ≤ _ from by omega), dif_neg (by omega)] at heq
    cases heq

/-- For `m2 = 0` and `lhs = 0`, `wheelChildrenWF` returns `none`. -/
private theorem wheelChildrenWF_zero_no_some
    (target num : Nat) :
    ∀ (front back lhs rhs : Nat), lhs = 0 →
      wheelChildrenWF 0 0 target num front back lhs rhs = none := by
  intro front back lhs rhs
  induction front, back, lhs, rhs using wheelChildrenWF.induct
    (m2 := 0) (m := 0) (target := target) (num := num) with
  | case1 front back lhs rhs hfront =>
    intro _; rw [wheelChildrenWF]; simp [hfront]
  | case2 front back lhs rhs hfront hext =>
    intro _; rw [wheelChildrenWF]; simp [hfront, hext]
  | case3 front back lhs rhs hfront hext =>
    intro hlhs
    exfalso
    exact extendWF_zero_lhs_no_tooLarge front back lhs rhs hlhs hext
  | case4 front back lhs rhs hfront b lhs' rhs' hext _ hrec =>
    intro _
    rw [wheelChildrenWF]
    simp only [hfront, dif_neg, not_false_eq_true, hext]
    rw [hrec]
  | case5 front back lhs rhs hfront b lhs' rhs' hext _ rest hrec =>
    rename_i ih
    intro hlhs
    exfalso
    have hlhs' : lhs' = 0 :=
      extendWF_zero_lhs_window_zero front back lhs rhs b lhs' rhs' hlhs hext
    have hlhs'_p : lhs' / primes[front] = 0 := by rw [hlhs']; simp
    have := ih hlhs'_p
    rw [this] at hrec; cases hrec

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
  rcases Nat.eq_zero_or_pos num with hnum0 | hnum_pos
  · -- num = 0 case
    subst hnum0
    rw [children] at h
    split at h
    · cases h
    · -- m = B / 0 = 0
      simp only [Nat.div_zero, Nat.mul_zero] at h
      rw [wheelChildren_eq_wheelChildrenWF (by omega)] at h
      rw [wheelChildrenWF_zero_no_some target 0 minIdx minIdx 0 _ rfl] at h
      simp at h
  · -- num ≥ 1 case
    rw [children] at h
    split at h
    · cases h
    · rename_i p0 hp0
      set m := B / num with hmdef
      -- h is wheelChildren ... = some cs. Translate to wheelChildrenWF.
      have hfuel : primes.size + 1 - minIdx ≤ primes.size + 1 := by omega
      rw [wheelChildren_eq_wheelChildrenWF hfuel] at h
      generalize hwf : wheelChildrenWF (m * m) m target num minIdx minIdx
        (p0 * m) (target * (p0 - 1)) = wf at h
      match wf, hwf, h with
      | some L, hwf, h =>
        simp at h; subst h
        obtain ⟨⟨ht_pos, htP⟩, htlt, htσ⟩ := ht
        have hminIdx_lt : minIdx < primes.size := by
          by_contra h
          rw [Array.getElem?_eq_none (Nat.not_lt.mp h)] at hp0
          injection hp0
        rw [Array.getElem?_eq_getElem hminIdx_lt] at hp0
        obtain hp0_val : p0 = primes[minIdx] := Option.some.inj hp0.symm
        subst hp0_val
        have hlhs_eq : primes[minIdx] * m = m * primesProd minIdx minIdx := by
          rw [primesProd_self hminIdx_lt]; ring
        have hrhs_eq : target * (primes[minIdx] - 1) =
            target * primesProdM1 minIdx minIdx := by
          rw [primesProdM1_self hminIdx_lt]
        rw [hlhs_eq, hrhs_eq] at hwf
        have ht2 : 2 ≤ t := by omega
        exact wheelChildrenWF_witness hmdef hnum_pos minIdx minIdx _ _ L rfl rfl
          (by omega) hwf t ht2 ⟨ht_pos, htP⟩ htlt htσ

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

/-- `step = some true` ⟹ every node on the stack has an empty witness set. -/
theorem step_true {B fuel : Nat} {stack : List (Nat × Nat × Nat)}
    (h : step B fuel stack = some true) :
    ∀ node ∈ stack, W B node.1 node.2.1 node.2.2 = ∅ := by
  induction fuel generalizing stack with
  | zero => simp [step] at h
  | succ fuel ih =>
    rcases stack with _ | ⟨⟨target, num, minIdx⟩, rest⟩
    · simp
    · rw [step] at h
      by_cases ht : target ≤ 1
      · simp only [ht, if_true] at h
        by_cases hn : num < B
        · simp [hn] at h
        · simp only [hn, if_false] at h
          have ih_rest := ih h
          intro node hnode
          simp only [List.mem_cons] at hnode
          rcases hnode with rfl | hnode
          · ext t
            simp only [W, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
            rintro ⟨⟨ht1, _⟩, htlt, _⟩
            push Not at hn
            have := Nat.le_mul_of_pos_right num ht1
            omega
          · exact ih_rest _ hnode
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
            · obtain ⟨c, hc, hwc⟩ :=
                (children_spec hch).mp ⟨t, htW, h1⟩
              have : W B c.1 c.2.1 c.2.2 = ∅ :=
                ih_all c (List.mem_append.mpr (Or.inl hc))
              exact hwc this
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
  · simp only [hB, if_false] at h
    have hW : W (lcmRange n) (σ₁ (lcmRange n)) 1 0 = ∅ :=
      step_true h (σ₁ (lcmRange n), 1, 0) List.mem_cons_self
    by_contra hcontra
    push Not at hcontra
    have hmW : m ∈ W (lcmRange n) (σ₁ (lcmRange n)) 1 0 := by
      refine ⟨⟨hm_pos, ?_⟩, by simpa using hm_lt, hcontra⟩
      intro q hqPrime _
      exact ⟨2, by decide, hqPrime.two_le⟩
    rw [hW] at hmW
    exact hmW

end Sage
