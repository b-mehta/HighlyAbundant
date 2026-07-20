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

local notation:max "p_" i:max => nth Nat.Prime i

attribute [grind .] sigma_pos

namespace Sage

/-! ### Ceiling division -/

@[grind =]
private theorem ceilDiv_le_iff {a b c : ℕ} (hb : b ≠ 0) : ceilDiv a b ≤ c ↔ a ≤ c * b := by
  rw [ceilDiv, div_le_iff_le_mul_add_pred (Nat.pos_of_ne_zero hb), mul_comm]; lia

@[grind =]
private theorem lt_ceilDiv_iff {a b c : ℕ} (hb : b ≠ 0) : c < ceilDiv a b ↔ c * b < a :=
  lt_iff_lt_of_le_iff_le (ceilDiv_le_iff hb)

private theorem le_ceilDiv_mul {a b : ℕ} (hb : b ≠ 0) : a ≤ ceilDiv a b * b :=
  (ceilDiv_le_iff hb).mp le_rfl

/-! ### The `primes` table -/

private lemma primesRArray_get_eq_nth_aux (i : Fin 49) :
    primesRArray.get i.val = nth Nat.Prime i.val := by
  have hp : ∀ i : Fin 49, Nat.Prime (primesRArray.get i.val) := by
    intro i
    refine checkPrime_true ?_
    decide +kernel +revert
  rw [← nth_count (hp i)]
  congr 1
  decide +kernel +revert

/-- The wheel's array lookup gives the `i`-th prime. -/
@[grind <=]
private lemma primesRArray_get_eq_nth {i : ℕ} (hi : i < 49) :
    primesRArray.get i = p_ i :=
  primesRArray_get_eq_nth_aux ⟨i, hi⟩

/-! ### Specification: `P` and `W` -/

/-- `P j`: nonzero naturals whose every prime factor is at least the `j`-th prime. -/
def P (j : ℕ) : Set ℕ :=
  {t | t ≠ 0 ∧ ∀ q : ℕ, q.Prime → q ∣ t → p_ j ≤ q}

@[grind =] lemma mem_P {j t : ℕ} :
    t ∈ P j ↔ t ≠ 0 ∧ ∀ q : ℕ, q.Prime → q ∣ t → p_ j ≤ q :=
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
    (h : ∀ q, q.Prime → q ∣ x → p_ front < q) : x ∈ P (front + 1) :=
  ⟨hx, fun q hq hqd => by by_contra! hlt; grind [le_nth_of_lt_nth_succ hlt hq]⟩

/-- If `p ≥ p_ front` is prime, `t = p^k * t'` with `t'` nonzero and coprime to `p`,
and every prime factor of `t` is `≥ p`, then `t' ∈ P (front + 1)`. -/
private lemma mem_P_succ_of_coprime {t t' p k front : ℕ}
    (hp_prime : p.Prime) (hp_geprimes : p_ front ≤ p)
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

/-- Factoring the prime-window product at the front. -/
@[grind =] private theorem prod_primes_succ_front {front B : ℕ} (hB : front ≤ B) :
    ∏ i ∈ Icc front B, p_ i = p_ front * ∏ i ∈ Icc (front + 1) B, p_ i := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_eq_prod_Ico_succ_bot (by lia),
    Finset.Ico_add_one_right_eq_Icc]

/-- Factoring the `p - 1` window product at the front. -/
@[grind =] private theorem prod_primesM1_succ_front {front B : ℕ} (hB : front ≤ B) :
    ∏ i ∈ Icc front B, (p_ i - 1)
      = (p_ front - 1) * ∏ i ∈ Icc (front + 1) B, (p_ i - 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_eq_prod_Ico_succ_bot (by lia),
    Finset.Ico_add_one_right_eq_Icc]

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

/-- The σ value appearing in `expChildren`'s loop: `(p ^ k * p - 1) / (p - 1) = σ₁ (p ^ k)`. -/
@[grind =] private theorem sigma_pow_expChildren_eq {p k : ℕ} (hp : p.Prime) :
    (p ^ k * p - 1) / (p - 1) = σ₁ (p ^ k) := by rw [← pow_succ, ← sigma_one_apply_prime_pow' hp]

/-! ### The two main bounds: σ-window and radical -/

/-- `σ₁ t * ∏ (p_ i - 1) ≤ t * ∏ p_ i` over `Icc front B`, for `t ∈ P front` with at most
`B - front + 1` distinct primes. -/
private theorem sigma_bound_window {t front : ℕ} (B : ℕ) (ht : t ≠ 0) (hP : t ∈ P front)
    (hBsize : B + 1 ≤ 49) (hcard : t.primeFactors.card + front ≤ B + 1) :
    σ₁ t * ∏ i ∈ Icc front B, (p_ i - 1) ≤ t * ∏ i ∈ Icc front B, p_ i := by
  induction t using Nat.strongRecOn generalizing front B with
  | ind t ih =>
    obtain rfl | ht1 := eq_or_ne t 1
    · simpa using prod_le_prod' (g := fun i => p_ i) fun i _ => Nat.sub_le _ 1
    have ht2 : 2 ≤ t := by lia
    obtain ⟨p, k, t', hk₀, rfl, ht'₀, ht'_lt, hcoprime, hmin⟩ := exists_minFac_decomp ht2
    have hp_prime : p.Prime := hmin.prop.1
    have hp_geprimes : p_ front ≤ p := hP.2 p hp_prime hmin.prop.2
    have hcard := card_primeFactors_coprime hp_prime hk₀.ne' rfl hcoprime
    have ht'P : t' ∈ P (front + 1) :=
      mem_P_succ_of_coprime hp_prime hp_geprimes (fun q hq hqd => hmin.le ⟨hq, hqd⟩)
        rfl ht'₀.ne' hcoprime
    have IH := ih t' ht'_lt B ht'₀.ne' ht'P hBsize (by lia)
    have hcons : σ₁ (p ^ k) * (p_ front - 1) ≤ p ^ k * p_ front :=
      sigma_pow_le_window_factor hp_prime (prime_nth_prime front).two_le hp_geprimes
    calc σ₁ (p ^ k * t') * ∏ i ∈ Icc front B, (p_ i - 1)
        = σ₁ (p ^ k) * (p_ front - 1) * (σ₁ t' * ∏ i ∈ Icc (front + 1) B, (p_ i - 1)) := by
          rw [isMultiplicative_sigma.map_mul_of_coprime (hcoprime.pow_left k),
            prod_primesM1_succ_front (by lia)]
          ring
      _ ≤ p ^ k * p_ front * (t' * ∏ i ∈ Icc (front + 1) B, p_ i) := by gcongr
      _ = p ^ k * t' * ∏ i ∈ Icc front B, p_ i := by grind

/-- `∏ p_ i ≤ t` over `Icc front (front + j - 1)`, for `t ∈ P front` with `j ≥ 1`
distinct primes and `front + j ≤ 49`. -/
private theorem primesProd_le_t {t front : ℕ} (ht : t ≠ 0) (hP : t ∈ P front) (j : ℕ)
    (hj : j ≠ 0) (hjle : j ≤ t.primeFactors.card) (hsize : front + j ≤ 49) :
    ∏ i ∈ Icc front (front + j - 1), p_ i ≤ t := by
  induction t using Nat.strongRecOn generalizing front j with
  | ind t ih =>
    have ht1 : t ≠ 1 := by grind [primeFactors_one]
    have ht2 : 2 ≤ t := by lia
    obtain ⟨p, k, t', hk₀, rfl, ht'₀, ht'_lt, hcoprime, hmin⟩ := exists_minFac_decomp ht2
    have hp_prime : p.Prime := hmin.prop.1
    have hp_dvd : p ∣ p ^ k * t' := (dvd_pow_self p (by lia)).mul_right _
    have hp_geprimes : p_ front ≤ p := hP.2 p hp_prime hp_dvd
    have hpk_ge : p_ front ≤ p ^ k := hp_geprimes.trans (le_self_pow (by lia) p)
    rcases lt_or_ge 1 j with hj2 | hj2
    · have ht'P : t' ∈ P (front + 1) :=
        mem_P_succ_of_coprime hp_prime hp_geprimes (fun q hq hqd => hmin.le ⟨hq, hqd⟩)
          rfl ht'₀.ne' hcoprime
      have hcard := card_primeFactors_coprime hp_prime hk₀.ne' rfl hcoprime
      have IH := ih t' ht'_lt ht'₀.ne' ht'P (j - 1) (by lia) (by lia) (by lia)
      rw [(by lia : (front + 1) + (j - 1) - 1 = front + j - 1)] at IH
      calc ∏ i ∈ Icc front (front + j - 1), p_ i
          = p_ front * ∏ i ∈ Icc (front + 1) (front + j - 1), p_ i :=
            prod_primes_succ_front (by lia)
        _ ≤ p ^ k * t' := by gcongr
    · obtain rfl : j = 1 := by lia
      rw [Nat.add_sub_cancel, Finset.Icc_self, Finset.prod_singleton]
      exact hpk_ge.trans (Nat.le_mul_of_pos_right _ ht'₀)

/-! ### Ruling out `.tooLarge` from a witness -/

/-- At a wheel `.tooLarge` state with `back + 1 < 49`, the witness `t` with
`t ≤ m`, `t ∈ P front`, `goal ≤ σ₁ t` gives `False`. -/
@[grind .] private theorem extend_tooLarge_contra
    {m goal front back lhs rhs t : ℕ}
    (hlhs : lhs = m * ∏ i ∈ Icc front back, p_ i)
    (hrhs : rhs = goal * ∏ i ∈ Icc front back, (p_ i - 1))
    (hfront : front ≤ back + 1)
    (hback_lt : back + 1 < 49)
    (hsmall : lhs < rhs)
    (hbig : m * m < lhs * primesRArray.get (back + 1))
    (ht2 : 2 ≤ t) (htP : t ∈ P front) (htm : t ≤ m) (htσ : goal ≤ σ₁ t) : False := by
  rw [primesRArray_get_eq_nth hback_lt] at hbig
  rcases lt_or_ge t.primeFactors.card (back + 2 - front) with hcard | hcard
  · have hbound := sigma_bound_window back (by lia) htP (by lia) (by lia)
    have h_chain : σ₁ t * ∏ i ∈ Icc front back, (p_ i - 1)
        < goal * ∏ i ∈ Icc front back, (p_ i - 1) := by
      nlinarith [Nat.mul_le_mul_right (∏ i ∈ Icc front back, p_ i) htm]
    exact absurd htσ (Nat.lt_of_mul_lt_mul_right h_chain).not_ge
  · have hrad := primesProd_le_t (by lia) htP (back + 2 - front) (by lia) hcard (by lia)
    have hidx : front + (back + 2 - front) - 1 = back + 1 := by lia
    rw [hidx] at hrad
    have hppsm : m < ∏ i ∈ Icc front (back + 1), p_ i := Nat.lt_of_mul_lt_mul_left (a := m)
      (by rwa [prod_Icc_succ_top (by lia : front ≤ back + 1) _, ← mul_assoc, ← hlhs])
    lia

/-- At a wheel `.tooLarge` empty-window state with `front < 49`, the witness `t`
with `t ≤ m`, `t ∈ P front`, `t ≥ 2` gives `False`. -/
@[grind .] private theorem extend_tooLarge_empty_contra
    {m front back lhs : ℕ} {t : ℕ}
    (hlhs : lhs = m * ∏ i ∈ Icc front back, p_ i) (hfront_lt : front < 49)
    (hempty : back + 1 = front)
    (hbig : m * m < lhs * primesRArray.get front)
    (ht2 : 2 ≤ t) (htP : t ∈ P front) (htm : t ≤ m) : False := by
  rw [Finset.Icc_eq_empty (by lia : ¬ front ≤ back), Finset.prod_empty, mul_one] at hlhs
  rw [primesRArray_get_eq_nth hfront_lt, hlhs] at hbig
  have h1 : p_ front ≤ t.minFac := htP.2 _ (minFac_prime (by lia)) (minFac_dvd t)
  grind [Nat.lt_of_mul_lt_mul_left hbig, minFac_le]

/-- If `t` is a witness, `extend` cannot return `.tooLarge`. -/
@[grind .] private theorem extend_ne_tooLarge {fuel m goal front t : ℕ} (ht2 : 2 ≤ t)
    (htP : t ∈ P front) (htm : t ≤ m) (htσ : goal ≤ σ₁ t)
    {back lhs rhs : ℕ} (hlhs : lhs = m * ∏ i ∈ Icc front back, p_ i)
    (hrhs : rhs = goal * ∏ i ∈ Icc front back, (p_ i - 1)) (hfront : front ≤ back + 1) :
    extend fuel (m * m) front back lhs rhs ≠ .tooLarge := by
  fun_induction extend fuel (m * m) front back lhs rhs with
    grind [= prod_Icc_succ_top, Finset.Icc_eq_empty]

/-! ### Window invariants -/

/-- When `extend` returns `.window`, the new `(b, lhs', rhs')` satisfy the wheel invariants
shifted to `b`, and `b ≥ back`. -/
private theorem extend_window_invariant {fuel m goal front back lhs rhs b lhs' rhs' : ℕ}
    (hlhs : lhs = m * ∏ i ∈ Icc front back, p_ i)
    (hrhs : rhs = goal * ∏ i ∈ Icc front back, (p_ i - 1))
    (hfront : front ≤ back + 1)
    (heq : extend fuel (m * m) front back lhs rhs = Wheel.window b lhs' rhs') :
    lhs' = m * ∏ i ∈ Icc front b, p_ i ∧ rhs' = goal * ∏ i ∈ Icc front b, (p_ i - 1) ∧
    back ≤ b ∧ front ≤ b := by
  fun_induction extend with grind [= prod_Icc_succ_top, Finset.Icc_eq_empty]

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
private theorem wheelChildren_zero_eq_none {fuel goal cand front back lhs rhs : ℕ}
    {acc : List (ℕ × ℕ × ℕ)} (hlhs : lhs = 0) :
    wheelChildren fuel 0 0 goal cand front back lhs rhs acc = none := by
  fun_induction wheelChildren with grind [Nat.zero_div]

/-! ### `expChildren` analysis -/

section
variable {fuel goal cand next m p pk : ℕ}

/-- One step of `expChildren` when `pk ≤ m` and `σ(pk) < goal`. -/
private theorem expChildren_step (hfuel : 1 ≤ fuel) (hpkm : pk ≤ m)
    (hsig_lt : (pk * p - 1) / (p - 1) < goal) :
    expChildren fuel goal cand next m p pk =
      (ceilDiv goal ((pk * p - 1) / (p - 1)), cand * pk, next) ::
      expChildren (fuel - 1) goal cand next m p (pk * p) := by fun_induction expChildren with grind

/-- One step of `expChildren` when `pk ≤ m` and `σ(pk) ≥ goal` (final child). -/
private theorem expChildren_stop (hfuel : 1 ≤ fuel) (hpkm : pk ≤ m)
    (hsig_le : goal ≤ (pk * p - 1) / (p - 1)) :
    expChildren fuel goal cand next m p pk =
      [(ceilDiv goal ((pk * p - 1) / (p - 1)), cand * pk, next)] := by
  fun_induction expChildren with grind

end

/-- Every entry of `expChildren ... (p ^ k₀)` (for prime `p`, `k₀ ≥ 1`) has the form
`(⌈goal / σ₁(p^k)⌉, cand * p^k, next)` for some `k ≥ k₀` with `p ^ k ≤ m`. -/
private theorem mem_expChildren {fuel goal cand next m p k₀ : ℕ}
    (hp : p.Prime) (hk₀ : 1 ≤ k₀) {c : ℕ × ℕ × ℕ}
    (hc : c ∈ expChildren fuel goal cand next m p (p ^ k₀)) :
    ∃ k, k₀ ≤ k ∧ p ^ k ≤ m ∧ c = (ceilDiv goal (σ₁ (p ^ k)), cand * p ^ k, next) := by
  induction fuel generalizing k₀ with grind [expChildren, =_ pow_succ]

/-- Witness `1` for the stop arm of `expChildren_witness_walk`: when `σ(p ^ j₀) ≥ goal`,
the child `(ceilDiv goal σ(p ^ j₀), cand*p ^ j₀, next)` has `1` as a witness. -/
private lemma one_witnesses_stop {B cand goal next p k j₀ s : ℕ}
    (hp : p.Prime) (hjk : j₀ ≤ k) (hs₀ : 1 ≤ s)
    (hat : cand * p ^ k * s < B) (hσg : goal ≤ σ₁ (p ^ j₀)) :
    1 ∈ W B (ceilDiv goal (σ₁ (p ^ j₀))) (cand * p ^ j₀) next := by
  simp only [mem_W, one_mem_P, mul_one, sigma_one, true_and]
  constructor
  · grind [Nat.mul_le_mul_left cand (Nat.pow_le_pow_right hp.one_lt.le hjk),
      Nat.le_mul_of_pos_right (cand * p ^ k) hs₀]
  · grind [sigma_pos, pow_ne_zero, hp.pos]

/-- Walk `expChildren` from `pk₀ = p ^ j₀` looking for a child with a witness, given
a parent witness `t = p ^ k * s` (factored at `p` with `s` coprime to `p`). -/
private theorem expChildren_witness_walk {B cand goal m p : ℕ} (hp : p.Prime) (next : ℕ)
    (n k j₀ : ℕ) (hn : k - j₀ = n) (hj₀ : 1 ≤ j₀) (hj₀_k : j₀ ≤ k) (hpkm : p ^ k ≤ m)
    {s : ℕ} (hs₀ : 1 ≤ s) (hsP : s ∈ P next) (hat : cand * p ^ k * s < B)
    (htσ : goal ≤ σ₁ (p ^ k) * σ₁ s) (fuel : ℕ) (hfuel : n + 1 ≤ fuel) :
    ∃ c ∈ expChildren fuel goal cand next m p (p ^ j₀), (W B c.1 c.2.1 c.2.2).Nonempty := by
  induction n generalizing j₀ fuel with
  | zero =>
    obtain rfl : j₀ = k := by lia
    have h_sig_eq : (p ^ j₀ * p - 1) / (p - 1) = σ₁ (p ^ j₀) := sigma_pow_expChildren_eq hp
    by_cases hσg : goal ≤ σ₁ (p ^ j₀)
    · rw [expChildren_stop (by lia) hpkm (h_sig_eq ▸ hσg), h_sig_eq]
      exact ⟨_, List.mem_singleton.mpr rfl, ⟨_, one_witnesses_stop hp hj₀_k hs₀ hat hσg⟩⟩
    push Not at hσg
    rw [expChildren_step (by lia) hpkm (h_sig_eq.symm ▸ hσg), h_sig_eq]
    refine ⟨_, List.mem_cons_self, ⟨s, hsP, hat, ?_⟩⟩
    grind [hp.pos]
  | succ n ih =>
    have hpjm : p ^ j₀ ≤ m := (Nat.pow_le_pow_right hp.one_lt.le hj₀_k).trans hpkm
    have h_sig_eq : (p ^ j₀ * p - 1) / (p - 1) = σ₁ (p ^ j₀) := sigma_pow_expChildren_eq hp
    by_cases hσg : goal ≤ σ₁ (p ^ j₀)
    · rw [expChildren_stop (by lia) hpjm (h_sig_eq.symm ▸ hσg), h_sig_eq]
      exact ⟨_, List.mem_singleton.mpr rfl, ⟨_, one_witnesses_stop hp hj₀_k hs₀ hat hσg⟩⟩
    push Not at hσg
    rw [expChildren_step (by lia) hpjm (h_sig_eq.symm ▸ hσg), h_sig_eq, ← pow_succ]
    obtain ⟨c, hc, hwit⟩ := ih (j₀ + 1) (by lia) (by lia) (by lia) (fuel - 1) (by lia)
    grind

end Sage
