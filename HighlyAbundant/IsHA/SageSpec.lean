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
`W B goal cand i` collects the `t` a node `(goal, cand, i)` still admits: `t ∈ P i` with
`cand * t < B` and `goal ≤ σ₁ t`, where `P j` is the naturals all of whose prime factors are at
least the `j`-th prime. The search answers `some true` exactly when the root witness set is empty,
which for `(B, sL) = (lcmUpto n, σ₁ (lcmUpto n))` says `lcmUpto n` is highly abundant.
-/
-- todo: put this in the lakefile not just here
set_option linter.mathlibStandardSet true

open Nat Finset ArithmeticFunction

local notation:max "p_ " i:max => nth Nat.Prime i

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

private lemma nth_prime_strictMono : StrictMono (nth Nat.Prime) :=
  nth_strictMono infinite_setOfPred_prime

private lemma nth_prime_le {i j : ℕ} (h : i ≤ j) : p_ i ≤ p_ j :=
  nth_prime_strictMono.monotone h

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

/-- The witness set of a node `(goal, cand, i)` for bound `B`. -/
def W (B goal cand i : ℕ) : Set ℕ :=
  {t | t ∈ P i ∧ cand * t < B ∧ goal ≤ σ₁ t}

@[simp, grind =] lemma mem_W {B goal cand i t : ℕ} :
    t ∈ W B goal cand i ↔ t ∈ P i ∧ cand * t < B ∧ goal ≤ σ₁ t :=
  Iff.rfl

/-! ### Membership in `P` -/

/-- If `x ≠ 0` and every prime factor of `x` exceeds the `lo`-th prime, then
`x ∈ P (lo + 1)`. -/
private lemma mem_P_succ_of_factors_gt {x lo : ℕ} (hx : x ≠ 0)
    (h : ∀ q, q.Prime → q ∣ x → p_ lo < q) : x ∈ P (lo + 1) :=
  ⟨hx, fun q hq hqd => by by_contra! hlt; grind [le_nth_of_lt_nth_succ hlt hq]⟩

/-- If `p ≥ p_ lo` is prime, `t = p^k * t'` with `t'` nonzero and coprime to `p`,
and every prime factor of `t` is `≥ p`, then `t' ∈ P (lo + 1)`. -/
private lemma mem_P_succ_of_coprime {t t' p k lo : ℕ}
    (hp_prime : p.Prime) (hp_geprimes : p_ lo ≤ p)
    (hp_min : ∀ q, q.Prime → q ∣ t → p ≤ q) (hpk_t : p ^ k * t' = t)
    (ht'₀ : t' ≠ 0) (hcoprime : Nat.Coprime p t') : t' ∈ P (lo + 1) := by
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

/-- Factoring a product over `Icc lo B` at its low end. -/
private theorem prod_Icc_succ_lo {M : Type*} [CommMonoid M] {lo B : ℕ} (f : ℕ → M) (hB : lo ≤ B) :
    ∏ i ∈ Icc lo B, f i = f lo * ∏ i ∈ Icc (lo + 1) B, f i := by
  rw [← Ico_add_one_right_eq_Icc, prod_eq_prod_Ico_succ_bot (by lia),
    Ico_add_one_right_eq_Icc]

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

/-- `σ₁ t * ∏ (p_ i - 1) ≤ t * ∏ p_ i` over `Icc lo B`, for `t ∈ P lo` with at most
`B - lo + 1` distinct primes. -/
private theorem sigma_bound_window {t lo : ℕ} (B : ℕ) (ht : t ≠ 0) (hP : t ∈ P lo)
    (hBsize : B + 1 ≤ 49) (hcard : t.primeFactors.card + lo ≤ B + 1) :
    σ₁ t * ∏ i ∈ Icc lo B, (p_ i - 1) ≤ t * ∏ i ∈ Icc lo B, p_ i := by
  induction t using Nat.strongRecOn generalizing lo B with
  | ind t ih =>
    obtain rfl | ht1 := eq_or_ne t 1
    · simpa using prod_le_prod' (g := fun i => p_ i) fun i _ => Nat.sub_le _ 1
    have ht2 : 2 ≤ t := by lia
    obtain ⟨p, k, t', hk₀, rfl, ht'₀, ht'_lt, hcoprime, hmin⟩ := exists_minFac_decomp ht2
    have hp_geprimes : p_ lo ≤ p := hP.2 p hmin.prop.1 hmin.prop.2
    have hcard' := card_primeFactors_coprime hmin.prop.1 hk₀.ne' rfl hcoprime
    have ht'P : t' ∈ P (lo + 1) :=
      mem_P_succ_of_coprime hmin.prop.1 hp_geprimes (fun q hq hqd => hmin.le ⟨hq, hqd⟩)
        rfl ht'₀.ne' hcoprime
    have IH := ih t' ht'_lt B ht'₀.ne' ht'P hBsize (by lia)
    have hcons : σ₁ (p ^ k) * (p_ lo - 1) ≤ p ^ k * p_ lo :=
      sigma_pow_le_window_factor hmin.prop.1 (prime_nth_prime lo).two_le hp_geprimes
    calc σ₁ (p ^ k * t') * ∏ i ∈ Icc lo B, (p_ i - 1)
        = σ₁ (p ^ k) * (p_ lo - 1) * (σ₁ t' * ∏ i ∈ Icc (lo + 1) B, (p_ i - 1)) := by
          rw [isMultiplicative_sigma.map_mul_of_coprime (hcoprime.pow_left k),
            prod_Icc_succ_lo (fun i ↦ p_ i - 1) (by lia)]
          ring
      _ ≤ p ^ k * p_ lo * (t' * ∏ i ∈ Icc (lo + 1) B, p_ i) := by gcongr
      _ = p ^ k * t' * ∏ i ∈ Icc lo B, p_ i := by grind [= prod_Icc_succ_lo]

/-- `∏ p_ i ≤ t` over `Icc lo (lo + j - 1)`, for `t ∈ P lo` with `j ≥ 1`
distinct primes and `lo + j ≤ 49`. -/
private theorem primesProd_le_t {t lo : ℕ} (ht : t ≠ 0) (hP : t ∈ P lo) (j : ℕ)
    (hj : j ≠ 0) (hjle : j ≤ #t.primeFactors) (hsize : lo + j ≤ 49) :
    ∏ i ∈ Icc lo (lo + j - 1), p_ i ≤ t := by
  induction t using Nat.strongRecOn generalizing lo j with
  | ind t ih =>
    have ht1 : t ≠ 1 := by grind [primeFactors_one]
    have ht2 : 2 ≤ t := by lia
    obtain ⟨p, k, t', hk₀, rfl, ht'₀, ht'_lt, hcoprime, hmin⟩ := exists_minFac_decomp ht2
    have hp_prime : p.Prime := hmin.prop.1
    have hp_dvd : p ∣ p ^ k * t' := (dvd_pow_self p (by lia)).mul_right _
    have hp_geprimes : p_ lo ≤ p := hP.2 p hp_prime hp_dvd
    have hpk_ge : p_ lo ≤ p ^ k := hp_geprimes.trans (le_self_pow (by lia) p)
    rcases lt_or_ge 1 j with hj2 | hj2
    · have ht'P : t' ∈ P (lo + 1) :=
        mem_P_succ_of_coprime hp_prime hp_geprimes (fun q hq hqd => hmin.le ⟨hq, hqd⟩)
          rfl ht'₀.ne' hcoprime
      have hcard := card_primeFactors_coprime hp_prime hk₀.ne' rfl hcoprime
      have IH := ih t' ht'_lt ht'₀.ne' ht'P (j - 1) (by lia) (by lia) (by lia)
      rw [(by lia : (lo + 1) + (j - 1) - 1 = lo + j - 1)] at IH
      calc ∏ i ∈ Icc lo (lo + j - 1), p_ i
          = p_ lo * ∏ i ∈ Icc (lo + 1) (lo + j - 1), p_ i :=
            prod_Icc_succ_lo _ (by lia)
        _ ≤ p ^ k * t' := by gcongr
    · obtain rfl : j = 1 := by lia
      rw [Nat.add_sub_cancel, Icc_self, prod_singleton]
      exact hpk_ge.trans (Nat.le_mul_of_pos_right _ ht'₀)

/-! ### Ruling out `.tooLarge` from a witness -/

/-- At a wheel `.tooLarge` state with `hi + 1 < 49`, the witness `t` with
`t ≤ m`, `t ∈ P lo`, `goal ≤ σ₁ t` gives `False`. -/
@[grind .] private theorem extend_tooLarge_contra
    {m goal lo hi lhs rhs t : ℕ}
    (hlhs : lhs = m * ∏ i ∈ Icc lo hi, p_ i)
    (hrhs : rhs = goal * ∏ i ∈ Icc lo hi, (p_ i - 1))
    (hlo : lo ≤ hi + 1) (hhi_lt : hi + 1 < 49) (hsmall : lhs < rhs)
    (hbig : m * m < lhs * p_ (hi + 1))
    (ht2 : 2 ≤ t) (htP : t ∈ P lo) (htm : t ≤ m) (htσ : goal ≤ σ₁ t) : False := by
  rcases lt_or_ge #t.primeFactors (hi + 2 - lo) with hcard | hcard
  · have h_chain : σ₁ t * ∏ i ∈ Icc lo hi, (p_ i - 1) < goal * ∏ i ∈ Icc lo hi, (p_ i - 1) := by
      grw [sigma_bound_window hi (by lia) htP (by lia) (by lia), htm, ← hlhs, hsmall, hrhs]
    grind [Nat.lt_of_mul_lt_mul_right h_chain]
  · have hrad := primesProd_le_t (by lia) htP (hi + 2 - lo) (by lia) hcard (by lia)
    have hidx : lo + (hi + 2 - lo) - 1 = hi + 1 := by lia
    rw [hidx] at hrad
    have hppsm : m < ∏ i ∈ Icc lo (hi + 1), p_ i := by
      apply Nat.lt_of_mul_lt_mul_left (a := m)
      rwa [prod_Icc_succ_top (by lia), ← mul_assoc, ← hlhs]
    lia

/-- At a wheel `.tooLarge` empty-window state with `lo < 49`, the witness `t`
with `t ≤ m`, `t ∈ P lo`, `t ≥ 2` gives `False`. -/
@[grind .] private theorem extend_tooLarge_empty_contra
    {m lo hi lhs t : ℕ}
    (hlhs : lhs = m * ∏ i ∈ Icc lo hi, p_ i)
    (hempty : hi + 1 = lo)
    (hbig : m * m < lhs * p_ lo)
    (ht2 : 2 ≤ t) (htP : t ∈ P lo) (htm : t ≤ m) : False := by
  rw [Icc_eq_empty (by lia), prod_empty, mul_one] at hlhs
  rw [hlhs] at hbig
  have h1 : p_ lo ≤ t.minFac := htP.2 _ (minFac_prime (by lia)) (minFac_dvd t)
  grind [Nat.lt_of_mul_lt_mul_left hbig, minFac_le]

/-- If `t` is a witness, `extend` cannot return `.tooLarge`. -/
@[grind .] private theorem extend_ne_tooLarge {fuel m goal lo t : ℕ} (ht2 : 2 ≤ t)
    (htP : t ∈ P lo) (htm : t ≤ m) (htσ : goal ≤ σ₁ t)
    {hi lhs rhs : ℕ} (hlhs : lhs = m * ∏ i ∈ Icc lo hi, p_ i)
    (hrhs : rhs = goal * ∏ i ∈ Icc lo hi, (p_ i - 1)) (hlo : lo ≤ hi + 1) :
    extend fuel (m * m) lo hi lhs rhs ≠ .tooLarge := by
  fun_induction extend fuel (m * m) lo hi lhs rhs with
  | case3 fuel hi lhs rhs hle hnsmall hlt =>
    have hb := primesRArray_get_eq_nth hlt
    grind [= prod_Icc_succ_top, Icc_eq_empty]
  | _ =>
    grind [= prod_Icc_succ_top, Icc_eq_empty, = prod_Icc_succ_lo]


/-! ### Window invariants -/

/-- When `extend` returns `.window`, the new `(b, lhs', rhs')` satisfy the wheel invariants
shifted to `b`, and `b ≥ hi`. -/
private theorem extend_window_invariant {fuel m goal lo hi lhs rhs b lhs' rhs' : ℕ}
    (hlhs : lhs = m * ∏ i ∈ Icc lo hi, p_ i)
    (hrhs : rhs = goal * ∏ i ∈ Icc lo hi, (p_ i - 1))
    (hlo : lo ≤ hi + 1)
    (heq : extend fuel (m * m) lo hi lhs rhs = Wheel.window b lhs' rhs') :
    lhs' = m * ∏ i ∈ Icc lo b, p_ i ∧ rhs' = goal * ∏ i ∈ Icc lo b, (p_ i - 1) ∧
    hi ≤ b ∧ lo ≤ b := by
  fun_induction extend with
    grind [= prod_Icc_succ_top, Icc_eq_empty, = prod_Icc_succ_lo]

/-! ### Degenerate case: `lhs = 0` -/

/-- For `m2 = 0` and `lhs = 0`: `extend` returns either `.exhaustedTable` or
`.window b 0 rhs'` (so never `.tooLarge`, and any `.window` has `lhs' = 0`). -/
@[grind .]
private lemma extend_zero_lhs {fuel lo hi lhs rhs : ℕ} (hlhs : lhs = 0) :
    extend fuel 0 lo hi lhs rhs = Wheel.exhaustedTable ∨
    ∃ b rhs', extend fuel 0 lo hi lhs rhs = Wheel.window b 0 rhs' := by
  fun_induction extend fuel 0 lo hi lhs rhs with
  | case2 => simp [hlhs]
  | _ => grind

/-- For `m2 = 0` and `lhs = 0`, `wheelChildren` returns `none`. -/
@[grind =]
private theorem wheelChildren_zero_eq_none {fuel goal cand lo hi lhs rhs : ℕ}
    {acc : List (ℕ × ℕ × ℕ)} (hlhs : lhs = 0) :
    wheelChildren fuel 0 0 goal cand lo hi lhs rhs acc = none := by
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

/-! ### `wheelChildren` and `children` -/

/-- Each entry of `wheelChildren`'s output is either from `acc` or of the form
`(⌈goal / σ₁(p^k)⌉, cand * p^k, i + 1)` for some `i ≥ lo`, `k ≥ 1` with
`p = p_ i` and `p^k ≤ m`. -/
private theorem mem_wheelChildren {fuel m2 m goal cand lo hi lhs rhs : ℕ}
    {acc : List (ℕ × ℕ × ℕ)} {L : List (ℕ × ℕ × ℕ)}
    (h : wheelChildren fuel m2 m goal cand lo hi lhs rhs acc = some L)
    {c : ℕ × ℕ × ℕ} (hc : c ∈ L) :
    c ∈ acc ∨ ∃ i k, lo ≤ i ∧ 1 ≤ k ∧ p_ i ^ k ≤ m ∧
      c = (ceilDiv goal (σ₁ (p_ i ^ k)), cand * p_ i ^ k, i + 1) := by
  fun_induction wheelChildren generalizing L with
  | case4 lo _ _ _ acc _ _ _ _ _ hp p =>
    rename_i hrec
    have hp : p = p_ lo := primesRArray_get_eq_nth hp
    rcases hrec h hc with hcacc | ⟨i, k, hle, hk, hpkm, hceq⟩
    · rcases List.mem_append.mp hcacc with hcexp | hcorig
      · obtain ⟨k, hk, hpkm, hceq⟩ := mem_expChildren (prime_nth_prime lo) le_rfl
          (by rwa [pow_one, ← hp])
        grind
      · exact Or.inl hcorig
    · exact Or.inr ⟨i, k, by grind⟩
  | _ => grind

/-- Everything in `acc` on the way in is still in the output `L`. -/
private lemma wheelChildren_acc_subset {fuel m2 m goal cand lo hi lhs rhs : ℕ}
    {acc L : List (ℕ × ℕ × ℕ)}
    (h : wheelChildren fuel m2 m goal cand lo hi lhs rhs acc = some L) : acc ⊆ L := by
  fun_induction wheelChildren generalizing L with grind [List.mem_append_right]

/-- Given the wheel invariants and a witness `t`, some child in `wheelChildren`'s
output `L` has a nonempty witness set. -/
private theorem wheelChildren_witness {B cand m goal : ℕ} (hmdef : m = B / cand)
    (hcand₀ : 1 ≤ cand) {fuel lo hi lhs rhs : ℕ} {acc L : List (ℕ × ℕ × ℕ)}
    (hfuel : 49 + 1 - lo ≤ fuel)
    (hlhs : lhs = m * ∏ i ∈ Icc lo hi, p_ i)
    (hrhs : rhs = goal * ∏ i ∈ Icc lo hi, (p_ i - 1))
    (hlo_le : lo ≤ hi + 1)
    (hwc : wheelChildren fuel (m * m) m goal cand lo hi lhs rhs acc = some L)
    {t : ℕ} (ht2 : 2 ≤ t) (htP : t ∈ P lo) (hat : cand * t < B) (htσ : goal ≤ σ₁ t) :
    ∃ c ∈ L, (W B c.1 c.2.1 c.2.2).Nonempty := by
  have htm : t ≤ m := hmdef ▸ (le_div_iff_mul_le hcand₀).mpr (by linarith)
  fun_induction wheelChildren generalizing L with
  | case1 | case2 | case5 => cases hwc
  | case3 => grind
  | case4 lo hi lhs rhs acc _ b lhs' rhs' hext hp p =>
    rename_i hrec
    have hp : p = p_ lo := primesRArray_get_eq_nth hp
    have hp_prime : (p_ lo).Prime := prime_nth_prime lo
    obtain ⟨hlhs', hrhs', _, hlo_b⟩ := extend_window_invariant hlhs hrhs hlo_le hext
    replace hlhs : lhs' / p = m * ∏ i ∈ Icc (lo + 1) b, p_ i := by
      rw [hp, hlhs', prod_Icc_succ_lo _ hlo_b, mul_left_comm,
        Nat.mul_div_cancel_left _ hp_prime.pos]
    replace hrhs : rhs' / (p - 1) = goal * ∏ i ∈ Icc (lo + 1) b, (p_ i - 1) := by
      rw [hp, hrhs', prod_Icc_succ_lo _ hlo_b, mul_left_comm,
        Nat.mul_div_cancel_left _ (Nat.sub_pos_of_lt hp_prime.one_lt)]
    by_cases hdvd : p_ lo ∣ t
    · obtain ⟨k, s, hk₀, hpk_t, hs₀, _, hcoprime⟩ :=
        exists_factor_decomp hp_prime hdvd (by lia)
      have hpkm : p_ lo ^ k ≤ m :=
        (le_of_dvd (by lia) ⟨s, hpk_t.symm⟩).trans htm
      have htσ' : goal ≤ σ₁ (p_ lo ^ k) * σ₁ s := by
        rwa [← isMultiplicative_sigma.map_mul_of_coprime (hcoprime.pow_left k), hpk_t]
      have hsP : s ∈ P (lo + 1) :=
        mem_P_succ_of_coprime hp_prime le_rfl htP.2 hpk_t hs₀.ne' hcoprime
      obtain ⟨c, hc, hwit⟩ := expChildren_witness_walk hp_prime (lo + 1) (k - 1) k 1
        (by lia) (by lia) hk₀ hpkm hs₀ hsP
        (by rwa [mul_assoc, hpk_t]) htσ' (m + 1)
        (by have : k ≤ m := (Nat.lt_pow_self hp_prime.one_lt).le.trans hpkm; lia)
      exact ⟨c, wheelChildren_acc_subset hwc (List.mem_append_left _ (by grind)), hwit⟩
    · exact hrec (by lia) hlhs hrhs (by lia) hwc
        (mem_P_succ_of_factors_gt (by lia) fun q' hq'_prime hq'_dvd =>
          lt_of_le_of_ne (htP.2 q' hq'_prime hq'_dvd) (by grind))

/-- Every `c` in `children`'s output has the form
`(⌈goal / σ₁(p^k)⌉, cand * p^k, j + 1)` for some `j ≥ i`, `k ≥ 1` with
`p = p_ j` and `p^k ≤ B / cand`. -/
private theorem mem_children {B goal cand i : ℕ} {cs : List (ℕ × ℕ × ℕ)}
    (h : children B goal cand i = some cs) {c : ℕ × ℕ × ℕ} (hc : c ∈ cs) :
    ∃ j k, i ≤ j ∧ 1 ≤ k ∧ p_ j ^ k ≤ B / cand ∧
      c = (ceilDiv goal (σ₁ (p_ j ^ k)),
        cand * p_ j ^ k, j + 1) := by
  rw [children] at h
  split at h <;> [grind [mem_wheelChildren h hc]; grind]

/-- If `t'` is a witness of the child `(⌈goal / σ₁(p ^ k)⌉, cand * p ^ k, j + 1)`
with `p = p_ j`, then `p ^ k * t'` is a nontrivial witness of the
parent `(goal, cand, i)`. -/
private theorem child_witness_to_parent {B goal cand i j k : ℕ}
    (hmi : i ≤ j) (hk : 1 ≤ k) {t' : ℕ}
    (ht' : t' ∈ W B (ceilDiv goal (σ₁ (p_ j ^ k)))
      (cand * p_ j ^ k) (j + 1)) :
    p_ j ^ k * t' ∈ W B goal cand i ∧
      p_ j ^ k * t' ≠ 1 := by
  set p := p_ j
  obtain ⟨⟨ht'1, ht'P⟩, ht'lt, ht'σ⟩ := ht'
  have hpPrime : p.Prime := prime_nth_prime j
  have hpk_ge2 : 2 ≤ p ^ k := hpPrime.two_le.trans (le_self_pow (by lia) p)
  have hpkt'_ge2 : 2 ≤ p ^ k * t' :=
    hpk_ge2.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero ht'1))
  have hcop : Nat.Coprime (p ^ k) t' := by
    refine (hpPrime.coprime_iff_not_dvd.mpr fun hpdvd => ?_).pow_left _
    linarith [ht'P p hpPrime hpdvd, nth_prime_strictMono (lt_succ_self j)]
  refine ⟨⟨⟨by lia, fun q hqPrime hqDvd => ?_⟩, by rwa [← mul_assoc], ?_⟩, by lia⟩
  · rcases hqPrime.dvd_mul.mp hqDvd with h1 | h2
    · obtain rfl : q = p :=
        (prime_dvd_prime_iff_eq hqPrime hpPrime).mp (hqPrime.dvd_of_dvd_pow h1)
      exact nth_prime_le hmi
    · exact (nth_prime_le (by lia)).trans (ht'P q hqPrime h2)
  · have hmul : σ₁ (p ^ k * t') = σ₁ (p ^ k) * σ₁ t' :=
      isMultiplicative_sigma.map_mul_of_coprime hcop
    have hpk_pos : σ₁ (p ^ k) ≠ 0 := by grind [sigma_pos, pow_ne_zero, hpPrime.pos]
    calc goal ≤ ceilDiv goal (σ₁ (p ^ k)) * σ₁ (p ^ k) := le_ceilDiv_mul hpk_pos
      _ ≤ σ₁ t' * σ₁ (p ^ k) := by gcongr
      _ = σ₁ (p ^ k * t') := by rw [hmul, Nat.mul_comm]

/-- A nontrivial witness of the parent gives a witness for some child in `cs`. -/
private theorem witness_to_child {B goal cand i : ℕ} {cs : List (ℕ × ℕ × ℕ)}
    (h : children B goal cand i = some cs) {t : ℕ}
    (ht : t ∈ W B goal cand i) (h1 : t ≠ 1) :
    ∃ c ∈ cs, (W B c.1 c.2.1 c.2.2).Nonempty := by
  rcases Nat.eq_zero_or_pos cand with rfl | hcand₀
  · grind [children]
  · simp only [children] at h
    split at h
    · rename_i hidx_lt
      obtain ⟨⟨ht₀, htP⟩, htlt, htσ⟩ := ht
      have e1 : ∏ j ∈ Icc i i, p_ j = p_ i := by rw [Icc_self, prod_singleton]
      have e2 : ∏ j ∈ Icc i i, (p_ j - 1) = p_ i - 1 := by rw [Icc_self, prod_singleton]
      rw [primesRArray_get_eq_nth hidx_lt, ← e2,
        mul_comm (p_ i) (B / cand), ← e1] at h
      exact wheelChildren_witness rfl hcand₀ (by lia) rfl rfl (by lia) h
        (by lia) ⟨ht₀, htP⟩ htlt htσ
    · cases h

/-- `children` reduces nontrivial witnesses of a node to witnesses of its children. -/
theorem children_spec {B goal cand i : ℕ} {cs : List (ℕ × ℕ × ℕ)}
    (h : children B goal cand i = some cs) :
    (∃ t ∈ W B goal cand i, t ≠ 1) ↔
      ∃ c ∈ cs, (W B c.1 c.2.1 c.2.2).Nonempty := by
  refine ⟨fun ⟨t, ht, h1⟩ => witness_to_child h ht h1, ?_⟩
  rintro ⟨c, hc, t', ht'⟩
  obtain ⟨j, k, hmi, hk, _, hceq⟩ := mem_children h hc
  rw [hceq] at ht'
  obtain ⟨hw, hne⟩ := child_witness_to_parent hmi hk ht'
  exact ⟨_, hw, hne⟩

/-! ### Step correctness and top-level result -/

/-- A node with `2 ≤ goal` has an empty witness set once all its children do. -/
theorem W_eq_empty_of_partial {B goal cand i : ℕ} {cs : List (ℕ × ℕ × ℕ)}
    (hgoal : 2 ≤ goal)
    (hch : children B goal cand i = some cs)
    (hcs : ∀ c ∈ cs, W B c.1 c.2.1 c.2.2 = ∅) :
    W B goal cand i = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro t ht
  obtain rfl | h1 := eq_or_ne t 1
  · grind [sigma_one]
  · obtain ⟨c, hc, hwc⟩ := (children_spec hch).mp ⟨t, ht, h1⟩
    grind [Set.not_nonempty_iff_eq_empty]

/-- `step = some true` gives an empty witness set for every node on the stack. -/
theorem step_true {B fuel : ℕ} {stack : List (ℕ × ℕ × ℕ)}
    (h : step B fuel stack = some true) :
    ∀ node ∈ stack, W B node.1 node.2.1 node.2.2 = ∅ := by
  fun_induction step with
  | case1 | case2 | case3 | case5 => grind
  | case4 _ goal cand i _ _ _ ih =>
    suffices ∀ t ∈ W B goal cand i, False by grind
    intro t
    have := Nat.le_mul_of_pos_right (m := t) cand
    grind
  | case6 _ _ _ _ _ _ _ hch ih1 =>
    simp_all [W_eq_empty_of_partial (by lia) hch (fun c ↦ by grind)]

/-- An empty root witness set makes `lcm (1..n)` highly abundant. -/
theorem isHighlyAbundant_of_root_W_eq_empty {n : ℕ}
    (hW : W (lcmUpto n) (σ₁ (lcmUpto n)) 1 0 = ∅) :
    IsHighlyAbundant (lcmUpto n) := by
  intro m hm₀ hm_lt
  by_contra! hcontra
  have h2 : p_ 0 = 2 := Nat.nth_prime_zero_eq_two
  have hmW : m ∈ W (lcmUpto n) (σ₁ (lcmUpto n)) 1 0 := by grind [Nat.Prime.two_le]
  rwa [hW] at hmW

/-- Certify `lcm (1..n)` from an empty witness set for each root child. -/
theorem highlyAbundantLcm_correct_partial_W {n : ℕ} {cs : List (ℕ × ℕ × ℕ)}
    (hn : 2 ≤ n)
    (hch : children (lcmUpto n) (σ₁ (lcmUpto n)) 1 0 = some cs)
    (hcs : ∀ c ∈ cs, W (lcmUpto n) c.1 c.2.1 c.2.2 = ∅) :
    IsHighlyAbundant (lcmUpto n) :=
  isHighlyAbundant_of_root_W_eq_empty
    (W_eq_empty_of_partial (two_le_sigma_lcmUpto hn) hch hcs)

end Sage
