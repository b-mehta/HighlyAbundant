/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.Basic
import HighlyAbundant.SetupPrimes
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.Compare

/-!
# Helpers for formalising ladders
-/

open ArithmeticFunction hiding id

section

local instance {α : Type*} : IsStrictWeakOrder (ℕ × α) (fun a b ↦ a.1 < b.1) where
  incomp_trans := by grind
  trans := by grind
  irrefl := by grind

structure ProofData where
  lo : ℕ
  hi : ℕ
  muls : List (ℕ × ℕ × ℕ)
  divs : List ℕ
  h_muls : ∀ pk ∈ muls, pk.1.Prime := by norm_num
  h_divs : ∀ p ∈ divs, p.Prime := by norm_num
  h_muls_chain : muls.IsChain (·.1 < ·.1) := by decide
  h_divs_chain : divs.IsChain (· < ·) := by decide
  h_disjoint' : ∀ pki ∈ muls, pki.1 ∉ divs := by decide
  h_divs_lo : ∀ p ∈ divs, p ≤ lo := by decide
  h_divs_hi : ∀ p ∈ divs, hi < p ^ 2 := by decide
  h_muls_hi : ∀ pki ∈ muls, pki.1 ^ pki.2.2 ≤ hi ∧ hi < pki.1 ^ (pki.2.2 + 1) := by decide
  h_sigma_prod :
    (muls.map (fun pk ↦ (pk.1 ^ (pk.2.2 + 1) - 1))).prod * (divs.map (· + 1)).prod ≤
    (muls.map (fun pk ↦ (pk.1 ^ (pk.2.2 + pk.2.1 + 1) - 1))).prod := by decide
  h_prod : (muls.map (fun pk ↦ pk.1 ^ pk.2.1)).prod < divs.prod := by decide

namespace ProofData

variable (d : ProofData)

lemma h_muls_sorted : d.muls.Pairwise (·.1 < ·.1) := d.h_muls_chain.pairwise
lemma h_muls_pairwise : d.muls.Pairwise (·.1 ≠ ·.1) := d.h_muls_sorted.imp ne_of_lt
lemma h_divs_sorted : d.divs.Pairwise (· < ·) := d.h_divs_chain.pairwise
lemma h_muls_nodup : d.muls.Nodup := d.h_muls_sorted.nodup
lemma h_divs_nodup : d.divs.Nodup := d.h_divs_sorted.nodup

lemma h_muls_setPairwise : {x | x ∈ d.muls}.Pairwise (·.1 ≠ ·.1) :=
  d.h_muls_pairwise.set_pairwise (by grind [Symmetric])

lemma h_disjoint : ∀ pki ∈ d.muls, pki.1 ∉ d.divs := d.h_disjoint'

def mul : ℕ := (d.muls.map (fun pk ↦ pk.1 ^ pk.2.1)).prod
def div : ℕ := d.divs.prod

lemma h_muls_hi' : ∀ pki ∈ d.muls, (lcmRange d.hi).factorization pki.1 = pki.2.2 := by
  intro pki hpki
  exact factorization_lcmRange_eq (d.h_muls_hi _ hpki).1 (d.h_muls_hi _ hpki).2 (d.h_muls _ hpki)

lemma h_muls_i {i : ℕ} (hi : i ∈ Finset.Icc d.lo d.hi) :
    ∀ pki ∈ d.muls, (lcmRange i).factorization pki.1 ≤ pki.2.2 := by
  simp only [Finset.mem_Icc] at hi
  intro pki hpki
  exact factorization_lcmRange_le (hi.2.trans_lt (d.h_muls_hi _ hpki).2) (d.h_muls _ hpki)

lemma h_divs_i {i : ℕ} (hi : i ∈ Finset.Icc d.lo d.hi) :
    ∀ p ∈ d.divs, (lcmRange i).factorization p = 1 := by
  simp only [Finset.mem_Icc] at hi
  intro p hp
  exact factorization_lcmRange_eq_one (d.h_divs _ hp)
    (by have := d.h_divs_lo; grind) (by have := d.h_divs_hi; grind)

lemma mul_eq : d.mul = (∏ pk ∈ d.muls.toFinset, pk.1 ^ pk.2.1) := by
  rw [mul, List.prod_toFinset _ d.h_muls_nodup]

lemma div_eq : d.div = (∏ i ∈ d.divs.toFinset, i) := by
  rw [div, List.prod_toFinset _ d.h_divs_nodup, List.map_id']

def K (i : ℕ) : ℕ :=
  (∏ p ∈ (lcmRange i).primeFactors with p ∉ d.muls.map (·.1), p ^ (lcmRange i).factorization p)

def M (i : ℕ) : ℕ := (lcmRange i) / d.div * d.mul

lemma mem_of_dvd {p i : ℕ} (hp : p.Prime) (h : p ∣ d.K i) :
    p ∉ d.muls.map (·.1) := by
  obtain ⟨q, hq₁, hq₂⟩ := Prime.exists_mem_finset_dvd hp.prime h
  simp only [Finset.mem_filter, Nat.mem_primeFactors, ne_eq] at hq₁
  cases Nat.prime_eq_prime_of_dvd_pow hp hq₁.1.1 hq₂
  exact hq₁.2

lemma h_div_K {i : ℕ} (hi : i ∈ Finset.Icc d.lo d.hi) : d.div ∣ d.K i := by
  rw [div_eq]
  apply Finset.prod_dvd_of_isRelPrime
  · simp only [Set.Pairwise, Function.onFun, List.coe_toFinset, Set.mem_setOf_eq, ne_eq,
      ← Nat.coprime_iff_isRelPrime]
    intro p₁ hp₁ p₂ hp₂ h
    rwa [Nat.coprime_primes (d.h_divs _ hp₁) (d.h_divs _ hp₂)]
  simp only [List.mem_toFinset]
  intro p hp
  have hpl : p ∈ (lcmRange i).primeFactors := by
    rw [Nat.mem_primeFactors_of_ne_zero lcmRange_ne_zero]
    refine ⟨d.h_divs _ hp, ?_⟩
    exact dvd_lcmRange_of_le (d.h_divs p hp).ne_zero
      (by have := d.h_divs_lo; grind)
  have : p ∉ d.muls.map (·.1) := by have := d.h_disjoint; grind
  convert_to p ^ (lcmRange i).factorization p ∣ d.K i
  · rfl
  · rw [d.h_divs_i hi _ hp, Nat.pow_one]
  exact Finset.dvd_prod_of_mem _ (by simp [hpl, this])

lemma L_eq {i : ℕ} :
    lcmRange i = (∏ pki ∈ d.muls.toFinset, pki.1 ^ (lcmRange i).factorization pki.1) * d.K i := by
  conv_lhs =>
    rw [← Nat.prod_factorization_pow_eq_self (n := lcmRange i) lcmRange_ne_zero, Finsupp.prod,
      Nat.support_factorization]
  rw [← Finset.prod_filter_mul_prod_filter_not (lcmRange i).primeFactors (· ∈ d.muls.map (·.1)) _]
  change _ * d.K i = _
  suffices
      ∏ x ∈ (lcmRange i).primeFactors with x ∈ d.muls.map (·.1),
            x ^ (lcmRange i).factorization x =
      (∏ pki ∈ d.muls.toFinset, pki.1 ^ (lcmRange i).factorization pki.1) by
    rw [this]
  apply (Finset.prod_bij_ne_one (fun pki _ _ ↦ pki.1) _ _ _ (by simp)).symm
  · rintro ⟨p, k, i⟩ hpki h₂
    dsimp at h₂ ⊢
    simp only [List.mem_toFinset] at hpki
    simp only [List.mem_map, Prod.exists, exists_and_right, exists_eq_right, Finset.mem_filter,
      Nat.mem_primeFactors, ne_eq]
    refine ⟨⟨(d.h_muls _ hpki), ?_, lcmRange_ne_zero⟩, _, _, hpki⟩
    exact Nat.dvd_of_factorization_pos (by intro h; simp [h] at h₂)
  · simp only [List.mem_toFinset, ne_eq, Nat.pow_eq_one, not_or, and_imp, Prod.forall]
    rintro p₁ k₁ i₁ hpki₁ hp₁ hLp₁ p₂ k₂ i₂ hpki₂ hp₂ hLp₂ rfl
    by_contra! h
    exact (d.h_muls_sorted.imp ne_of_lt).set_pairwise (by grind [Symmetric]) hpki₁ hpki₂ h rfl
  · simp +contextual

lemma K_div_L {i : ℕ} : d.K i ∣ lcmRange i := by
  rw [d.L_eq]
  simp

lemma div_dvd_L {i : ℕ} (hi : i ∈ Finset.Icc d.lo d.hi) : d.div ∣ lcmRange i :=
  (d.h_div_K hi).trans (d.K_div_L)

lemma M_lt_L {i : ℕ} (hi : i ∈ Finset.Icc d.lo d.hi) : d.M i < lcmRange i := by
  rw [M]
  have : d.div ∣ lcmRange i := (d.h_div_K hi).trans (d.K_div_L)
  rw [Nat.div_mul_right_comm this]
  apply Nat.div_lt_of_lt_mul
  have := lcmRange_pos (n := i)
  rw [mul_comm]
  apply Nat.mul_lt_mul_of_pos_right _ this
  exact d.h_prod

lemma div_coprime {i : ℕ} (hi : i ∈ Finset.Icc d.lo d.hi) : d.div.Coprime (d.K i / d.div) := by
  apply Nat.coprime_of_dvd
  intro p hp hdiv h'
  rw [Nat.dvd_div_iff_mul_dvd (d.h_div_K hi)] at h'
  have hpK : p * p ∣ d.K i := (Nat.mul_dvd_mul_right hdiv _).trans h'
  rw [← pow_two] at hpK
  have : p ∈ d.divs := by
    rw [div_eq] at hdiv
    obtain ⟨q, hq, hpq⟩ := hp.prime.exists_mem_finset_dvd hdiv
    simp only [List.mem_toFinset] at hq
    cases (Nat.prime_dvd_prime_iff_eq hp (d.h_divs _ hq)).1 hpq
    assumption
  simp only [Finset.mem_Icc] at hi
  exact sq_not_dvd hp ((d.h_divs_hi _ this).trans_le' hi.2) (hpK.trans d.K_div_L)

lemma M_eq {i : ℕ} (hi : i ∈ Finset.Icc d.lo d.hi) :
    d.M i =
      (∏ pki ∈ d.muls.toFinset, pki.1 ^ ((lcmRange i).factorization pki.1 + pki.2.1)) *
      (d.K i / d.div) := by
  simp only [ProofData.M]
  conv_lhs => rw [d.L_eq]
  rw [Nat.mul_div_assoc _ (d.h_div_K hi), mul_right_comm, d.mul_eq, ← Finset.prod_mul_distrib]
  simp_rw [Nat.pow_add]

lemma div_ne_zero : d.div ≠ 0 := by
  apply List.prod_ne_zero
  intro hp
  exact (d.h_divs _ hp).ne_zero rfl

lemma K_ne_zero {i : ℕ} : d.K i ≠ 0 := by
  rintro hK
  have := d.L_eq (i := i)
  rw [hK, mul_zero] at this
  exact lcmRange_ne_zero this

lemma sigma_K_ne_zero {i : ℕ} : σ₁ (d.K i) ≠ 0 := by simp [d.K_ne_zero]

lemma prod_coprime_K {f : ℕ × ℕ × ℕ → ℕ} {i : ℕ} :
    (∏ p ∈ d.muls.toFinset, p.1 ^ f p).Coprime (d.K i) := by
  apply Nat.coprime_of_dvd
  intro p hp hp' hpK
  obtain ⟨q, hq, hpq⟩ := hp.prime.exists_mem_finset_dvd hp'
  simp only [List.mem_toFinset] at hq
  cases Nat.prime_eq_prime_of_dvd_pow hp (d.h_muls _ hq) hpq
  have := d.mem_of_dvd hp hpK
  grind

lemma M_pos {i} (hi : i ∈ Finset.Icc d.lo d.hi) : 0 < d.M i := by
  rw [M]
  apply Nat.mul_pos (Nat.div_pos (Nat.le_of_dvd (lcmRange_pos) (d.div_dvd_L hi)) _) _
  · rw [div_eq]
    simp only [CanonicallyOrderedAdd.prod_pos, List.mem_toFinset]
    intro i hi
    exact (d.h_divs _ hi).pos
  · simp only [mul_eq, CanonicallyOrderedAdd.prod_pos, List.mem_toFinset]
    intro i hi
    exact Nat.pow_pos (d.h_muls _ hi).pos

lemma sig_eq {i} (hi : i ∈ Finset.Icc d.lo d.hi) : σ₁ (d.M i) / σ₁ (lcmRange i) =
        (∏ pki ∈ d.muls.toFinset,
          (pki.1 ^ ((lcmRange i).factorization pki.1 + pki.2.1 + 1) - 1 : ℕ) /
          (pki.1 ^ ((lcmRange i).factorization pki.1 + 1) - 1 : ℕ) : ℚ) /
        (∏ p ∈ d.divs.toFinset, (p + 1)) := by
  have h₁ : (σ₁ (d.K i / d.div) : ℚ) = (σ₁ (d.K i)) / (σ₁ d.div) :=
      (isMultiplicative_sigma (k := 1)).natCast.map_div_of_coprime (R := ℚ) (d.h_div_K hi)
      (d.div_coprime hi).symm (by simp [sigma_eq_zero, d.div_ne_zero])
  have h₂ : σ₁ (lcmRange i) =
      σ₁ (∏ pki ∈ d.muls.toFinset, pki.1 ^ (lcmRange i).factorization pki.1) * σ₁ (d.K i) := by
    rw [← isMultiplicative_sigma.map_mul_of_coprime, ← L_eq]
    apply d.prod_coprime_K
  rw [d.M_eq hi, isMultiplicative_sigma.map_mul_of_coprime, Nat.cast_mul, h₁, h₂, Nat.cast_mul]
  swap
  · apply Nat.Coprime.coprime_div_right d.prod_coprime_K _
    exact d.h_div_K hi
  have : σ₁ (d.K i) ≠ 0 := by simp [sigma_eq_zero, d.K_ne_zero]
  conv_lhs =>
  { equals
      ((σ₁ (∏ pki ∈ d.muls.toFinset, pki.1 ^ ((lcmRange i).factorization pki.1 + pki.2.1)) : ℚ) /
      (σ₁ (∏ pki ∈ d.muls.toFinset, pki.1 ^ (lcmRange i).factorization pki.1))) /
      (σ₁ d.div) =>
    field_simp [this] }
  rw [d.div_eq, isMultiplicative_sigma.map_prod, isMultiplicative_sigma.map_prod,
    isMultiplicative_sigma.map_prod, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  swap
  · simp only [Set.Pairwise, List.coe_toFinset, Set.mem_setOf_eq, ne_eq, Function.onFun]
    intro p hp q hq hpq
    rwa [Nat.coprime_primes (d.h_divs _ hp) (d.h_divs _ hq)]
  swap
  · simp only [Set.Pairwise, List.coe_toFinset, Set.mem_setOf_eq, ne_eq, Function.onFun]
    intro pki hpk qkj hqk hpq
    apply Nat.coprime_pow_primes _ _ (d.h_muls _ hpk) (d.h_muls _ hqk)
    exact d.h_muls_setPairwise hpk hqk hpq
  swap
  · simp only [Set.Pairwise, List.coe_toFinset, Set.mem_setOf_eq, ne_eq, Function.onFun]
    intro pki hpk qkj hqk hpq
    apply Nat.coprime_pow_primes _ _ (d.h_muls _ hpk) (d.h_muls _ hqk)
    exact d.h_muls_setPairwise hpk hqk hpq
  congr! 2 with pki hpki
  · have : pki.1.Prime := d.h_muls _ (by simpa using hpki)
    rw [cast_sigma_one_apply_prime_pow_aux' this, cast_sigma_one_apply_prime_pow_aux' this]
    rw [div_div_div_cancel_right₀]
    rw [Nat.cast_ne_zero]
    have := this.two_le
    omega
  congr! 1 with p hp
  rw [sigma_one_apply_prime]
  simp only [List.mem_toFinset] at hp
  exact d.h_divs _ hp

lemma test {p a b c : ℕ} (hp : 1 ≤ p) :
    (p ^ (a + b + c) - 1) * (p ^ a - 1) ≤ (p ^ (a + b) - 1) * (p ^ (a + c) - 1) := by
  zify
  have (n : ℕ) : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp
  simp only [Nat.cast_sub (this _), Nat.cast_one]
  simp only [pow_add, Nat.cast_mul, Nat.cast_pow]
  have (n : ℕ) : (1 : ℤ) ≤ p ^ n := mod_cast (this n)
  have : (0 : ℤ) ≤ (p ^ b - 1) * (p ^ c - 1) := mul_nonneg (by grind) (by grind)
  linear_combination p ^ a * this

lemma inequality {p a a' b : ℕ} (ha : a' ≤ a) (hp : 2 ≤ p) :
    ((p ^ (a + b + 1) - 1 : ℕ) / (p ^ (a + 1) - 1 : ℕ) : ℚ) ≤
      (p ^ (a' + b + 1) - 1 : ℕ) / (p ^ (a' + 1) - 1 : ℕ) := by
  have : ∀ n, p ^ (n + 1) - 1 ≠ 0 := by
    intro n
    have : 2 ≤ p ^ (n + 1) := hp.trans (Nat.le_pow (by simp))
    lia
  rw [div_le_div_iff₀ (by have := this a; positivity) (by have := this a'; positivity)]
  norm_cast
  obtain ⟨c, rfl⟩ := ha.dest
  have := test (p := p) (a := a' + 1) (b := b) (c := c)
  grind

theorem not_HA' : ∀ i ∈ Finset.Icc d.lo d.hi, ¬ IsHighlyAbundant (lcmRange i) := by
  intro i hi
  set L := lcmRange i with hL
  have hsig_ge :
      (∏ pki ∈ d.muls.toFinset,
        (pki.1 ^ (pki.2.2 + pki.2.1 + 1) - 1 : ℕ) / (pki.1 ^ (pki.2.2 + 1) - 1 : ℕ) : ℚ) /
      (∏ p ∈ d.divs.toFinset, (p + 1)) ≤ σ₁ (d.M i) / σ₁ L := by
    rw [d.sig_eq hi]
    gcongr 2 with pki hpki
    exact inequality (d.h_muls_i hi _ (by simpa using hpki))
      (d.h_muls _ (by simpa using hpki)).two_le
  have : σ₁ L ≤ σ₁ (d.M i) := by
    have := d.h_sigma_prod
    rw [Finset.prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod,
      List.prod_toFinset _ d.h_muls_nodup, List.prod_toFinset _ d.h_muls_nodup,
      List.prod_toFinset _ d.h_divs_nodup] at hsig_ge
    grw [← this, Nat.cast_mul, div_div, div_self, one_le_div] at hsig_ge
    · exact mod_cast hsig_ge
    · simp [L]
    · rw [← Nat.cast_mul, Nat.cast_ne_zero]
      simp only [ne_eq, mul_eq_zero, List.prod_eq_zero_iff, List.mem_map, Prod.exists,
        Nat.add_eq_zero_iff, one_ne_zero, and_false, exists_const, or_false, not_exists, not_and]
      intro p k i hpki
      have : p.Prime := d.h_muls _ hpki
      have : 2 ≤ p ^ (i + 1) := this.two_le.trans (Nat.le_pow (by simp))
      omega
  intro h
  have := h (d.M i) (d.M_pos hi) (d.M_lt_L hi)
  lia

end ProofData

namespace List

variable {α : Type}

def BChain (r : α → α → Bool) : List α → Bool
  | [] => true
  | [_] => true
  | a :: b :: xs => r a b && BChain r (b :: xs)

def BChain' (r : α → α → Bool) : List α → Bool :=
  List.rec true fun a bxs t ↦ List.rec true (fun b _ _ ↦ (r a b).and t) bxs

lemma bChain_eq_bChain' (r : α → α → Bool) (l : List α) :
    l.BChain r = l.BChain' r := by
  fun_induction List.BChain with
  | case1 => rfl
  | case2 => rfl
  | case3 _ _ _ ih =>
    rw [BChain']
    dsimp
    rw [ih]
    rfl

@[simp] lemma bChain_iff_isChain (r : α → α → Bool) (l : List α) :
    l.BChain r ↔ l.IsChain (r · ·) := by fun_induction List.BChain with simp [*]

def allPrimeMuls (l : List (ℕ × ℕ × ℕ)) : Prop := ∀ x ∈ l, x.1.Prime
lemma allPrimeMuls_nil : allPrimeMuls [] := by simp [allPrimeMuls]
lemma allPrimeMuls_cons {x : ℕ} {y : ℕ × ℕ} {xs : List (ℕ × ℕ × ℕ)} (h₁ : x.Prime)
    (h₂ : allPrimeMuls xs) :
    allPrimeMuls ((x, y) :: xs) := by
  simp_all +contextual [allPrimeMuls]
  exact h₂

def allPrime (l : List ℕ) : Prop := ∀ x ∈ l, x.Prime
lemma allPrime_nil : allPrime [] := by simp [allPrime]
lemma allPrime_cons {x : ℕ} {xs : List ℕ} (h₁ : x.Prime) (h₂ : allPrime xs) :
    allPrime (x :: xs) := by
  simp_all +contextual [allPrime]

end List

section

theorem combine_ranges {a b c d : ℕ}
    (h : c.ble (b + 1))
    (h₁ : ∀ i, a ≤ i → i ≤ b → ¬ IsHighlyAbundant (lcmRange i))
    (h₂ : ∀ i, c ≤ i → i ≤ d → ¬ IsHighlyAbundant (lcmRange i)) :
    ∀ i, a ≤ i → i ≤ d → ¬ IsHighlyAbundant (lcmRange i) := by
  intro i ha hd
  simp only [Nat.ble_eq] at h
  grind

end

theorem not_HA (lo hi : ℕ) (muls : List (ℕ × ℕ × ℕ)) (divs : List ℕ)
    (muls_chain : muls.BChain (Nat.blt ·.1 ·.1))
    (divs_chain : divs.BChain Nat.blt)
    (h_disjoint' : muls.all (fun i ↦ !divs.contains i.1))
    (h_divs : divs.all fun p ↦ p.ble lo && hi.blt (p ^ 2))
    (h_muls : muls.all fun pki ↦ (pki.1.pow pki.2.2).ble hi && hi.blt (pki.1.pow pki.2.2.succ))
    (h_sigma_prod :
      Nat.ble ((muls.map (fun pk ↦ (pk.1 ^ (pk.2.2 + 1) - 1))).prod * (divs.map (· + 1)).prod)
        (muls.map (fun pk ↦ (pk.1 ^ (pk.2.2 + pk.2.1 + 1) - 1))).prod)
    (h_prod : Nat.blt (muls.map (fun pk ↦ pk.1 ^ pk.2.1)).prod divs.prod)
    (h_muls_prime : muls.allPrimeMuls)
    (h_divs_prime : divs.allPrime) :
    ∀ i, lo ≤ i → i ≤ hi → ¬ IsHighlyAbundant (lcmRange i) := by
  intro i hlo hhi
  let d : ProofData :=
  { lo := lo,
    hi := hi,
    muls := muls,
    divs := divs,
    h_muls := h_muls_prime,
    h_divs := h_divs_prime,
    h_muls_chain := by simpa using muls_chain,
    h_divs_chain := by simpa using divs_chain,
    h_disjoint' := by simpa using h_disjoint',
    h_divs_lo := by simp_all,
    h_divs_hi := by simp_all,
    h_muls_hi := by simpa using h_muls,
    h_sigma_prod := by simpa using h_sigma_prod,
    h_prod := by simpa using h_prod }
  exact d.not_HA' i (by simp_all [d])

section

open Lean Elab

declare_syntax_cat bounds
declare_syntax_cat primepow
declare_syntax_cat dict
declare_syntax_cat entry
declare_syntax_cat entri
declare_syntax_cat ladder

syntax "[" num "," ppSpace num "]" : bounds
syntax num ":" ppSpace num : primepow
syntax "{" primepow,* "}" : dict
syntax bounds ";" ppSpace dict ";" ppSpace dict ppSpace : entry

def ladder : Parser.Parser := leading_parser
  Lean.Parser.sepBy (Parser.categoryParser `tactic 0) "\n"

def parseBounds : TSyntax `bounds → MetaM (ℕ × ℕ)
  | `(bounds| [$lo:num, $hi:num]) => return (lo.getNat, hi.getNat)
  | _ => throwError "??b"

def parsePrimePow : TSyntax `primepow → MetaM (ℕ × ℕ)
  | `(primepow| $k:num : $v:num) => return (k.getNat, v.getNat)
  | _ => throwError "??p"

def parseDict : TSyntax `dict → MetaM (List (ℕ × ℕ))
  | `(dict| { $[$es],*}) => do
    let e ← es.mapM parsePrimePow
    return Array.toList (Array.qsort e (·.1 < ·.1))
  | _ => throwError "??d"

def parseEntry : TSyntax `entry → MetaM (ℕ × ℕ × List (ℕ × ℕ × ℕ) × List ℕ)
  | `(entry| $bounds:bounds; $muls:dict; $divs:dict) => do
    let (lo, hi) ← parseBounds bounds
    let muls ← parseDict muls
    let divs ← parseDict divs
    let mulsl := muls.map fun (p, k) ↦ (p, k, Nat.log p hi)
    let divsl := divs.map (·.1)
    return (lo, hi, mulsl, divsl)
  | _ => throwError "??e"

end

section

open Lean Elab Tactic Meta

syntax "rung" ppSpace entry : tactic
syntax "ladder" ppSpace (entry,+,?) : tactic

def proveAllPrimeMuls : (l : List (ℕ × ℕ × ℕ)) → TacticM Expr
  | [] => return mkConst `List.allPrimeMuls_nil
  | (p, k) :: xs => do
    let h₁ ← Prime.mkCachedPrimalityProof p
    let h₂ ← proveAllPrimeMuls xs
    return mkApp5 (mkConst ``List.allPrimeMuls_cons) (mkNatLit p) (toExpr k) (toExpr xs) h₁ h₂

def proveAllPrime : (l : List ℕ) → TacticM Expr
  | [] => return mkConst `List.allPrime_nil
  | p :: xs => do
    let h₁ ← Prime.mkCachedPrimalityProof p
    let h₂ ← proveAllPrime xs
    return mkApp4 (mkConst ``List.allPrime_cons) (mkNatLit p) (toExpr xs) h₁ h₂

def proveRung (lo hi : ℕ) (muls : List (ℕ × ℕ × ℕ)) (divs : List ℕ) : TacticM Expr := do
  let pf1 ← proveAllPrimeMuls muls
  let pf2 ← proveAllPrime divs
  let pf3 := mkApp4 (mkConst ``not_HA) (mkNatLit lo) (mkNatLit hi) (toExpr muls) (toExpr divs)
  return mkApp9 pf3 reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue
    reflBoolTrue pf1 pf2

-- elab_rules : tactic
--   | `(tactic| rung $e) =>
    -- liftMetaFinishingTactic fun goal ↦ do
    -- let (lo, hi, muls, divs) ← parseEntry e
    -- let pf ← proveRung lo hi muls divs
    -- goal.assign pf

def proveLadder : (l : List (ℕ × ℕ × List (ℕ × ℕ × ℕ) × List ℕ)) → TacticM ((ℕ × ℕ) × Expr)
  | [] => throwError "empty ladder"
  | [(lo, hi, muls, divs)] => do
    let pf1 ← proveRung lo hi muls divs
    return ((lo, hi), pf1)
  | (lo, hi, muls, divs) :: xs => do
    let pf1 ← proveRung lo hi muls divs
    let ((lo', hi'), pf2) ← proveLadder xs
    return ((lo, hi'), mkApp7 (mkConst ``combine_ranges) (mkNatLit lo) (mkNatLit hi) (mkNatLit lo')
      (mkNatLit hi') reflBoolTrue pf1 pf2)

elab_rules : tactic
  | `(tactic| ladder $[$es],*) => do
    let r := Array.toList (← es.mapM (fun e ↦ parseEntry e))
    withMainContext do
      let g ← getMainGoal
      let (_, pf) ← proveLadder r
      g.assign pf
      replaceMainGoal []

end

end
