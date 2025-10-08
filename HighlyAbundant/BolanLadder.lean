/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.Basic

/-!
# Proofs of non-high-abundance of lcm(1..n) for the n where it is true, for n ≤ 100000

This file will soon be made obsolete by later files, which give these proofs in a faster and more
efficient way.
-/

open ArithmeticFunction

section

structure PrimeList where
  entries : List (ℕ × ℕ)
  prime : ∀ pk ∈ entries, pk.1.Prime := by norm_num
  -- TODO: change to make better use of reflection
  isChain : entries.IsChain (fun a b ↦ a.1 < b.1) := by decide

namespace PrimeList

variable (l : PrimeList)

attribute [grind] PrimeList.prime PrimeList.isChain

local instance : IsStrictWeakOrder (ℕ × ℕ) (fun a b ↦ a.1 < b.1) where
  incomp_trans := by grind
  trans := by grind
  irrefl := by grind

@[grind] lemma sorted : l.entries.Sorted (fun a b ↦ a.1 < b.1) := l.isChain.pairwise

@[grind] lemma pairwise_fst : l.entries.Pairwise (fun a b ↦ a.1 ≠ b.1) := l.sorted.imp (by grind)

@[grind] lemma nodup : l.entries.Nodup := l.sorted.nodup

def prod : ℕ := l.entries.foldl (fun acc pk ↦ acc * pk.1 ^ pk.2) 1

def sigma : ℕ := l.entries.foldl (fun acc pk ↦ acc * ((pk.1 ^ (pk.2 + 1) - 1) / (pk.1 - 1))) 1

lemma prod_eq_listProd : l.prod = (l.entries.map (fun pk ↦ pk.1 ^ pk.2)).prod := by
  rw [prod, List.prod_eq_foldl, List.foldl_map]

lemma prod_eq_finsetProd : l.prod = ∏ pk ∈ l.entries.toFinset, pk.1 ^ pk.2 := by
  rw [prod_eq_listProd, List.prod_toFinset _ (by grind)]

lemma dvd_of_mem {p k : ℕ} (hpk : (p, k) ∈ l.entries) : p ^ k ∣ l.prod := by
  rw [prod_eq_finsetProd]
  exact Finset.dvd_prod_of_mem _ (s := l.entries.toFinset) (a := (p, k)) (by simpa)

lemma prod_pos : 0 < l.prod := by
  rw [prod_eq_listProd]
  apply List.prod_pos
  simp only [List.mem_map, Prod.exists, forall_exists_index, and_imp]
  rintro _ p k hpk rfl
  exact Nat.pow_pos (l.prime _ hpk).pos

lemma mem_of_dvd {p : ℕ} (hp : p.Prime) (h : p ∣ l.prod) : ∃ k, (p, k) ∈ l.entries := by
  rw [prod_eq_finsetProd] at h
  obtain ⟨⟨q, k⟩, h₁, h₂⟩ := Prime.exists_mem_finset_dvd hp.prime h
  cases Nat.prime_eq_prime_of_dvd_pow hp (l.prime _ (by simpa using h₁)) h₂
  use k
  simpa using h₁

lemma sigmaPrimeList_eq_listProd :
    l.sigma = (l.entries.map (fun pk ↦ (pk.1 ^ (pk.2 + 1) - 1) / (pk.1 - 1))).prod := by
  rw [sigma, List.prod_eq_foldl, List.foldl_map]

lemma prime_pow_coprime_prod {p k : ℕ}
    (hp : p.Prime) (hpk : ∀ x ∈ l.entries, x.1 ≠ p) :
    (p ^ k).Coprime l.prod := by
  rw [prod_eq_listProd, Nat.coprime_list_prod_right_iff]
  simp only [List.mem_map, Prod.exists, forall_exists_index, and_imp]
  rintro _ p' k' h rfl
  apply Nat.Coprime.pow_left
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_primes hp (l.prime _ h)]
  grind

lemma sigma_ofPrimeList : σ₁ l.prod = l.sigma := by
  rw [prod_eq_listProd, sigmaPrimeList_eq_listProd]
  cases l with | mk ps hps₁ hps₂
  induction ps with
  | nil => simp
  | cons pk tl ih =>
    rcases pk with ⟨p, k⟩
    dsimp only [List.map_cons, List.prod_cons]
    simp only at ih
    simp only [List.mem_cons, forall_eq_or_imp] at hps₁
    specialize ih hps₁.2 hps₂.tail
    rw [isMultiplicative_sigma.map_mul_of_coprime, ih, sigma_one_apply_prime_pow' hps₁.1]
    let l : PrimeList := ⟨tl, hps₁.2, hps₂.tail⟩
    convert_to (p ^ k).gcd l.prod = 1 using 2
    · rw [prod_eq_listProd]
    apply prime_pow_coprime_prod _ hps₁.1
    have := hps₂.pairwise
    grind [List.pairwise_cons]

lemma prod_dvd_lcmRange {lo n : ℕ} (h : l.entries.all fun pk ↦ pk.1 ^ pk.2 ≤ lo) (hlo : lo ≤ n) :
    l.prod ∣ lcmRange n := by
  rw [prod_eq_finsetProd]
  simp only [List.all_eq_true, decide_eq_true_eq, Prod.forall] at h
  apply Finset.prod_dvd_of_isRelPrime
  · simp only [Set.Pairwise, Function.onFun, List.coe_toFinset, Set.mem_setOf_eq,
      ← Nat.coprime_iff_isRelPrime, ne_eq, Prod.forall]
    intro p₁ k₁ h₁ p₂ k₂ h₂ h
    apply Nat.coprime_pow_primes _ _ (l.prime _ h₁) (l.prime _ h₂)
    exact l.pairwise_fst.set_pairwise (by grind [Symmetric]) h₁ h₂ h
  · simp only [List.mem_toFinset]
    intro pk hpk
    exact dvd_lcmRange_of_le (pow_ne_zero _ (l.prime _ hpk).ne_zero) ((h _ _ hpk).trans hlo)

lemma prod_coprime_lcmRange_div_aux {lo hi n p k : ℕ} (hpk : (p, k) ∈ l.entries)
    (h : l.entries.all fun pk ↦ pk.1 ^ pk.2 ≤ lo ∧ hi < pk.1 ^ (pk.2 + 1))
    (hlo : lo ≤ n) (hhi : n ≤ hi) :
    ¬ (p ∣ lcmRange n / l.prod) := by
  simp only [Bool.decide_and, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    Prod.forall, imp_and, forall_and] at h
  have dvd := l.prod_dvd_lcmRange (n := n) (by simpa using h.1) hlo
  intro h'
  rw [Nat.dvd_div_iff_mul_dvd dvd] at h'
  have : p ^ (k + 1) ∣ lcmRange n := by
    rw [Nat.pow_succ]
    exact (Nat.mul_dvd_mul_right (dvd_of_mem _ hpk) _).trans h'
  exact not_dvd_of_lt (hhi.trans_lt (h.2 _ _ hpk)) (l.prime _ hpk) this

lemma prod_coprime_lcmRange_div₁ {lo hi n : ℕ}
    (h : l.entries.all fun pk ↦ pk.1 ^ pk.2 ≤ lo ∧ hi < pk.1 ^ (pk.2 + 1))
    (hlo : lo ≤ n) (hhi : n ≤ hi) :
    l.prod.Coprime (lcmRange n / l.prod) := by
  apply Nat.coprime_of_dvd
  intro p hp hpl h'
  obtain ⟨k, hk⟩ := l.mem_of_dvd hp hpl
  exact l.prod_coprime_lcmRange_div_aux hk h hlo hhi h'

lemma prod_coprime_lcmRange_div₂ (m : PrimeList) {lo hi n : ℕ}
    (hl : l.entries.all fun pk ↦ pk.1 ^ pk.2 ≤ lo ∧ hi < pk.1 ^ (pk.2 + 1))
    -- TODO: consider changing hlm to something easier to decide
    (hlm : ∀ i ∈ m.entries, i.1 ≤ hi → ∃ j ∈ l.entries, j.1 = i.1)
    (hlo : lo ≤ n) (hhi : n ≤ hi) :
    m.prod.Coprime (lcmRange n / l.prod) := by
  apply Nat.coprime_of_dvd
  intro p hp hpm h'
  have dvd : l.prod ∣ lcmRange n := l.prod_dvd_lcmRange (n := n) (by grind) hlo
  obtain ⟨k, hk⟩ := m.mem_of_dvd hp hpm
  rcases lt_or_ge hi p with hnp | hpn
  · have : ¬ p ∣ lcmRange n := by
      simpa using not_dvd_of_lt (k := 0) (by grind) hp
    apply this
    rw [Nat.dvd_div_iff_mul_dvd dvd] at h'
    exact (Nat.dvd_mul_left _ _).trans h'
  obtain ⟨⟨p, k'⟩, h, (rfl : p = _)⟩ := hlm _ hk hpn
  exact l.prod_coprime_lcmRange_div_aux h (by simpa using hl) hlo hhi h'

end PrimeList

open PrimeList

theorem prove_not_HA {lo hi : ℕ} (l m : PrimeList)
    (hl : l.entries.all fun pk ↦ pk.1 ^ pk.2 ≤ lo ∧ hi < pk.1 ^ (pk.2 + 1))
    (hlm : ∀ i ∈ m.entries, i.1 ≤ hi → ∃ j ∈ l.entries, j.1 = i.1)
    (hprod : m.prod < l.prod)
    (hsigma : l.sigma ≤ m.sigma) :
    ∀ i ∈ Finset.Icc lo hi, ¬ IsHighlyAbundant (lcmRange i) := by
  intro i hi
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.1 hi
  set l' : PrimeList := l
  set l : ℕ := l'.prod
  set m' : PrimeList := m
  set m : ℕ := m'.prod
  set K : ℕ := lcmRange i / l
  have hli : l ∣ lcmRange i := prod_dvd_lcmRange _ (by grind) hlo
  have hL : lcmRange i = l * K := by rw [Nat.mul_div_cancel' hli]
  have hlK : l.Coprime K := prod_coprime_lcmRange_div₁ _ hl hlo hhi
  have hmK : m.Coprime K := prod_coprime_lcmRange_div₂ _ _ hl hlm hlo hhi
  have hl : 0 < l := prod_pos _
  have hm : 0 < m := prod_pos _
  have hK : 0 < K := by
    simp only [Nat.div_pos_iff, K]
    refine ⟨hl, ?_⟩
    apply Nat.le_of_dvd (by simp) hli
  intro h
  have hml : m < l := hprod
  have hML : m * K < lcmRange i := by
    rw [hL]
    exact Nat.mul_lt_mul_of_pos_right hml hK
  have := h (m * K) (by positivity) hML
  rw [hL, isMultiplicative_sigma.map_mul_of_coprime hmK,
    isMultiplicative_sigma.map_mul_of_coprime hlK] at this
  have h₁ := Nat.lt_of_mul_lt_mul_right this
  simp only [l, m, sigma_ofPrimeList] at h₁
  have h₂ : l'.sigma ≤ m'.sigma := hsigma
  exact h₁.not_ge h₂

theorem prove_not_HA' {lo hi : ℕ} (l m : List (ℕ × ℕ))
    (hlp : ∀ pk ∈ l, pk.1.Prime := by norm_num)
    (hlc : l.IsChain fun a b ↦ a.1 < b.1 := by decide)
    (hmp : ∀ pk ∈ m, pk.1.Prime := by norm_num)
    (hmc : m.IsChain fun a b ↦ a.1 < b.1 := by decide)
    (hl : l.all fun pk ↦ pk.1 ^ pk.2 ≤ lo ∧ hi < pk.1 ^ (pk.2 + 1) := by decide)
    (hlm : ∀ i ∈ m, i.1 ≤ hi → ∃ j ∈ l, j.1 = i.1 := by decide)
    (hprod : Nat.blt (m.foldl (fun acc pk ↦ acc * pk.1 ^ pk.2) 1)
      (l.foldl (fun acc pk ↦ acc * pk.1 ^ pk.2) 1) := by decide)
    (hsigma : Nat.ble (l.foldl (fun acc pk ↦ acc * ((pk.1 ^ (pk.2 + 1) - 1) / (pk.1 - 1))) 1)
      (m.foldl (fun acc pk ↦ acc * ((pk.1 ^ (pk.2 + 1) - 1) / (pk.1 - 1))) 1) := by decide) :
    ∀ i ∈ Finset.Icc lo hi, ¬ IsHighlyAbundant (lcmRange i) := by
  let l : PrimeList := ⟨l, hlp, hlc⟩
  let m : PrimeList := ⟨m, hmp, hmc⟩
  exact prove_not_HA l m hl hlm (by simpa using hprod) (by simpa using hsigma)

set_option linter.style.longLine false

lemma not_HA_block_256 : ∀ i ∈ Finset.Icc 256 256, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 8), (3, 5), (5, 3), (7, 2), (17, 1), (19, 1), (227, 1), (239, 1), (241, 1)]
    [(2, 7), (3, 7), (5, 4), (7, 3), (17, 2), (19, 2), (257, 1)]

lemma not_HA_block_71 : ∀ i ∈ Finset.Icc 71 78, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 6), (3, 3), (5, 2), (67, 1), (71, 1)]
    [(2, 8), (3, 4), (5, 3), (79, 1)]

lemma not_HA_block_79 : ∀ i ∈ Finset.Icc 79 80, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 6), (3, 3), (5, 2), (11, 1), (67, 1), (79, 1)]
    [(2, 11), (3, 4), (5, 3), (11, 2)]

lemma not_HA_block_97 : ∀ i ∈ Finset.Icc 97 120, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 6), (3, 4), (5, 2), (11, 1), (13, 1), (89, 1), (97, 1)]
    [(2, 8), (3, 5), (5, 3), (11, 2), (13, 2)]

lemma not_HA_block_113 : ∀ i ∈ Finset.Icc 113 124, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 6), (5, 2), (7, 2), (101, 1), (113, 1)]
    [(2, 7), (5, 3), (7, 3), (163, 1)]

lemma not_HA_block_149 : ∀ i ∈ Finset.Icc 149 156, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 7), (5, 3), (13, 1), (137, 1), (149, 1)]
    [(2, 8), (5, 4), (13, 2), (157, 1)]

lemma not_HA_block_151 : ∀ i ∈ Finset.Icc 151 168, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 7), (5, 3), (13, 1), (149, 1), (151, 1)]
    [(2, 8), (5, 4), (13, 2), (173, 1)]

lemma not_HA_block_173 : ∀ i ∈ Finset.Icc 173 242, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 7), (3, 4), (7, 2), (17, 1), (19, 1), (157, 1), (173, 1)]
    [(2, 9), (3, 5), (7, 3), (17, 2), (19, 2)]

lemma not_HA_block_227 : ∀ i ∈ Finset.Icc 227 255, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 7), (5, 3), (17, 1), (197, 1), (227, 1)]
    [(2, 8), (5, 4), (17, 2), (263, 1)]

-- skipping 256
lemma not_HA_block_257 : ∀ i ∈ Finset.Icc 257 306, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 8), (3, 5), (5, 3), (7, 2), (251, 1), (257, 1)]
    [(2, 9), (3, 6), (5, 4), (7, 3), (307, 1)]

lemma not_HA_block_277 : ∀ i ∈ Finset.Icc 277 330, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 8), (3, 5), (5, 3), (7, 2), (251, 1), (277, 1)]
    [(2, 9), (3, 6), (5, 4), (7, 3), (331, 1)]

lemma not_HA_block_313 : ∀ i ∈ Finset.Icc 313 360, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 8), (5, 3), (19, 1), (241, 1), (313, 1)]
    [(2, 9), (5, 4), (19, 2), (397, 1)]

lemma not_HA_block_359 : ∀ i ∈ Finset.Icc 359 382, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 8), (3, 5), (23, 1), (337, 1), (347, 1), (359, 1)]
    [(2, 10), (3, 6), (23, 2), (383, 1), (397, 1)]

lemma not_HA_block_379 : ∀ i ∈ Finset.Icc 379 438, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 8), (7, 3), (23, 1), (373, 1), (379, 1)]
    [(2, 9), (7, 4), (23, 2), (439, 1)]

lemma not_HA_block_383 : ∀ i ∈ Finset.Icc 383 511, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 8), (5, 3), (23, 1), (379, 1), (383, 1)]
    [(2, 9), (5, 4), (23, 2), (631, 1)]

lemma not_HA_block_449 : ∀ i ∈ Finset.Icc 449 511, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 8), (5, 3), (23, 1), (439, 1), (449, 1)]
    [(2, 9), (5, 4), (23, 2), (857, 1)]

lemma not_HA_block_449' : ∀ i ∈ Finset.Icc 512 528, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 9), (5, 3), (23, 1), (439, 1), (449, 1)]
    [(2, 10), (5, 4), (23, 2), (857, 1)]

lemma not_HA_block_521 : ∀ i ∈ Finset.Icc 521 624, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 9), (5, 3), (29, 1), (457, 1), (521, 1)]
    [(2, 10), (5, 4), (29, 2), (821, 1)]

lemma not_HA_block_571 : ∀ i ∈ Finset.Icc 571 624, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(3, 5), (5, 3), (29, 1), (563, 1), (571, 1)]
    [(3, 6), (5, 4), (29, 2), (739, 1)]

lemma not_HA_block_571' : ∀ i ∈ Finset.Icc 625 728, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(3, 5), (5, 4), (29, 1), (563, 1), (571, 1)]
    [(3, 6), (5, 5), (29, 2), (739, 1)]

lemma not_HA_block_691 : ∀ i ∈ Finset.Icc 691 732, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 9), (11, 2), (29, 1), (677, 1), (691, 1)]
    [(2, 10), (11, 3), (29, 2), (733, 1)]

lemma not_HA_block_701 : ∀ i ∈ Finset.Icc 701 738, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 9), (11, 2), (29, 1), (673, 1), (701, 1)]
    [(2, 10), (11, 3), (29, 2), (739, 1)]

lemma not_HA_block_727 : ∀ i ∈ Finset.Icc 727 786, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 9), (11, 2), (29, 1), (691, 1), (727, 1)]
    [(2, 10), (11, 3), (29, 2), (787, 1)]

lemma not_HA_block_739 : ∀ i ∈ Finset.Icc 739 820, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 9), (11, 2), (29, 1), (709, 1), (739, 1)]
    [(2, 10), (11, 3), (29, 2), (821, 1)]

lemma not_HA_block_743 : ∀ i ∈ Finset.Icc 743 840, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 9), (11, 2), (29, 1), (733, 1), (743, 1)]
    [(2, 10), (11, 3), (29, 2), (853, 1)]

lemma not_HA_block_811 : ∀ i ∈ Finset.Icc 811 1023, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 9), (3, 6), (7, 3), (11, 2), (797, 1), (811, 1)]
    [(2, 10), (3, 7), (7, 4), (11, 3), (1399, 1)]

lemma not_HA_block_1019 : ∀ i ∈ Finset.Icc 1019 1030, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(7, 3), (11, 2), (13, 2), (1013, 1), (1019, 1)]
    [(7, 4), (11, 3), (13, 3), (1031, 1)]

lemma not_HA_block_1031 : ∀ i ∈ Finset.Icc 1031 1116, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(5, 4), (11, 2), (17, 2), (1013, 1), (1031, 1)]
    [(5, 5), (11, 3), (17, 3), (1117, 1)]

lemma not_HA_block_1051 : ∀ i ∈ Finset.Icc 1051 1330, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(5, 4), (11, 2), (13, 2), (1013, 1), (1051, 1)]
    [(5, 5), (11, 3), (13, 3), (1489, 1)]

lemma not_HA_block_1291 : ∀ i ∈ Finset.Icc 1291 2047, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 10), (3, 6), (7, 3), (13, 2), (1249, 1), (1291, 1)]
    [(2, 11), (3, 7), (7, 4), (13, 3), (2953, 1)]

lemma not_HA_block_1531 : ∀ i ∈ Finset.Icc 1531 2062, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(5, 4), (13, 2), (17, 2), (1489, 1), (1531, 1)]
    [(5, 5), (13, 3), (17, 3), (2063, 1)]

lemma not_HA_block_1621 : ∀ i ∈ Finset.Icc 1621 2196, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(5, 4), (13, 2), (17, 2), (1559, 1), (1621, 1)]
    [(5, 5), (13, 3), (17, 3), (2287, 1)]

lemma not_HA_block_2131 : ∀ i ∈ Finset.Icc 2131 2186, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 11), (3, 6), (17, 2), (19, 2), (2089, 1), (2131, 1)]
    [(2, 12), (3, 7), (17, 3), (19, 3), (2297, 1)]

lemma not_HA_block_2131' : ∀ i ∈ Finset.Icc 2187 2296, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 11), (3, 7), (17, 2), (19, 2), (2089, 1), (2131, 1)]
    [(2, 12), (3, 8), (17, 3), (19, 3), (2297, 1)]

lemma not_HA_block_2203 : ∀ i ∈ Finset.Icc 2203 2380, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(5, 4), (17, 2), (23, 2), (2113, 1), (2203, 1)]
    [(5, 5), (17, 3), (23, 3), (2381, 1)]

lemma not_HA_block_2239 : ∀ i ∈ Finset.Icc 2239 2970, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(5, 4), (17, 2), (19, 2), (2143, 1), (2239, 1)]
    [(5, 5), (17, 3), (19, 3), (2971, 1)]

lemma not_HA_block_2339 : ∀ i ∈ Finset.Icc 2339 3124, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(5, 4), (17, 2), (19, 2), (2311, 1), (2339, 1)]
    [(5, 5), (17, 3), (19, 3), (3347, 1)]

lemma not_HA_block_3049 : ∀ i ∈ Finset.Icc 3049 4095, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 11), (3, 7), (17, 2), (19, 2), (3001, 1), (3049, 1)]
    [(2, 12), (3, 8), (17, 3), (19, 3), (4721, 1)]

lemma not_HA_block_3169 : ∀ i ∈ Finset.Icc 3169 4095, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 11), (3, 7), (17, 2), (19, 2), (3089, 1), (3169, 1)]
    [(2, 12), (3, 8), (17, 3), (19, 3), (5051, 1)]

lemma not_HA_block_3169' : ∀ i ∈ Finset.Icc 4096 4912, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 12), (3, 7), (17, 2), (19, 2), (3089, 1), (3169, 1)]
    [(2, 13), (3, 8), (17, 3), (19, 3), (5051, 1)]

lemma not_HA_block_4799 : ∀ i ∈ Finset.Icc 4799 6560, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 12), (3, 7), (19, 2), (23, 2), (4787, 1), (4799, 1)]
    [(2, 13), (3, 8), (19, 3), (23, 3), (8761, 1)]

lemma not_HA_block_5581 : ∀ i ∈ Finset.Icc 5581 6858, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(7, 4), (19, 2), (23, 2), (5531, 1), (5581, 1)]
    [(7, 5), (19, 3), (23, 3), (10091, 1)]

lemma not_HA_block_6793 : ∀ i ∈ Finset.Icc 6793 8191, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 12), (3, 8), (23, 2), (29, 2), (6791, 1), (6793, 1)]
    [(2, 13), (3, 9), (23, 3), (29, 3), (11527, 1)]

lemma not_HA_block_8081 : ∀ i ∈ Finset.Icc 8081 8886, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(11, 3), (23, 2), (29, 2), (8069, 1), (8081, 1)]
    [(11, 4), (23, 3), (29, 3), (8887, 1)]

lemma not_HA_block_8821 : ∀ i ∈ Finset.Icc 8821 10558, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(11, 3), (23, 2), (29, 2), (8783, 1), (8821, 1)]
    [(11, 4), (23, 3), (29, 3), (10559, 1)]

lemma not_HA_block_10457 : ∀ i ∈ Finset.Icc 10457 12166, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(7, 4), (23, 2), (29, 2), (10429, 1), (10457, 1)]
    [(7, 5), (23, 3), (29, 3), (23357, 1)]

lemma not_HA_block_12161 : ∀ i ∈ Finset.Icc 12161 15624, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(2, 13), (5, 5), (19, 3), (29, 2), (12097, 1), (12161, 1)]
    [(2, 14), (5, 6), (19, 4), (29, 3), (26699, 1)]

lemma not_HA_block_13903 : ∀ i ∈ Finset.Icc 13903 16806, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(7, 4), (29, 2), (31, 2), (13873, 1), (13903, 1)]
    [(7, 5), (29, 3), (31, 3), (30649, 1)]

lemma not_HA_block_16703 : ∀ i ∈ Finset.Icc 16703 23856, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(13, 3), (29, 2), (31, 2), (16693, 1), (16703, 1)]
    [(13, 4), (29, 3), (31, 3), (23857, 1)]

lemma not_HA_block_22031 : ∀ i ∈ Finset.Icc 22031 24648, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(157, 1), (163, 1), (167, 1), (173, 1), (179, 1), (181, 1), (191, 1), (193, 1), (197, 1), (199, 1), (211, 1), (223, 1), (227, 1), (229, 1), (233, 1), (239, 1), (241, 1), (21247, 1), (21673, 1), (21859, 1), (21937, 1), (21961, 1), (21977, 1), (21997, 1), (22003, 1), (22031, 1)]
    [(157, 2), (163, 2), (167, 2), (173, 2), (179, 2), (181, 2), (191, 2), (193, 2), (197, 2), (199, 2), (211, 2), (223, 2), (227, 2), (229, 2), (233, 2), (239, 2), (241, 2)]

lemma not_HA_block_23827 : ∀ i ∈ Finset.Icc 23827 26568, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(163, 1), (167, 1), (173, 1), (179, 1), (181, 1), (191, 1), (193, 1), (197, 1), (199, 1), (211, 1), (223, 1), (227, 1), (229, 1), (233, 1), (239, 1), (241, 1), (251, 1), (20173, 1), (22229, 1), (23269, 1), (23311, 1), (23357, 1), (23719, 1), (23761, 1), (23813, 1), (23827, 1)]
    [(163, 2), (167, 2), (173, 2), (179, 2), (181, 2), (191, 2), (193, 2), (197, 2), (199, 2), (211, 2), (223, 2), (227, 2), (229, 2), (233, 2), (239, 2), (241, 2), (251, 2)]

lemma not_HA_block_24379 : ∀ i ∈ Finset.Icc 24379 28560, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(13, 3), (23, 3), (31, 2), (24281, 1), (24379, 1)]
    [(13, 4), (23, 4), (31, 3), (63863, 1)]

lemma not_HA_block_26387 : ∀ i ∈ Finset.Icc 26387 29928, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(173, 1), (179, 1), (181, 1), (191, 1), (193, 1), (197, 1), (199, 1), (211, 1), (223, 1), (227, 1), (229, 1), (233, 1), (239, 1), (241, 1), (251, 1), (257, 1), (263, 1), (23981, 1), (24611, 1), (24851, 1), (25391, 1), (25997, 1), (26017, 1), (26021, 1), (26083, 1), (26387, 1)]
    [(173, 2), (179, 2), (181, 2), (191, 2), (193, 2), (197, 2), (199, 2), (211, 2), (223, 2), (227, 2), (229, 2), (233, 2), (239, 2), (241, 2), (251, 2), (257, 2), (263, 2)]

lemma not_HA_block_29399 : ∀ i ∈ Finset.Icc 29399 32760, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(181, 1), (191, 1), (193, 1), (197, 1), (199, 1), (211, 1), (223, 1), (227, 1), (229, 1), (233, 1), (239, 1), (241, 1), (251, 1), (257, 1), (263, 1), (269, 1), (271, 1), (26417, 1), (26669, 1), (26731, 1), (28183, 1), (28211, 1), (28607, 1), (28859, 1), (29221, 1), (29399, 1)]
    [(181, 2), (191, 2), (193, 2), (197, 2), (199, 2), (211, 2), (223, 2), (227, 2), (229, 2), (233, 2), (239, 2), (241, 2), (251, 2), (257, 2), (263, 2), (269, 2), (271, 2)]

lemma not_HA_block_30757 : ∀ i ∈ Finset.Icc 30757 36480, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(191, 1), (193, 1), (197, 1), (199, 1), (211, 1), (223, 1), (227, 1), (229, 1), (233, 1), (239, 1), (241, 1), (251, 1), (257, 1), (263, 1), (269, 1), (271, 1), (277, 1), (26947, 1), (28789, 1), (29059, 1), (29167, 1), (29297, 1), (30097, 1), (30181, 1), (30197, 1), (30757, 1)]
    [(191, 2), (193, 2), (197, 2), (199, 2), (211, 2), (223, 2), (227, 2), (229, 2), (233, 2), (239, 2), (241, 2), (251, 2), (257, 2), (263, 2), (269, 2), (271, 2), (277, 2)]

lemma not_HA_block_34361 : ∀ i ∈ Finset.Icc 34361 38808, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(197, 1), (199, 1), (211, 1), (223, 1), (227, 1), (229, 1), (233, 1), (239, 1), (241, 1), (251, 1), (257, 1), (263, 1), (269, 1), (271, 1), (277, 1), (281, 1), (283, 1), (27997, 1), (29131, 1), (30323, 1), (32609, 1), (32869, 1), (33487, 1), (33599, 1), (34211, 1), (34361, 1)]
    [(197, 2), (199, 2), (211, 2), (223, 2), (227, 2), (229, 2), (233, 2), (239, 2), (241, 2), (251, 2), (257, 2), (263, 2), (269, 2), (271, 2), (277, 2), (281, 2), (283, 2)]

lemma not_HA_block_36541 : ∀ i ∈ Finset.Icc 36541 44520, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(211, 1), (223, 1), (227, 1), (229, 1), (233, 1), (239, 1), (241, 1), (251, 1), (257, 1), (263, 1), (269, 1), (271, 1), (277, 1), (281, 1), (283, 1), (293, 1), (307, 1), (32621, 1), (33247, 1), (34841, 1), (34871, 1), (35521, 1), (35729, 1), (36073, 1), (36493, 1), (36541, 1)]
    [(211, 2), (223, 2), (227, 2), (229, 2), (233, 2), (239, 2), (241, 2), (251, 2), (257, 2), (263, 2), (269, 2), (271, 2), (277, 2), (281, 2), (283, 2), (293, 2), (307, 2)]

lemma not_HA_block_44501 : ∀ i ∈ Finset.Icc 44501 49728, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(223, 1), (227, 1), (229, 1), (233, 1), (239, 1), (241, 1), (251, 1), (257, 1), (263, 1), (269, 1), (271, 1), (277, 1), (281, 1), (283, 1), (293, 1), (307, 1), (311, 1), (313, 1), (317, 1), (35837, 1), (36187, 1), (38461, 1), (39133, 1), (39419, 1), (41593, 1), (43411, 1), (43577, 1), (43669, 1), (44501, 1)]
    [(223, 2), (227, 2), (229, 2), (233, 2), (239, 2), (241, 2), (251, 2), (257, 2), (263, 2), (269, 2), (271, 2), (277, 2), (281, 2), (283, 2), (293, 2), (307, 2), (311, 2), (313, 2), (317, 2)]

lemma not_HA_block_45181 : ∀ i ∈ Finset.Icc 45181 51528, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(227, 1), (229, 1), (233, 1), (239, 1), (241, 1), (251, 1), (257, 1), (263, 1), (269, 1), (271, 1), (277, 1), (281, 1), (283, 1), (293, 1), (307, 1), (311, 1), (313, 1), (317, 1), (331, 1), (36871, 1), (36973, 1), (41357, 1), (41969, 1), (42443, 1), (43793, 1), (43963, 1), (44621, 1), (44797, 1), (45181, 1)]
    [(227, 2), (229, 2), (233, 2), (239, 2), (241, 2), (251, 2), (257, 2), (263, 2), (269, 2), (271, 2), (277, 2), (281, 2), (283, 2), (293, 2), (307, 2), (311, 2), (313, 2), (317, 2), (331, 2)]

lemma not_HA_block_50411 : ∀ i ∈ Finset.Icc 50411 57120, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(239, 1), (241, 1), (251, 1), (257, 1), (263, 1), (269, 1), (271, 1), (277, 1), (281, 1), (283, 1), (293, 1), (307, 1), (311, 1), (313, 1), (317, 1), (331, 1), (337, 1), (347, 1), (349, 1), (43391, 1), (44449, 1), (45833, 1), (45893, 1), (48619, 1), (49139, 1), (49193, 1), (49199, 1), (49757, 1), (50411, 1)]
    [(239, 2), (241, 2), (251, 2), (257, 2), (263, 2), (269, 2), (271, 2), (277, 2), (281, 2), (283, 2), (293, 2), (307, 2), (311, 2), (313, 2), (317, 2), (331, 2), (337, 2), (347, 2), (349, 2)]

lemma not_HA_block_55717 : ∀ i ∈ Finset.Icc 55717 63000, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(251, 1), (257, 1), (263, 1), (269, 1), (271, 1), (277, 1), (281, 1), (283, 1), (293, 1), (307, 1), (311, 1), (313, 1), (317, 1), (331, 1), (337, 1), (347, 1), (349, 1), (353, 1), (359, 1), (45821, 1), (47189, 1), (50077, 1), (50957, 1), (51971, 1), (52051, 1), (52289, 1), (53681, 1), (55457, 1), (55717, 1)]
    [(251, 2), (257, 2), (263, 2), (269, 2), (271, 2), (277, 2), (281, 2), (283, 2), (293, 2), (307, 2), (311, 2), (313, 2), (317, 2), (331, 2), (337, 2), (347, 2), (349, 2), (353, 2), (359, 2)]

lemma not_HA_block_59273 : ∀ i ∈ Finset.Icc 59273 66048, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(257, 1), (263, 1), (269, 1), (271, 1), (277, 1), (281, 1), (283, 1), (293, 1), (307, 1), (311, 1), (313, 1), (317, 1), (331, 1), (337, 1), (347, 1), (349, 1), (353, 1), (359, 1), (367, 1), (373, 1), (379, 1), (55763, 1), (58109, 1), (58147, 1), (58217, 1), (58441, 1), (58573, 1), (58757, 1), (58907, 1), (58913, 1), (58963, 1), (59273, 1)]
    [(257, 2), (263, 2), (269, 2), (271, 2), (277, 2), (281, 2), (283, 2), (293, 2), (307, 2), (311, 2), (313, 2), (317, 2), (331, 2), (337, 2), (347, 2), (349, 2), (353, 2), (359, 2), (367, 2), (373, 2), (379, 2)]

lemma not_HA_block_64937 : ∀ i ∈ Finset.Icc 64937 72360, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(269, 1), (271, 1), (277, 1), (281, 1), (283, 1), (293, 1), (307, 1), (311, 1), (313, 1), (317, 1), (331, 1), (337, 1), (347, 1), (349, 1), (353, 1), (359, 1), (367, 1), (373, 1), (379, 1), (383, 1), (389, 1), (59419, 1), (60703, 1), (61043, 1), (61169, 1), (62827, 1), (63059, 1), (63799, 1), (63823, 1), (64439, 1), (64877, 1), (64937, 1)]
    [(269, 2), (271, 2), (277, 2), (281, 2), (283, 2), (293, 2), (307, 2), (311, 2), (313, 2), (317, 2), (331, 2), (337, 2), (347, 2), (349, 2), (353, 2), (359, 2), (367, 2), (373, 2), (379, 2), (383, 2), (389, 2)]

lemma not_HA_block_70639 : ∀ i ∈ Finset.Icc 70639 78960, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(281, 1), (283, 1), (293, 1), (307, 1), (311, 1), (313, 1), (317, 1), (331, 1), (337, 1), (347, 1), (349, 1), (353, 1), (359, 1), (367, 1), (373, 1), (379, 1), (383, 1), (389, 1), (397, 1), (401, 1), (409, 1), (67651, 1), (67807, 1), (69337, 1), (69557, 1), (70249, 1), (70373, 1), (70381, 1), (70423, 1), (70459, 1), (70489, 1), (70639, 1)]
    [(281, 2), (283, 2), (293, 2), (307, 2), (311, 2), (313, 2), (317, 2), (331, 2), (337, 2), (347, 2), (349, 2), (353, 2), (359, 2), (367, 2), (373, 2), (379, 2), (383, 2), (389, 2), (397, 2), (401, 2), (409, 2)]

lemma not_HA_block_77069 : ∀ i ∈ Finset.Icc 77069 85848, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(293, 1), (307, 1), (311, 1), (313, 1), (317, 1), (331, 1), (337, 1), (347, 1), (349, 1), (353, 1), (359, 1), (367, 1), (373, 1), (379, 1), (383, 1), (389, 1), (397, 1), (401, 1), (409, 1), (419, 1), (421, 1), (71549, 1), (72277, 1), (73351, 1), (75079, 1), (75521, 1), (75539, 1), (75571, 1), (75937, 1), (76579, 1), (76667, 1), (77069, 1)]
    [(293, 2), (307, 2), (311, 2), (313, 2), (317, 2), (331, 2), (337, 2), (347, 2), (349, 2), (353, 2), (359, 2), (367, 2), (373, 2), (379, 2), (383, 2), (389, 2), (397, 2), (401, 2), (409, 2), (419, 2), (421, 2)]

lemma not_HA_block_81077 : ∀ i ∈ Finset.Icc 81077 94248, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(307, 1), (311, 1), (313, 1), (317, 1), (331, 1), (337, 1), (347, 1), (349, 1), (353, 1), (359, 1), (367, 1), (373, 1), (379, 1), (383, 1), (389, 1), (397, 1), (401, 1), (409, 1), (419, 1), (421, 1), (431, 1), (75401, 1), (75403, 1), (75539, 1), (76481, 1), (76541, 1), (77731, 1), (77929, 1), (78649, 1), (79139, 1), (80747, 1), (81077, 1)]
    [(307, 2), (311, 2), (313, 2), (317, 2), (331, 2), (337, 2), (347, 2), (349, 2), (353, 2), (359, 2), (367, 2), (373, 2), (379, 2), (383, 2), (389, 2), (397, 2), (401, 2), (409, 2), (419, 2), (421, 2), (431, 2)]

lemma not_HA_block_86263 : ∀ i ∈ Finset.Icc 86263 97968, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(313, 1), (317, 1), (331, 1), (337, 1), (347, 1), (349, 1), (353, 1), (359, 1), (367, 1), (373, 1), (379, 1), (383, 1), (389, 1), (397, 1), (401, 1), (409, 1), (419, 1), (421, 1), (431, 1), (433, 1), (439, 1), (78401, 1), (79531, 1), (79841, 1), (82267, 1), (82811, 1), (83459, 1), (83833, 1), (84191, 1), (84221, 1), (85121, 1), (86263, 1)]
    [(313, 2), (317, 2), (331, 2), (337, 2), (347, 2), (349, 2), (353, 2), (359, 2), (367, 2), (373, 2), (379, 2), (383, 2), (389, 2), (397, 2), (401, 2), (409, 2), (419, 2), (421, 2), (431, 2), (433, 2), (439, 2)]

lemma not_HA_block_97367 : ∀ i ∈ Finset.Icc 97367 109560, ¬ IsHighlyAbundant (lcmRange i) :=
  prove_not_HA'
    [(331, 1), (337, 1), (347, 1), (349, 1), (353, 1), (359, 1), (367, 1), (373, 1), (379, 1), (383, 1), (389, 1), (397, 1), (401, 1), (409, 1), (419, 1), (421, 1), (431, 1), (433, 1), (439, 1), (443, 1), (449, 1), (457, 1), (461, 1), (88493, 1), (93179, 1), (93559, 1), (94151, 1), (94541, 1), (94841, 1), (95111, 1), (96059, 1), (96323, 1), (96443, 1), (96953, 1), (97367, 1)]
    [(331, 2), (337, 2), (347, 2), (349, 2), (353, 2), (359, 2), (367, 2), (373, 2), (379, 2), (383, 2), (389, 2), (397, 2), (401, 2), (409, 2), (419, 2), (421, 2), (431, 2), (433, 2), (439, 2), (443, 2), (449, 2), (457, 2), (461, 2)]

end

theorem smallish : ∀ n, n ≥ 173 → n ≤ 100000 → ¬ IsHighlyAbundant (lcmRange n) := by
  intro n hn
  grind [not_HA_block_173, not_HA_block_227, not_HA_block_256, not_HA_block_257, not_HA_block_277,
    not_HA_block_313, not_HA_block_359, not_HA_block_379, not_HA_block_383, not_HA_block_449,
    not_HA_block_449', not_HA_block_521, not_HA_block_571, not_HA_block_571', not_HA_block_691,
    not_HA_block_701, not_HA_block_727, not_HA_block_739, not_HA_block_743, not_HA_block_811,
    not_HA_block_1019, not_HA_block_1031, not_HA_block_1051, not_HA_block_1291,
    not_HA_block_1531, not_HA_block_1621, not_HA_block_2131, not_HA_block_2131',
    not_HA_block_2203, not_HA_block_2239, not_HA_block_2339, not_HA_block_3049,
    not_HA_block_3169, not_HA_block_3169', not_HA_block_4799, not_HA_block_5581,
    not_HA_block_6793, not_HA_block_8081, not_HA_block_8821, not_HA_block_10457,
    not_HA_block_12161, not_HA_block_13903, not_HA_block_16703, not_HA_block_22031,
    not_HA_block_23827, not_HA_block_24379, not_HA_block_26387, not_HA_block_29399,
    not_HA_block_30757, not_HA_block_34361, not_HA_block_36541, not_HA_block_44501,
    not_HA_block_45181, not_HA_block_50411, not_HA_block_55717, not_HA_block_59273,
    not_HA_block_64937, not_HA_block_70639, not_HA_block_77069, not_HA_block_81077,
    not_HA_block_86263, not_HA_block_97367, Finset.mem_Icc]
