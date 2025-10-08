/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.Basic

/-!
# Proofs of non-high-abundance of lcm(1..n) for the n where it is true, for prime power n ≤ 373

This file is now made obsolete by later files, which give these proofs in a faster and more
efficient way.
-/

open Nat ArithmeticFunction

local macro "pat1" : tactic =>
  `(tactic|
    { repeat rw [isMultiplicative_sigma.map_mul_of_coprime rfl]
      repeat rw [sigma_one_apply_prime_pow' (by norm_num)]
      norm_num [sigma_one_apply_prime] })

local macro "pat2" : tactic => set_option hygiene false in
  `(tactic|
    { set L : ℕ := lcmRange j
      set K : ℕ := L / l
      set M : ℕ := m * K with hM
      have hL : L = l * K := by decide +kernel
      have hLK : Nat.gcd l K = 1 := by decide +kernel
      have hMK : Nat.gcd m K = 1 := by decide +kernel
      have hK : 0 < K := by decide +kernel
      clear_value K
      intro h
      have := h M (by cutsat) (by cutsat)
      rw [hM, hL, isMultiplicative_sigma.map_mul_of_coprime hMK,
        isMultiplicative_sigma.map_mul_of_coprime hLK, hσL, hσM] at this
      cutsat })

lemma not_HA_block1 : ∀ i ∈ [71, 73], ¬ IsHighlyAbundant (lcmRange i) := by
  set l : ℕ := 2 ^ 6 * 3 ^ 3 * 5 ^ 2 * 67 * 71
  set m : ℕ := 2 ^ 8 * 3 ^ 4 * 5 ^ 3 * 79
  have hσL : σ₁ l = 771022080 := by pat1
  have hσM : σ₁ m = 771650880 := by pat1
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  let j := i
  obtain rfl | rfl := hi
  all_goals pat2

lemma not_HA_block2 : ¬ IsHighlyAbundant (lcmRange 79) := by
  set l : ℕ := 2 ^ 6 * 3 ^ 3 * 5 ^ 2 * 11 * 67 * 79
  set m : ℕ := 2 ^ (6 + 5) * 3 ^ (3 + 1) * 5 ^ (2 + 1) * 11 ^ 2
  have hσL : σ₁ l = 10280294400 := by pat1
  have hσM : σ₁ m = 10280530260 := by pat1
  let j := 79
  pat2

lemma not_HA_block3 : ∀ i ∈ [97, 101, 103, 107, 109, 113], ¬ IsHighlyAbundant (lcmRange i) := by
  set l : ℕ := 2 ^ 6 * 3 ^ 4 * 5 ^ 2 * 11 * 13 * 89 * 97
  set m : ℕ := 2 ^ 8 * 3 ^ 5 * 5 ^ 3 * 11 ^ 2 * 13 ^ 2
  have hσL : σ₁ l = 705876383520 := by pat1
  have hσM : σ₁ m = 706235611536 := by pat1
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  let j := i
  obtain rfl | rfl | rfl | rfl | rfl | rfl := hi
  all_goals pat2

lemma not_HA_block4 : ¬ IsHighlyAbundant (lcmRange 121) := by
  set l : ℕ := 2 ^ 6 * 5 ^ 2 * 7 ^ 2 * 101 * 113
  set m : ℕ := 2 ^ 7 * 5 ^ 3 * 7 ^ 3 * 163
  have hσL : σ₁ l = 2609427852 := by pat1
  have hσM : σ₁ m = 2609568000 := by pat1
  let j := 121
  pat2

lemma not_HA_block5 : ∀ i ∈ [149, 151], ¬ IsHighlyAbundant (lcmRange i) := by
  set l : ℕ := 2 ^ 7 * 5 ^ 3 * 13 * 137 * 149
  set m : ℕ := 2 ^ 8 * 5 ^ 4 * 13 ^ 2 * 157
  have hσL : σ₁ l = 11528244000 := by pat1
  have hσM : σ₁ m = 11539317174 := by pat1
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  let j := i
  obtain rfl | rfl := hi
  all_goals pat2

lemma not_HA_block6 : ∀ i ∈ [157, 163, 167], ¬ IsHighlyAbundant (lcmRange i) := by
  set l : ℕ := 2 ^ 7 * 5 ^ 3 * 13 * 149 * 151
  set m : ℕ := 2 ^ 8 * 5 ^ 4 * 13 ^ 2 * 173
  have hσL : σ₁ l = 12697776000 := by pat1
  have hσM : σ₁ m = 12707855622 := by pat1
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  let j := i
  obtain rfl | rfl | rfl := hi
  all_goals pat2

lemma not_HA_block7 :
    ∀ i ∈ [173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241],
      ¬ IsHighlyAbundant (lcmRange i) := by
  set l : ℕ := 2 ^ 7 * 3 ^ 4 * 7 ^ 2 * 17 * 19 * 157 * 173
  set m : ℕ := 2 ^ 9 * 3 ^ 5 * 7 ^ 3 * 17 ^ 2 * 19 ^ 2
  have hσL : σ₁ l = 17406411343200 := by pat1
  have hσM : σ₁ m = 17422094289600 := by pat1
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  let j := i
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl := hi
  all_goals pat2

lemma not_HA_block8 : ∀ i ∈ [243, 251], ¬ IsHighlyAbundant (lcmRange i) := by
  let lst := [2, 5, 17]
  set l : ℕ := 2 ^ 7 * 5 ^ 3 * 17 * 197 * 227
  set m : ℕ := 2 ^ 8 * 5 ^ 4 * 17 ^ 2 * 263
  have hσL : σ₁ l = 32324909760 := by pat1
  have hσM : σ₁ m = 32345527368 := by pat1
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  let j := i
  obtain rfl | rfl := hi
  all_goals pat2

lemma not_HA_block9 : ¬ IsHighlyAbundant (lcmRange 256) := by
  let lst := [2, 3, 5, 7, 17, 19, 227]
  set l : ℕ := 2 ^ 8 * 3 ^ 5 * 5 ^ 3 * 7 ^ 2 * 17 * 19 * 227 * 239 * 241
  set m : ℕ := 2 ^ 7 * 3 ^ 7 * 5 ^ 4 * 7 ^ 3 * 17 ^ 2 * 19 ^ 2 * 257
  have hσL : σ₁ l = 7884709431434035200 := by pat1
  have hσM : σ₁ m = 7885116358320960000 := by pat1
  let j := 256
  pat2

lemma not_HA_block10 : ∀ i ∈ [367, 373], ¬ IsHighlyAbundant (lcmRange i) := by
  let lst := [2, 3, 23, 157]
  set l : ℕ := 2 ^ 8 * 3 ^ 5 * 23 * 337 * 347 * 359
  set m : ℕ := 2 ^ 10 * 3 ^ 6 * 23 ^ 2 * 383 * 397
  have hσL : σ₁ l = 189030538045440 := by pat1
  have hσM : σ₁ m = 189093862223616 := by pat1
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  let j := i
  obtain rfl | rfl := hi
  all_goals pat2

def smallCounterexamples : List ℕ := [71, 73, 79, 97, 101, 103, 107, 109, 113, 121,
    149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227,
    229, 233, 239, 241, 243, 251, 256, 367, 373]

theorem combined : ∀ i ∈ smallCounterexamples, ¬ IsHighlyAbundant (lcmRange i) := by
  simp [smallCounterexamples, not_HA_block1, not_HA_block2,
    not_HA_block3, not_HA_block4, not_HA_block5, not_HA_block6, not_HA_block7,
    not_HA_block8, not_HA_block9, not_HA_block10]
