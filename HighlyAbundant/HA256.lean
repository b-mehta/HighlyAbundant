/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.Basic
import HighlyAbundant.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Proof of non-high-abundance of lcm(1..256)

This file is special-cased as the counterexample for 256 has particular undesirable properties not
shared by any other counterexamples, so doesn't fit nicely into the general verification framework
set up here.
-/

open Nat ArithmeticFunction

@[grind .] lemma not_HA_block256 : ¬ IsHighlyAbundant (lcmRange 256) := by
  set l : ℕ := 2 ^ 8 * 3 ^ 5 * 5 ^ 3 * 7 ^ 2 * 17 * 19 * 227 * 239 * 241
  set m : ℕ := 2 ^ 7 * 3 ^ 7 * 5 ^ 4 * 7 ^ 3 * 17 ^ 2 * 19 ^ 2 * 257
  have hσL : σ₁ l = 7884709431434035200 := by
    repeat rw [isMultiplicative_sigma.map_mul_of_coprime rfl]
    repeat rw [sigma_one_apply_prime_pow' (by norm_num)]
    norm_num [sigma_one_apply_prime]
  have hσM : σ₁ m = 7885116358320960000 := by
    repeat rw [isMultiplicative_sigma.map_mul_of_coprime rfl]
    repeat rw [sigma_one_apply_prime_pow' (by norm_num)]
    norm_num [sigma_one_apply_prime]
  set L : ℕ := lcmRange 256
  set K : ℕ := L / l
  set M : ℕ := m * K with hM
  have hL₀ : 0 < L := lcmRange_pos
  have hL : L = l * K := by decide +kernel
  have hLK : Nat.gcd l K = 1 := by decide +kernel
  have hMK : Nat.gcd m K = 1 := by decide +kernel
  have hK : 0 < K := by lia
  clear_value K
  intro h
  have := h M (by lia) (by lia)
  rw [hM, hL, isMultiplicative_sigma.map_mul_of_coprime hMK,
    isMultiplicative_sigma.map_mul_of_coprime hLK, hσL, hσM] at this
  lia
