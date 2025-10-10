/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.Basic
import Mathlib

/-!
# Using six primes to show certain numbers are not highly abundant

Partial progress towards a formal statement of Tao's result here
https://mathoverflow.net/a/501229/117945
which enables proving that certain large numbers are not highly abundant using six primes.
-/

open Nat ArithmeticFunction

namespace six_primes

variable {n p₁ p₂ p₃ q₁ q₂ q₃ : ℕ}

structure Condition (n p₁ p₂ p₃ q₁ q₂ q₃ : ℕ) : Prop where
  nlt : n < p₁ ^ 2
  p₁p₂ : p₁ < p₂
  p₂p₃ : p₂ < p₃
  p₃q₁ : p₃ < q₁
  q₁q₂ : q₁ < q₂
  q₂q₃ : q₂ < q₃
  ngt : q₃ < n
  hp₁ : p₁.Prime
  hp₂ : p₂.Prime
  hp₃ : p₃.Prime
  hq₁ : q₁.Prime
  hq₂ : q₂.Prime
  hq₃ : q₃.Prime
  h : (1 + (q₁ : ℚ)⁻¹) * (1 + (q₂ : ℚ)⁻¹) * (1 + (q₃ : ℚ)⁻¹) ≤
      (1 + 3 / (8 * n)) * (1 - (4 * p₁ * p₂ * p₃) / (q₁ * q₂ * q₃)) *
      (1 + (p₁ * (p₁ + 1) : ℚ)⁻¹) *
      (1 + (p₂ * (p₂ + 1) : ℚ)⁻¹) *
      (1 + (p₃ * (p₃ + 1) : ℚ)⁻¹)

lemma Condition.particular (h : Condition n p₁ p₂ p₃ q₁ q₂ q₃) :
    4 * p₁ * p₂ * p₃ < q₁ * q₂ * q₃ := by
  have : 0 < (1 + (q₁ : ℚ)⁻¹) * (1 + (q₂ : ℚ)⁻¹) * (1 + (q₃ : ℚ)⁻¹) := by positivity
  have h' := this.trans_le h.h
  have hn : (0 : ℚ) < 1 + 3 / (8 * n) := by positivity
  have h1 : 0 < (1 + (p₁ * (p₁ + 1) : ℚ)⁻¹) := by positivity
  have h2 : 0 < (1 + (p₂ * (p₂ + 1) : ℚ)⁻¹) := by positivity
  have h3 : 0 < (1 + (p₃ * (p₃ + 1) : ℚ)⁻¹) := by positivity
  rw [Rat.mul_pos_iff_of_pos_right h3, Rat.mul_pos_iff_of_pos_right h2,
    Rat.mul_pos_iff_of_pos_right h1, Rat.mul_pos_iff_of_pos_left hn] at h'
  rw [sub_pos, div_lt_one] at h'
  · exact mod_cast h'
  · simp [h.hq₁.pos, h.hq₂.pos, h.hq₃.pos]

lemma Condition.q_dvd_lcmRange (h : Condition n p₁ p₂ p₃ q₁ q₂ q₃) :
     q₁ * q₂ * q₃ ∣ lcmRange n :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd
    (Nat.Coprime.mul_left
      (Nat.coprime_of_lt_prime h.hq₁.ne_zero (h.q₁q₂.trans h.q₂q₃) h.hq₃).symm
      (Nat.coprime_of_lt_prime h.hq₂.ne_zero h.q₂q₃ h.hq₃).symm)
    (Nat.Prime.dvd_mul_of_dvd_ne h.q₁q₂.ne h.hq₁ h.hq₂
      (dvd_lcmRange_of_le h.hq₁.ne_zero (by cases h; cutsat))
      (dvd_lcmRange_of_le h.hq₂.ne_zero (by cases h; cutsat)))
    (dvd_lcmRange_of_le h.hq₃.ne_zero h.ngt.le)

local notation "L'" => lcmRange n / (q₁ * q₂ * q₃)

lemma Condition.not_q₁_dvd_div (h : Condition n p₁ p₂ p₃ q₁ q₂ q₃) :
    ¬ q₁ ∣ L' := by
  rw [Nat.dvd_div_iff_mul_dvd (h.q_dvd_lcmRange)]
  intro h'
  have : q₁ ^ 2 ∣ lcmRange n := Dvd.dvd.trans ⟨q₂ * q₃, by ring⟩ h'
  exact sq_not_dvd h.hq₁ (show n < _ by cases h; rw [← Nat.sqrt_lt'] at *; cutsat) this

lemma Condition.not_q₂_dvd_div (h : Condition n p₁ p₂ p₃ q₁ q₂ q₃) :
    ¬ q₂ ∣ L' := by
  rw [Nat.dvd_div_iff_mul_dvd (h.q_dvd_lcmRange)]
  intro h'
  have : q₂ ^ 2 ∣ lcmRange n := Dvd.dvd.trans ⟨q₁ * q₃, by ring⟩ h'
  exact sq_not_dvd h.hq₂ (show n < _ by cases h; rw [← Nat.sqrt_lt'] at *; cutsat) this

lemma Condition.not_q₃_dvd_div (h : Condition n p₁ p₂ p₃ q₁ q₂ q₃) :
    ¬ q₃ ∣ L' := by
  rw [Nat.dvd_div_iff_mul_dvd (h.q_dvd_lcmRange)]
  intro h'
  have : q₃ ^ 2 ∣ lcmRange n := Dvd.dvd.trans ⟨q₁ * q₂, by ring⟩ h'
  exact sq_not_dvd h.hq₃ (show n < _ by cases h; rw [← Nat.sqrt_lt'] at *; cutsat) this

lemma Condition.coprime (h : Condition n p₁ p₂ p₃ q₁ q₂ q₃) : (q₁ * q₂ * q₃).Coprime L' := by
  apply Nat.Coprime.mul_left
  · apply Nat.Coprime.mul_left
    · rw [h.hq₁.coprime_iff_not_dvd]
      exact h.not_q₁_dvd_div
    · rw [h.hq₂.coprime_iff_not_dvd]
      exact h.not_q₂_dvd_div
  · rw [h.hq₃.coprime_iff_not_dvd]
    exact h.not_q₃_dvd_div

lemma eqn2 (h : Condition n p₁ p₂ p₃ q₁ q₂ q₃) :
    (σ₁ (lcmRange n) / lcmRange n : ℚ) =
    (σ₁ L' / L' : ℚ) * (1 + 1 / q₁) * (1 + 1 / q₂) * (1 + 1 / q₃) := by calc
  (_ : ℚ) = σ₁ (L' * (q₁ * q₂ * q₃)) / (L' * (q₁ * q₂ * q₃)) := by
    rw [Nat.div_mul_cancel h.q_dvd_lcmRange, div_mul_cancel₀]
    simp [h.hq₁.ne_zero, h.hq₂.ne_zero, h.hq₃.ne_zero]
  _ = (σ₁ L' * σ₁ q₁ * σ₁ q₂ * σ₁ q₃) / (L' * (q₁ * q₂ * q₃)) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime h.coprime.symm,
      isMultiplicative_sigma.map_mul_of_coprime, isMultiplicative_sigma.map_mul_of_coprime]
    · simp [mul_assoc]
    · exact (Nat.coprime_of_lt_prime h.hq₁.ne_zero h.q₁q₂ h.hq₂).symm
    apply (Nat.Coprime.mul_left
      (Nat.coprime_of_lt_prime h.hq₁.ne_zero (h.q₁q₂.trans h.q₂q₃) h.hq₃).symm
      (Nat.coprime_of_lt_prime h.hq₂.ne_zero h.q₂q₃ h.hq₃).symm)
  _ = _ := by
    rw [sigma_one_apply_prime h.hq₁, sigma_one_apply_prime h.hq₂,
      sigma_one_apply_prime h.hq₃]
    simp only [Nat.cast_add_one]
    have : (q₁ : ℚ) ≠ 0 := by simp [h.hq₁.ne_zero]
    have : (q₂ : ℚ) ≠ 0 := by simp [h.hq₂.ne_zero]
    have : (q₃ : ℚ) ≠ 0 := by simp [h.hq₃.ne_zero]
    field_simp

local notation "m" => q₁ * q₂ * q₃ / (4 * p₁ * p₂ * p₃)
local notation "r" => q₁ * q₂ * q₃ % (4 * p₁ * p₂ * p₃)

lemma q_eq : q₁ * q₂ * q₃ = 4 * p₁ * p₂ * p₃ * m + r := by rw [Nat.div_add_mod]

lemma r_lt (h : Condition n p₁ p₂ p₃ q₁ q₂ q₃) : r < 4 * p₁ * p₂ * p₃ := by
  apply Nat.mod_lt _
  have := h.hp₁.pos
  have := h.hp₂.pos
  have := h.hp₃.pos
  positivity

lemma r_pos (h : Condition n p₁ p₂ p₃ q₁ q₂ q₃) : 0 < r := by
  sorry

theorem not_HA_of_condition (h : Condition n p₁ p₂ p₃ q₁ q₂ q₃) : ¬ IsHighlyAbundant n := by
  have hdvd : q₁ * q₂ * q₃ ∣ lcmRange n := h.q_dvd_lcmRange
  sorry

end six_primes
