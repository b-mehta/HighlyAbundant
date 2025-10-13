/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.Prime.PowMod
import Mathlib.NumberTheory.LucasPrimality

def pratt_predicate (p a x : ℕ) : Prop := ∀ q ∈ x.primeFactors, powMod a ((p - 1) / q) p ≠ 1

@[simp]
lemma pratt_predicate_iff (p a x : ℕ) :
    pratt_predicate p a x ↔ ∀ q ∈ x.primeFactors, powMod a ((p - 1) / q) p ≠ 1 :=
  Iff.rfl

def pratt_zero (p a : ℕ) : pratt_predicate p a 0 := by simp!
def pratt_axiom (p a : ℕ) : pratt_predicate p a 1 := by simp!

open Nat

lemma pratt_rule_1 {p a x q : ℕ} (h : pratt_predicate p a x) (hq : q.Prime)
    (h' : powMod a ((p - 1) / q) p ≠ 1) : pratt_predicate p a (q * x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rwa [mul_zero]
  intro r hr
  rw [Nat.mem_primeFactors_iff_mem_primeFactorsList,
    mem_primeFactorsList_mul hq.ne_zero hx, primeFactorsList_prime hq, List.mem_singleton] at hr
  rw [← Nat.mem_primeFactors_iff_mem_primeFactorsList] at hr
  rcases hr with rfl | hr
  exacts [h', h r hr]

lemma pratt_rule_1' (q x : ℕ) {p a y : ℕ} (hq : q.Prime)
    (hy : q * x = y)
    (h' : powMod a ((p - 1) / q) p ≠ 1) (h : pratt_predicate p a x) : pratt_predicate p a y := by
  rw [← hy]
  exact pratt_rule_1 h hq h'

lemma pratt_rule_2 (a : ℕ) {p : ℕ} (hp : p ≠ 0) (h : pratt_predicate p a (p - 1))
    (h' : powMod a (p - 1) p = 1) : p.Prime := by
  rw [powMod] at h'
  rcases p with rfl | rfl | p
  · cases hp rfl
  · simp at h'
  rw [pratt_predicate, succ_sub_one] at h
  rw [succ_sub_one] at h'
  simp only [mem_primeFactors_of_ne_zero (succ_ne_zero _), ne_eq, and_imp] at h
  let a' : ZMod (p + 2) := a
  have := lucas_primality _ a'
  simp only [a', ← Nat.cast_pow] at this
  refine this ?_ (fun q hq hq' ↦ ?_)
  · rw [← ZMod.natCast_mod, succ_sub_one, h', Nat.cast_one]
  rw [← ZMod.natCast_mod, ←@Nat.cast_one (ZMod (p+2)), ne_eq, ZMod.natCast_eq_natCast_iff,
    Nat.ModEq, mod_mod, one_mod]
  simp only [powMod] at h
  exact h _ hq hq'

lemma pratt_rule_2' (a : ℕ) {p : ℕ} (hp : p ≠ 0)
    (h' : powMod a (p - 1) p = 1)
    (h : pratt_predicate p a (p - 1)) : p.Prime :=
  pratt_rule_2 a hp h h'

lemma prove_prime_step (p a q o t r k : ℕ) (ho : ((p.sub 1).div q).beq o) (hq : q.Prime)
    (ht : (r.mul (q.pow k)).beq t)
    (hpow : (powModTR a o p).beq 1 = false)
    (h : pratt_predicate p a r) :
    pratt_predicate p a t := by
  simp only [sub_eq, div_eq_div, beq_eq, pow_eq, mul_eq] at ho ht
  replace hpow := Nat.ne_of_beq_eq_false hpow
  simp only [powModTR_eq] at hpow
  subst ho ht
  induction k with
  | zero => rwa [pow_zero, mul_one]
  | succ n ih => exact pratt_rule_1' q _ hq (by ring) hpow ih

lemma prove_prime_end {p : ℕ} (p' a : ℕ) (hp : p'.succ.beq p) (hpow : (powModTR a p' p).beq 1)
    (h : pratt_predicate p a p') : p.Prime := by
  simp only [beq_eq, powModTR_eq] at hpow
  simp only [succ_eq_add_one, beq_eq] at hp
  cases hp
  exact pratt_rule_2' a (by omega) hpow h
