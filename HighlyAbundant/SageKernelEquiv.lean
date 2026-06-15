/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.SageKernel
import Mathlib.Data.Nat.Log

/-!
# Equivalence of kernel-friendly and ordinary decider functions

For each kernel-friendly definition in `HighlyAbundant.SageKernel`, prove it
agrees with the corresponding definition in `HighlyAbundant.Sage`.
-/

namespace Sage

theorem ceilDivK_eq_ceilDiv : ceilDivK = ceilDiv := rfl

theorem appendK_eq_append {α : Type _} (xs ys : List α) : appendK xs ys = xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons x _ ih => exact congrArg (x :: ·) ih

private theorem extendK_succ (n m2 front back lhs rhs : Nat) :
    extendK (n + 1) m2 front back lhs rhs =
      if front ≤ back then
        if lhs ≥ rhs then .window back lhs rhs
        else if back + 1 < 49 then
          let q := primesRArray.get (back + 1)
          let lhs' := lhs * q
          if lhs' > m2 then .tooLarge else extendK n m2 front (back + 1) lhs' (rhs * (q - 1))
        else .exhaustedTable
      else
        if front < 49 then
          let q := primesRArray.get front
          let lhs' := lhs * q
          if lhs' > m2 then .tooLarge else extendK n m2 front front lhs' (rhs * (q - 1))
        else .exhaustedTable := by
  simp only [extendK, Bool.rec_eq, Nat.ble_eq, Nat.lt_succ_iff,
    Nat.succ_le_succ_iff, ← Nat.not_le, ite_not]
  rfl

theorem extendK_eq_extend : extendK = extend := by
  funext fuel m2 front back lhs rhs
  induction fuel generalizing back lhs rhs with
  | zero => rfl
  | succ n ih =>
    rw [extend, extendK_succ]
    simp only [ih]

private theorem expChildrenK_succ (n target num next m p pk : Nat) :
    expChildrenK (n + 1) target num next m p pk =
      if pk > m then []
      else
        let spk := (pk * p - 1) / (p - 1)
        let child := (ceilDiv target spk, num * pk, next)
        if spk ≥ target then [child]
        else child :: expChildrenK n target num next m p (pk * p) := by
  simp only [expChildrenK, Bool.rec_eq, Nat.ble_eq, ← Nat.not_le, ite_not]
  rfl

theorem expChildrenK_eq_expChildren : expChildrenK = expChildren := by
  funext fuel target num next m p pk
  induction fuel generalizing pk with
  | zero => rfl
  | succ n ih =>
    rw [expChildren, expChildrenK_succ]
    simp only [ih]

private theorem wheelChildrenK_succ (n m2 m target num front back lhs rhs : Nat)
    (acc : List (Nat × Nat × Nat)) :
    wheelChildrenK (n + 1) m2 m target num front back lhs rhs acc =
      match extend 50 m2 front back lhs rhs with
      | .exhaustedTable => none
      | .tooLarge => some acc
      | .window b lhs' rhs' =>
        if front < 49 then
          let p := primesRArray.get front
          wheelChildrenK n m2 m target num (front + 1) b (lhs' / p) (rhs' / (p - 1))
            (expChildren (m + 1) target num (front + 1) m p p ++ acc)
        else none := by
  simp only [wheelChildrenK, Bool.rec_eq, Nat.ble_eq, Nat.lt_succ_iff,
    extendK_eq_extend, expChildrenK_eq_expChildren, appendK_eq_append]
  cases extend 50 m2 front back lhs rhs <;> rfl

theorem wheelChildrenK_eq_wheelChildren : wheelChildrenK = wheelChildren := by
  funext fuel m2 m target num front back lhs rhs acc
  induction fuel generalizing front back lhs rhs acc with
  | zero => rfl
  | succ n ih =>
    rw [wheelChildren, wheelChildrenK_succ]
    cases extend 50 m2 front back lhs rhs <;> simp only [ih]

theorem childrenK_eq_children : childrenK = children := by
  funext B target num minIdx
  simp only [childrenK, children, Bool.rec_eq, Nat.ble_eq, Nat.lt_succ_iff,
    wheelChildrenK_eq_wheelChildren]
  rfl

private theorem stepK_succ_cons (B n target num minIdx : Nat)
    (rest : List (Nat × Nat × Nat)) :
    stepK B (n + 1) ((target, num, minIdx) :: rest) =
      if target ≤ 1 then
        if num < B then some false else stepK B n rest
      else (children B target num minIdx).rec none (fun cs ↦ stepK B n (cs ++ rest)) := by
  simp only [stepK, Bool.rec_eq, Nat.ble_eq, childrenK_eq_children, appendK_eq_append,
    ← Nat.not_le, ite_not]

theorem stepK_eq_step : stepK = step := by
  funext B fuel stack
  induction fuel generalizing stack with
  | zero => rfl
  | succ n ih =>
    cases stack with
    | nil => rfl
    | cons head tail =>
      obtain ⟨target, num, minIdx⟩ := head
      rw [stepK_succ_cons, step.eq_def]
      simp only [ih]
      split
      · rfl
      · cases children B target num minIdx <;> rfl

theorem highlyAbundantLcmK_eq_highlyAbundantLcm :
    highlyAbundantLcmK? = highlyAbundantLcm? := by
  funext B sL
  simp only [highlyAbundantLcmK?, highlyAbundantLcm?, Bool.rec_eq, Nat.ble_eq,
    stepK_eq_step]

/-- `(lcmRange n, σ₁ (lcmRange n))` computed as
`(∏ p^{⌊log_p n⌋}, ∏ σ(p^{⌊log_p n⌋}))` over the primes `p ≤ n` in the table.
For `#eval` use to supply `(B, sL)` to `highlyAbundantLcm?`; the formal proof
goes through `lcmRange` directly, so this equivalence is not used. -/
def lcmData (n : ℕ) : ℕ × ℕ :=
  (primes.toList.takeWhile (· ≤ n)).foldl
    (fun (acc : ℕ × ℕ) p =>
      let e := Nat.log p n
      (acc.1 * p ^ e, acc.2 * ((p ^ (e + 1) - 1) / (p - 1)))) (1, 1)

elab "quickRfl" : tactic => Lean.Elab.Tactic.liftMetaFinishingTactic fun g ↦ g.assign Lean.reflBoolTrue
#eval lcmData 64
-- (1182266884102822267511361600, 8469504822020624477061120000)
-- (9419588158802421600, 61155010116845568000)

set_option diagnostics true in
example : stepK 5354228880 2000 [(28078202880, 1, 0)] == some true := by quickRfl

end Sage
