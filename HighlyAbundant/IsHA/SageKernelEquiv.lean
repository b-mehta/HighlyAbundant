/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.IsHA.SageKernel
import HighlyAbundant.IsHA.SageSpec

open Nat

/-!
# Equivalence of kernel-friendly and ordinary decider functions

The kernel form in `HighlyAbundant.SageKernel` represents search-tree nodes as `SageNode` while the
spec form in `HighlyAbundant.Sage` uses `Nat × Nat × Nat`. `fromSageNode` bridges the two, and each
kernel-form definition equals the spec-form definition under that bridge.
-/

namespace Sage

private theorem appendK_eq_append (xs ys : List SageNode) : appendK xs ys = xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons x _ ih => exact congrArg (x :: ·) ih

private theorem extendK_succ (n m2 lo hi lhs rhs : Nat) :
    extendK (n + 1) m2 lo hi lhs rhs =
      if lo ≤ hi then
        if lhs ≥ rhs then .window hi lhs rhs
        else if hi + 1 < 49 then
          let q := primesRArray.get (hi + 1)
          let lhs' := lhs * q
          if lhs' > m2 then .tooLarge else extendK n m2 lo (hi + 1) lhs' (rhs * (q - 1))
        else .exhaustedTable
      else
        if lo < 49 then
          let q := primesRArray.get lo
          let lhs' := lhs * q
          if lhs' > m2 then .tooLarge else extendK n m2 lo lo lhs' (rhs * (q - 1))
        else .exhaustedTable := by
  simp only [extendK, brecPhase, brecBound, brecSize, brecStop, Bool.rec_eq, Nat.ble_eq,
    Nat.lt_succ_iff, Nat.succ_le_succ_iff, ← Nat.not_le, ite_not]
  rfl

private theorem extendK_eq_extend : extendK = extend := by
  funext fuel m2 lo hi lhs rhs
  induction fuel generalizing hi lhs rhs with
  | zero => rfl
  | succ n ih =>
    rw [extend, extendK_succ]
    simp only [ih]

private theorem expChildrenK_succ (n goal cand next m p pk : Nat) :
    expChildrenK (n + 1) goal cand next m p pk =
      if pk > m then []
      else
        let spk := (pk * p - 1) / (p - 1)
        let child : SageNode := ⟨ceilDiv goal spk, cand * pk, next⟩
        if spk ≥ goal then [child]
        else child :: expChildrenK n goal cand next m p (pk * p) := by
  simp only [expChildrenK, brecExpBound, brecExpStop, Bool.rec_eq, Nat.ble_eq, ← Nat.not_le,
    ite_not]
  rfl

private theorem expChildrenK_eq_expChildren (fuel goal cand next m p pk : Nat) :
    (expChildrenK fuel goal cand next m p pk).map fromSageNode =
      expChildren fuel goal cand next m p pk := by
  induction fuel generalizing pk with
  | zero => rfl
  | succ n ih =>
    rw [expChildren, expChildrenK_succ]
    by_cases hm : pk > m
    · simp [hm]
    · simp only [hm, if_false]
      by_cases ht : (pk * p - 1) / (p - 1) ≥ goal
      · simp [ht, List.map_cons, List.map_nil, fromSageNode]
      · simp [ht, List.map_cons, fromSageNode, ih]

private theorem wheelChildrenK_succ (n m2 m goal cand lo hi lhs rhs : Nat)
    (acc : List SageNode) :
    wheelChildrenK (n + 1) m2 m goal cand lo hi lhs rhs acc =
      match extend 50 m2 lo hi lhs rhs with
      | .exhaustedTable => none
      | .tooLarge => some acc
      | .window b lhs' rhs' =>
        if lo < 49 then
          let p := primesRArray.get lo
          wheelChildrenK n m2 m goal cand (lo + 1) b (lhs' / p) (rhs' / (p - 1))
            (expChildrenK (m + 1) goal cand (lo + 1) m p p ++ acc)
        else none := by
  simp only [wheelChildrenK, brecWheelBound, Bool.rec_eq, Nat.ble_eq, Nat.lt_succ_iff,
    extendK_eq_extend, appendK_eq_append]
  cases extend 50 m2 lo hi lhs rhs <;> rfl

private theorem wheelChildrenK_eq_wheelChildren (fuel m2 m goal cand lo hi lhs rhs : Nat)
    (acc : List SageNode) :
    (wheelChildrenK fuel m2 m goal cand lo hi lhs rhs acc).map (·.map fromSageNode) =
      wheelChildren fuel m2 m goal cand lo hi lhs rhs (acc.map fromSageNode) := by
  induction fuel generalizing lo hi lhs rhs acc with
  | zero => rfl
  | succ n ih =>
    rw [wheelChildren, wheelChildrenK_succ]
    cases extend 50 m2 lo hi lhs rhs with
    | exhaustedTable | tooLarge => rfl
    | window b lhs' rhs' =>
      by_cases h : lo < 49
      · simp only [h, if_true, ih, List.map_append, expChildrenK_eq_expChildren]
      · simp only [h, if_false, Option.map]

private theorem childrenK_eq_children (B goal cand i : Nat) :
    (childrenK B goal cand i).map (·.map fromSageNode) = children B goal cand i := by
  simp only [childrenK, children, brecChildBound, Bool.rec_eq, Nat.ble_eq, ← Nat.lt_succ_iff]
  by_cases h : i < 49
  · simp only [h, ↓reduceIte]
    exact wheelChildrenK_eq_wheelChildren 50 ((B / cand) * (B / cand)) (B / cand) goal cand
      i i (primesRArray.get i * (B / cand)) (goal * (primesRArray.get i - 1)) []
  · simp only [h, ↓reduceIte, Option.map_none]

private theorem stepK_succ_cons (B n goal cand i : Nat) (rest : List SageNode) :
    stepK B (n + 1) (⟨goal, cand, i⟩ :: rest) =
      if goal ≤ 1 then
        if cand < B then some false else stepK B n rest
      else (childrenK B goal cand i).rec none (fun cs ↦ stepK B n (cs ++ rest)) := by
  simp only [stepK, brecStepGoal, brecStepCand, Bool.rec_eq, Nat.ble_eq, appendK_eq_append,
    ← Nat.not_le, ite_not]

/-- Translate a `childrenK = some cs` cert (kernel form, `cs : List SageNode`) to the corresponding
`children = some (cs.map fromSageNode)` cert (spec form). -/
private theorem children_of_childrenK {B goal cand i : Nat} {cs : List SageNode}
    (hch : childrenK B goal cand i = some cs) :
    children B goal cand i = some (cs.map fromSageNode) := by
  simpa [hch] using (childrenK_eq_children B goal cand i).symm

/-- Translate a `childrenK = none` cert to `children = none`. -/
private theorem children_of_childrenK_none {B goal cand i : Nat}
    (hch : childrenK B goal cand i = none) : children B goal cand i = none := by
  simpa [hch] using (childrenK_eq_children B goal cand i).symm

theorem stepK_eq_step (B fuel : Nat) (xs : List SageNode) :
    stepK B fuel xs = step B fuel (xs.map fromSageNode) := by
  induction fuel generalizing xs with
  | zero => rfl
  | succ n ih =>
    match xs with
    | [] => rfl
    | ⟨goal, cand, i⟩ :: rest =>
      rw [stepK_succ_cons, step.eq_def]
      simp only [List.map_cons, fromSageNode]
      split
      · split <;> simp [ih]
      · cases hck : childrenK B goal cand i with
        | none => rw [children_of_childrenK_none hck]
        | some cs => simp [children_of_childrenK hck, ih, List.map_append]

/-- `W = ∅` recursive split phrased with `childrenK`: from `W = ∅` on each child of a node,
conclude `W = ∅` on the node itself. -/
theorem W_eq_empty_of_partialK {B g a i : ℕ} {cs : List SageNode}
    (hg : 2 ≤ g)
    (hch : childrenK B g a i = some cs)
    (hcs : ∀ c ∈ cs, W B c.goal c.cand c.i = ∅) :
    W B g a i = ∅ := by
  refine W_eq_empty_of_partial (cs := cs.map fromSageNode) hg
    (children_of_childrenK hch) ?_
  intro c' hc'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
  simpa [fromSageNode] using hcs c hc

/-- `W`-based partial verification using `childrenK`: takes `W = ∅` for each root child, so the
metaprogram can expand large children recursively. -/
theorem highlyAbundantLcm_correct_partialK_W {n : ℕ} {cs : List SageNode}
    (hsL : 2 ≤ σ₁ (lcmUpto n))
    (hch : childrenK (lcmUpto n) (σ₁ (lcmUpto n)) 1 0 = some cs)
    (hcs : ∀ c ∈ cs, W (lcmUpto n) c.goal c.cand c.i = ∅) :
    IsHighlyAbundant (lcmUpto n) := by
  refine highlyAbundantLcm_correct_partial_W (cs := cs.map fromSageNode) hsL
    (children_of_childrenK hch) ?_
  intro c' hc'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
  simpa [fromSageNode] using hcs c hc

end Sage
