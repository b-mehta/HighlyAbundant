/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.IsHA.SageKernel
import HighlyAbundant.IsHA.SageSpec
import Mathlib.Data.Nat.Log

/-!
# Equivalence of kernel-friendly and ordinary decider functions

The kernel form in `HighlyAbundant.SageKernel` represents search-tree nodes as
`SageNode` while the spec form in `HighlyAbundant.Sage` uses `Nat × Nat × Nat`.
The two representations are isomorphic via `toSageNode` / `fromSageNode`, and
each kernel-form definition equals the spec-form definition under that bridge.
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
        let child : SageNode := ⟨ceilDiv target spk, num * pk, next⟩
        if spk ≥ target then [child]
        else child :: expChildrenK n target num next m p (pk * p) := by
  simp only [expChildrenK, Bool.rec_eq, Nat.ble_eq, ← Nat.not_le, ite_not]
  rfl

theorem expChildrenK_eq_expChildren (fuel target num next m p pk : Nat) :
    (expChildrenK fuel target num next m p pk).map fromSageNode =
      expChildren fuel target num next m p pk := by
  induction fuel generalizing pk with
  | zero => rfl
  | succ n ih =>
    rw [expChildren, expChildrenK_succ]
    by_cases hm : pk > m
    · simp [hm]
    · simp only [hm, if_false]
      by_cases ht : (pk * p - 1) / (p - 1) ≥ target
      · simp [ht, List.map_cons, List.map_nil, fromSageNode]
      · simp [ht, List.map_cons, fromSageNode, ih]

private theorem wheelChildrenK_succ (n m2 m target num front back lhs rhs : Nat)
    (acc : List SageNode) :
    wheelChildrenK (n + 1) m2 m target num front back lhs rhs acc =
      match extend 50 m2 front back lhs rhs with
      | .exhaustedTable => none
      | .tooLarge => some acc
      | .window b lhs' rhs' =>
        if front < 49 then
          let p := primesRArray.get front
          wheelChildrenK n m2 m target num (front + 1) b (lhs' / p) (rhs' / (p - 1))
            (expChildrenK (m + 1) target num (front + 1) m p p ++ acc)
        else none := by
  simp only [wheelChildrenK, Bool.rec_eq, Nat.ble_eq, Nat.lt_succ_iff,
    extendK_eq_extend, appendK_eq_append]
  cases extend 50 m2 front back lhs rhs <;> rfl

theorem wheelChildrenK_eq_wheelChildren (fuel m2 m target num front back lhs rhs : Nat)
    (acc : List SageNode) :
    (wheelChildrenK fuel m2 m target num front back lhs rhs acc).map (·.map fromSageNode) =
      wheelChildren fuel m2 m target num front back lhs rhs (acc.map fromSageNode) := by
  induction fuel generalizing front back lhs rhs acc with
  | zero => rfl
  | succ n ih =>
    rw [wheelChildren, wheelChildrenK_succ]
    cases extend 50 m2 front back lhs rhs with
    | exhaustedTable | tooLarge => rfl
    | window b lhs' rhs' =>
      by_cases h : front < 49
      · simp only [h, if_true, ih, List.map_append, expChildrenK_eq_expChildren]
      · simp only [h, if_false, Option.map]

theorem childrenK_eq_children (B target num minIdx : Nat) :
    (childrenK B target num minIdx).map (·.map fromSageNode) =
      children B target num minIdx := by
  simp only [childrenK, children, Bool.rec_eq, Nat.ble_eq, ← Nat.lt_succ_iff]
  by_cases h : minIdx < 49
  · simp only [h, ↓reduceIte]
    exact wheelChildrenK_eq_wheelChildren 50 ((B / num) * (B / num)) (B / num) target num
      minIdx minIdx (primesRArray.get minIdx * (B / num))
      (target * (primesRArray.get minIdx - 1)) []
  · simp only [h, ↓reduceIte, Option.map_none]

private theorem stepK_succ_cons (B n target num minIdx : Nat)
    (rest : List SageNode) :
    stepK B (n + 1) (⟨target, num, minIdx⟩ :: rest) =
      if target ≤ 1 then
        if num < B then some false else stepK B n rest
      else (childrenK B target num minIdx).rec none (fun cs ↦ stepK B n (cs ++ rest)) := by
  simp only [stepK, Bool.rec_eq, Nat.ble_eq, appendK_eq_append,
    ← Nat.not_le, ite_not]

/-- Translate a `childrenK = some cs` cert (kernel form, `cs : List SageNode`)
to the corresponding `children = some (cs.map fromSageNode)` cert (spec form). -/
private theorem children_of_childrenK {B target num minIdx : Nat} {cs : List SageNode}
    (hch : childrenK B target num minIdx = some cs) :
    children B target num minIdx = some (cs.map fromSageNode) := by
  simpa [hch] using (childrenK_eq_children B target num minIdx).symm

/-- Translate a `childrenK = none` cert to `children = none`. -/
private theorem children_of_childrenK_none {B target num minIdx : Nat}
    (hch : childrenK B target num minIdx = none) :
    children B target num minIdx = none := by
  simpa [hch] using (childrenK_eq_children B target num minIdx).symm

theorem stepK_eq_step (B fuel : Nat) (xs : List SageNode) :
    stepK B fuel xs = step B fuel (xs.map fromSageNode) := by
  induction fuel generalizing xs with
  | zero => rfl
  | succ n ih =>
    match xs with
    | [] => rfl
    | ⟨target, num, minIdx⟩ :: rest =>
      rw [stepK_succ_cons, step.eq_def]
      simp only [List.map_cons, fromSageNode]
      split
      · split <;> simp [ih]
      · cases hck : childrenK B target num minIdx with
        | none => rw [children_of_childrenK_none hck]
        | some cs => simp [children_of_childrenK hck, ih, List.map_append]

theorem highlyAbundantLcmK_eq_highlyAbundantLcm :
    highlyAbundantLcmK? = highlyAbundantLcm? := by
  funext B sL
  simp only [highlyAbundantLcmK?, highlyAbundantLcm?, Bool.rec_eq, Nat.ble_eq]
  split
  · rfl
  · rw [stepK_eq_step]
    simp [fromSageNode]

/-- `(lcmUpto n, σ₁ (lcmUpto n))` computed as
`(∏ p^{⌊log_p n⌋}, ∏ σ(p^{⌊log_p n⌋}))` over the primes `p ≤ n` in the table.
For `#eval` use to supply `(B, sL)` to `highlyAbundantLcm?`; the formal proof
goes through `lcmUpto` directly, so this equivalence is not used. -/
def lcmData (n : ℕ) : ℕ × ℕ :=
  (primes.toList.takeWhile (· ≤ n)).foldl
    (fun (acc : ℕ × ℕ) p =>
      let e := Nat.log p n
      (acc.1 * p ^ e, acc.2 * ((p ^ (e + 1) - 1) / (p - 1)))) (1, 1)

/-- Partial verification using the K-versions of `children` and `step`
(`childrenK`/`stepK`) to drive `highlyAbundantLcm_correct_partial`. -/
theorem highlyAbundantLcm_correct_partialK {n : ℕ} {cs : List SageNode}
    (hsL : 2 ≤ σ₁ (lcmUpto n))
    (hch : childrenK (lcmUpto n) (σ₁ (lcmUpto n)) 1 0 = some cs)
    (hcs : ∀ c ∈ cs, stepK (lcmUpto n) searchFuel [c] = some true) :
    IsHighlyAbundant (lcmUpto n) := by
  refine highlyAbundantLcm_correct_partial (cs := cs.map fromSageNode) hsL
    (children_of_childrenK hch) ?_
  intro c' hc'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
  simpa using (stepK_eq_step _ _ _).symm.trans (hcs c hc)

/-- `W = ∅` recursive split phrased with `childrenK`: from `W = ∅` on each child
of a node, conclude `W = ∅` on the node itself. -/
theorem W_eq_empty_of_partialK {B g a minIdx : ℕ} {cs : List SageNode}
    (hg : 2 ≤ g)
    (hch : childrenK B g a minIdx = some cs)
    (hcs : ∀ c ∈ cs, W B c.target c.num c.minIdx = ∅) :
    W B g a minIdx = ∅ := by
  refine W_eq_empty_of_partial (cs := cs.map fromSageNode) hg
    (children_of_childrenK hch) ?_
  intro c' hc'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
  simpa [fromSageNode] using hcs c hc

/-- `W`-based partial verification using `childrenK`: takes `W = ∅` for each root
child, so the metaprogram can expand large children recursively. -/
theorem highlyAbundantLcm_correct_partialK_W {n : ℕ} {cs : List SageNode}
    (hsL : 2 ≤ σ₁ (lcmUpto n))
    (hch : childrenK (lcmUpto n) (σ₁ (lcmUpto n)) 1 0 = some cs)
    (hcs : ∀ c ∈ cs, W (lcmUpto n) c.target c.num c.minIdx = ∅) :
    IsHighlyAbundant (lcmUpto n) := by
  refine highlyAbundantLcm_correct_partial_W (cs := cs.map fromSageNode) hsL
    (children_of_childrenK hch) ?_
  intro c' hc'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
  simpa [fromSageNode] using hcs c hc

end Sage
