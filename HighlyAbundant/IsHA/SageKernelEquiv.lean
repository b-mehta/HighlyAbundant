/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

public import HighlyAbundant.ForLean
public import HighlyAbundant.IsHA.SageKernel
public import HighlyAbundant.IsHA.SageSpec

public section

open Nat

/-!
# Equality of the kernel and specification deciders

Search nodes are `SageNode` in `HighlyAbundant.SageKernel` and `Nat × Nat × Nat` in
`HighlyAbundant.Sage`. Each kernel definition equals its specification counterpart along
`fromSageNode`.
-/

namespace Sage

/-- Read a kernel-side `SageNode` as the specification's `(Nat × Nat × Nat)`. -/
def fromSageNode (n : SageNode) : Nat × Nat × Nat := (n.goal, n.cand, n.i)

@[simp, grind =] private theorem appendK_eq_append {xs ys : List SageNode} :
    appendK xs ys = xs ++ ys := by
  induction xs with grind [appendK]

@[simp] private theorem ceilDivK_eq_ceilDiv {a b : Nat} : ceilDivK a b = ceilDiv a b := rfl

private theorem extendKLoop_succ {n m2 hi lhs rhs : Nat} :
    extendKLoop (n + 1) m2 hi lhs rhs =
      if lhs ≥ rhs then .window hi lhs rhs
      else if hi + 1 < 49 then
        let q := primesRArray.get (hi + 1)
        let lhs' := lhs * q
        if lhs' > m2 then .tooLarge else extendKLoop n m2 (hi + 1) lhs' (rhs * (q - 1))
      else .exhaustedTable := by
  simp only [extendKLoop]
  grind [Nat.ble_eq, Bool.rec_eq]

@[grind <=]
private theorem extendKLoop_eq_extend {fuel m2 lo hi lhs rhs : Nat} (hle : lo ≤ hi) :
    extendKLoop fuel m2 hi lhs rhs = extend fuel m2 lo hi lhs rhs := by
  induction fuel generalizing hi lhs rhs with
  | zero => rfl
  | succ n ih => grind [extend, extendKLoop_succ]

@[simp, grind =]
private theorem extendK_eq_extend : extendK = extend := by
  funext fuel m2 lo hi lhs rhs
  cases fuel with
  | zero => rfl
  | succ n => grind [extendK, extend, Bool.rec_eq, Nat.ble_eq]

private theorem expChildrenK_succ {n goal cand next m p pk : Nat} :
    expChildrenK (n + 1) goal cand next m p pk =
      if pk > m then []
      else
        let spk := (pk * p - 1) / (p - 1)
        ⟨ceilDiv goal spk, cand * pk, next⟩ ::
          (if spk ≥ goal then [] else expChildrenK n goal cand next m p (pk * p)) := by
  rw [← ite_not]
  simp [expChildrenK, Bool.rec_eq, Nat.ble_eq, not_lt, ceilDivK_eq_ceilDiv]

private theorem expChildrenK_eq_expChildren {fuel goal cand next m p pk : Nat} :
    (expChildrenK fuel goal cand next m p pk).map fromSageNode =
      expChildren fuel goal cand next m p pk := by
  induction fuel generalizing pk with
  | zero => rfl
  | succ n ih => grind [expChildren, expChildrenK_succ, fromSageNode]

private theorem wheelChildrenK_succ {n m2 m goal cand lo hi lhs rhs : Nat}
    {acc : List SageNode} :
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
  simp only [wheelChildrenK, Bool.rec_eq, Nat.ble_eq, Nat.lt_succ_iff, extendK_eq_extend,
    appendK_eq_append]
  cases extend 50 m2 lo hi lhs rhs <;> rfl

private theorem wheelChildrenK_eq_wheelChildren {fuel m2 m goal cand lo hi lhs rhs : Nat}
    {acc : List SageNode} :
    (wheelChildrenK fuel m2 m goal cand lo hi lhs rhs acc).map (·.map fromSageNode) =
      wheelChildren fuel m2 m goal cand lo hi lhs rhs (acc.map fromSageNode) := by
  induction fuel generalizing lo hi lhs rhs acc with
  | zero => rfl
  | succ n ih => grind [wheelChildren, wheelChildrenK_succ, expChildrenK_eq_expChildren]

private theorem childrenK_eq_children {B goal cand i : Nat} :
    (childrenK B goal cand i).map (·.map fromSageNode) = children B goal cand i := by
  grind [childrenK, children, Bool.rec_eq, Nat.ble_eq, wheelChildrenK_eq_wheelChildren]

private theorem stepK_succ_cons {B n goal cand i : Nat} {rest : List SageNode} :
    stepK B (n + 1) (⟨goal, cand, i⟩ :: rest) =
      if goal ≤ 1 then
        if cand < B then some false else stepK B n rest
      else (childrenK B goal cand i).rec none (fun cs ↦ stepK B n (cs ++ rest)) := by
  simp only [stepK, Bool.rec_eq, Nat.ble_eq, appendK_eq_append, ← Nat.not_le, ite_not]

/-- Read a `childrenK = some cs` certificate as `children = some (cs.map fromSageNode)`. -/
private theorem children_of_childrenK {B goal cand i : Nat} {cs : List SageNode}
    (hch : childrenK B goal cand i = some cs) :
    children B goal cand i = some (cs.map fromSageNode) := by
  simp [← childrenK_eq_children, hch]

/-- Read a `childrenK = none` certificate as `children = none`. -/
private theorem children_of_childrenK_none {B goal cand i : Nat}
    (hch : childrenK B goal cand i = none) : children B goal cand i = none := by
  simp [← childrenK_eq_children, hch]

theorem stepK_eq_step {B fuel : Nat} {xs : List SageNode} :
    stepK B fuel xs = step B fuel (xs.map fromSageNode) := by
  induction fuel generalizing xs with
  | zero => rfl
  | succ n ih =>
    match xs with
    | [] => rfl
    | ⟨goal, cand, i⟩ :: rest =>
      rw [stepK_succ_cons, step.eq_def]
      cases hck : childrenK B goal cand i with grind [childrenK_eq_children, fromSageNode]

/-- `W` is empty at a node once it is empty at every child given by `childrenK`. -/
theorem W_eq_empty_of_partialK {B goal cand i : ℕ} {cs : List SageNode}
    (hgoal : 2 ≤ goal)
    (hch : childrenK B goal cand i = some cs)
    (hcs : ∀ c ∈ cs, W B c.goal c.cand c.i = ∅) :
    W B goal cand i = ∅ :=
  W_eq_empty_of_partial hgoal (children_of_childrenK hch) (by grind [fromSageNode])

/-- `lcmUpto n` is highly abundant once `W` is empty at every root child given by `childrenK`. -/
theorem highlyAbundantLcm_correct_partialK_W {n : ℕ} {cs : List SageNode}
    (hn : 2 ≤ n)
    (hch : childrenK (lcmUpto n) (σ₁ (lcmUpto n)) 1 0 = some cs)
    (hcs : ∀ c ∈ cs, W (lcmUpto n) c.goal c.cand c.i = ∅) :
    IsHighlyAbundant (lcmUpto n) :=
  highlyAbundantLcm_correct_partial_W hn (children_of_childrenK hch) (by grind [fromSageNode])

end Sage
