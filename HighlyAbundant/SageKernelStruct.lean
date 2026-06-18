/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.SageKernel

/-!
# Struct-based kernel decider — experiment

A side-by-side variant of `stepK`/`childrenK`/`wheelChildrenK`/`expChildrenK` that
uses a flat `SageNode` struct instead of `Nat × Nat × Nat`. The kernel
diagnostic for n=64 shows `Prod.rec` accounts for ~7% of unfoldings (80,566 out
of ~1.4M total significant unfolds); a struct destructures all three fields in
one `SageNode.rec` rather than two nested `Prod.rec`, cutting that roughly in
half.

This module is for benchmarking only — not used by the main proof path. Compare
`stepK` (Prod) vs `stepK_S` (struct) timings via `Bench/N064.lean` and
`Bench/N064S.lean`.
-/

namespace Sage

/-- Flat 3-field representation of a search-tree node. Avoids the nested
`Prod (Nat × Nat × Nat)` and its two-step `Prod.rec` destructuring. -/
structure SageNode where
  target : Nat
  num : Nat
  minIdx : Nat
deriving DecidableEq, Repr

/-- Convert a `(Nat × Nat × Nat)` to `SageNode`. -/
def toSageNode (p : Nat × Nat × Nat) : SageNode :=
  ⟨p.1, p.2.1, p.2.2⟩

/-- Emit children `(⌈target / σ(p^k)⌉, num * p^k, next)` for `k ≥ 1` with
`p^k ≤ m`, as `SageNode`s. -/
noncomputable def expChildrenK_S (fuel target num next m p : Nat) :
    Nat → List SageNode :=
  fuel.rec (fun _ ↦ []) fun _ r pk ↦
    (pk.ble m).rec []
      (let spk := ((pk.mul p).sub (nat_lit 1)).div (p.sub (nat_lit 1))
       let child : SageNode := ⟨ceilDivK target spk, num.mul pk, next⟩
       (target.ble spk).rec (child :: r (pk.mul p)) [child])

noncomputable def wheelChildrenK_S (fuel m2 m target num : Nat) :
    Nat → Nat → Nat → Nat → List SageNode → Option (List SageNode) :=
  fuel.rec (fun _ _ _ _ _ ↦ none) fun _ r front back lhs rhs acc ↦
    (extendK (nat_lit 50) m2 front back lhs rhs).rec
      none
      (some acc)
      (fun b lhs' rhs' ↦
        (front.ble (nat_lit 48)).rec none <|
          let p := primesRArray.get front
          r front.succ b (lhs'.div p) (rhs'.div (p.sub (nat_lit 1)))
            (appendK (expChildrenK_S m.succ target num front.succ m p p) acc))

noncomputable def childrenK_S (B target num minIdx : Nat) : Option (List SageNode) :=
  (minIdx.ble (nat_lit 48)).rec none <|
    let p0 := primesRArray.get minIdx
    let m := B.div num
    wheelChildrenK_S (nat_lit 50) (m.mul m) m target num minIdx minIdx (p0.mul m)
      (target.mul (p0.sub (nat_lit 1))) []

noncomputable def stepK_S (B : Nat) : Nat → List SageNode → Option Bool :=
  fun fuel ↦ fuel.rec (fun _ ↦ none) fun _ r stack ↦
    stack.rec (some true) fun node rest _ ↦
      node.rec fun target num minIdx ↦
        (target.ble (nat_lit 1)).rec
          ((childrenK_S B target num minIdx).rec none (fun cs ↦ r (appendK cs rest)))
          ((B.ble num).rec (some false) (r rest))

end Sage
