/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import Lean.Elab.Tactic
import HighlyAbundant.SageKernel

/-!
# `partial_certs` tactic

`StepCerts B fuel xs` is an opaque wrapper for `∀ c ∈ xs, stepK B fuel [c] = some true`.
The two helper lemmas `step_certs_nil` and `step_certs_cons` let a proof of
`StepCerts B fuel <list literal>` be constructed as a linear chain of applications.

The `partial_certs` tactic closes a goal of the form `StepCerts B fuel kids`
where `kids` is a concrete `List SageNode` literal. For each `c` in `kids` it
adds an auxiliary lemma `stepK B fuel [c] = some true` whose value is `Eq.refl`
— the kernel's type-check is the actual stepK reduction. It then builds the
`step_certs_cons` / `step_certs_nil` chain by direct `mkAppN`, with no binder
construction and no unification.
-/

open Lean Meta Elab Tactic

namespace Sage

/-- `∀ c ∈ xs, stepK B fuel [c] = some true`, wrapped so the kernel doesn't
descend through the binders during chain construction. -/
def StepCerts (B fuel : Nat) (xs : List SageNode) : Prop :=
  ∀ c ∈ xs, stepK B fuel [c] = some true

theorem step_certs_nil (B fuel : Nat) : StepCerts B fuel [] :=
  fun _ h => nomatch h

theorem step_certs_cons {B fuel : Nat} {x : SageNode} {xs : List SageNode}
    (h : stepK B fuel [x] = some true) (hs : StepCerts B fuel xs) :
    StepCerts B fuel (x :: xs) := fun c hc =>
  match hc with
  | .head _ => h
  | .tail _ hc' => hs c hc'

/-- Walk a fully-reduced `List.cons`/`List.nil` chain and return its elements. -/
private partial def listElems (e : Expr) : MetaM (Array Expr) := do
  let e ← whnf e
  match_expr e with
  | List.cons _ head tail =>
    let rest ← listElems tail
    return #[head] ++ rest
  | List.nil _ => return #[]
  | _ => throwError "expected concrete `List` literal, got: {← Meta.ppExpr e}"

/-- Close a goal `Sage.StepCerts B fuel <kids>` where `<kids>` is a concrete list.
For each element `c` of `<kids>`, an auxiliary lemma asserting
`stepK B fuel [c] = some true` is added; its value is `Eq.refl (some true)`, so
the kernel's type-check is exactly the kernel reduction of `stepK B fuel [c]`.
The dispatch is a linear chain of `step_certs_cons` ending in `step_certs_nil`. -/
elab "partial_certs" : tactic =>
  liftMetaFinishingTactic fun g => do
    let target ← g.getType
    match_expr target with
    | Sage.StepCerts B fuel kidsExpr =>
      let kids ← listElems kidsExpr
      let nodeTy := mkConst ``Sage.SageNode
      let optBool := mkApp (mkConst ``Option [.zero]) (mkConst ``Bool)
      let someTrue :=
        mkApp2 (mkConst ``Option.some [.zero]) (mkConst ``Bool) (mkConst ``Bool.true)
      let nilExpr := mkApp (mkConst ``List.nil [.zero]) nodeTy
      let certValue := mkApp2 (mkConst ``Eq.refl [.succ .zero]) optBool someTrue
      -- One auxiliary lemma per child.
      let mut certNames : Array Name := #[]
      for c in kids do
        let singletonC := mkApp3 (mkConst ``List.cons [.zero]) nodeTy c nilExpr
        let stepKApp := mkAppN (mkConst ``Sage.stepK) #[B, fuel, singletonC]
        let certType := mkApp3 (mkConst ``Eq [.succ .zero]) optBool stepKApp someTrue
        let auxName ← mkAuxLemma [] certType certValue
        certNames := certNames.push auxName
      -- Build the chain right-to-left: nil, then prepend each `step_certs_cons`.
      let mut chain := mkAppN (mkConst ``Sage.step_certs_nil) #[B, fuel]
      let mut xsExpr := nilExpr
      for cert in certNames.reverse, x in kids.reverse do
        chain := mkAppN (mkConst ``Sage.step_certs_cons)
          #[B, fuel, x, xsExpr, mkConst cert, chain]
        xsExpr := mkApp3 (mkConst ``List.cons [.zero]) nodeTy x xsExpr
      g.assign chain
    | _ => throwError "expected `StepCerts B fuel xs`, got: {← Meta.ppExpr target}"

end Sage
