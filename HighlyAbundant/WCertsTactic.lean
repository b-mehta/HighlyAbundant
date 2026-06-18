/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.PartialCerts
import HighlyAbundant.SageKernelEquiv

/-!
# `WCerts` and the `w_certs` tactic

`WCerts B xs := ∀ c ∈ xs, W B c.1 c.2.1 c.2.2 = ∅` — the witness-set version
of `StepCerts`. Used to compose leaf-level kernel certificates with the
recursive-split lemma `W_eq_empty_of_partialK` for heavy children.

`w_certs` is the analog of `partial_certs` for `WCerts` goals; it generates
one leaf cert per child via `stepK B searchFuel [c] = some true`, converts it
to `W = ∅` via `step_true`, and chains via `w_certs_cons`/`w_certs_nil`.
-/

open Lean Meta Elab Tactic

namespace Sage

/-- `∀ c ∈ xs, W B c.1 c.2.1 c.2.2 = ∅`, wrapped opaquely so the kernel doesn't
descend through the binders during chain construction. -/
def WCerts (B : Nat) (xs : List (Nat × Nat × Nat)) : Prop :=
  ∀ c ∈ xs, W B c.1 c.2.1 c.2.2 = ∅

theorem w_certs_nil (B : Nat) : WCerts B [] :=
  fun _ h => nomatch h

theorem w_certs_cons {B : Nat} {x : Nat × Nat × Nat} {xs : List (Nat × Nat × Nat)}
    (h : W B x.1 x.2.1 x.2.2 = ∅) (hs : WCerts B xs) :
    WCerts B (x :: xs) := fun c hc =>
  match hc with
  | .head _ => h
  | .tail _ hc' => hs c hc'

/-- Convert a singleton-stack `stepK = some true` to `W = ∅` for the same node.
The leaf-level cert produced by kernel reduction lands here, then enters the
`w_certs_cons` chain. -/
theorem W_eq_empty_of_stepK_singleton {B fuel : ℕ} {c : Nat × Nat × Nat}
    (h : stepK B fuel [c] = some true) :
    W B c.1 c.2.1 c.2.2 = ∅ := by
  rw [stepK_eq_step] at h
  exact step_true h c List.mem_cons_self

/-- Walk a fully-reduced `List.cons`/`List.nil` chain and return its elements. -/
private partial def listElemsW (e : Expr) : MetaM (Array Expr) := do
  let e ← whnf e
  match_expr e with
  | List.cons _ head tail =>
    let rest ← listElemsW tail
    return #[head] ++ rest
  | List.nil _ => return #[]
  | _ => throwError "expected concrete `List` literal, got: {← Meta.ppExpr e}"

/-- Close a goal `Sage.WCerts B <kids>` where `<kids>` is a concrete list. Each
child gets an anonymous lemma `stepK B searchFuel [c] = some true` (value
`Eq.refl (some true)`, kernel verified). That's converted to `W = ∅` via
`W_eq_empty_of_stepK_singleton` and combined via the `w_certs_cons` chain. -/
elab "w_certs" : tactic =>
  liftMetaFinishingTactic fun g => do
    let target ← g.getType
    match_expr target with
    | Sage.WCerts B kidsExpr =>
      let kids ← listElemsW kidsExpr
      let nat := mkConst ``Nat
      let tripleTy := mkApp2 (mkConst ``Prod [.zero, .zero]) nat
        (mkApp2 (mkConst ``Prod [.zero, .zero]) nat nat)
      let optBool := mkApp (mkConst ``Option [.zero]) (mkConst ``Bool)
      let someTrue :=
        mkApp2 (mkConst ``Option.some [.zero]) (mkConst ``Bool) (mkConst ``Bool.true)
      let nilExpr := mkApp (mkConst ``List.nil [.zero]) tripleTy
      let certValue := mkApp2 (mkConst ``Eq.refl [.succ .zero]) optBool someTrue
      -- The fuel value used in `stepK [c] = some true`. We use `searchFuel`.
      let fuel := mkConst ``Sage.searchFuel
      -- Add per-child cert `stepK B searchFuel [c] = some true`.
      let mut certNames : Array Name := #[]
      for c in kids do
        let singletonC := mkApp3 (mkConst ``List.cons [.zero]) tripleTy c nilExpr
        let stepKApp := mkAppN (mkConst ``Sage.stepK) #[B, fuel, singletonC]
        let certType := mkApp3 (mkConst ``Eq [.succ .zero]) optBool stepKApp someTrue
        let auxName ← mkAuxLemma [] certType certValue
        certNames := certNames.push auxName
      -- Build the chain right-to-left: nil, prepend each `w_certs_cons` with
      -- `W_eq_empty_of_stepK_singleton (cert)` as the head witness.
      let mut chain := mkApp (mkConst ``Sage.w_certs_nil) B
      let mut xsExpr := nilExpr
      for cert in certNames.reverse, x in kids.reverse do
        let stepKWitness := mkConst cert
        let wWitness :=
          mkApp4 (mkConst ``Sage.W_eq_empty_of_stepK_singleton) B fuel x stepKWitness
        chain := mkAppN (mkConst ``Sage.w_certs_cons)
          #[B, x, xsExpr, wWitness, chain]
        xsExpr := mkApp3 (mkConst ``List.cons [.zero]) tripleTy x xsExpr
      g.assign chain
    | _ => throwError "expected `WCerts B xs`, got: {← Meta.ppExpr target}"

end Sage
