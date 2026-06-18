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

Two forms:
- `w_certs` — every child gets a leaf cert (kernel-reduce `stepK [c] = some true`).
- `w_certs [i₁, i₂, …]` — children at those indices are expanded one level via
  `childrenK`, and their `W = ∅` is built recursively (leaf certs on the
  grandchildren combined via `W_eq_empty_of_partialK`).
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

/-- Extract the three `Nat` values from a `(Nat × Nat × Nat)` literal Expr. -/
private def tupleNats (c : Expr) : MetaM (Nat × Nat × Nat) := do
  let c ← whnf c
  match_expr c with
  | Prod.mk _ _ tExpr rest =>
    let some t := tExpr.nat? | throwError "child target not a literal"
    let rest ← whnf rest
    match_expr rest with
    | Prod.mk _ _ nExpr mExpr =>
      let some n := nExpr.nat? | throwError "child num not a literal"
      let some m := mExpr.nat? | throwError "child minIdx not a literal"
      return (t, n, m)
    | _ => throwError "child rest not a `Prod.mk`"
  | _ => throwError "child not a `Prod.mk`"

/-- Build a `(Nat × Nat × Nat)` Expr from three `Nat`s. -/
private def tupleExpr (t n m : Nat) : Expr :=
  let nat := mkConst ``Nat
  let prodNN := mkApp2 (mkConst ``Prod [.zero, .zero]) nat nat
  mkApp4 (mkConst ``Prod.mk [.zero, .zero]) nat prodNN
    (mkNatLit t)
    (mkApp4 (mkConst ``Prod.mk [.zero, .zero]) nat nat (mkNatLit n) (mkNatLit m))

/-- Common Exprs cached for chain construction. -/
private structure CommonExprs where
  nat : Expr
  tripleTy : Expr
  optBool : Expr
  someTrue : Expr
  nilExpr : Expr
  certValue : Expr

private def mkCommonExprs : CommonExprs :=
  let nat := mkConst ``Nat
  let tripleTy := mkApp2 (mkConst ``Prod [.zero, .zero]) nat
    (mkApp2 (mkConst ``Prod [.zero, .zero]) nat nat)
  let optBool := mkApp (mkConst ``Option [.zero]) (mkConst ``Bool)
  let someTrue :=
    mkApp2 (mkConst ``Option.some [.zero]) (mkConst ``Bool) (mkConst ``Bool.true)
  let nilExpr := mkApp (mkConst ``List.nil [.zero]) tripleTy
  let certValue := mkApp2 (mkConst ``Eq.refl [.succ .zero]) optBool someTrue
  { nat, tripleTy, optBool, someTrue, nilExpr, certValue }

/-- Build a leaf `W B c.1 c.2.1 c.2.2 = ∅` witness for child `c`: kernel-reduce
`stepK B searchFuel [c] = some true`, then apply `W_eq_empty_of_stepK_singleton`. -/
private def buildLeafWWitness (ce : CommonExprs) (B fuel c : Expr) : MetaM Expr := do
  let singletonC := mkApp3 (mkConst ``List.cons [.zero]) ce.tripleTy c ce.nilExpr
  let stepKApp := mkAppN (mkConst ``Sage.stepK) #[B, fuel, singletonC]
  let certType := mkApp3 (mkConst ``Eq [.succ .zero]) ce.optBool stepKApp ce.someTrue
  let auxName ← mkAuxLemma [] certType ce.certValue
  let stepKWitness := mkConst auxName
  return mkApp4 (mkConst ``Sage.W_eq_empty_of_stepK_singleton) B fuel c stepKWitness

/-- Build a `WCerts B kids` proof by chaining `w_certs_cons` over leaf witnesses.
Returns the proof Expr. -/
private def buildWCertsChain (ce : CommonExprs) (B fuel : Expr) (kids : Array Expr) :
    MetaM Expr := do
  let witnesses ← kids.mapM (buildLeafWWitness ce B fuel)
  let mut chain := mkApp (mkConst ``Sage.w_certs_nil) B
  let mut xsExpr := ce.nilExpr
  for w in witnesses.reverse, x in kids.reverse do
    chain := mkAppN (mkConst ``Sage.w_certs_cons) #[B, x, xsExpr, w, chain]
    xsExpr := mkApp3 (mkConst ``List.cons [.zero]) ce.tripleTy x xsExpr
  return chain

/-- Build a recursive-expansion `W B c.1 c.2.1 c.2.2 = ∅` witness for a child `c`:
compute its children via `Sage.children`, build leaf certs on the grandchildren,
and combine via `W_eq_empty_of_partialK`. -/
private def buildExpandedWWitness (ce : CommonExprs) (B fuel c : Expr) : MetaM Expr := do
  let (t, n, m) ← tupleNats c
  let some Bval := B.nat? | throwError "B not a literal"
  -- Compute grandchildren via Sage.children at the metaprogram level.
  let some grandchildren := Sage.children Bval t n m
    | throwError "Sage.children returned none for ({t}, {n}, {m})"
  -- Convert grandchildren back to a List literal Expr.
  let mut xsExpr := ce.nilExpr
  let grandchildExprs := grandchildren.toArray.map fun (a, b, d) => tupleExpr a b d
  for gx in grandchildExprs.reverse do
    xsExpr := mkApp3 (mkConst ``List.cons [.zero]) ce.tripleTy gx xsExpr
  -- Build `WCerts B grandchildren` via leaf chain.
  let grandchildrenWCerts ← buildWCertsChain ce B fuel grandchildExprs
  -- `2 ≤ t` proof: kernel verifies `Nat.ble 2 t = true` via `Eq.refl true`,
  -- then `Nat.le_of_ble_eq_true` lifts to `2 ≤ t`.
  let tExpr := mkNatLit t
  let bleApp := mkApp2 (mkConst ``Nat.ble) (mkNatLit 2) tExpr
  let boolTy := mkConst ``Bool
  let trueExpr := mkConst ``Bool.true
  let bleType := mkApp3 (mkConst ``Eq [.succ .zero]) boolTy bleApp trueExpr
  let bleValue := mkApp2 (mkConst ``Eq.refl [.succ .zero]) boolTy trueExpr
  let bleName ← mkAuxLemma [] bleType bleValue
  let twoLeT := mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (mkNatLit 2) tExpr (mkConst bleName)
  -- `childrenK B t n m = some grandchildren` — provable by rfl after kernel reduces children.
  let nExpr := mkNatLit n
  let mExpr := mkNatLit m
  let childrenKApp := mkAppN (mkConst ``Sage.childrenK) #[B, tExpr, nExpr, mExpr]
  let optListTy := mkApp (mkConst ``Option [.zero]) (mkApp (mkConst ``List [.zero]) ce.tripleTy)
  let someGrandchildren := mkApp2 (mkConst ``Option.some [.zero])
    (mkApp (mkConst ``List [.zero]) ce.tripleTy) xsExpr
  let hchType := mkApp3 (mkConst ``Eq [.succ .zero]) optListTy childrenKApp someGrandchildren
  let hchValue := mkApp2 (mkConst ``Eq.refl [.succ .zero]) optListTy someGrandchildren
  let hchName ← mkAuxLemma [] hchType hchValue
  let hch := mkConst hchName
  return mkAppN (mkConst ``Sage.W_eq_empty_of_partialK)
    #[B, tExpr, nExpr, mExpr, xsExpr, twoLeT, hch, grandchildrenWCerts]

/-- Close a `WCerts B kids` goal with optional expansion of specific child indices. -/
private def closeWCertsGoal (g : MVarId) (expandIdxs : Array Nat) : MetaM Unit := do
  let target ← g.getType
  match_expr target with
  | Sage.WCerts B kidsExpr =>
    let kids ← listElemsW kidsExpr
    let ce := mkCommonExprs
    let fuel := mkConst ``Sage.searchFuel
    -- For each child, build the witness — leaf or expanded based on index.
    let witnesses ← kids.mapIdxM fun i c =>
      if expandIdxs.contains i then
        buildExpandedWWitness ce B fuel c
      else
        buildLeafWWitness ce B fuel c
    let mut chain := mkApp (mkConst ``Sage.w_certs_nil) B
    let mut xsExpr := ce.nilExpr
    for w in witnesses.reverse, x in kids.reverse do
      chain := mkAppN (mkConst ``Sage.w_certs_cons) #[B, x, xsExpr, w, chain]
      xsExpr := mkApp3 (mkConst ``List.cons [.zero]) ce.tripleTy x xsExpr
    g.assign chain
  | _ => throwError "expected `WCerts B xs`, got: {← Meta.ppExpr target}"

/-- Close a goal `Sage.WCerts B <kids>` with every child as a leaf cert. -/
elab "w_certs" : tactic =>
  liftMetaFinishingTactic fun g => closeWCertsGoal g #[]

/-- Close a goal `Sage.WCerts B <kids>`; the children at the given indices are
expanded one level (their `W = ∅` is built from their grandchildren via
`W_eq_empty_of_partialK`), the rest get a leaf kernel cert. -/
elab "w_certs" "[" idxs:num,* "]" : tactic =>
  liftMetaFinishingTactic fun g => do
    let idxArr := idxs.getElems.map (·.getNat)
    closeWCertsGoal g idxArr

/-! ### Sanity tests -/

/-- The 9 children of n=8's root (B=840, sL=2880). Used by the sanity tests below. -/
private def kids_test_n8 : List (Nat × Nat × Nat) :=
  [(960, 2, 1), (412, 4, 1), (192, 8, 1), (93, 16, 1), (46, 32, 1), (23, 64, 1),
   (12, 128, 1), (6, 256, 1), (3, 512, 1)]

/-- Leaf path: all 9 children get a direct kernel cert. -/
private example : WCerts 840 kids_test_n8 := by w_certs

/-- Recursive path: child #5 (target=23) is "expanded" through its grandchildren.
For n=8 every cert is cheap, so the index choice doesn't matter — just exercises
the recursive code path. -/
private example : WCerts 840 kids_test_n8 := by w_certs [5]

end Sage
