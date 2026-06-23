/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.SageKernelEquiv

/-!
# `WCerts` and the `w_certs` tactic

`WCerts B xs := ∀ c ∈ xs, W B c.target c.num c.minIdx = ∅`. Used to compose
leaf-level kernel certificates with the recursive-split lemma
`W_eq_empty_of_partialK` for heavy children.

Two forms:
- `w_certs` — every child gets a leaf cert (kernel-reduce `stepK [c] = some true`).
- `w_certs [i₁, i₂, …]` — children at those indices are expanded one level via
  `childrenK`, and their `W = ∅` is built recursively (leaf certs on the
  grandchildren combined via `W_eq_empty_of_partialK`).
-/

open Lean Meta Elab Tactic

namespace Sage

/-- `∀ c ∈ xs, W B c.target c.num c.minIdx = ∅`, wrapped opaquely so the kernel
doesn't descend through the binders during chain construction. -/
def WCerts (B : Nat) (xs : List SageNode) : Prop :=
  ∀ c ∈ xs, W B c.target c.num c.minIdx = ∅

theorem w_certs_nil (B : Nat) : WCerts B [] :=
  fun _ h => nomatch h

theorem w_certs_cons {B : Nat} {x : SageNode} {xs : List SageNode}
    (h : W B x.target x.num x.minIdx = ∅) (hs : WCerts B xs) :
    WCerts B (x :: xs) := fun c hc =>
  match hc with
  | .head _ => h
  | .tail _ hc' => hs c hc'

/-- Combine certificates for two sublists, so a heavy `WCerts B kids` proof can be
split across files (each proving `WCerts B` for an in-order slice) and built in
parallel, then recombined via `kids = xs ++ ys`. -/
theorem w_certs_append {B : Nat} {xs ys : List SageNode}
    (hx : WCerts B xs) (hy : WCerts B ys) : WCerts B (xs ++ ys) := fun c hc =>
  (List.mem_append.1 hc).elim (hx c) (hy c)

/-- Convert a singleton-stack `stepK = some true` to `W = ∅` for the same node.
The leaf-level cert produced by kernel reduction lands here, then enters the
`w_certs_cons` chain. -/
theorem W_eq_empty_of_stepK_singleton {B fuel : ℕ} {c : SageNode}
    (h : stepK B fuel [c] = some true) :
    W B c.target c.num c.minIdx = ∅ := by
  rw [stepK_eq_step] at h
  simpa [List.map_cons, List.map_nil, fromSageNode]
    using step_true h (fromSageNode c) List.mem_cons_self

/-- Walk a fully-reduced `List.cons`/`List.nil` chain and return its elements. -/
private partial def listElemsW (e : Expr) : MetaM (Array Expr) := do
  let e ← whnf e
  match_expr e with
  | List.cons _ head tail =>
    let rest ← listElemsW tail
    return #[head] ++ rest
  | List.nil _ => return #[]
  | _ => throwError "expected concrete `List` literal, got: {← Meta.ppExpr e}"

/-- Extract the three `Nat` values from a `SageNode` literal Expr. -/
private def nodeNats (c : Expr) : MetaM (Nat × Nat × Nat) := do
  let c ← whnf c
  match_expr c with
  | Sage.SageNode.mk tExpr nExpr mExpr =>
    let some t := tExpr.nat? | throwError "node target not a literal"
    let some n := nExpr.nat? | throwError "node num not a literal"
    let some m := mExpr.nat? | throwError "node minIdx not a literal"
    return (t, n, m)
  | _ => throwError "child not a `SageNode.mk`"

/-- Build a `SageNode` Expr from three `Nat`s. -/
private def nodeExpr (t n m : Nat) : Expr :=
  mkApp3 (mkConst ``Sage.SageNode.mk) (mkNatLit t) (mkNatLit n) (mkNatLit m)

/-- Common Exprs cached for chain construction. -/
private structure CommonExprs where
  nodeTy : Expr
  optBool : Expr
  someTrue : Expr
  nilExpr : Expr
  certValue : Expr

private def mkCommonExprs : CommonExprs :=
  let nodeTy := mkConst ``Sage.SageNode
  let optBool := mkApp (mkConst ``Option [.zero]) (mkConst ``Bool)
  let someTrue :=
    mkApp2 (mkConst ``Option.some [.zero]) (mkConst ``Bool) (mkConst ``Bool.true)
  let nilExpr := mkApp (mkConst ``List.nil [.zero]) nodeTy
  let certValue := mkApp2 (mkConst ``Eq.refl [.succ .zero]) optBool someTrue
  { nodeTy, optBool, someTrue, nilExpr, certValue }

/-- Build a leaf `W B c.target c.num c.minIdx = ∅` witness for child `c`:
kernel-reduce `stepK B searchFuel [c] = some true`, then apply
`W_eq_empty_of_stepK_singleton`. -/
private def buildLeafWWitness (ce : CommonExprs) (B fuel c : Expr) : MetaM Expr := do
  let singletonC := mkApp3 (mkConst ``List.cons [.zero]) ce.nodeTy c ce.nilExpr
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
    xsExpr := mkApp3 (mkConst ``List.cons [.zero]) ce.nodeTy x xsExpr
  return chain

/-- Build a recursive-expansion `W B c.target c.num c.minIdx = ∅` witness for a
child `c`: compute its children via `Sage.children` (spec form), translate to
`SageNode` literals, build leaf certs on the grandchildren, and combine via
`W_eq_empty_of_partialK`. -/
private def buildExpandedWWitness (ce : CommonExprs) (B fuel c : Expr) : MetaM Expr := do
  let (t, n, m) ← nodeNats c
  let some Bval := B.nat? | throwError "B not a literal"
  -- Compute grandchildren via Sage.children (spec form, returns tuples).
  let some grandchildren := Sage.children Bval t n m
    | throwError "Sage.children returned none for ({t}, {n}, {m})"
  -- Convert grandchildren tuples to SageNode literal Exprs.
  let mut xsExpr := ce.nilExpr
  let grandchildExprs := grandchildren.toArray.map fun (a, b, d) => nodeExpr a b d
  for gx in grandchildExprs.reverse do
    xsExpr := mkApp3 (mkConst ``List.cons [.zero]) ce.nodeTy gx xsExpr
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
  -- `childrenK B t n m = some grandchildren` — provable by rfl after kernel reduces.
  let nExpr := mkNatLit n
  let mExpr := mkNatLit m
  let childrenKApp := mkAppN (mkConst ``Sage.childrenK) #[B, tExpr, nExpr, mExpr]
  let optListTy := mkApp (mkConst ``Option [.zero]) (mkApp (mkConst ``List [.zero]) ce.nodeTy)
  let someGrandchildren := mkApp2 (mkConst ``Option.some [.zero])
    (mkApp (mkConst ``List [.zero]) ce.nodeTy) xsExpr
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
      xsExpr := mkApp3 (mkConst ``List.cons [.zero]) ce.nodeTy x xsExpr
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

/-! ### Auto-heuristic recursive expansion -/

/-- Count nodes visited by `step` to assess subtree size; bounded by `fuel`.
Operates on `(target, num, minIdx)` Nat triples since this is a metaprogram-side
compiled helper with no kernel involvement. -/
private def subtreeSize (B : Nat) (fuel : Nat) (c : Nat × Nat × Nat) : Nat :=
  go fuel [c] 0
where
  go : Nat → List (Nat × Nat × Nat) → Nat → Nat
    | 0, _, acc => acc
    | _, [], acc => acc
    | fuel + 1, (target, num, minIdx) :: rest, acc =>
      if target ≤ 1 then
        if num < B then acc else go fuel rest (acc + 1)
      else match children B target num minIdx with
        | none => acc
        | some cs => go fuel (cs ++ rest) (acc + 1)

/-- Build the `W B (t,n,m) = ∅` witness recursively: if the `(t, n, m)` node's
subtree size is ≤ `threshold`, generate a leaf kernel cert; otherwise expand
one level via `Sage.children` and recurse on each grandchild. The Nat triple
is threaded directly so the recursion never calls `whnf` to re-extract Nats
from an Expr we built from those same Nats one level up. -/
private partial def buildWWitnessAuto (ce : CommonExprs) (B fuel : Expr) (Bval : Nat)
    (t n m : Nat) (threshold : Nat) : MetaM Expr := do
  let size := subtreeSize Bval 200_000_000 (t, n, m)
  if size ≤ threshold then
    buildLeafWWitness ce B fuel (nodeExpr t n m)
  else
    let some grandchildren := Sage.children Bval t n m
      | throwError "Sage.children returned none for ({t}, {n}, {m})"
    let grandchildren := grandchildren.toArray
    let grandchildExprs := grandchildren.map fun (a, b, d) => nodeExpr a b d
    -- Recursively build each grandchild's W = ∅ witness, threading Nats directly.
    let grandchildWitnesses ← grandchildren.mapM
      fun (a, b, d) => buildWWitnessAuto ce B fuel Bval a b d threshold
    -- Chain the grandchild witnesses into `WCerts B grandchildren`.
    let mut xsExpr := ce.nilExpr
    let mut grandchildrenChain := mkApp (mkConst ``Sage.w_certs_nil) B
    for w in grandchildWitnesses.reverse, x in grandchildExprs.reverse do
      grandchildrenChain := mkAppN (mkConst ``Sage.w_certs_cons)
        #[B, x, xsExpr, w, grandchildrenChain]
      xsExpr := mkApp3 (mkConst ``List.cons [.zero]) ce.nodeTy x xsExpr
    -- Apply `W_eq_empty_of_partialK` to combine.
    let tExpr := mkNatLit t
    let nExpr := mkNatLit n
    let mExpr := mkNatLit m
    let bleApp := mkApp2 (mkConst ``Nat.ble) (mkNatLit 2) tExpr
    let boolTy := mkConst ``Bool
    let trueExpr := mkConst ``Bool.true
    let bleType := mkApp3 (mkConst ``Eq [.succ .zero]) boolTy bleApp trueExpr
    let bleValue := mkApp2 (mkConst ``Eq.refl [.succ .zero]) boolTy trueExpr
    let bleName ← mkAuxLemma [] bleType bleValue
    let twoLeT := mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (mkNatLit 2) tExpr (mkConst bleName)
    let childrenKApp := mkAppN (mkConst ``Sage.childrenK) #[B, tExpr, nExpr, mExpr]
    let optListTy := mkApp (mkConst ``Option [.zero])
      (mkApp (mkConst ``List [.zero]) ce.nodeTy)
    let someGrandchildren := mkApp2 (mkConst ``Option.some [.zero])
      (mkApp (mkConst ``List [.zero]) ce.nodeTy) xsExpr
    let hchType := mkApp3 (mkConst ``Eq [.succ .zero]) optListTy childrenKApp someGrandchildren
    let hchValue := mkApp2 (mkConst ``Eq.refl [.succ .zero]) optListTy someGrandchildren
    let hchName ← mkAuxLemma [] hchType hchValue
    return mkAppN (mkConst ``Sage.W_eq_empty_of_partialK)
      #[B, tExpr, nExpr, mExpr, xsExpr, twoLeT, mkConst hchName, grandchildrenChain]

/-- Close a `WCerts B kids` goal using the auto-heuristic: each child is
expanded as deep as needed for every leaf node's subtree to fit the threshold. -/
private def closeWCertsGoalAuto (g : MVarId) (threshold : Nat) : MetaM Unit := do
  let target ← g.getType
  match_expr target with
  | Sage.WCerts B kidsExpr =>
    let some Bval := B.nat? | throwError "B not a literal"
    let kids ← listElemsW kidsExpr
    let ce := mkCommonExprs
    let fuel := mkConst ``Sage.searchFuel
    -- Extract Nats from each kid once at the root; recursion threads Nats directly.
    let kidNats ← kids.mapM nodeNats
    let witnesses ← kidNats.mapM
      fun (t, n, m) => buildWWitnessAuto ce B fuel Bval t n m threshold
    let mut chain := mkApp (mkConst ``Sage.w_certs_nil) B
    let mut xsExpr := ce.nilExpr
    for w in witnesses.reverse, x in kids.reverse do
      chain := mkAppN (mkConst ``Sage.w_certs_cons) #[B, x, xsExpr, w, chain]
      xsExpr := mkApp3 (mkConst ``List.cons [.zero]) ce.nodeTy x xsExpr
    g.assign chain
  | _ => throwError "expected `WCerts B xs`, got: {← Meta.ppExpr target}"

/-- Close a goal `Sage.WCerts B <kids>` using the auto-heuristic: any child
whose subtree exceeds `threshold` nodes is expanded one level, recursing
until every leaf cert fits. Example: `w_certs_auto 10000`. -/
elab "w_certs_auto" sz:num : tactic =>
  liftMetaFinishingTactic fun g => closeWCertsGoalAuto g sz.getNat

/-! ### Sanity tests -/

/-- The 9 children of n=8's root (B=840, sL=2880). Used by the sanity tests below. -/
private def kids_test_n8 : List SageNode :=
  [⟨960, 2, 1⟩, ⟨412, 4, 1⟩, ⟨192, 8, 1⟩, ⟨93, 16, 1⟩, ⟨46, 32, 1⟩, ⟨23, 64, 1⟩,
   ⟨12, 128, 1⟩, ⟨6, 256, 1⟩, ⟨3, 512, 1⟩]

/-- Leaf path: all 9 children get a direct kernel cert. -/
private example : WCerts 840 kids_test_n8 := by w_certs

/-- Recursive path: child #5 (target=23) is "expanded" through its grandchildren.
For n=8 every cert is cheap, so the index choice doesn't matter — just exercises
the recursive code path. -/
private example : WCerts 840 kids_test_n8 := by w_certs [5]

/-- Auto-heuristic path: threshold 50 — any child with subtree > 50 nodes is
expanded recursively. Just exercises the auto codepath; n=8 children are all
small so this picks up a few recursions deep. -/
private example : WCerts 840 kids_test_n8 := by w_certs_auto 50

end Sage
