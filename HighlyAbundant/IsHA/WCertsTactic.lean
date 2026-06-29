/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.IsHA.SageKernelEquiv
import HighlyAbundant.IsHA.SageKernelBeq

/-!
# `WCerts`, the `w_certs_auto` tactic, and `ha_lcm_compose`

`WCerts B xs := ∀ c ∈ xs, W B c.target c.num c.minIdx = ∅`. Built by composing
leaf-level kernel certificates (`stepK [c] = some true`) with the recursive-split
lemma `W_eq_empty_of_partialK` for heavy children.

- `w_certs_auto <threshold>` closes `WCerts B kids`: any child whose subtree
  exceeds `threshold` nodes is expanded one level via `childrenK`, recursing until
  every leaf cert fits.
- `ha_lcm_compose eB eg <threshold>` closes `IsHighlyAbundant (lcmRange n)`
  directly: emits the root children as an auxiliary `kids` def, builds the `WCerts`
  proof via the same auto heuristic, and combines with the `childrenK` cert.
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

/-- Combine certificates for two sublists, so a large `WCerts B kids` proof can be
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

/-- Build a `WCerts B <kidExprs>` proof via the auto-heuristic: each child's
`W = ∅` witness is built by `buildWWitnessAuto` (expanding as deep as the
`threshold` requires), then chained with `w_certs_cons`/`w_certs_nil`. The
`kidNats` array is the `(t, n, m)` triples of `kidExprs`, in the same order. -/
private def buildWCertsAutoChain (ce : CommonExprs) (B fuel : Expr) (Bval : Nat)
    (kidExprs : Array Expr) (kidNats : Array (Nat × Nat × Nat)) (threshold : Nat) :
    MetaM Expr := do
  let witnesses ← kidNats.mapM
    fun (t, n, m) => buildWWitnessAuto ce B fuel Bval t n m threshold
  let mut chain := mkApp (mkConst ``Sage.w_certs_nil) B
  let mut xsExpr := ce.nilExpr
  for w in witnesses.reverse, x in kidExprs.reverse do
    chain := mkAppN (mkConst ``Sage.w_certs_cons) #[B, x, xsExpr, w, chain]
    xsExpr := mkApp3 (mkConst ``List.cons [.zero]) ce.nodeTy x xsExpr
  return chain

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
    let chain ← buildWCertsAutoChain ce B fuel Bval kids kidNats threshold
    g.assign chain
  | _ => throwError "expected `WCerts B xs`, got: {← Meta.ppExpr target}"

/-- Close a goal `Sage.WCerts B <kids>` using the auto-heuristic: any child
whose subtree exceeds `threshold` nodes is expanded one level, recursing
until every leaf cert fits. Example: `w_certs_auto 10000`. -/
elab "w_certs_auto" sz:num : tactic =>
  liftMetaFinishingTactic fun g => closeWCertsGoalAuto g sz.getNat

/-! ### One-shot composition tactic `ha_lcm_compose`

Closes a goal `IsHighlyAbundant (lcmRange n)` in one invocation: it emits the root
children as an aux def, builds the `WCerts` proof, and combines with the
`childrenK` cert.
-/

/-- Lambda-free `Bool` predicate hiding the `Option.elim`/`fun cs ↦ …` binder of
`childrenK_eq_of_beq`'s hypothesis, so the metaprogram can build the cert type
without constructing a lambda. The kernel unfolds this to the `elim` form. -/
noncomputable def childrenKBeqCert (B target num minIdx : Nat) (kids : List SageNode) : Bool :=
  (childrenK B target num minIdx).elim false (fun cs ↦ sageListBeq cs kids)

theorem childrenKBeqCert_eq_some {B target num minIdx : Nat} {kids : List SageNode}
    (h : childrenKBeqCert B target num minIdx kids = true) :
    childrenK B target num minIdx = some kids :=
  childrenK_eq_of_beq h

/-- Bridges the literal-`B`/`g`-phrased certificates produced by `ha_lcm_compose`
to the `lcmRange n`/`σ₁ (lcmRange n)` form that
`highlyAbundantLcm_correct_partialK_W` consumes. `subst` hides all motive/binder
transport, so the tactic only builds a flat application. -/
theorem ha_lcm_compose_bridge {n B g : ℕ} {cs : List SageNode}
    (eB : lcmRange n = B) (eg : σ₁ (lcmRange n) = g)
    (hsL : 2 ≤ g) (hch : childrenKBeqCert B g 1 0 cs = true) (hcs : WCerts B cs) :
    IsHighlyAbundant (lcmRange n) := by
  subst eB eg
  exact highlyAbundantLcm_correct_partialK_W hsL (childrenKBeqCert_eq_some hch) hcs

/-- `ha_lcm_compose eB eg threshold` closes a goal `IsHighlyAbundant (lcmRange n)`.
`eB : lcmRange n = B` and `eg : σ₁ (lcmRange n) = g` supply the literals `B`, `g`;
`threshold` is the `w_certs_auto` subtree-size bound. The root children are
computed meta-side, emitted as a named auxiliary `def` (`kids`), and three aux
lemmas (`WCerts B kids`, the `childrenK` `Bool` cert, and `2 ≤ g`) are built and
combined via `ha_lcm_compose_bridge`. No inline `kids` list appears at the call site. -/
elab "ha_lcm_compose" eBStx:term:max egStx:term:max thr:num : tactic => do
  let threshold := thr.getNat
  let eBexpr ← instantiateMVars (← elabTerm eBStx none)
  let egexpr ← instantiateMVars (← elabTerm egStx none)
  let eBty ← instantiateMVars (← inferType eBexpr)
  let egty ← instantiateMVars (← inferType egexpr)
  let some (_, lhsB, BExpr) := eBty.eq?
    | throwError "first argument must prove `lcmRange n = B`, got: {← Meta.ppExpr eBty}"
  let_expr lcmRange nExpr := lhsB
    | throwError "first argument's LHS must be `lcmRange n`, got: {← Meta.ppExpr lhsB}"
  let some Bval := BExpr.nat?
    | throwError "`B` is not a `Nat` literal: {← Meta.ppExpr BExpr}"
  let some (_, _, gExpr) := egty.eq?
    | throwError "second argument must prove `σ₁ (lcmRange n) = g`, got: {← Meta.ppExpr egty}"
  let some gval := gExpr.nat?
    | throwError "`g` is not a `Nat` literal: {← Meta.ppExpr gExpr}"
  liftMetaFinishingTactic fun g => do
    let ce := mkCommonExprs
    let fuel := mkConst ``Sage.searchFuel
    let some rootKidsList := Sage.children Bval gval 1 0
      | throwError "Sage.children returned none for root ({gval}, 1, 0)"
    let rootKids := rootKidsList.toArray
    -- (3) `kids` as a named auxiliary definition (never inlined below).
    let listTy := mkApp (mkConst ``List [.zero]) ce.nodeTy
    let mut kidsListExpr := ce.nilExpr
    for (a, b, d) in rootKids.reverse do
      kidsListExpr := mkApp3 (mkConst ``List.cons [.zero]) ce.nodeTy (nodeExpr a b d) kidsListExpr
    let kidsName ← mkAuxDeclName `kids
    let kidsE ← mkAuxDefinition kidsName listTy kidsListExpr (compile := false)
    -- (4) `hcs : WCerts B kids` via the auto chain.
    let kidExprs := rootKids.map fun (a, b, d) => nodeExpr a b d
    let chain ← buildWCertsAutoChain ce BExpr fuel Bval kidExprs rootKids threshold
    let wcertsTy := mkApp2 (mkConst ``Sage.WCerts) BExpr kidsE
    let hcs := mkConst (← mkAuxLemma [] wcertsTy chain)
    -- (5) `childrenK` `Bool` cert: `childrenKBeqCert B g 1 0 kids = true` by `Eq.refl`.
    let boolTy := mkConst ``Bool
    let trueExpr := mkConst ``Bool.true
    let cbcApp := mkAppN (mkConst ``Sage.childrenKBeqCert)
      #[BExpr, gExpr, mkNatLit 1, mkNatLit 0, kidsE]
    let cbcTy := mkApp3 (mkConst ``Eq [.succ .zero]) boolTy cbcApp trueExpr
    let cbcVal := mkApp2 (mkConst ``Eq.refl [.succ .zero]) boolTy trueExpr
    let hch := mkConst (← mkAuxLemma [] cbcTy cbcVal)
    -- (6) `hsL : 2 ≤ g` via `Nat.le_of_ble_eq_true` + a `Nat.ble 2 g = true` cert.
    let bleApp := mkApp2 (mkConst ``Nat.ble) (mkNatLit 2) gExpr
    let bleTy := mkApp3 (mkConst ``Eq [.succ .zero]) boolTy bleApp trueExpr
    let bleVal := mkApp2 (mkConst ``Eq.refl [.succ .zero]) boolTy trueExpr
    let hsL := mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (mkNatLit 2) gExpr
      (mkConst (← mkAuxLemma [] bleTy bleVal))
    -- (7) assemble via the bridge (transports literal certs to `lcmRange n` form).
    g.assign <| mkAppN (mkConst ``Sage.ha_lcm_compose_bridge)
      #[nExpr, BExpr, gExpr, kidsE, eBexpr, egexpr, hsL, hch, hcs]

/-! ### Sanity tests -/

/-- The 9 children of n=8's root (B=840, sL=2880). Used by the sanity tests below. -/
private def kids_test_n8 : List SageNode :=
  [⟨960, 2, 1⟩, ⟨412, 4, 1⟩, ⟨192, 8, 1⟩, ⟨93, 16, 1⟩, ⟨46, 32, 1⟩, ⟨23, 64, 1⟩,
   ⟨12, 128, 1⟩, ⟨6, 256, 1⟩, ⟨3, 512, 1⟩]

/-- Auto-heuristic path: threshold 50. Any child with subtree > 50 nodes is
expanded recursively. Exercises the auto codepath; n=8 children are all
small, so it recurses only a few levels deep. -/
private example : WCerts 840 kids_test_n8 := by w_certs_auto 50

end Sage
