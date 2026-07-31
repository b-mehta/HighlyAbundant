/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.IsHA.SageKernelEquiv
import HighlyAbundant.IsHA.SageKernelBeq
import HighlyAbundant.IsHA.SigmaFactor

open Nat

/-!
# `WCerts` and the `ha_lcm_compose` tactic

`WCerts B xs := ∀ c ∈ xs, W B c.goal c.cand c.i = ∅`. Built by composing
leaf-level kernel certificates (`stepK [c] = some true`) with the recursive-split
lemma `W_eq_empty_of_partialK` for heavy children.

`ha_lcm_compose` takes two forms sharing one code path:

- `ha_lcm_compose <threshold>` closes `WCerts B kids`, for a `kids` list certified
  across several modules building in parallel.
- `ha_lcm_compose <n> <threshold>` closes `IsHighlyAbundant (lcmUpto n)` outright.

In both, a child whose subtree exceeds `threshold` nodes is expanded one level via
`childrenK`, recursing until every leaf cert fits.
-/

open Lean Meta Elab Tactic

namespace Sage

/-- `∀ c ∈ xs, W B c.goal c.cand c.i = ∅`, wrapped opaquely so the kernel
doesn't descend through the binders during chain construction. -/
def WCerts (B : Nat) (xs : List SageNode) : Prop :=
  ∀ c ∈ xs, W B c.goal c.cand c.i = ∅

theorem w_certs_nil (B : Nat) : WCerts B [] :=
  fun _ h => nomatch h

theorem w_certs_cons {B : Nat} {x : SageNode} {xs : List SageNode}
    (h : W B x.goal x.cand x.i = ∅) (hs : WCerts B xs) :
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
    W B c.goal c.cand c.i = ∅ := by
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
    -- Accepts both the `OfNat` form written in source and the raw form the tactic builds.
    let natOf (e : Expr) : Option Nat := e.rawNatLit? <|> e.nat?
    let some t := natOf tExpr | throwError "node goal not a literal"
    let some n := natOf nExpr | throwError "node cand not a literal"
    let some m := natOf mExpr | throwError "node index not a literal"
    return (t, n, m)
  | _ => throwError "child not a `SageNode.mk`"

/-- Build a `SageNode` Expr from three `Nat`s, as raw literals for the kernel to read directly. -/
private def nodeExpr (t n m : Nat) : Expr :=
  mkApp3 (mkConst ``Sage.SageNode.mk) (mkRawNatLit t) (mkRawNatLit n) (mkRawNatLit m)

/-- Common Exprs cached for chain construction. -/
private structure CommonExprs where
  nodeTy : Expr
  nilExpr : Expr
  boolTy : Expr
  trueExpr : Expr

private def mkCommonExprs : CommonExprs :=
  let nodeTy := mkConst ``Sage.SageNode
  let nilExpr := mkApp (mkConst ``List.nil [.zero]) nodeTy
  { nodeTy, nilExpr, boolTy := mkConst ``Bool, trueExpr := mkConst ``Bool.true }

/-- Build a leaf `W B c.goal c.cand c.i = ∅` witness for child `c`: a `Bool`
cert `stepKSingletonBeqCert B searchFuel c = true` discharged by `Lean.reflBoolTrue`,
converted to `stepK B searchFuel [c] = some true`, then `W_eq_empty_of_stepK_singleton`. -/
private def buildLeafWWitness (ce : CommonExprs) (B fuel c : Expr) : MetaM Expr := do
  let beqApp := mkAppN (mkConst ``Sage.stepKSingletonBeqCert) #[B, fuel, c]
  let certType := mkApp3 (mkConst ``Eq [.succ .zero]) ce.boolTy beqApp ce.trueExpr
  let auxName ← mkAuxLemma [] certType Lean.reflBoolTrue
  let stepKWitness :=
    mkAppN (mkConst ``Sage.stepK_singleton_of_beqCert) #[B, fuel, c, mkConst auxName]
  return mkApp4 (mkConst ``Sage.W_eq_empty_of_stepK_singleton) B fuel c stepKWitness

/-! ### Auto-heuristic recursive expansion -/

/-- Fuel for the meta-side subtree walk, above any subtree size the search reaches. -/
private def sizeFuel : Nat := 200_000_000

/-- Count nodes visited by `step` to assess subtree size; bounded by `fuel`.
Operates on `(goal, cand, i)` Nat triples since this is a metaprogram-side
compiled helper with no kernel involvement. -/
private def subtreeSize (B : Nat) (fuel : Nat) (c : Nat × Nat × Nat) : Nat :=
  go fuel [c] 0
where
  go : Nat → List (Nat × Nat × Nat) → Nat → Nat
    | 0, _, acc => acc
    | _, [], acc => acc
    | fuel + 1, (goal, cand, i) :: rest, acc =>
      if goal ≤ 1 then
        if cand < B then acc else go fuel rest (acc + 1)
      else match children B goal cand i with
        | none => acc
        | some cs => go fuel (cs ++ rest) (acc + 1)

/-- Build the `W B (t,n,m) = ∅` witness recursively: if the `(t, n, m)` node's
subtree size is ≤ `threshold`, generate a leaf kernel cert; otherwise expand
one level via `Sage.children` and recurse on each grandchild. The Nat triple
is threaded directly so the recursion never calls `whnf` to re-extract Nats
from an Expr we built from those same Nats one level up. `size` is the node's
own subtree size, measured by the caller during its own walk. -/
private partial def buildWWitnessAuto (ce : CommonExprs) (B fuel : Expr) (Bval : Nat)
    (t n m : Nat) (size : Nat) (threshold : Nat) : MetaM Expr := do
  if size ≤ threshold then
    buildLeafWWitness ce B fuel (nodeExpr t n m)
  else
    let some grandchildren := Sage.children Bval t n m
      | throwError "Sage.children returned none for ({t}, {n}, {m})"
    let grandchildren := grandchildren.toArray
    let grandchildExprs := grandchildren.map fun (a, b, d) => nodeExpr a b d
    -- One walk per grandchild covers this node's subtree exactly once, and each
    -- size travels down with its node, so a level's sizes are measured once.
    let grandchildSizes := grandchildren.map (subtreeSize Bval sizeFuel)
    -- Recursively build each grandchild's W = ∅ witness, threading Nats directly.
    let grandchildWitnesses ← (grandchildren.zip grandchildSizes).mapM
      fun ((a, b, d), sz) => buildWWitnessAuto ce B fuel Bval a b d sz threshold
    -- Chain the grandchild witnesses into `WCerts B grandchildren`.
    let mut xsExpr := ce.nilExpr
    let mut grandchildrenChain := mkApp (mkConst ``Sage.w_certs_nil) B
    for w in grandchildWitnesses.reverse, x in grandchildExprs.reverse do
      grandchildrenChain := mkAppN (mkConst ``Sage.w_certs_cons)
        #[B, x, xsExpr, w, grandchildrenChain]
      xsExpr := mkApp3 (mkConst ``List.cons [.zero]) ce.nodeTy x xsExpr
    -- Apply `W_eq_empty_of_partialK` to combine.
    let tExpr := mkRawNatLit t
    let nExpr := mkRawNatLit n
    let mExpr := mkRawNatLit m
    let boolTy := mkConst ``Bool
    let trueExpr := mkConst ``Bool.true
    let twoLeT := mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (mkRawNatLit 2) tExpr Lean.reflBoolTrue
    let cbcApp := mkAppN (mkConst ``Sage.childrenKBeqCert) #[B, tExpr, nExpr, mExpr, xsExpr]
    let cbcType := mkApp3 (mkConst ``Eq [.succ .zero]) boolTy cbcApp trueExpr
    let cbcName ← mkAuxLemma [] cbcType Lean.reflBoolTrue
    let hch := mkAppN (mkConst ``Sage.childrenKBeqCert_eq_some)
      #[B, tExpr, nExpr, mExpr, xsExpr, mkConst cbcName]
    return mkAppN (mkConst ``Sage.W_eq_empty_of_partialK)
      #[B, tExpr, nExpr, mExpr, xsExpr, twoLeT, hch, grandchildrenChain]

/-- Build a `WCerts B <kidExprs>` proof via the auto-heuristic: each child's
`W = ∅` witness is built by `buildWWitnessAuto` (expanding as deep as the
`threshold` requires), then chained with `w_certs_cons`/`w_certs_nil`. The
`kidNats` array is the `(t, n, m)` triples of `kidExprs`, in the same order. -/
private def buildWCertsAutoChain (ce : CommonExprs) (B fuel : Expr) (Bval : Nat)
    (kidExprs : Array Expr) (kidNats : Array (Nat × Nat × Nat)) (threshold : Nat) :
    MetaM Expr := do
  let witnesses ← kidNats.mapM
    fun c => buildWWitnessAuto ce B fuel Bval c.1 c.2.1 c.2.2 (subtreeSize Bval sizeFuel c) threshold
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

/-! ### The composition tactic `ha_lcm_compose`

Two forms, one code path. `ha_lcm_compose <threshold>` closes a `WCerts B kids`
goal, expanding any child whose subtree exceeds `threshold` nodes one level and
recursing until every leaf cert fits. `ha_lcm_compose <n> <threshold>` closes
`IsHighlyAbundant (lcmUpto n)` outright, computing the root children itself,
emitting them as an aux def, proving `WCerts` over them by the same expansion,
and combining with the `childrenK` cert.
-/

/-- Bridges the literal-`B`/`g`-phrased certificates produced by `ha_lcm_compose`
to the `lcmUpto n`/`σ₁ (lcmUpto n)` form that
`highlyAbundantLcm_correct_partialK_W` consumes. `subst` hides all motive/binder
transport, so the tactic only builds a flat application. -/
theorem ha_lcm_compose_bridge {n B g : ℕ} {cs : List SageNode}
    (eB : lcmUpto n = B) (eg : σ₁ (lcmUpto n) = g)
    (hsL : 2 ≤ g) (hch : childrenKBeqCert B g 1 0 cs = true) (hcs : WCerts B cs) :
    IsHighlyAbundant (lcmUpto n) := by
  subst eB eg
  exact highlyAbundantLcm_correct_partialK_W hsL (childrenKBeqCert_eq_some hch) hcs

/-- `ha_lcm_compose threshold` closes a goal `Sage.WCerts B <kids>`: any child whose
subtree exceeds `threshold` nodes is expanded one level, recursing until every leaf
cert fits. This is the slice form, used where one `kids` list is certified across
several modules building in parallel. -/
elab "ha_lcm_compose" sz:num : tactic =>
  liftMetaFinishingTactic fun g => closeWCertsGoalAuto g sz.getNat

/-- `ha_lcm_compose n threshold` closes a goal `IsHighlyAbundant (lcmUpto n)` for a
literal `n`. The value `B = lcmUpto n` and `g = σ₁ (lcmUpto n)` are computed and
kernel-certified by `Sage.proveLcmUptoValues` (no standalone literal lemmas needed);
`threshold` is the subtree-size bound. The root children are computed
meta-side, emitted as a named auxiliary `def` (`kids`), and three aux lemmas
(`WCerts B kids`, the `childrenK` `Bool` cert, and `2 ≤ g`) are built and combined
via `ha_lcm_compose_bridge`. No inline `kids` list appears at the call site. -/
elab "ha_lcm_compose" nStx:num thr:num : tactic => do
  let n := nStx.getNat
  let threshold := thr.getNat
  liftMetaFinishingTactic fun g => do
    let (Bval, gval, eBexpr, egexpr) ← Sage.proveLcmUptoValues n
    let nExpr := mkNatLit n
    let BExpr := mkNatLit Bval
    let gExpr := mkNatLit gval
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
    -- (5) `childrenK` `Bool` cert: `childrenKBeqCert B g 1 0 kids = true` by `reflBoolTrue`.
    let boolTy := mkConst ``Bool
    let trueExpr := mkConst ``Bool.true
    let cbcApp := mkAppN (mkConst ``Sage.childrenKBeqCert)
      #[BExpr, gExpr, mkNatLit 1, mkNatLit 0, kidsE]
    let cbcTy := mkApp3 (mkConst ``Eq [.succ .zero]) boolTy cbcApp trueExpr
    let hch := mkConst (← mkAuxLemma [] cbcTy Lean.reflBoolTrue)
    -- (6) `hsL : 2 ≤ g` via `Nat.le_of_ble_eq_true` on an inline `Nat.ble 2 g = true` cert.
    let hsL := mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (mkNatLit 2) gExpr Lean.reflBoolTrue
    -- (7) assemble via the bridge (transports literal certs to `lcmUpto n` form).
    g.assign <| mkAppN (mkConst ``Sage.ha_lcm_compose_bridge)
      #[nExpr, BExpr, gExpr, kidsE, eBexpr, egexpr, hsL, hch, hcs]

/-- `lcm_upto_facts n` adds two kernel-certified hypotheses for a literal `n`:
`eB : lcmUpto n = <B>` and `eg : σ₁ (lcmUpto n) = <g>`. Used by the split `n = 169`
proof, which composes its two halves manually rather than through `ha_lcm_compose`. -/
elab "lcm_upto_facts" nStx:num : tactic => do
  let n := nStx.getNat
  liftMetaTactic fun g => do
    let (_, _, eB, eg) ← Sage.proveLcmUptoValues n
    let g ← g.assert `eB (← inferType eB) eB
    let (_, g) ← g.intro1P
    let g ← g.assert `eg (← inferType eg) eg
    let (_, g) ← g.intro1P
    return [g]

/-- `gen_root_kids name n lo hi` defines `name : List SageNode` as children `[lo, hi)`
of the root of the search for `lcmUpto n`, computed meta-side by `Sage.children`. The
assembly's `childrenKBeqCert` kernel-checks that the pieces concatenate to the real
root children, so a wrong range fails loudly there. -/
elab doc:(docComment)? "gen_root_kids " id:ident n:num lo:num hi:num : command =>
  Elab.Command.liftTermElabM do
    let (Bval, gval) := Sage.lcmUptoValues n.getNat
    let some rootKids := Sage.children Bval gval 1 0
      | throwError "Sage.children returned none for the root of lcmUpto {n.getNat}"
    let lo := lo.getNat
    let slice := (rootKids.drop lo).take (hi.getNat - lo)
    let ce := mkCommonExprs
    let mut value := ce.nilExpr
    for (a, b, d) in slice.reverse do
      value := mkApp3 (mkConst ``List.cons [.zero]) ce.nodeTy (nodeExpr a b d) value
    -- Same reducibility hint an ordinary `def` receives (Lean/Meta/Closure.lean:438).
    let hints := ReducibilityHints.regular (getMaxHeight (← getEnv) value + 1)
    let declName := (← getCurrNamespace) ++ id.getId
    addDecl <| .defnDecl {
      name := declName
      levelParams := []
      type := mkApp (mkConst ``List [.zero]) ce.nodeTy
      value, hints, safety := .safe }
    addDocString' declName Syntax.missing doc

/-! ### Sanity tests -/

/-- The 9 children of n=8's root (B=840, sL=2880). Used by the sanity tests below. -/
private def kids_test_n8 : List SageNode :=
  [⟨960, 2, 1⟩, ⟨412, 4, 1⟩, ⟨192, 8, 1⟩, ⟨93, 16, 1⟩, ⟨46, 32, 1⟩, ⟨23, 64, 1⟩,
   ⟨12, 128, 1⟩, ⟨6, 256, 1⟩, ⟨3, 512, 1⟩]

/-- Slice form at threshold 50. Any child with subtree > 50 nodes is expanded
recursively. Exercises the expansion codepath; n=8 children are all small, so it
recurses only a few levels deep. -/
private example : WCerts 840 kids_test_n8 := by ha_lcm_compose 50

/-- The 9 root children of n=8, generated. Carries a docstring, as the n=169 slices do. -/
gen_root_kids kids_gen_n8 8 0 9

/-- The generator reproduces the hand-written list, so the two agree on order and
on every field. -/
private example : kids_gen_n8 = kids_test_n8 := rfl

/-- The slice form accepts a generated list, which carries raw numerals. -/
private example : WCerts 840 kids_gen_n8 := by ha_lcm_compose 50

end Sage
