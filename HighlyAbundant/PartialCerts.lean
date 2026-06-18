/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import Lean.Elab.Command
import HighlyAbundant.SageKernel

/-!
# Metaprogram: generate per-child `stepK` certificates and dispatch

For a fully-determined `def kids : List (Nat × Nat × Nat) := [...]`, the command

  `partial_certs <prefix> base <B> fuel <fuel> children <kidsName>`

generates, for each `i`-th element `c_i` of `kids`, a top-level theorem
`<prefix>_c<i> : (stepK B fuel [c_i] == some true) = true` proved by kernel
reduction (`Lean.reflBoolTrue`). It then generates a dispatch theorem
`<prefix>_dispatch : ∀ c ∈ kids, stepK B fuel [c] = some true`.

Each per-child cert is a separate top-level declaration, so the kernel
type-checks them independently and the whnf cache does not accumulate across
them — the memory-isolation property the partial verification path needs.
-/

open Lean Meta Elab Command

namespace Sage

/-- Assign `Lean.reflBoolTrue` to a goal of the form `(b : Bool) = true`,
where `b` reduces to `true` by kernel iota. -/
elab "quickRfl" : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic fun g ↦ g.assign Lean.reflBoolTrue

/-- `(stepK == some true) = true` ↔ `stepK = some true`. -/
theorem stepK_eq_of_beq {B fuel : Nat} {stack : List (Nat × Nat × Nat)}
    (h : (stepK B fuel stack == some true) = true) :
    stepK B fuel stack = some true := by
  cases hs : stepK B fuel stack with
  | none => simp [hs] at h
  | some b =>
    cases b
    · simp [hs] at h
    · rfl

/-- Walk a fully-reduced `List.cons`/`List.nil` chain and return its elements. -/
private partial def listElems (e : Expr) : MetaM (Array Expr) := do
  let e ← whnf e
  match_expr e with
  | List.cons _ head tail =>
    let rest ← listElems tail
    return #[head] ++ rest
  | List.nil _ => return #[]
  | _ =>
    throwError "expected concrete `List` literal, got: {← Meta.ppExpr e}"

/-- Build the dispatch tactic recursively. After `simp only [kids, …, or_false] at hc`,
`hc` has type `c = c₀ ∨ c = c₁ ∨ … ∨ c = c_{n-1}`. We unwind one disjunct at a time
via `cases hc`. -/
private partial def buildDispatch (i : Nat) (certs : Array Name) :
    Command.CommandElabM (TSyntax `tactic) := do
  if i + 1 == certs.size then
    -- Last cert: `hc : c = c_{n-1}`. Substitute and apply.
    let certName := mkIdent certs[i]!
    `(tactic| (subst hc; exact stepK_eq_of_beq $certName))
  else
    let certName := mkIdent certs[i]!
    let inner ← buildDispatch (i + 1) certs
    `(tactic| cases hc with
      | inl heq => subst heq; exact stepK_eq_of_beq $certName
      | inr hc => $inner:tactic)

syntax (name := partialCertsCmd) "partial_certs " ident " base " term:max
  " fuel " term:max " children " ident : command

@[command_elab partialCertsCmd]
def elabPartialCerts : CommandElab := fun stx => do
  match stx with
  | `(partial_certs $px:ident base $bTerm:term fuel $fTerm:term children $kidsId:ident) => do
    let kidsName ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo kidsId
    let kids ← liftTermElabM <| listElems (mkConst kidsName)
    let prefix' := px.getId
    let certNames : Array Name :=
      (Array.range kids.size).map (fun i => prefix'.appendAfter s!"_c{i}")
    -- Per-child certs.
    for i in [:kids.size] do
      let cStx ← liftTermElabM <| PrettyPrinter.delab kids[i]!
      let thmNameStx := mkIdent certNames[i]!
      let cmd ← `(command|
        theorem $thmNameStx :
          Sage.stepK $bTerm $fTerm [$cStx] == some true := by quickRfl)
      elabCommand cmd
    -- Dispatch theorem.
    let dispatchStx := mkIdent (prefix'.appendAfter "_dispatch")
    let kidsStx := mkIdent kidsName
    let dispatch ← buildDispatch 0 certNames
    let cmd ← `(command|
      theorem $dispatchStx :
          ∀ c ∈ $kidsStx, Sage.stepK $bTerm $fTerm [c] = some true := by
        intro c hc
        simp only [$kidsStx:ident, List.mem_cons, List.not_mem_nil, or_false] at hc
        $dispatch:tactic)
    elabCommand cmd
  | _ => throwError "unexpected syntax"

end Sage
