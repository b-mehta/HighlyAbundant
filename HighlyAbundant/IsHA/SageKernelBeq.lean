/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.IsHA.SageKernel
import Lean.Elab.Tactic.Basic

/-!
# Bool-valued equality check for child lists

Proving `childrenK … = some kids` with `decide +kernel` routes the comparison
through `DecidableEq → Nat.decEq` and the proof-carrying `Eq.rec`/`Eq.ndrec`
machinery, which the kernel reduces without the GMP `Nat` fast-path. On the
large numbers here that is far slower than reducing `childrenK` itself, even
though that reduction is cheap.

Instead we compare with a structural `Bool` check built from `Nat.beq` (kernel
GMP-native) and `Bool.and'` (a single `Bool.rec` rather than `Bool.and`'s
`match`), discharged by `Lean.reflBoolTrue` via the `quickRfl` tactic.
`childrenK_eq_of_beq` converts the `Bool` result back to
the propositional equality the correctness lemmas need; it is proved once,
abstractly, so applying it per-`n` re-runs no kernel reduction.

This file imports only `HighlyAbundant.SageKernel`, so the per-`n` certificates
that use it stay independent of mathlib's elaboration cost.
-/

namespace Sage

/-- Structural beq on `SageNode` via `Nat.beq` (kernel GMP-native) and `Bool.and'`.
Deliberately not a `BEq` instance: `BEq Nat`/`BEq SageNode` resolve to
`instBEqOfDecidableEq`, i.e. `fun a b => decide (a = b)`, which drags the whole
`DecidableEq` machinery back in. -/
noncomputable def SageNode.beq (a b : SageNode) : Bool :=
  Bool.and' (a.target.beq b.target) (Bool.and' (a.num.beq b.num) (a.minIdx.beq b.minIdx))

/-- Pointwise `SageNode.beq` over two lists, via `List.rec` directly (no equation
compiler), so the kernel sees only `List.rec`, with no `.match_1`/`._f` aux. -/
noncomputable def sageListBeq : List SageNode → List SageNode → Bool :=
  fun xs ↦ xs.rec
    (fun ys ↦ ys.rec true (fun _ _ _ ↦ false))
    (fun x _ ih ys ↦ ys.rec false (fun y ys' _ ↦ Bool.and' (SageNode.beq x y) (ih ys')))

/-- Discharge a `<bool expr> = true` goal by kernel reduction, via the
`Lean.reflBoolTrue` certificate. -/
elab "quickRfl" : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic fun g ↦ g.assign Lean.reflBoolTrue

theorem SageNode.eq_of_beq {a b : SageNode} (h : SageNode.beq a b = true) : a = b := by
  unfold SageNode.beq at h
  simp only [Bool.and'_eq_and, Bool.and_eq_true] at h
  obtain ⟨at_, an, ai⟩ := a
  obtain ⟨bt, bn, bi⟩ := b
  obtain ⟨h1, h2, h3⟩ := h
  simp only [SageNode.mk.injEq]
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3⟩

theorem sageListBeq_sound : ∀ {xs ys : List SageNode}, sageListBeq xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [sageListBeq] at h
  | _ :: _, [], h => by simp [sageListBeq] at h
  | x :: xs, y :: ys, h => by
      have he : sageListBeq (x :: xs) (y :: ys)
          = Bool.and' (SageNode.beq x y) (sageListBeq xs ys) := rfl
      rw [he] at h
      simp only [Bool.and'_eq_and, Bool.and_eq_true] at h
      rw [SageNode.eq_of_beq h.1, sageListBeq_sound h.2]

/-- Convert the `Bool` check back to the propositional equality the
correctness lemmas consume. Abstract over the arguments, so per-`n` application
re-runs no kernel reduction: the `childrenK` reduction happens once, inside the
`quickRfl`-proved hypothesis. -/
theorem childrenK_eq_of_beq {B target num minIdx : Nat} {kids : List SageNode}
    (h : (childrenK B target num minIdx).elim false (fun cs ↦ sageListBeq cs kids) = true) :
    childrenK B target num minIdx = some kids := by
  cases hc : childrenK B target num minIdx with
  | none => rw [hc] at h; simp [Option.elim] at h
  | some cs => rw [hc] at h; simp only [Option.elim] at h; rw [sageListBeq_sound h]

/-- Bool-valued form of the leaf certificate `stepK B fuel [c] = some true`, so
the metaprogram can discharge it with `Lean.reflBoolTrue` on a `Bool = true` goal
instead of `Eq.refl` on the `Option Bool` goal. -/
noncomputable def stepKSingletonBeqCert (B fuel : Nat) (c : SageNode) : Bool :=
  (stepK B fuel [c]).elim false (fun b ↦ b)

/-- Convert the `Bool` leaf cert back to `stepK B fuel [c] = some true`, once and
abstractly, so per-`c` application re-runs no kernel reduction. -/
theorem stepK_singleton_of_beqCert {B fuel : Nat} {c : SageNode}
    (h : stepKSingletonBeqCert B fuel c = true) : stepK B fuel [c] = some true := by
  unfold stepKSingletonBeqCert at h
  cases hc : stepK B fuel [c] with
  | none => rw [hc] at h; simp [Option.elim] at h
  | some b => rw [hc] at h; simp only [Option.elim] at h; rw [h]

/-- Lambda-free `Bool` predicate hiding the `Option.elim`/`fun cs ↦ …` binder of
`childrenK_eq_of_beq`'s hypothesis, so the metaprogram builds the cert type without
constructing a lambda. The kernel unfolds this to the `elim` form. -/
noncomputable def childrenKBeqCert (B target num minIdx : Nat) (kids : List SageNode) : Bool :=
  (childrenK B target num minIdx).elim false (fun cs ↦ sageListBeq cs kids)

theorem childrenKBeqCert_eq_some {B target num minIdx : Nat} {kids : List SageNode}
    (h : childrenKBeqCert B target num minIdx kids = true) :
    childrenK B target num minIdx = some kids :=
  childrenK_eq_of_beq h

end Sage
