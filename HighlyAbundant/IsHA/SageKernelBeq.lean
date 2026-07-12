/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import HighlyAbundant.IsHA.SageKernel

public section

/-!
# Bool-valued equality check for child lists

A structural `Bool` check on `childrenK … = some kids`, built from `Nat.beq` (kernel GMP-native)
and `Bool.and'` (one `Bool.rec`), discharged by `Lean.reflBoolTrue` through `quickRfl`. Reducing it
stays on the kernel's GMP `Nat` path, where `childrenK` itself is cheap to reduce. The
`DecidableEq`-routed `decide +kernel` comparison is much slower on numbers this size.

`childrenK_eq_of_beq` turns the `Bool` result into the propositional equality the correctness lemmas
take, proved once and applied per `n`. This file imports only `HighlyAbundant.IsHA.SageKernel`, so
the per-`n` certificates stay independent of mathlib's elaboration cost.
-/

namespace Sage

/-! ### Definitions -/

/-- Structural `beq` on `SageNode` from `Nat.beq` and `Bool.and'`. -/
@[expose] noncomputable def SageNode.beq (a b : SageNode) : Bool :=
  (a.target.beq b.target).and' ((a.num.beq b.num).and' (a.minIdx.beq b.minIdx))

/-- Pointwise `SageNode.beq` on two lists via `List.rec`, so the kernel sees a plain `List.rec`. -/
@[expose] noncomputable def sageListBeq : List SageNode → List SageNode → Bool :=
  fun xs ↦ xs.rec
    (fun ys ↦ ys.rec true (fun _ _ _ ↦ false))
    fun x _ ih ys ↦ ys.rec false fun y ys' _ ↦ (x.beq y).and' (ih ys')

/-- `Bool` form of the leaf certificate `stepK B fuel [c] = some true`. -/
@[expose] noncomputable def stepKSingletonBeqCert (B fuel : Nat) (c : SageNode) : Bool :=
  (stepK B fuel [c]).elim false fun b ↦ b

/-- `Bool` form of the `childrenK` certificate, as a flat predicate the metaprogram applies to
literal arguments. The kernel unfolds it to the `Option.elim` form. -/
@[expose] noncomputable def childrenKBeqCert (B target num minIdx : Nat) (kids : List SageNode) :
    Bool :=
  (childrenK B target num minIdx).elim false fun cs ↦ sageListBeq cs kids

/-! ### Proofs -/

theorem SageNode.eq_of_beq {a b : SageNode} (h : SageNode.beq a b = true) : a = b := by
  grind [cases SageNode, SageNode.beq, Bool.and'_eq_and, Nat.beq_eq]

theorem sageListBeq_sound : ∀ {xs ys : List SageNode}, sageListBeq xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    have he : sageListBeq (x :: xs) (y :: ys) = (x.beq y).and' (sageListBeq xs ys) := rfl
    rw [he, Bool.and'_eq_and, Bool.and_eq_true] at h
    rw [SageNode.eq_of_beq h.1, sageListBeq_sound h.2]

/-- Turn the `Bool` certificate into the propositional equality the correctness lemmas take. Abstract
in its arguments, so the `childrenK` reduction runs once inside the `quickRfl`-proved hypothesis and
each per-`n` use is free. -/
theorem childrenKBeqCert_eq_some {B target num minIdx : Nat} {kids : List SageNode}
    (h : childrenKBeqCert B target num minIdx kids) :
    childrenK B target num minIdx = some kids := by
  cases hc : childrenK B target num minIdx with grind [childrenKBeqCert, sageListBeq_sound]

/-- Turn the `Bool` leaf certificate into `stepK B fuel [c] = some true`, proved once and abstractly
so each per-`c` use is free. -/
theorem stepK_singleton_of_beqCert {B fuel : Nat} {c : SageNode}
    (h : stepKSingletonBeqCert B fuel c) : stepK B fuel [c] = some true := by
  cases hc : stepK B fuel [c] with grind [stepKSingletonBeqCert]

end Sage
