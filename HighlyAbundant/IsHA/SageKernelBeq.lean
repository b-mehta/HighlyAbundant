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

A `Bool` equality check on child lists, from `Nat.beq` and `Bool.and'`, so a `childrenK … = some
kids` certificate reduces in the kernel via `Lean.reflBoolTrue` (through `quickRfl`) on `Nat.beq`.
`childrenKBeqCert_eq_some` recovers the `Option` equality the correctness lemmas take.
-/

namespace Sage

/-! ### Definitions -/

/-- Structural `beq` on `SageNode` from `Nat.beq` and `Bool.and'`. -/
@[expose] noncomputable def SageNode.beq (a b : SageNode) : Bool :=
  (a.goal.beq b.goal).and' ((a.cand.beq b.cand).and' (a.i.beq b.i))

/-- Pointwise `SageNode.beq` on two lists, written with `List.rec`. -/
@[expose] noncomputable def sageListBeq : List SageNode → List SageNode → Bool :=
  fun xs ↦ xs.rec
    (fun ys ↦ ys.rec true (fun _ _ _ ↦ false))
    fun x _ ih ys ↦ ys.rec false fun y ys' _ ↦ (x.beq y).and' (ih ys')

/-- `Bool` form of the leaf certificate `stepK B fuel [c] = some true`, written with `Option.rec`
so the kernel reduces it directly. -/
@[expose] noncomputable def stepKSingletonBeqCert (B fuel : Nat) (c : SageNode) : Bool :=
  (stepK B fuel [c]).rec false fun b ↦ b

/-- `Bool` form of the `childrenK` certificate, written with `Option.rec` so the metaprogram builds
it from literal arguments. -/
@[expose] noncomputable def childrenKBeqCert (B goal cand i : Nat) (kids : List SageNode) :
    Bool :=
  (childrenK B goal cand i).rec false fun cs ↦ sageListBeq cs kids

/-! ### Proofs -/

theorem SageNode.eq_of_beq {a b : SageNode} (h : SageNode.beq a b = true) : a = b := by
  grind [cases SageNode, SageNode.beq, Bool.and'_eq_and, Nat.beq_eq]

theorem sageListBeq_sound : ∀ {xs ys : List SageNode}, sageListBeq xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    have he : sageListBeq (x :: xs) (y :: ys) = (x.beq y).and' (sageListBeq xs ys) := rfl
    rw [he, Bool.and'_eq_and, Bool.and_eq_true] at h
    rw [SageNode.eq_of_beq h.1, sageListBeq_sound h.2]

/-- Recover `childrenK … = some kids` from its `Bool` certificate. -/
theorem childrenKBeqCert_eq_some {B goal cand i : Nat} {kids : List SageNode}
    (h : childrenKBeqCert B goal cand i kids) :
    childrenK B goal cand i = some kids := by
  cases hc : childrenK B goal cand i with
  | none => simp [childrenKBeqCert, hc] at h
  | some cs =>
    have hb : sageListBeq cs kids = true := by simpa [childrenKBeqCert, hc] using h
    rw [sageListBeq_sound hb]

/-- Recover `stepK B fuel [c] = some true` from its `Bool` leaf certificate. -/
theorem stepK_singleton_of_beqCert {B fuel : Nat} {c : SageNode}
    (h : stepKSingletonBeqCert B fuel c) : stepK B fuel [c] = some true := by
  cases hc : stepK B fuel [c] with
  | none => simp [stepKSingletonBeqCert, hc] at h
  | some b =>
    have hb : b = true := by simpa [stepKSingletonBeqCert, hc] using h
    rw [hb]

end Sage
