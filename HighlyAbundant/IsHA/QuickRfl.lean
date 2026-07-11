/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Lean.Elab.Tactic.Basic
meta import Lean.Elab.Tactic.Basic

public section

/-!
# The `quickRfl` tactic

`quickRfl` closes a `<bool> = true` goal by kernel reduction, using the `Lean.reflBoolTrue`
certificate. The kernel-reducible `Bool` certificates in the highly-abundant search use it.
-/

/-- Discharge a `<bool> = true` goal by kernel reduction, using `Lean.reflBoolTrue`. -/
elab "quickRfl" : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic fun g ↦ g.assign Lean.reflBoolTrue
