/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.SageKernel
import Lean.Elab.Tactic.Basic

/-! Kernel certificate for `lcm(1..125)`. -/

namespace Sage


set_option maxRecDepth 1000000
set_option maxHeartbeats 0
elab "quickRfl" : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic fun g ↦ g.assign Lean.reflBoolTrue

theorem stepK_lcm_125 :
    stepK 52573842877942565273243107104095419458814459401768000 searchFuel
      [(440841516948592182764054142045278420379874885632000000, 1, 0)] == some true := by quickRfl

end Sage
