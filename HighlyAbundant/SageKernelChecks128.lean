/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.SageKernel
import Lean.Elab.Tactic.Basic

/-! Kernel certificate for `lcm(1..128)`. -/

namespace Sage


elab "quickRfl" : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic fun g ↦ g.assign Lean.reflBoolTrue

theorem stepK_lcm_128 :
    stepK 13353756090997411579403749204440236542538872688049072000 searchFuel
      [(113299741048835030278887615719353445993693828874240000000, 1, 0)] == some true := by quickRfl

end Sage
