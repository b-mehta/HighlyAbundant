/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.SageKernel
import Lean.Elab.Tactic.Basic

/-! Kernel certificate for `lcm(1..169)`. -/

namespace Sage


elab "quickRfl" : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic fun g ↦ g.assign Lean.reflBoolTrue

theorem stepK_lcm_169 :
    stepK 41640927904370300154508936603455936348626591748630593262827592445686864000 searchFuel
      [(374867757601140118512603512682984851689582369732924776330622402560000000000, 1, 0)] == some true := by quickRfl

end Sage
