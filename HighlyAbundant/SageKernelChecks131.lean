/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.SageKernel
import Lean.Elab.Tactic.Basic

/-! Kernel certificate for `lcm(1..131)`. -/

namespace Sage

elab "quickRfl" : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic fun g ↦ g.assign Lean.reflBoolTrue

theorem stepK_lcm_131 :
    stepK 1749342047920660916901891145781670987072592322134428432000 searchFuel
      [(14955565818446223996813165274954654871167585411399680000000, 1, 0)] == some true := by quickRfl

end Sage
