/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.SageKernel
import Lean.Elab.Tactic.Basic

/-! Kernel certificate for `lcm(1..139)`. -/

namespace Sage


set_option maxRecDepth 1000000
set_option maxHeartbeats 0
elab "quickRfl" : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic fun g ↦ g.assign Lean.reflBoolTrue

theorem stepK_lcm_139 :
    stepK 33312720618553145840562713089120360606823375590405920630576000 searchFuel
      [(288941531612381047618430353112123932110957750148241817600000000, 1, 0)] == some true := by quickRfl

end Sage
