/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.SageKernel
import Lean.Elab.Tactic.Basic

/-! Kernel certificate for `lcm(1..127)`. -/

namespace Sage


set_option maxRecDepth 1000000
set_option maxHeartbeats 0
elab "quickRfl" : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic fun g ↦ g.assign Lean.reflBoolTrue

theorem stepK_lcm_127 :
    stepK 6676878045498705789701874602220118271269436344024536000 searchFuel
      [(56427714169419799393798930181795637808623985360896000000, 1, 0)] == some true := by quickRfl

end Sage
