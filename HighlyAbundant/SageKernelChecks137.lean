/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.SageKernel
import Lean.Elab.Tactic.Basic

/-! Kernel certificate for `lcm(1..137)`. -/

namespace Sage

elab "quickRfl" : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic fun g ↦ g.assign Lean.reflBoolTrue

theorem stepK_lcm_137 :
    stepK 239659860565130545615559086972088925228945148132416695184000 searchFuel
      [(2063868082945578911560216807943742372221126786773155840000000, 1, 0)] == some true := by quickRfl

end Sage
