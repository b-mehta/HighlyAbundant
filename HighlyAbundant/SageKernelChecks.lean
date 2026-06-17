/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.SageKernel
import Lean.Elab.Tactic.Basic

/-!
# Kernel certificates: `stepK == some true` for `n ≤ 49`

The smallest batch of certificates. Larger `n` live in separate companion
files (`SageKernelChecksMid`, `SageKernelChecks<n>`) so that each lean
invocation stays well inside the standard 7 GB CI runner.
-/

namespace Sage

elab "quickRfl" : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic fun g ↦ g.assign Lean.reflBoolTrue

theorem stepK_lcm_2 :
    stepK 2 searchFuel [(3, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_3 :
    stepK 6 searchFuel [(12, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_4 :
    stepK 12 searchFuel [(28, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_5 :
    stepK 60 searchFuel [(168, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_7 :
    stepK 420 searchFuel [(1344, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_8 :
    stepK 840 searchFuel [(2880, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_9 :
    stepK 2520 searchFuel [(9360, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_11 :
    stepK 27720 searchFuel [(112320, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_13 :
    stepK 360360 searchFuel [(1572480, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_16 :
    stepK 720720 searchFuel [(3249792, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_17 :
    stepK 12252240 searchFuel [(58496256, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_19 :
    stepK 232792560 searchFuel [(1169925120, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_23 :
    stepK 5354228880 searchFuel [(28078202880, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_25 :
    stepK 26771144400 searchFuel [(145070714880, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_27 :
    stepK 80313433200 searchFuel [(446371430400, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_29 :
    stepK 2329089562800 searchFuel [(13391142912000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_31 :
    stepK 72201776446800 searchFuel [(428516573184000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_32 :
    stepK 144403552893600 searchFuel [(870856261632000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_37 :
    stepK 5342931457063200 searchFuel [(33092537942016000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_41 :
    stepK 219060189739591200 searchFuel
      [(1389886593564672000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_43 :
    stepK 9419588158802421600 searchFuel
      [(61155010116845568000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_47 :
    stepK 442720643463713815200 searchFuel
      [(2935440485608587264000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_49 :
    stepK 3099044504245996706400 searchFuel
      [(20915013459961184256000, 1, 0)] == some true := by quickRfl

end Sage
