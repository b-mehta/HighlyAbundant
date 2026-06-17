/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.SageKernel
import Lean.Elab.Tactic.Basic

/-! Kernel certificates: `stepK == some true` for `53 ≤ n ≤ 89`. -/

namespace Sage

elab "quickRfl" : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic fun g ↦ g.assign Lean.reflBoolTrue

theorem stepK_lcm_53 :
    stepK 164249358725037825439200 searchFuel
      [(1129410726837903949824000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_59 :
    stepK 9690712164777231700912800 searchFuel
      [(67764643610274236989440000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_61 :
    stepK 591133442051411133755680800 searchFuel
      [(4201407903837002693345280000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_64 :
    stepK 1182266884102822267511361600 searchFuel
      [(8469504822020624477061120000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_67 :
    stepK 79211881234889091923261227200 searchFuel
      [(575926327897402464440156160000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_81 :
    stepK 97301577764381948734868316916891200 searchFuel
      [(742585584959041199989990788956160000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_83 :
    stepK 8076030954443701744994070304101969600 searchFuel
      [(62377189136559460799159226272317440000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_89 :
    stepK 718766754945489455304472257065075294400 searchFuel
      [(5613947022290351471924330364508569600000, 1, 0)] == some true := by quickRfl

end Sage
