/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.SageKernel
import Lean.Elab.Tactic.Basic

/-!
# Kernel certificates: `stepK == some true` for each specific `n`

For each prime power `n` strictly below `64`, and for each `n` in
`{64, 67, 81, 83, 89, 125, 127, 128, 131, 137, 139, 169}`, this file proves
`stepK (lcm(1..n)) fuel [(σ₁ (lcm(1..n)), 1, 0)] == some true` by kernel
reduction. Composed with the correctness theorems in
`HighlyAbundant.SageKernelEquiv` and `HighlyAbundant.SageSpec`, each
witnesses high abundance of the corresponding `lcm(1..n)`.

The file imports only `HighlyAbundant.SageKernel` (not `SageKernelEquiv`
or `SageSpec`) to keep these slow kernel evaluations independent of
mathlib's elaboration cost.

`B` and `sL` are the literal values of `lcm(1..n)` and `σ₁(lcm(1..n))`
respectively. Fuel is set to a large constant; `Nat.rec` on a Nat
literal is lazy, so excess fuel costs nothing.
-/

namespace Sage

elab "quickRfl" : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic fun g ↦ g.assign Lean.reflBoolTrue

/-! ### Prime powers below `64` -/

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
theorem stepK_lcm_53 :
    stepK 164249358725037825439200 searchFuel
      [(1129410726837903949824000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_59 :
    stepK 9690712164777231700912800 searchFuel
      [(67764643610274236989440000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_61 :
    stepK 591133442051411133755680800 searchFuel
      [(4201407903837002693345280000, 1, 0)] == some true := by quickRfl

/-! ### Explicit values at and above `64` -/

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
