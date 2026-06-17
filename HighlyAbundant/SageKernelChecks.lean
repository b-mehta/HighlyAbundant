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
    stepK 2 200000000 [(3, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_3 :
    stepK 6 200000000 [(12, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_4 :
    stepK 12 200000000 [(28, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_5 :
    stepK 60 200000000 [(168, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_7 :
    stepK 420 200000000 [(1344, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_8 :
    stepK 840 200000000 [(2880, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_9 :
    stepK 2520 200000000 [(9360, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_11 :
    stepK 27720 200000000 [(112320, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_13 :
    stepK 360360 200000000 [(1572480, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_16 :
    stepK 720720 200000000 [(3249792, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_17 :
    stepK 12252240 200000000 [(58496256, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_19 :
    stepK 232792560 200000000 [(1169925120, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_23 :
    stepK 5354228880 200000000 [(28078202880, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_25 :
    stepK 26771144400 200000000 [(145070714880, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_27 :
    stepK 80313433200 200000000 [(446371430400, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_29 :
    stepK 2329089562800 200000000 [(13391142912000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_31 :
    stepK 72201776446800 200000000 [(428516573184000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_32 :
    stepK 144403552893600 200000000 [(870856261632000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_37 :
    stepK 5342931457063200 200000000 [(33092537942016000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_41 :
    stepK 219060189739591200 200000000
      [(1389886593564672000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_43 :
    stepK 9419588158802421600 200000000
      [(61155010116845568000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_47 :
    stepK 442720643463713815200 200000000
      [(2935440485608587264000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_49 :
    stepK 3099044504245996706400 200000000
      [(20915013459961184256000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_53 :
    stepK 164249358725037825439200 200000000
      [(1129410726837903949824000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_59 :
    stepK 9690712164777231700912800 200000000
      [(67764643610274236989440000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_61 :
    stepK 591133442051411133755680800 200000000
      [(4201407903837002693345280000, 1, 0)] == some true := by quickRfl

/-! ### Explicit values at and above `64` -/

theorem stepK_lcm_64 :
    stepK 1182266884102822267511361600 200000000
      [(8469504822020624477061120000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_67 :
    stepK 79211881234889091923261227200 200000000
      [(575926327897402464440156160000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_81 :
    stepK 97301577764381948734868316916891200 200000000
      [(742585584959041199989990788956160000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_83 :
    stepK 8076030954443701744994070304101969600 200000000
      [(62377189136559460799159226272317440000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_89 :
    stepK 718766754945489455304472257065075294400 200000000
      [(5613947022290351471924330364508569600000, 1, 0)] == some true := by quickRfl
theorem stepK_lcm_125 :
    stepK 52573842877942565273243107104095419458814459401768000 200000000
      [(440841516948592182764054142045278420379874885632000000, 1, 0)] == some true := by
  quickRfl
theorem stepK_lcm_127 :
    stepK 6676878045498705789701874602220118271269436344024536000 200000000
      [(56427714169419799393798930181795637808623985360896000000, 1, 0)] == some true := by
  quickRfl
theorem stepK_lcm_128 :
    stepK 13353756090997411579403749204440236542538872688049072000 200000000
      [(113299741048835030278887615719353445993693828874240000000, 1, 0)] == some true := by
  quickRfl
theorem stepK_lcm_131 :
    stepK 1749342047920660916901891145781670987072592322134428432000 200000000
      [(14955565818446223996813165274954654871167585411399680000000, 1, 0)] == some true := by
  quickRfl
theorem stepK_lcm_137 :
    stepK 239659860565130545615559086972088925228945148132416695184000 200000000
      [(2063868082945578911560216807943742372221126786773155840000000, 1, 0)] == some true := by
  quickRfl
theorem stepK_lcm_139 :
    stepK 33312720618553145840562713089120360606823375590405920630576000 200000000
      [(288941531612381047618430353112123932110957750148241817600000000, 1, 0)] == some true := by
  quickRfl
theorem stepK_lcm_169 :
    stepK 41640927904370300154508936603455936348626591748630593262827592445686864000
      200000000
      [(374867757601140118512603512682984851689582369732924776330622402560000000000,
        1, 0)] == some true := by quickRfl

end Sage
