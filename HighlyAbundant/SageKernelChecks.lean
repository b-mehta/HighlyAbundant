/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.SageKernel
import Lean.Elab.Tactic.Basic

/-!
# Kernel certificates for `lcm (1..n)` being highly abundant

For each prime power `n` strictly below `64`, and for the explicit list
`64, 67, 81, 83, 89, 125, 127, 128, 131, 137, 139, 169`, this file evaluates
`stepK (lcm (1..n)) fuel [(σ₁ (lcm (1..n)), 1, 0)] == some true` by kernel
reduction.

Composed with the correctness theorems in `HighlyAbundant.SageKernelEquiv` /
`HighlyAbundant.SageSpec`, each kernel certificate witnesses high abundance of
the corresponding `lcm (1..n)`.

The file deliberately imports `HighlyAbundant.SageKernel` only (not
`SageKernelEquiv` or `SageSpec`) to skip mathlib and keep these slow kernel
evaluations independent from the rest of the build.

Fuel is set generously; `Nat.rec` on a large literal is lazy, so excess fuel
costs nothing.
-/

namespace Sage

elab "quickRfl" : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic fun g ↦ g.assign Lean.reflBoolTrue

/-! ### Prime powers below 64 -/

example : stepK 2 200000000 [(3, 1, 0)] == some true := by quickRfl
example : stepK 6 200000000 [(12, 1, 0)] == some true := by quickRfl
example : stepK 12 200000000 [(28, 1, 0)] == some true := by quickRfl
example : stepK 60 200000000 [(168, 1, 0)] == some true := by quickRfl
example : stepK 420 200000000 [(1344, 1, 0)] == some true := by quickRfl
example : stepK 840 200000000 [(2880, 1, 0)] == some true := by quickRfl
example : stepK 2520 200000000 [(9360, 1, 0)] == some true := by quickRfl
example : stepK 27720 200000000 [(112320, 1, 0)] == some true := by quickRfl
example : stepK 360360 200000000 [(1572480, 1, 0)] == some true := by quickRfl
example : stepK 720720 200000000 [(3249792, 1, 0)] == some true := by quickRfl
example : stepK 12252240 200000000 [(58496256, 1, 0)] == some true := by quickRfl
example : stepK 232792560 200000000 [(1169925120, 1, 0)] == some true := by quickRfl
example : stepK 5354228880 200000000 [(28078202880, 1, 0)] == some true := by quickRfl
example : stepK 26771144400 200000000 [(145070714880, 1, 0)] == some true := by quickRfl
example : stepK 80313433200 200000000 [(446371430400, 1, 0)] == some true := by quickRfl
example : stepK 2329089562800 200000000 [(13391142912000, 1, 0)] == some true := by quickRfl
example : stepK 72201776446800 200000000 [(428516573184000, 1, 0)] == some true := by quickRfl
example : stepK 144403552893600 200000000 [(870856261632000, 1, 0)] == some true := by quickRfl
example : stepK 5342931457063200 200000000 [(33092537942016000, 1, 0)] == some true := by quickRfl
example : stepK 219060189739591200 200000000
    [(1389886593564672000, 1, 0)] == some true := by quickRfl
example : stepK 9419588158802421600 200000000
    [(61155010116845568000, 1, 0)] == some true := by quickRfl
example : stepK 442720643463713815200 200000000
    [(2935440485608587264000, 1, 0)] == some true := by quickRfl
example : stepK 3099044504245996706400 200000000
    [(20915013459961184256000, 1, 0)] == some true := by quickRfl
example : stepK 164249358725037825439200 200000000
    [(1129410726837903949824000, 1, 0)] == some true := by quickRfl
example : stepK 9690712164777231700912800 200000000
    [(67764643610274236989440000, 1, 0)] == some true := by quickRfl
example : stepK 591133442051411133755680800 200000000
    [(4201407903837002693345280000, 1, 0)] == some true := by quickRfl

/-! ### Explicit list at and above 64 -/

example : stepK 1182266884102822267511361600 200000000
    [(8469504822020624477061120000, 1, 0)] == some true := by quickRfl
example : stepK 79211881234889091923261227200 200000000
    [(575926327897402464440156160000, 1, 0)] == some true := by quickRfl
example : stepK 97301577764381948734868316916891200 200000000
    [(742585584959041199989990788956160000, 1, 0)] == some true := by quickRfl
example : stepK 8076030954443701744994070304101969600 200000000
    [(62377189136559460799159226272317440000, 1, 0)] == some true := by quickRfl
example : stepK 718766754945489455304472257065075294400 200000000
    [(5613947022290351471924330364508569600000, 1, 0)] == some true := by quickRfl
example : stepK 52573842877942565273243107104095419458814459401768000 200000000
    [(440841516948592182764054142045278420379874885632000000, 1, 0)] == some true := by quickRfl
example : stepK 6676878045498705789701874602220118271269436344024536000 200000000
    [(56427714169419799393798930181795637808623985360896000000, 1, 0)] == some true := by quickRfl
example : stepK 13353756090997411579403749204440236542538872688049072000 200000000
    [(113299741048835030278887615719353445993693828874240000000, 1, 0)] == some true := by quickRfl
example : stepK 1749342047920660916901891145781670987072592322134428432000 200000000
    [(14955565818446223996813165274954654871167585411399680000000, 1, 0)]
    == some true := by quickRfl
example : stepK 239659860565130545615559086972088925228945148132416695184000 200000000
    [(2063868082945578911560216807943742372221126786773155840000000, 1, 0)]
    == some true := by quickRfl
example : stepK 33312720618553145840562713089120360606823375590405920630576000 200000000
    [(288941531612381047618430353112123932110957750148241817600000000, 1, 0)]
    == some true := by quickRfl
example :
    stepK 41640927904370300154508936603455936348626591748630593262827592445686864000
      200000000
      [(374867757601140118512603512682984851689582369732924776330622402560000000000,
        1, 0)] == some true := by quickRfl

end Sage
