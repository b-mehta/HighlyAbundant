/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.SageKernel
import Lean.Elab.Tactic.Basic

/-!
# Kernel certificates: `stepK == some true` for the large `n` cases

Companion to `HighlyAbundant.SageKernelChecks`, holding the large-`n`
entries `(n ≥ 125)` so the smaller cases do not have to share a single
kernel evaluation with them.

For each `n ∈ {125, 127, 128, 131, 137, 139, 169}`, this file proves
`stepK (lcm(1..n)) fuel [(σ₁ (lcm(1..n)), 1, 0)] == some true` by kernel
reduction. The split exists purely to keep peak memory bounded; the
statements and proofs follow the same pattern as `SageKernelChecks`.
-/

namespace Sage

elab "quickRfl" : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic fun g ↦ g.assign Lean.reflBoolTrue

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
