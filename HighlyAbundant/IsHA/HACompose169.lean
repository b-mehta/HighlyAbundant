/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.IsHA.WCertsTactic
import HighlyAbundant.IsHA.LcmRangeProofs
import HighlyAbundant.IsHA.SageKernelBeq
import HighlyAbundant.IsHA.HACompose169a
import HighlyAbundant.IsHA.HACompose169b

/-!
# Partial-form kernel certificate for `IsHighlyAbundant (lcmRange 169)`

The root-level partial form (one big `stepK` per child of the root) does NOT
fit in CI's 7 GB — empirically the heaviest root-children have subtree sizes
of 200k–870k nodes. We use `w_certs_auto 10000`: any node whose subtree exceeds
10000 nodes is expanded one level via `childrenK`, recursing until every leaf
cert fits the budget. The children are split across `HACompose169a`/`169b` so
the kernel work runs as two parallel modules.
-/

namespace Sage

private def kids169 : List SageNode := kids169a ++ kids169b

private theorem hcs_lcm_169 :
    WCerts 41640927904370300154508936603455936348626591748630593262827592445686864000 kids169 :=
  w_certs_append hcs_lcm_169a hcs_lcm_169b

private theorem childrenK_lcm_169 :
    (childrenK 41640927904370300154508936603455936348626591748630593262827592445686864000
      374867757601140118512603512682984851689582369732924776330622402560000000000 1 0).elim false
        (fun cs ↦ sageListBeq cs kids169) = true := by
  quickRfl

/-- `lcm (1..169)` is highly abundant, proven via the W-based partial-verification
path. The `w_certs_auto 10000` heuristic decides per node whether to give the
kernel a direct subtree search or to split via `childrenK`. -/
theorem isHighlyAbundant_lcmRange_169 : IsHighlyAbundant (lcmRange 169) := by
  apply highlyAbundantLcm_correct_partialK_W (cs := kids169)
  · rw [sigma_lcmRange_169]; norm_num
  · rw [sigma_lcmRange_169, lcmRange_169]; exact childrenK_eq_of_beq childrenK_lcm_169
  · rw [lcmRange_169]; exact hcs_lcm_169

end Sage
