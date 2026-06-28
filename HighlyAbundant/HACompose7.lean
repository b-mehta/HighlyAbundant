/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.WCertsTactic
import HighlyAbundant.LcmRangeProofs
import HighlyAbundant.SageKernelBeq

/-!
# Kernel certificate for `IsHighlyAbundant (lcmRange 7)`

Proved via `ha_lcm_compose`, which expands the root of the Sage search into its
children, discharges each child's witness set with `w_certs_auto`, and combines
them through `highlyAbundantLcm_correct_partialK_W`.
-/

namespace Sage

theorem isHighlyAbundant_lcmRange_7 : IsHighlyAbundant (lcmRange 7) := by
  ha_lcm_compose lcmRange_7 sigma_lcmRange_7 10000

end Sage
