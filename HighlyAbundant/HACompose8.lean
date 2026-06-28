/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.WCertsTactic
import HighlyAbundant.LcmRangeProofs
import HighlyAbundant.SageKernelBeq

/-!
# Kernel certificate for `IsHighlyAbundant (lcmRange 8)`

Proved via `ha_lcm_compose`, which expands the root of the Sage search into its
children, discharges each child's witness set with `w_certs_auto`, and combines
them through `highlyAbundantLcm_correct_partialK_W`.
-/

namespace Sage

theorem isHighlyAbundant_lcmRange_8 : IsHighlyAbundant (lcmRange 8) := by
  ha_lcm_compose lcmRange_8 sigma_lcmRange_8 10000

end Sage
