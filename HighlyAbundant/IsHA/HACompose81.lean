/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.IsHA.WCertsTactic
import HighlyAbundant.IsHA.LcmRangeProofs
import HighlyAbundant.IsHA.SageKernelBeq

/-!
# Kernel certificate for `IsHighlyAbundant (lcmRange 81)`

Proof that `lcmRange 81` is highly abundant, closed by the `ha_lcm_compose` tactic.
-/

namespace Sage

theorem isHighlyAbundant_lcmRange_81 : IsHighlyAbundant (lcmRange 81) := by
  ha_lcm_compose lcmRange_81 sigma_lcmRange_81 10000

end Sage
