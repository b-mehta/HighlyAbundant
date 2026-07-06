/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.IsHA.WCertsTactic
import HighlyAbundant.IsHA.LcmRangeProofs
import HighlyAbundant.IsHA.SageKernelBeq

open Nat

/-!
# Kernel certificate for `IsHighlyAbundant (lcmUpto 83)`

Proof that `lcmUpto 83` is highly abundant, closed by the `ha_lcm_compose` tactic.
-/

namespace Sage

theorem isHighlyAbundant_lcmUpto_83 : IsHighlyAbundant (lcmUpto 83) := by
  ha_lcm_compose lcmUpto_83 sigma_lcmUpto_83 10000

end Sage
