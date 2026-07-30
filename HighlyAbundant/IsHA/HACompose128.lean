/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.IsHA.WCertsTactic
import HighlyAbundant.IsHA.SageKernelBeq

open Nat

set_option maxRecDepth 100000

/-!
# Kernel certificate for `IsHighlyAbundant (lcmUpto 128)`

Proof that `lcmUpto 128` is highly abundant, closed by the `ha_lcm_compose` tactic.
-/

namespace Sage

theorem isHighlyAbundant_lcmUpto_128 : IsHighlyAbundant (lcmUpto 128) := by
  ha_lcm_compose 128 10000

end Sage
