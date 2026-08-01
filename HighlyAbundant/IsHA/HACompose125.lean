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
# Kernel certificates for `IsHighlyAbundant (lcmUpto n)`, `n = 125` and `n = 128`

Each theorem is a single `ha_lcm_compose` invocation. Together they stay under the build's
critical path, so they share one module.
-/

namespace Sage

theorem isHighlyAbundant_lcmUpto_125 : IsHighlyAbundant (lcmUpto 125) := by
  ha_lcm_compose 125 10000

theorem isHighlyAbundant_lcmUpto_128 : IsHighlyAbundant (lcmUpto 128) := by
  ha_lcm_compose 128 10000

end Sage
