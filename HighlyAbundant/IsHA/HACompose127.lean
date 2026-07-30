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
# Kernel certificate for `IsHighlyAbundant (lcmUpto 127)`

Proof that `lcmUpto 127` is highly abundant, closed by the `ha_lcm_compose` tactic.
-/

namespace Sage

theorem isHighlyAbundant_lcmUpto_127 : IsHighlyAbundant (lcmUpto 127) := by
  ha_lcm_compose 127 10000

end Sage
