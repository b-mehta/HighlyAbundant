/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.IsHA.WCertsTactic

open Nat

set_option maxRecDepth 100000

/-!
# Kernel certificate for `IsHighlyAbundant (lcmUpto 139)`

Proof that `lcmUpto 139` is highly abundant, closed by the `ha_lcm_compose` tactic.
-/

namespace Sage

theorem isHighlyAbundant_lcmUpto_139 : IsHighlyAbundant (lcmUpto 139) := by
  ha_lcm_compose 139 40000

end Sage
