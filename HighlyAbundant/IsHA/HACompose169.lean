/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

public import HighlyAbundant.IsHA.WCertsTactic

open Nat

set_option maxRecDepth 100000
set_option Elab.async false

/-!
# Kernel certificate for `IsHighlyAbundant (lcmUpto 169)`

Empirically the heaviest root-children have subtree sizes of 200k to 870k nodes. We use
`ha_lcm_compose 40000`: any node whose subtree exceeds 40000 nodes is expanded one level via
`childrenK`, recursing until every leaf cert fits the budget.
-/

namespace Sage

set_option maxHeartbeats 51200000 in
public theorem isHighlyAbundant_lcmUpto_169 : IsHighlyAbundant (lcmUpto 169) := by
  ha_lcm_compose 169 40000

end Sage
