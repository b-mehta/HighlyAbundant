/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.IsHA.WCertsTactic

set_option maxRecDepth 100000

namespace Sage

/-- Heaviest in-order slice (children 1-10, ~53% of subtree weight) of n=169's
root children; the rest are in `HACompose169b`. Split so the two halves' `WCerts`
proofs build in parallel; n=169 is the heaviest module. -/
gen_root_kids kids169a 169 0 10

set_option maxHeartbeats 1000000 in
theorem hcs_lcm_169a :
    WCerts 41640927904370300154508936603455936348626591748630593262827592445686864000 kids169a := by ha_lcm_compose 10000

end Sage
