/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.IsHA.WCertsTactic

set_option maxRecDepth 100000

namespace Sage

/-- Lighter in-order slice (children 11-244, ~47% of subtree weight) of n=169's
root children; see `HACompose169a`. -/
gen_root_kids kids169b 169 10 244

set_option maxHeartbeats 1000000 in
theorem hcs_lcm_169b :
    WCerts 41640927904370300154508936603455936348626591748630593262827592445686864000 kids169b := by ha_lcm_compose 40000

end Sage
