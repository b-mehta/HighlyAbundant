import HighlyAbundant.IsHA.WCertsTactic
import HighlyAbundant.IsHA.SageKernelBeq

open Nat

set_option maxRecDepth 100000

namespace Sage

theorem benchN83 : IsHighlyAbundant (lcmUpto 83) := by
  ha_lcm_compose 83 40000

end Sage
