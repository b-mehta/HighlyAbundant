import HighlyAbundant.SageKernel
import HighlyAbundant.Bench.QuickRfl

namespace Sage

theorem stepK_lcm_64 :
    stepK 1182266884102822267511361600 searchFuel
      [(8469504822020624477061120000, 1, 0)] == some true := by quickRfl

end Sage
