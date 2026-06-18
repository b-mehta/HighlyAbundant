import HighlyAbundant.SageKernelStruct
import HighlyAbundant.Bench.QuickRfl

namespace Sage

theorem stepK_S_lcm_64 :
    stepK_S 1182266884102822267511361600 searchFuel
      [⟨8469504822020624477061120000, 1, 0⟩] == some true := by quickRfl

end Sage
