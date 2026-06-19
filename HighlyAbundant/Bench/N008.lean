import HighlyAbundant.SageKernel
import HighlyAbundant.Bench.QuickRfl

namespace Sage

theorem stepK_lcm_8 :
    stepK 840 searchFuel [⟨2880, 1, 0⟩] == some true := by quickRfl

end Sage
