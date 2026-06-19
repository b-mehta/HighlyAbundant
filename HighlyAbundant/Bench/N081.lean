import HighlyAbundant.SageKernel
import HighlyAbundant.Bench.QuickRfl

namespace Sage

theorem stepK_lcm_81 :
    stepK 97301577764381948734868316916891200 searchFuel
      [⟨742585584959041199989990788956160000, 1, 0⟩] == some true := by quickRfl

end Sage
