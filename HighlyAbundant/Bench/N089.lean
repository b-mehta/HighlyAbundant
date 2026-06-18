import HighlyAbundant.SageKernel
import HighlyAbundant.Bench.QuickRfl

namespace Sage

theorem stepK_lcm_89 :
    stepK 718766754945489455304472257065075294400 searchFuel
      [(5613947022290351471924330364508569600000, 1, 0)] == some true := by quickRfl

end Sage
