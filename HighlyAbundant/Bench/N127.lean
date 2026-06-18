import HighlyAbundant.SageKernel
import HighlyAbundant.Bench.QuickRfl

namespace Sage

theorem stepK_lcm_127 :
    stepK 6676878045498705789701874602220118271269436344024536000 searchFuel
      [(56427714169419799393798930181795637808623985360896000000, 1, 0)] == some true := by
  quickRfl

end Sage
