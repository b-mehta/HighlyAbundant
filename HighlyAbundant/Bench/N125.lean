import HighlyAbundant.SageKernel
import HighlyAbundant.Bench.QuickRfl

namespace Sage

theorem stepK_lcm_125 :
    stepK 52573842877942565273243107104095419458814459401768000 searchFuel
      [⟨440841516948592182764054142045278420379874885632000000, 1, 0⟩] == some true := by
  quickRfl

end Sage
