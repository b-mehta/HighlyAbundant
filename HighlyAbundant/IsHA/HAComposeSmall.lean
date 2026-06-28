/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.IsHA.WCertsTactic
import HighlyAbundant.IsHA.LcmRangeProofs
import HighlyAbundant.IsHA.SageKernelBeq

/-!
# Kernel certificates for `IsHighlyAbundant (lcmRange n)`, prime powers `n ≤ 64`

Each theorem is a single `ha_lcm_compose` invocation. These cases are cheap, so
they share one module; the heavier `n ≥ 67` proofs stay in their own files to
keep CI module-parallelism.
-/

namespace Sage

theorem isHighlyAbundant_lcmRange_2 : IsHighlyAbundant (lcmRange 2) := by
  ha_lcm_compose lcmRange_2 sigma_lcmRange_2 10000

theorem isHighlyAbundant_lcmRange_3 : IsHighlyAbundant (lcmRange 3) := by
  ha_lcm_compose lcmRange_3 sigma_lcmRange_3 10000

theorem isHighlyAbundant_lcmRange_4 : IsHighlyAbundant (lcmRange 4) := by
  ha_lcm_compose lcmRange_4 sigma_lcmRange_4 10000

theorem isHighlyAbundant_lcmRange_5 : IsHighlyAbundant (lcmRange 5) := by
  ha_lcm_compose lcmRange_5 sigma_lcmRange_5 10000

theorem isHighlyAbundant_lcmRange_7 : IsHighlyAbundant (lcmRange 7) := by
  ha_lcm_compose lcmRange_7 sigma_lcmRange_7 10000

theorem isHighlyAbundant_lcmRange_8 : IsHighlyAbundant (lcmRange 8) := by
  ha_lcm_compose lcmRange_8 sigma_lcmRange_8 10000

theorem isHighlyAbundant_lcmRange_9 : IsHighlyAbundant (lcmRange 9) := by
  ha_lcm_compose lcmRange_9 sigma_lcmRange_9 10000

theorem isHighlyAbundant_lcmRange_11 : IsHighlyAbundant (lcmRange 11) := by
  ha_lcm_compose lcmRange_11 sigma_lcmRange_11 10000

theorem isHighlyAbundant_lcmRange_13 : IsHighlyAbundant (lcmRange 13) := by
  ha_lcm_compose lcmRange_13 sigma_lcmRange_13 10000

theorem isHighlyAbundant_lcmRange_16 : IsHighlyAbundant (lcmRange 16) := by
  ha_lcm_compose lcmRange_16 sigma_lcmRange_16 10000

theorem isHighlyAbundant_lcmRange_17 : IsHighlyAbundant (lcmRange 17) := by
  ha_lcm_compose lcmRange_17 sigma_lcmRange_17 10000

theorem isHighlyAbundant_lcmRange_19 : IsHighlyAbundant (lcmRange 19) := by
  ha_lcm_compose lcmRange_19 sigma_lcmRange_19 10000

theorem isHighlyAbundant_lcmRange_23 : IsHighlyAbundant (lcmRange 23) := by
  ha_lcm_compose lcmRange_23 sigma_lcmRange_23 10000

theorem isHighlyAbundant_lcmRange_25 : IsHighlyAbundant (lcmRange 25) := by
  ha_lcm_compose lcmRange_25 sigma_lcmRange_25 10000

theorem isHighlyAbundant_lcmRange_27 : IsHighlyAbundant (lcmRange 27) := by
  ha_lcm_compose lcmRange_27 sigma_lcmRange_27 10000

theorem isHighlyAbundant_lcmRange_29 : IsHighlyAbundant (lcmRange 29) := by
  ha_lcm_compose lcmRange_29 sigma_lcmRange_29 10000

theorem isHighlyAbundant_lcmRange_31 : IsHighlyAbundant (lcmRange 31) := by
  ha_lcm_compose lcmRange_31 sigma_lcmRange_31 10000

theorem isHighlyAbundant_lcmRange_32 : IsHighlyAbundant (lcmRange 32) := by
  ha_lcm_compose lcmRange_32 sigma_lcmRange_32 10000

theorem isHighlyAbundant_lcmRange_37 : IsHighlyAbundant (lcmRange 37) := by
  ha_lcm_compose lcmRange_37 sigma_lcmRange_37 10000

theorem isHighlyAbundant_lcmRange_41 : IsHighlyAbundant (lcmRange 41) := by
  ha_lcm_compose lcmRange_41 sigma_lcmRange_41 10000

theorem isHighlyAbundant_lcmRange_43 : IsHighlyAbundant (lcmRange 43) := by
  ha_lcm_compose lcmRange_43 sigma_lcmRange_43 10000

theorem isHighlyAbundant_lcmRange_47 : IsHighlyAbundant (lcmRange 47) := by
  ha_lcm_compose lcmRange_47 sigma_lcmRange_47 10000

theorem isHighlyAbundant_lcmRange_49 : IsHighlyAbundant (lcmRange 49) := by
  ha_lcm_compose lcmRange_49 sigma_lcmRange_49 10000

theorem isHighlyAbundant_lcmRange_53 : IsHighlyAbundant (lcmRange 53) := by
  ha_lcm_compose lcmRange_53 sigma_lcmRange_53 10000

theorem isHighlyAbundant_lcmRange_59 : IsHighlyAbundant (lcmRange 59) := by
  ha_lcm_compose lcmRange_59 sigma_lcmRange_59 10000

theorem isHighlyAbundant_lcmRange_61 : IsHighlyAbundant (lcmRange 61) := by
  ha_lcm_compose lcmRange_61 sigma_lcmRange_61 10000

theorem isHighlyAbundant_lcmRange_64 : IsHighlyAbundant (lcmRange 64) := by
  ha_lcm_compose lcmRange_64 sigma_lcmRange_64 10000

end Sage
