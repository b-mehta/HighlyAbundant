/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.IsHA.WCertsTactic
import HighlyAbundant.IsHA.LcmRangeProofs
import HighlyAbundant.IsHA.SageKernelBeq

open Nat

/-!
# Kernel certificates for `IsHighlyAbundant (lcmUpto n)`, prime powers `n ≤ 64`

Each theorem is a single `ha_lcm_compose` invocation. These cases are cheap, so
they share one module; the heavier `n ≥ 67` proofs stay in their own files to
keep CI module-parallelism.
-/

namespace Sage

theorem isHighlyAbundant_lcmUpto_2 : IsHighlyAbundant (lcmUpto 2) := by
  ha_lcm_compose lcmUpto_2 sigma_lcmUpto_2 10000

theorem isHighlyAbundant_lcmUpto_3 : IsHighlyAbundant (lcmUpto 3) := by
  ha_lcm_compose lcmUpto_3 sigma_lcmUpto_3 10000

theorem isHighlyAbundant_lcmUpto_4 : IsHighlyAbundant (lcmUpto 4) := by
  ha_lcm_compose lcmUpto_4 sigma_lcmUpto_4 10000

theorem isHighlyAbundant_lcmUpto_5 : IsHighlyAbundant (lcmUpto 5) := by
  ha_lcm_compose lcmUpto_5 sigma_lcmUpto_5 10000

theorem isHighlyAbundant_lcmUpto_7 : IsHighlyAbundant (lcmUpto 7) := by
  ha_lcm_compose lcmUpto_7 sigma_lcmUpto_7 10000

theorem isHighlyAbundant_lcmUpto_8 : IsHighlyAbundant (lcmUpto 8) := by
  ha_lcm_compose lcmUpto_8 sigma_lcmUpto_8 10000

theorem isHighlyAbundant_lcmUpto_9 : IsHighlyAbundant (lcmUpto 9) := by
  ha_lcm_compose lcmUpto_9 sigma_lcmUpto_9 10000

theorem isHighlyAbundant_lcmUpto_11 : IsHighlyAbundant (lcmUpto 11) := by
  ha_lcm_compose lcmUpto_11 sigma_lcmUpto_11 10000

theorem isHighlyAbundant_lcmUpto_13 : IsHighlyAbundant (lcmUpto 13) := by
  ha_lcm_compose lcmUpto_13 sigma_lcmUpto_13 10000

theorem isHighlyAbundant_lcmUpto_16 : IsHighlyAbundant (lcmUpto 16) := by
  ha_lcm_compose lcmUpto_16 sigma_lcmUpto_16 10000

theorem isHighlyAbundant_lcmUpto_17 : IsHighlyAbundant (lcmUpto 17) := by
  ha_lcm_compose lcmUpto_17 sigma_lcmUpto_17 10000

theorem isHighlyAbundant_lcmUpto_19 : IsHighlyAbundant (lcmUpto 19) := by
  ha_lcm_compose lcmUpto_19 sigma_lcmUpto_19 10000

theorem isHighlyAbundant_lcmUpto_23 : IsHighlyAbundant (lcmUpto 23) := by
  ha_lcm_compose lcmUpto_23 sigma_lcmUpto_23 10000

theorem isHighlyAbundant_lcmUpto_25 : IsHighlyAbundant (lcmUpto 25) := by
  ha_lcm_compose lcmUpto_25 sigma_lcmUpto_25 10000

theorem isHighlyAbundant_lcmUpto_27 : IsHighlyAbundant (lcmUpto 27) := by
  ha_lcm_compose lcmUpto_27 sigma_lcmUpto_27 10000

theorem isHighlyAbundant_lcmUpto_29 : IsHighlyAbundant (lcmUpto 29) := by
  ha_lcm_compose lcmUpto_29 sigma_lcmUpto_29 10000

theorem isHighlyAbundant_lcmUpto_31 : IsHighlyAbundant (lcmUpto 31) := by
  ha_lcm_compose lcmUpto_31 sigma_lcmUpto_31 10000

theorem isHighlyAbundant_lcmUpto_32 : IsHighlyAbundant (lcmUpto 32) := by
  ha_lcm_compose lcmUpto_32 sigma_lcmUpto_32 10000

theorem isHighlyAbundant_lcmUpto_37 : IsHighlyAbundant (lcmUpto 37) := by
  ha_lcm_compose lcmUpto_37 sigma_lcmUpto_37 10000

theorem isHighlyAbundant_lcmUpto_41 : IsHighlyAbundant (lcmUpto 41) := by
  ha_lcm_compose lcmUpto_41 sigma_lcmUpto_41 10000

theorem isHighlyAbundant_lcmUpto_43 : IsHighlyAbundant (lcmUpto 43) := by
  ha_lcm_compose lcmUpto_43 sigma_lcmUpto_43 10000

theorem isHighlyAbundant_lcmUpto_47 : IsHighlyAbundant (lcmUpto 47) := by
  ha_lcm_compose lcmUpto_47 sigma_lcmUpto_47 10000

theorem isHighlyAbundant_lcmUpto_49 : IsHighlyAbundant (lcmUpto 49) := by
  ha_lcm_compose lcmUpto_49 sigma_lcmUpto_49 10000

theorem isHighlyAbundant_lcmUpto_53 : IsHighlyAbundant (lcmUpto 53) := by
  ha_lcm_compose lcmUpto_53 sigma_lcmUpto_53 10000

theorem isHighlyAbundant_lcmUpto_59 : IsHighlyAbundant (lcmUpto 59) := by
  ha_lcm_compose lcmUpto_59 sigma_lcmUpto_59 10000

theorem isHighlyAbundant_lcmUpto_61 : IsHighlyAbundant (lcmUpto 61) := by
  ha_lcm_compose lcmUpto_61 sigma_lcmUpto_61 10000

theorem isHighlyAbundant_lcmUpto_64 : IsHighlyAbundant (lcmUpto 64) := by
  ha_lcm_compose lcmUpto_64 sigma_lcmUpto_64 10000

end Sage
