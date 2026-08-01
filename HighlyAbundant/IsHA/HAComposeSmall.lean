/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.IsHA.WCertsTactic
import HighlyAbundant.IsHA.SageKernelBeq

open Nat

set_option maxRecDepth 100000

/-!
# Kernel certificates for `IsHighlyAbundant (lcmUpto n)`, prime powers `n ≤ 89`

Each theorem is a single `ha_lcm_compose` invocation. These cases together take a few minutes,
well under the build's critical path, so they share one module; the heavier `n ≥ 125` proofs
stay in their own files to keep CI module-parallelism.
-/

namespace Sage

theorem isHighlyAbundant_lcmUpto_2 : IsHighlyAbundant (lcmUpto 2) := by
  ha_lcm_compose 2 10000

theorem isHighlyAbundant_lcmUpto_3 : IsHighlyAbundant (lcmUpto 3) := by
  ha_lcm_compose 3 10000

theorem isHighlyAbundant_lcmUpto_4 : IsHighlyAbundant (lcmUpto 4) := by
  ha_lcm_compose 4 10000

theorem isHighlyAbundant_lcmUpto_5 : IsHighlyAbundant (lcmUpto 5) := by
  ha_lcm_compose 5 10000

theorem isHighlyAbundant_lcmUpto_7 : IsHighlyAbundant (lcmUpto 7) := by
  ha_lcm_compose 7 10000

theorem isHighlyAbundant_lcmUpto_8 : IsHighlyAbundant (lcmUpto 8) := by
  ha_lcm_compose 8 10000

theorem isHighlyAbundant_lcmUpto_9 : IsHighlyAbundant (lcmUpto 9) := by
  ha_lcm_compose 9 10000

theorem isHighlyAbundant_lcmUpto_11 : IsHighlyAbundant (lcmUpto 11) := by
  ha_lcm_compose 11 10000

theorem isHighlyAbundant_lcmUpto_13 : IsHighlyAbundant (lcmUpto 13) := by
  ha_lcm_compose 13 10000

theorem isHighlyAbundant_lcmUpto_16 : IsHighlyAbundant (lcmUpto 16) := by
  ha_lcm_compose 16 10000

theorem isHighlyAbundant_lcmUpto_17 : IsHighlyAbundant (lcmUpto 17) := by
  ha_lcm_compose 17 10000

theorem isHighlyAbundant_lcmUpto_19 : IsHighlyAbundant (lcmUpto 19) := by
  ha_lcm_compose 19 10000

theorem isHighlyAbundant_lcmUpto_23 : IsHighlyAbundant (lcmUpto 23) := by
  ha_lcm_compose 23 10000

theorem isHighlyAbundant_lcmUpto_25 : IsHighlyAbundant (lcmUpto 25) := by
  ha_lcm_compose 25 10000

theorem isHighlyAbundant_lcmUpto_27 : IsHighlyAbundant (lcmUpto 27) := by
  ha_lcm_compose 27 10000

theorem isHighlyAbundant_lcmUpto_29 : IsHighlyAbundant (lcmUpto 29) := by
  ha_lcm_compose 29 10000

theorem isHighlyAbundant_lcmUpto_31 : IsHighlyAbundant (lcmUpto 31) := by
  ha_lcm_compose 31 10000

theorem isHighlyAbundant_lcmUpto_32 : IsHighlyAbundant (lcmUpto 32) := by
  ha_lcm_compose 32 10000

theorem isHighlyAbundant_lcmUpto_37 : IsHighlyAbundant (lcmUpto 37) := by
  ha_lcm_compose 37 10000

theorem isHighlyAbundant_lcmUpto_41 : IsHighlyAbundant (lcmUpto 41) := by
  ha_lcm_compose 41 10000

theorem isHighlyAbundant_lcmUpto_43 : IsHighlyAbundant (lcmUpto 43) := by
  ha_lcm_compose 43 10000

theorem isHighlyAbundant_lcmUpto_47 : IsHighlyAbundant (lcmUpto 47) := by
  ha_lcm_compose 47 10000

theorem isHighlyAbundant_lcmUpto_49 : IsHighlyAbundant (lcmUpto 49) := by
  ha_lcm_compose 49 10000

theorem isHighlyAbundant_lcmUpto_53 : IsHighlyAbundant (lcmUpto 53) := by
  ha_lcm_compose 53 10000

theorem isHighlyAbundant_lcmUpto_59 : IsHighlyAbundant (lcmUpto 59) := by
  ha_lcm_compose 59 10000

theorem isHighlyAbundant_lcmUpto_61 : IsHighlyAbundant (lcmUpto 61) := by
  ha_lcm_compose 61 10000

theorem isHighlyAbundant_lcmUpto_64 : IsHighlyAbundant (lcmUpto 64) := by
  ha_lcm_compose 64 10000

theorem isHighlyAbundant_lcmUpto_67 : IsHighlyAbundant (lcmUpto 67) := by
  ha_lcm_compose 67 10000

theorem isHighlyAbundant_lcmUpto_81 : IsHighlyAbundant (lcmUpto 81) := by
  ha_lcm_compose 81 10000

theorem isHighlyAbundant_lcmUpto_83 : IsHighlyAbundant (lcmUpto 83) := by
  ha_lcm_compose 83 10000

theorem isHighlyAbundant_lcmUpto_89 : IsHighlyAbundant (lcmUpto 89) := by
  ha_lcm_compose 89 10000

end Sage
