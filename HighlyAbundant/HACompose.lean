/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.LcmRangeProofs
import HighlyAbundant.SageKernelChecks

/-!
# `IsHighlyAbundant (lcmRange n)` for each `n` targeted by `SageKernelChecks*`

For each `n`, we combine the kernel certificate `stepK_lcm_n` with the
literal-value equalities `lcmRange_n` and `sigma_lcmRange_n` and the
correctness theorem `highlyAbundantLcm_correct` to derive
`IsHighlyAbundant (lcmRange n)`.

Scratch for now: just `n = 64` to validate the proof shape.
-/

namespace Sage

/-- `(stepK == some true) = true` ↔ `stepK = some true`. -/
private lemma stepK_eq_of_beq {B fuel : ℕ} {stack : List (ℕ × ℕ × ℕ)}
    (h : (stepK B fuel stack == some true) = true) :
    stepK B fuel stack = some true := by
  cases hs : stepK B fuel stack with
  | none => simp [hs] at h
  | some b =>
    cases b
    · simp [hs] at h
    · rfl

theorem isHighlyAbundant_lcmRange_64 : IsHighlyAbundant (lcmRange 64) := by
  apply highlyAbundantLcm_correct (n := 64)
  rw [highlyAbundantLcm?, lcmRange_64, sigma_lcmRange_64]
  simp only [show ¬ (1182266884102822267511361600 ≤ 1 : Prop) from by norm_num, if_false]
  rw [← stepK_eq_step]
  exact stepK_eq_of_beq stepK_lcm_64

end Sage
