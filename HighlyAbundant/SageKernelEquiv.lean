/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.SageKernel

/-!
# Equivalence of kernel-friendly and ordinary decider functions

For each kernel-friendly definition in `HighlyAbundant.SageKernel`, prove it
agrees with the corresponding definition in `HighlyAbundant.Sage`.
-/

namespace Sage

theorem ceilDivK_eq_ceilDiv : ceilDivK = ceilDiv := rfl

private theorem extendK_succ (n m2 front back lhs rhs : Nat) :
    extendK (n + 1) m2 front back lhs rhs =
      if front ≤ back then
        if lhs ≥ rhs then .window back lhs rhs
        else if back + 1 < 49 then
          let q := primesRArray.get (back + 1)
          let lhs' := lhs * q
          if lhs' > m2 then .tooLarge else extendK n m2 front (back + 1) lhs' (rhs * (q - 1))
        else .exhaustedTable
      else
        if front < 49 then
          let q := primesRArray.get front
          let lhs' := lhs * q
          if lhs' > m2 then .tooLarge else extendK n m2 front front lhs' (rhs * (q - 1))
        else .exhaustedTable := by
  simp only [extendK, Bool.rec_eq, Nat.ble_eq, Nat.blt_eq, Nat.lt_succ_iff,
    Nat.succ_le_succ_iff]
  rfl

theorem extendK_eq_extend : extendK = extend := by
  funext fuel m2 front back lhs rhs
  induction fuel generalizing back lhs rhs with
  | zero => rfl
  | succ n ih =>
    rw [extend, extendK_succ]
    simp only [ih]

end Sage
