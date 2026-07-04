/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.IsHA.SageKernelEquiv
import HighlyAbundant.IsHA.SageKernelBeq
import HighlyAbundant.IsHA.SigmaFactor

/-!
# Literal values of `lcmRange n` and `σ₁ (lcmRange n)`

For each `n` proved highly abundant in the `HACompose<n>` files, this file pins
`lcmRange n` and `σ₁ (lcmRange n)` to their literal natural numbers.

`lcmRange n = <literal>` reduces in the kernel via a `Nat.beq` check discharged
by `quickRfl` (`Lean.reflBoolTrue`), avoiding the `DecidableEq` wrapper of `decide`.
`σ₁ (lcmRange n) = <literal>` is closed by the `sigma_lcm` tactic: the elaborator
supplies the prime factorization of `lcmRange n`, and the kernel only verifies the
product `∏ p^k`, the σ closed form `∏ (p^(k+1)-1)/(p-1)`, and primality by trial
division. See `HighlyAbundant.IsHA.SigmaFactor`.
-/

open Nat ArithmeticFunction

namespace Sage

/-- `List` form of `lcmRange n`: kernel reduces over `List.foldr Nat.lcm 1`. -/
def lcmRangeList (n : ℕ) : ℕ := ((List.range' 1 n).map id).foldr Nat.lcm 1

lemma lcmRange_eq_lcmRangeList (n : ℕ) : lcmRange n = lcmRangeList n := by
  rw [lcmRange, lcmRangeList, Finset.lcm, Finset.fold, Nat.Icc_eq_range']
  change ((List.range' 1 (n + 1 - 1)).map id).foldr GCDMonoid.lcm 1 = _
  simp only [Nat.add_sub_cancel]
  induction List.range' 1 n with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, List.foldr_cons, List.foldr_cons, ih, lcm_eq_nat_lcm]

/-- Boilerplate for closing `lcmRange n = <literal>`. -/
private lemma lcmRange_aux (n : ℕ) {L : ℕ} (h : (lcmRangeList n).beq L = true) :
    lcmRange n = L := by
  rw [lcmRange_eq_lcmRangeList]; exact Nat.eq_of_beq_eq_true h

/-! ### Prime powers below `64` -/

theorem lcmRange_2 : lcmRange 2 = 2 := lcmRange_aux 2 (by quickRfl)
theorem sigma_lcmRange_2 : σ₁ (lcmRange 2) = 3 := by sigma_lcm lcmRange_2
theorem lcmRange_3 : lcmRange 3 = 6 := lcmRange_aux 3 (by quickRfl)
theorem sigma_lcmRange_3 : σ₁ (lcmRange 3) = 12 := by sigma_lcm lcmRange_3
theorem lcmRange_4 : lcmRange 4 = 12 := lcmRange_aux 4 (by quickRfl)
theorem sigma_lcmRange_4 : σ₁ (lcmRange 4) = 28 := by sigma_lcm lcmRange_4
theorem lcmRange_5 : lcmRange 5 = 60 := lcmRange_aux 5 (by quickRfl)
theorem sigma_lcmRange_5 : σ₁ (lcmRange 5) = 168 := by sigma_lcm lcmRange_5
theorem lcmRange_7 : lcmRange 7 = 420 := lcmRange_aux 7 (by quickRfl)
theorem sigma_lcmRange_7 : σ₁ (lcmRange 7) = 1344 := by sigma_lcm lcmRange_7
theorem lcmRange_8 : lcmRange 8 = 840 := lcmRange_aux 8 (by quickRfl)
theorem sigma_lcmRange_8 : σ₁ (lcmRange 8) = 2880 := by sigma_lcm lcmRange_8
theorem lcmRange_9 : lcmRange 9 = 2520 := lcmRange_aux 9 (by quickRfl)
theorem sigma_lcmRange_9 : σ₁ (lcmRange 9) = 9360 := by sigma_lcm lcmRange_9
theorem lcmRange_11 : lcmRange 11 = 27720 := lcmRange_aux 11 (by quickRfl)
theorem sigma_lcmRange_11 : σ₁ (lcmRange 11) = 112320 := by sigma_lcm lcmRange_11
theorem lcmRange_13 : lcmRange 13 = 360360 := lcmRange_aux 13 (by quickRfl)
theorem sigma_lcmRange_13 : σ₁ (lcmRange 13) = 1572480 := by sigma_lcm lcmRange_13
theorem lcmRange_16 : lcmRange 16 = 720720 := lcmRange_aux 16 (by quickRfl)
theorem sigma_lcmRange_16 : σ₁ (lcmRange 16) = 3249792 := by sigma_lcm lcmRange_16
theorem lcmRange_17 : lcmRange 17 = 12252240 := lcmRange_aux 17 (by quickRfl)
theorem sigma_lcmRange_17 : σ₁ (lcmRange 17) = 58496256 := by sigma_lcm lcmRange_17
theorem lcmRange_19 : lcmRange 19 = 232792560 := lcmRange_aux 19 (by quickRfl)
theorem sigma_lcmRange_19 : σ₁ (lcmRange 19) = 1169925120 := by sigma_lcm lcmRange_19
theorem lcmRange_23 : lcmRange 23 = 5354228880 := lcmRange_aux 23 (by quickRfl)
theorem sigma_lcmRange_23 : σ₁ (lcmRange 23) = 28078202880 := by sigma_lcm lcmRange_23
theorem lcmRange_25 : lcmRange 25 = 26771144400 := lcmRange_aux 25 (by quickRfl)
theorem sigma_lcmRange_25 : σ₁ (lcmRange 25) = 145070714880 := by sigma_lcm lcmRange_25
theorem lcmRange_27 : lcmRange 27 = 80313433200 := lcmRange_aux 27 (by quickRfl)
theorem sigma_lcmRange_27 : σ₁ (lcmRange 27) = 446371430400 := by sigma_lcm lcmRange_27
theorem lcmRange_29 : lcmRange 29 = 2329089562800 := lcmRange_aux 29 (by quickRfl)
theorem sigma_lcmRange_29 : σ₁ (lcmRange 29) = 13391142912000 := by sigma_lcm lcmRange_29
theorem lcmRange_31 : lcmRange 31 = 72201776446800 := lcmRange_aux 31 (by quickRfl)
theorem sigma_lcmRange_31 : σ₁ (lcmRange 31) = 428516573184000 := by sigma_lcm lcmRange_31
theorem lcmRange_32 : lcmRange 32 = 144403552893600 := lcmRange_aux 32 (by quickRfl)
theorem sigma_lcmRange_32 : σ₁ (lcmRange 32) = 870856261632000 := by sigma_lcm lcmRange_32
theorem lcmRange_37 : lcmRange 37 = 5342931457063200 := lcmRange_aux 37 (by quickRfl)
theorem sigma_lcmRange_37 : σ₁ (lcmRange 37) = 33092537942016000 := by sigma_lcm lcmRange_37
theorem lcmRange_41 : lcmRange 41 = 219060189739591200 :=
  lcmRange_aux 41 (by quickRfl)
theorem sigma_lcmRange_41 : σ₁ (lcmRange 41) = 1389886593564672000 := by sigma_lcm lcmRange_41
theorem lcmRange_43 : lcmRange 43 = 9419588158802421600 :=
  lcmRange_aux 43 (by quickRfl)
theorem sigma_lcmRange_43 : σ₁ (lcmRange 43) = 61155010116845568000 := by sigma_lcm lcmRange_43
theorem lcmRange_47 : lcmRange 47 = 442720643463713815200 :=
  lcmRange_aux 47 (by quickRfl)
theorem sigma_lcmRange_47 : σ₁ (lcmRange 47) = 2935440485608587264000 := by sigma_lcm lcmRange_47
theorem lcmRange_49 : lcmRange 49 = 3099044504245996706400 :=
  lcmRange_aux 49 (by quickRfl)
theorem sigma_lcmRange_49 : σ₁ (lcmRange 49) = 20915013459961184256000 := by sigma_lcm lcmRange_49
theorem lcmRange_53 : lcmRange 53 = 164249358725037825439200 :=
  lcmRange_aux 53 (by quickRfl)
theorem sigma_lcmRange_53 :
    σ₁ (lcmRange 53) = 1129410726837903949824000 := by sigma_lcm lcmRange_53
theorem lcmRange_59 : lcmRange 59 = 9690712164777231700912800 :=
  lcmRange_aux 59 (by quickRfl)
theorem sigma_lcmRange_59 :
    σ₁ (lcmRange 59) = 67764643610274236989440000 := by sigma_lcm lcmRange_59
theorem lcmRange_61 : lcmRange 61 = 591133442051411133755680800 :=
  lcmRange_aux 61 (by quickRfl)
theorem sigma_lcmRange_61 :
    σ₁ (lcmRange 61) = 4201407903837002693345280000 := by sigma_lcm lcmRange_61

/-! ### Explicit values at and above `64` -/

theorem lcmRange_64 : lcmRange 64 = 1182266884102822267511361600 :=
  lcmRange_aux 64 (by quickRfl)
theorem sigma_lcmRange_64 :
    σ₁ (lcmRange 64) = 8469504822020624477061120000 := by sigma_lcm lcmRange_64
theorem lcmRange_67 : lcmRange 67 = 79211881234889091923261227200 :=
  lcmRange_aux 67 (by quickRfl)
theorem sigma_lcmRange_67 :
    σ₁ (lcmRange 67) = 575926327897402464440156160000 := by sigma_lcm lcmRange_67
theorem lcmRange_81 :
    lcmRange 81 = 97301577764381948734868316916891200 := lcmRange_aux 81 (by quickRfl)
theorem sigma_lcmRange_81 :
    σ₁ (lcmRange 81) = 742585584959041199989990788956160000 := by sigma_lcm lcmRange_81
theorem lcmRange_83 :
    lcmRange 83 = 8076030954443701744994070304101969600 :=
  lcmRange_aux 83 (by quickRfl)
theorem sigma_lcmRange_83 :
    σ₁ (lcmRange 83) = 62377189136559460799159226272317440000 := by sigma_lcm lcmRange_83
theorem lcmRange_89 :
    lcmRange 89 = 718766754945489455304472257065075294400 :=
  lcmRange_aux 89 (by quickRfl)
theorem sigma_lcmRange_89 :
    σ₁ (lcmRange 89) = 5613947022290351471924330364508569600000 := by sigma_lcm lcmRange_89
theorem lcmRange_125 :
    lcmRange 125 = 52573842877942565273243107104095419458814459401768000 :=
  lcmRange_aux 125 (by quickRfl)
theorem sigma_lcmRange_125 :
    σ₁ (lcmRange 125) = 440841516948592182764054142045278420379874885632000000 := by sigma_lcm lcmRange_125
theorem lcmRange_127 :
    lcmRange 127 = 6676878045498705789701874602220118271269436344024536000 :=
  lcmRange_aux 127 (by quickRfl)
theorem sigma_lcmRange_127 :
    σ₁ (lcmRange 127) = 56427714169419799393798930181795637808623985360896000000 := by sigma_lcm lcmRange_127
theorem lcmRange_128 :
    lcmRange 128 = 13353756090997411579403749204440236542538872688049072000 :=
  lcmRange_aux 128 (by quickRfl)
theorem sigma_lcmRange_128 :
    σ₁ (lcmRange 128) = 113299741048835030278887615719353445993693828874240000000 := by sigma_lcm lcmRange_128
theorem lcmRange_131 :
    lcmRange 131 = 1749342047920660916901891145781670987072592322134428432000 :=
  lcmRange_aux 131 (by quickRfl)
theorem sigma_lcmRange_131 :
    σ₁ (lcmRange 131) = 14955565818446223996813165274954654871167585411399680000000 := by sigma_lcm lcmRange_131
theorem lcmRange_137 :
    lcmRange 137 = 239659860565130545615559086972088925228945148132416695184000 :=
  lcmRange_aux 137 (by quickRfl)
theorem sigma_lcmRange_137 :
    σ₁ (lcmRange 137) = 2063868082945578911560216807943742372221126786773155840000000 := by sigma_lcm lcmRange_137
theorem lcmRange_139 :
    lcmRange 139 = 33312720618553145840562713089120360606823375590405920630576000 :=
  lcmRange_aux 139 (by quickRfl)
theorem sigma_lcmRange_139 :
    σ₁ (lcmRange 139) = 288941531612381047618430353112123932110957750148241817600000000 := by sigma_lcm lcmRange_139
theorem lcmRange_169 :
    lcmRange 169 =
      41640927904370300154508936603455936348626591748630593262827592445686864000 :=
  lcmRange_aux 169 (by quickRfl)
theorem sigma_lcmRange_169 :
    σ₁ (lcmRange 169) =
      374867757601140118512603512682984851689582369732924776330622402560000000000 := by sigma_lcm lcmRange_169

end Sage
