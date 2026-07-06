/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.IsHA.SageKernelEquiv
import HighlyAbundant.IsHA.SageKernelBeq
import HighlyAbundant.IsHA.SigmaFactor

/-!
# Literal values of `lcmUpto n` and `σ₁ (lcmUpto n)`

For each `n` proved highly abundant in the `HACompose<n>` files, this file pins
`lcmUpto n` and `σ₁ (lcmUpto n)` to their literal natural numbers.

`lcmUpto n = <literal>` reduces in the kernel via a `Nat.beq` check discharged
by `quickRfl` (`Lean.reflBoolTrue`), avoiding the `DecidableEq` wrapper of `decide`.
`σ₁ (lcmUpto n) = <literal>` is closed by the `sigma_lcm` tactic: the elaborator
supplies the prime factorization of `lcmUpto n`, and the kernel only verifies the
product `∏ p^k`, the σ closed form `∏ (p^(k+1)-1)/(p-1)`, and primality by trial
division. See `HighlyAbundant.IsHA.SigmaFactor`.
-/

open Nat ArithmeticFunction

namespace Sage

/-- Fold form of `lcmUpto n`, computing the lcm over `List.foldr Nat.lcm 1`; the
kernel reduces this cheaply. -/
def lcmUptoFoldr (n : ℕ) : ℕ := (List.range' 1 n).foldr Nat.lcm 1

lemma lcmUpto_eq_lcmUptoFoldr (n : ℕ) : lcmUpto n = lcmUptoFoldr n := by
  rw [Nat.lcmUpto, lcmUptoFoldr, Finset.lcm, Finset.fold, Nat.Icc_eq_range']
  change ((List.range' 1 (n + 1 - 1)).map id).foldr GCDMonoid.lcm 1 = _
  simp only [Nat.add_sub_cancel, List.map_id]
  induction List.range' 1 n with
  | nil => rfl
  | cons a l ih => rw [List.foldr_cons, List.foldr_cons, ih, lcm_eq_nat_lcm]

/-- Boilerplate for closing `lcmUpto n = <literal>`. -/
private lemma lcmUpto_aux (n : ℕ) {L : ℕ} (h : (lcmUptoFoldr n).beq L = true) :
    lcmUpto n = L := by
  rw [lcmUpto_eq_lcmUptoFoldr]; exact Nat.eq_of_beq_eq_true h

/-! ### Prime powers below `64` -/

theorem lcmUpto_2 : lcmUpto 2 = 2 := lcmUpto_aux 2 (by quickRfl)
theorem sigma_lcmUpto_2 : σ₁ (lcmUpto 2) = 3 := by sigma_lcm lcmUpto_2
theorem lcmUpto_3 : lcmUpto 3 = 6 := lcmUpto_aux 3 (by quickRfl)
theorem sigma_lcmUpto_3 : σ₁ (lcmUpto 3) = 12 := by sigma_lcm lcmUpto_3
theorem lcmUpto_4 : lcmUpto 4 = 12 := lcmUpto_aux 4 (by quickRfl)
theorem sigma_lcmUpto_4 : σ₁ (lcmUpto 4) = 28 := by sigma_lcm lcmUpto_4
theorem lcmUpto_5 : lcmUpto 5 = 60 := lcmUpto_aux 5 (by quickRfl)
theorem sigma_lcmUpto_5 : σ₁ (lcmUpto 5) = 168 := by sigma_lcm lcmUpto_5
theorem lcmUpto_7 : lcmUpto 7 = 420 := lcmUpto_aux 7 (by quickRfl)
theorem sigma_lcmUpto_7 : σ₁ (lcmUpto 7) = 1344 := by sigma_lcm lcmUpto_7
theorem lcmUpto_8 : lcmUpto 8 = 840 := lcmUpto_aux 8 (by quickRfl)
theorem sigma_lcmUpto_8 : σ₁ (lcmUpto 8) = 2880 := by sigma_lcm lcmUpto_8
theorem lcmUpto_9 : lcmUpto 9 = 2520 := lcmUpto_aux 9 (by quickRfl)
theorem sigma_lcmUpto_9 : σ₁ (lcmUpto 9) = 9360 := by sigma_lcm lcmUpto_9
theorem lcmUpto_11 : lcmUpto 11 = 27720 := lcmUpto_aux 11 (by quickRfl)
theorem sigma_lcmUpto_11 : σ₁ (lcmUpto 11) = 112320 := by sigma_lcm lcmUpto_11
theorem lcmUpto_13 : lcmUpto 13 = 360360 := lcmUpto_aux 13 (by quickRfl)
theorem sigma_lcmUpto_13 : σ₁ (lcmUpto 13) = 1572480 := by sigma_lcm lcmUpto_13
theorem lcmUpto_16 : lcmUpto 16 = 720720 := lcmUpto_aux 16 (by quickRfl)
theorem sigma_lcmUpto_16 : σ₁ (lcmUpto 16) = 3249792 := by sigma_lcm lcmUpto_16
theorem lcmUpto_17 : lcmUpto 17 = 12252240 := lcmUpto_aux 17 (by quickRfl)
theorem sigma_lcmUpto_17 : σ₁ (lcmUpto 17) = 58496256 := by sigma_lcm lcmUpto_17
theorem lcmUpto_19 : lcmUpto 19 = 232792560 := lcmUpto_aux 19 (by quickRfl)
theorem sigma_lcmUpto_19 : σ₁ (lcmUpto 19) = 1169925120 := by sigma_lcm lcmUpto_19
theorem lcmUpto_23 : lcmUpto 23 = 5354228880 := lcmUpto_aux 23 (by quickRfl)
theorem sigma_lcmUpto_23 : σ₁ (lcmUpto 23) = 28078202880 := by sigma_lcm lcmUpto_23
theorem lcmUpto_25 : lcmUpto 25 = 26771144400 := lcmUpto_aux 25 (by quickRfl)
theorem sigma_lcmUpto_25 : σ₁ (lcmUpto 25) = 145070714880 := by sigma_lcm lcmUpto_25
theorem lcmUpto_27 : lcmUpto 27 = 80313433200 := lcmUpto_aux 27 (by quickRfl)
theorem sigma_lcmUpto_27 : σ₁ (lcmUpto 27) = 446371430400 := by sigma_lcm lcmUpto_27
theorem lcmUpto_29 : lcmUpto 29 = 2329089562800 := lcmUpto_aux 29 (by quickRfl)
theorem sigma_lcmUpto_29 : σ₁ (lcmUpto 29) = 13391142912000 := by sigma_lcm lcmUpto_29
theorem lcmUpto_31 : lcmUpto 31 = 72201776446800 := lcmUpto_aux 31 (by quickRfl)
theorem sigma_lcmUpto_31 : σ₁ (lcmUpto 31) = 428516573184000 := by sigma_lcm lcmUpto_31
theorem lcmUpto_32 : lcmUpto 32 = 144403552893600 := lcmUpto_aux 32 (by quickRfl)
theorem sigma_lcmUpto_32 : σ₁ (lcmUpto 32) = 870856261632000 := by sigma_lcm lcmUpto_32
theorem lcmUpto_37 : lcmUpto 37 = 5342931457063200 := lcmUpto_aux 37 (by quickRfl)
theorem sigma_lcmUpto_37 : σ₁ (lcmUpto 37) = 33092537942016000 := by sigma_lcm lcmUpto_37
theorem lcmUpto_41 : lcmUpto 41 = 219060189739591200 :=
  lcmUpto_aux 41 (by quickRfl)
theorem sigma_lcmUpto_41 : σ₁ (lcmUpto 41) = 1389886593564672000 := by sigma_lcm lcmUpto_41
theorem lcmUpto_43 : lcmUpto 43 = 9419588158802421600 :=
  lcmUpto_aux 43 (by quickRfl)
theorem sigma_lcmUpto_43 : σ₁ (lcmUpto 43) = 61155010116845568000 := by sigma_lcm lcmUpto_43
theorem lcmUpto_47 : lcmUpto 47 = 442720643463713815200 :=
  lcmUpto_aux 47 (by quickRfl)
theorem sigma_lcmUpto_47 : σ₁ (lcmUpto 47) = 2935440485608587264000 := by sigma_lcm lcmUpto_47
theorem lcmUpto_49 : lcmUpto 49 = 3099044504245996706400 :=
  lcmUpto_aux 49 (by quickRfl)
theorem sigma_lcmUpto_49 : σ₁ (lcmUpto 49) = 20915013459961184256000 := by sigma_lcm lcmUpto_49
theorem lcmUpto_53 : lcmUpto 53 = 164249358725037825439200 :=
  lcmUpto_aux 53 (by quickRfl)
theorem sigma_lcmUpto_53 :
    σ₁ (lcmUpto 53) = 1129410726837903949824000 := by sigma_lcm lcmUpto_53
theorem lcmUpto_59 : lcmUpto 59 = 9690712164777231700912800 :=
  lcmUpto_aux 59 (by quickRfl)
theorem sigma_lcmUpto_59 :
    σ₁ (lcmUpto 59) = 67764643610274236989440000 := by sigma_lcm lcmUpto_59
theorem lcmUpto_61 : lcmUpto 61 = 591133442051411133755680800 :=
  lcmUpto_aux 61 (by quickRfl)
theorem sigma_lcmUpto_61 :
    σ₁ (lcmUpto 61) = 4201407903837002693345280000 := by sigma_lcm lcmUpto_61

/-! ### Explicit values at and above `64` -/

theorem lcmUpto_64 : lcmUpto 64 = 1182266884102822267511361600 :=
  lcmUpto_aux 64 (by quickRfl)
theorem sigma_lcmUpto_64 :
    σ₁ (lcmUpto 64) = 8469504822020624477061120000 := by sigma_lcm lcmUpto_64
theorem lcmUpto_67 : lcmUpto 67 = 79211881234889091923261227200 :=
  lcmUpto_aux 67 (by quickRfl)
theorem sigma_lcmUpto_67 :
    σ₁ (lcmUpto 67) = 575926327897402464440156160000 := by sigma_lcm lcmUpto_67
theorem lcmUpto_81 :
    lcmUpto 81 = 97301577764381948734868316916891200 := lcmUpto_aux 81 (by quickRfl)
theorem sigma_lcmUpto_81 :
    σ₁ (lcmUpto 81) = 742585584959041199989990788956160000 := by sigma_lcm lcmUpto_81
theorem lcmUpto_83 :
    lcmUpto 83 = 8076030954443701744994070304101969600 :=
  lcmUpto_aux 83 (by quickRfl)
theorem sigma_lcmUpto_83 :
    σ₁ (lcmUpto 83) = 62377189136559460799159226272317440000 := by sigma_lcm lcmUpto_83
theorem lcmUpto_89 :
    lcmUpto 89 = 718766754945489455304472257065075294400 :=
  lcmUpto_aux 89 (by quickRfl)
theorem sigma_lcmUpto_89 :
    σ₁ (lcmUpto 89) = 5613947022290351471924330364508569600000 := by sigma_lcm lcmUpto_89
theorem lcmUpto_125 :
    lcmUpto 125 = 52573842877942565273243107104095419458814459401768000 :=
  lcmUpto_aux 125 (by quickRfl)
theorem sigma_lcmUpto_125 :
    σ₁ (lcmUpto 125) = 440841516948592182764054142045278420379874885632000000 := by sigma_lcm lcmUpto_125
theorem lcmUpto_127 :
    lcmUpto 127 = 6676878045498705789701874602220118271269436344024536000 :=
  lcmUpto_aux 127 (by quickRfl)
theorem sigma_lcmUpto_127 :
    σ₁ (lcmUpto 127) = 56427714169419799393798930181795637808623985360896000000 := by sigma_lcm lcmUpto_127
theorem lcmUpto_128 :
    lcmUpto 128 = 13353756090997411579403749204440236542538872688049072000 :=
  lcmUpto_aux 128 (by quickRfl)
theorem sigma_lcmUpto_128 :
    σ₁ (lcmUpto 128) = 113299741048835030278887615719353445993693828874240000000 := by sigma_lcm lcmUpto_128
theorem lcmUpto_131 :
    lcmUpto 131 = 1749342047920660916901891145781670987072592322134428432000 :=
  lcmUpto_aux 131 (by quickRfl)
theorem sigma_lcmUpto_131 :
    σ₁ (lcmUpto 131) = 14955565818446223996813165274954654871167585411399680000000 := by sigma_lcm lcmUpto_131
theorem lcmUpto_137 :
    lcmUpto 137 = 239659860565130545615559086972088925228945148132416695184000 :=
  lcmUpto_aux 137 (by quickRfl)
theorem sigma_lcmUpto_137 :
    σ₁ (lcmUpto 137) = 2063868082945578911560216807943742372221126786773155840000000 := by sigma_lcm lcmUpto_137
theorem lcmUpto_139 :
    lcmUpto 139 = 33312720618553145840562713089120360606823375590405920630576000 :=
  lcmUpto_aux 139 (by quickRfl)
theorem sigma_lcmUpto_139 :
    σ₁ (lcmUpto 139) = 288941531612381047618430353112123932110957750148241817600000000 := by sigma_lcm lcmUpto_139
theorem lcmUpto_169 :
    lcmUpto 169 =
      41640927904370300154508936603455936348626591748630593262827592445686864000 :=
  lcmUpto_aux 169 (by quickRfl)
theorem sigma_lcmUpto_169 :
    σ₁ (lcmUpto 169) =
      374867757601140118512603512682984851689582369732924776330622402560000000000 := by sigma_lcm lcmUpto_169

end Sage
