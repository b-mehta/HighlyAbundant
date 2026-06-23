/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.SageKernelEquiv
import Mathlib.NumberTheory.Chebyshev

/-!
# Literal values of `lcmRange n` and `σ₁ (lcmRange n)`

For each `n` proved highly abundant in the `HACompose<n>` files, this file pins
`lcmRange n` and `σ₁ (lcmRange n)` to their literal natural numbers.

`lcmRange n = <literal>` reduces cleanly in the kernel via `decide +kernel`.
For `σ₁ (lcmRange n) = <literal>`, evaluating `σ₁` directly is infeasible
(a divisor enumeration over a 70-digit number), so we rewrite through
`Nat.lcmUpto_eq_prod_pow_log` plus σ₁ multiplicativity to turn the goal
into a product of per-prime closed forms `(p^(k+1) - 1)/(p - 1)`, which
reduces in the kernel.
-/

open Nat ArithmeticFunction

namespace Sage

/-- `List` form of `lcmRange n`: kernel reduces over `List.foldr Nat.lcm 1`. -/
def lcmRangeList (n : ℕ) : ℕ := ((List.range' 1 n).map id).foldr Nat.lcm 1

/-- Primes `≤ n` as a `List`: kernel reduces over `List.filter`. -/
def primesLEList (n : ℕ) : List ℕ := (List.range (n + 1)).filter Nat.Prime

/-- `List` form of `σ₁ (lcmRange n)` via the prime-power factorization. -/
def sigmaLcmRangeList (n : ℕ) : ℕ :=
  ((primesLEList n).map (fun p ↦ (p ^ (p.log n + 1) - 1) / (p - 1))).foldr (· * ·) 1

lemma lcmRange_eq_lcmRangeList (n : ℕ) : lcmRange n = lcmRangeList n := by
  rw [lcmRange, lcmRangeList, Finset.lcm, Finset.fold, Nat.Icc_eq_range']
  change ((List.range' 1 (n + 1 - 1)).map id).foldr GCDMonoid.lcm 1 = _
  simp only [Nat.add_sub_cancel]
  induction List.range' 1 n with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, List.foldr_cons, List.foldr_cons, ih, lcm_eq_nat_lcm]

lemma primesLEList_nodup (n : ℕ) : (primesLEList n).Nodup :=
  List.nodup_range.filter _

lemma primesLEList_toFinset (n : ℕ) : (primesLEList n).toFinset = Nat.primesLE n := by
  ext p
  simp [primesLEList, Nat.primesLE, Nat.primesBelow]

/-- σ₁ on `Nat.lcmUpto n` expanded via the prime-power factorization. -/
private lemma sigma_lcmUpto_eq (n : ℕ) :
    σ₁ (Nat.lcmUpto n) = sigmaLcmRangeList n := by
  have hcop : ∀ p ∈ Nat.primesLE n, ∀ q ∈ Nat.primesLE n, p ≠ q →
      (p^(p.log n)).Coprime (q^(q.log n)) := fun p hp q hq hpq ↦
    (Nat.Coprime.pow_left _ ((Nat.coprime_primes
      (prime_of_mem_primesLE hp) (prime_of_mem_primesLE hq)).mpr hpq)).pow_right _
  rw [Nat.lcmUpto_eq_prod_pow_log, isMultiplicative_sigma.map_prod _ _ hcop,
    Finset.prod_congr rfl
      (fun p hp ↦ sigma_one_apply_prime_pow' (prime_of_mem_primesLE hp)),
    ← primesLEList_toFinset, List.prod_toFinset _ (primesLEList_nodup _)]
  rfl

/-- Boilerplate for closing `lcmRange n = <literal>`. -/
private lemma lcmRange_aux (n : ℕ) {L : ℕ} (h : lcmRangeList n = L) : lcmRange n = L := by
  rw [lcmRange_eq_lcmRangeList]; exact h

/-- Boilerplate for closing `σ₁ (lcmRange n) = <literal>`. -/
private lemma sigma_lcmRange_aux (n : ℕ) {sL : ℕ}
    (h : sigmaLcmRangeList n = sL) :
    σ₁ (lcmRange n) = sL := by
  have : lcmRange n = Nat.lcmUpto n := rfl
  rw [this, sigma_lcmUpto_eq]; exact h

/-! ### Prime powers below `64` -/

theorem lcmRange_2 : lcmRange 2 = 2 := lcmRange_aux 2 (by decide +kernel +revert)
theorem sigma_lcmRange_2 : σ₁ (lcmRange 2) = 3 :=
  sigma_lcmRange_aux 2 (by decide +kernel +revert)
theorem lcmRange_3 : lcmRange 3 = 6 := lcmRange_aux 3 (by decide +kernel +revert)
theorem sigma_lcmRange_3 : σ₁ (lcmRange 3) = 12 :=
  sigma_lcmRange_aux 3 (by decide +kernel +revert)
theorem lcmRange_4 : lcmRange 4 = 12 := lcmRange_aux 4 (by decide +kernel +revert)
theorem sigma_lcmRange_4 : σ₁ (lcmRange 4) = 28 :=
  sigma_lcmRange_aux 4 (by decide +kernel +revert)
theorem lcmRange_5 : lcmRange 5 = 60 := lcmRange_aux 5 (by decide +kernel +revert)
theorem sigma_lcmRange_5 : σ₁ (lcmRange 5) = 168 :=
  sigma_lcmRange_aux 5 (by decide +kernel +revert)
theorem lcmRange_7 : lcmRange 7 = 420 := lcmRange_aux 7 (by decide +kernel +revert)
theorem sigma_lcmRange_7 : σ₁ (lcmRange 7) = 1344 :=
  sigma_lcmRange_aux 7 (by decide +kernel +revert)
theorem lcmRange_8 : lcmRange 8 = 840 := lcmRange_aux 8 (by decide +kernel +revert)
theorem sigma_lcmRange_8 : σ₁ (lcmRange 8) = 2880 :=
  sigma_lcmRange_aux 8 (by decide +kernel +revert)
theorem lcmRange_9 : lcmRange 9 = 2520 := lcmRange_aux 9 (by decide +kernel +revert)
theorem sigma_lcmRange_9 : σ₁ (lcmRange 9) = 9360 :=
  sigma_lcmRange_aux 9 (by decide +kernel +revert)
theorem lcmRange_11 : lcmRange 11 = 27720 := lcmRange_aux 11 (by decide +kernel +revert)
theorem sigma_lcmRange_11 : σ₁ (lcmRange 11) = 112320 :=
  sigma_lcmRange_aux 11 (by decide +kernel +revert)
theorem lcmRange_13 : lcmRange 13 = 360360 := lcmRange_aux 13 (by decide +kernel +revert)
theorem sigma_lcmRange_13 : σ₁ (lcmRange 13) = 1572480 :=
  sigma_lcmRange_aux 13 (by decide +kernel +revert)
theorem lcmRange_16 : lcmRange 16 = 720720 := lcmRange_aux 16 (by decide +kernel +revert)
theorem sigma_lcmRange_16 : σ₁ (lcmRange 16) = 3249792 :=
  sigma_lcmRange_aux 16 (by decide +kernel +revert)
theorem lcmRange_17 : lcmRange 17 = 12252240 := lcmRange_aux 17 (by decide +kernel +revert)
theorem sigma_lcmRange_17 : σ₁ (lcmRange 17) = 58496256 :=
  sigma_lcmRange_aux 17 (by decide +kernel +revert)
theorem lcmRange_19 : lcmRange 19 = 232792560 := lcmRange_aux 19 (by decide +kernel +revert)
theorem sigma_lcmRange_19 : σ₁ (lcmRange 19) = 1169925120 :=
  sigma_lcmRange_aux 19 (by decide +kernel +revert)
theorem lcmRange_23 : lcmRange 23 = 5354228880 := lcmRange_aux 23 (by decide +kernel +revert)
theorem sigma_lcmRange_23 : σ₁ (lcmRange 23) = 28078202880 :=
  sigma_lcmRange_aux 23 (by decide +kernel +revert)
theorem lcmRange_25 : lcmRange 25 = 26771144400 := lcmRange_aux 25 (by decide +kernel +revert)
theorem sigma_lcmRange_25 : σ₁ (lcmRange 25) = 145070714880 :=
  sigma_lcmRange_aux 25 (by decide +kernel +revert)
theorem lcmRange_27 : lcmRange 27 = 80313433200 := lcmRange_aux 27 (by decide +kernel +revert)
theorem sigma_lcmRange_27 : σ₁ (lcmRange 27) = 446371430400 :=
  sigma_lcmRange_aux 27 (by decide +kernel +revert)
theorem lcmRange_29 : lcmRange 29 = 2329089562800 := lcmRange_aux 29 (by decide +kernel +revert)
theorem sigma_lcmRange_29 : σ₁ (lcmRange 29) = 13391142912000 :=
  sigma_lcmRange_aux 29 (by decide +kernel +revert)
theorem lcmRange_31 : lcmRange 31 = 72201776446800 := lcmRange_aux 31 (by decide +kernel +revert)
theorem sigma_lcmRange_31 : σ₁ (lcmRange 31) = 428516573184000 :=
  sigma_lcmRange_aux 31 (by decide +kernel +revert)
theorem lcmRange_32 : lcmRange 32 = 144403552893600 := lcmRange_aux 32 (by decide +kernel +revert)
theorem sigma_lcmRange_32 : σ₁ (lcmRange 32) = 870856261632000 :=
  sigma_lcmRange_aux 32 (by decide +kernel +revert)
theorem lcmRange_37 : lcmRange 37 = 5342931457063200 := lcmRange_aux 37 (by decide +kernel +revert)
theorem sigma_lcmRange_37 : σ₁ (lcmRange 37) = 33092537942016000 :=
  sigma_lcmRange_aux 37 (by decide +kernel +revert)
theorem lcmRange_41 : lcmRange 41 = 219060189739591200 :=
  lcmRange_aux 41 (by decide +kernel +revert)
theorem sigma_lcmRange_41 : σ₁ (lcmRange 41) = 1389886593564672000 :=
  sigma_lcmRange_aux 41 (by decide +kernel +revert)
theorem lcmRange_43 : lcmRange 43 = 9419588158802421600 :=
  lcmRange_aux 43 (by decide +kernel +revert)
theorem sigma_lcmRange_43 : σ₁ (lcmRange 43) = 61155010116845568000 :=
  sigma_lcmRange_aux 43 (by decide +kernel +revert)
theorem lcmRange_47 : lcmRange 47 = 442720643463713815200 :=
  lcmRange_aux 47 (by decide +kernel +revert)
theorem sigma_lcmRange_47 : σ₁ (lcmRange 47) = 2935440485608587264000 :=
  sigma_lcmRange_aux 47 (by decide +kernel +revert)
theorem lcmRange_49 : lcmRange 49 = 3099044504245996706400 :=
  lcmRange_aux 49 (by decide +kernel +revert)
theorem sigma_lcmRange_49 : σ₁ (lcmRange 49) = 20915013459961184256000 :=
  sigma_lcmRange_aux 49 (by decide +kernel +revert)
theorem lcmRange_53 : lcmRange 53 = 164249358725037825439200 :=
  lcmRange_aux 53 (by decide +kernel +revert)
theorem sigma_lcmRange_53 :
    σ₁ (lcmRange 53) = 1129410726837903949824000 :=
  sigma_lcmRange_aux 53 (by decide +kernel +revert)
theorem lcmRange_59 : lcmRange 59 = 9690712164777231700912800 :=
  lcmRange_aux 59 (by decide +kernel +revert)
theorem sigma_lcmRange_59 :
    σ₁ (lcmRange 59) = 67764643610274236989440000 :=
  sigma_lcmRange_aux 59 (by decide +kernel +revert)
theorem lcmRange_61 : lcmRange 61 = 591133442051411133755680800 :=
  lcmRange_aux 61 (by decide +kernel +revert)
theorem sigma_lcmRange_61 :
    σ₁ (lcmRange 61) = 4201407903837002693345280000 :=
  sigma_lcmRange_aux 61 (by decide +kernel +revert)

/-! ### Explicit values at and above `64` -/

theorem lcmRange_64 : lcmRange 64 = 1182266884102822267511361600 :=
  lcmRange_aux 64 (by decide +kernel +revert)
theorem sigma_lcmRange_64 :
    σ₁ (lcmRange 64) = 8469504822020624477061120000 :=
  sigma_lcmRange_aux 64 (by decide +kernel +revert)
theorem lcmRange_67 : lcmRange 67 = 79211881234889091923261227200 :=
  lcmRange_aux 67 (by decide +kernel +revert)
theorem sigma_lcmRange_67 :
    σ₁ (lcmRange 67) = 575926327897402464440156160000 :=
  sigma_lcmRange_aux 67 (by decide +kernel +revert)
theorem lcmRange_81 :
    lcmRange 81 = 97301577764381948734868316916891200 := lcmRange_aux 81 (by decide +kernel +revert)
theorem sigma_lcmRange_81 :
    σ₁ (lcmRange 81) = 742585584959041199989990788956160000 :=
  sigma_lcmRange_aux 81 (by decide +kernel +revert)
theorem lcmRange_83 :
    lcmRange 83 = 8076030954443701744994070304101969600 :=
  lcmRange_aux 83 (by decide +kernel +revert)
theorem sigma_lcmRange_83 :
    σ₁ (lcmRange 83) = 62377189136559460799159226272317440000 :=
  sigma_lcmRange_aux 83 (by decide +kernel +revert)
theorem lcmRange_89 :
    lcmRange 89 = 718766754945489455304472257065075294400 :=
  lcmRange_aux 89 (by decide +kernel +revert)
theorem sigma_lcmRange_89 :
    σ₁ (lcmRange 89) = 5613947022290351471924330364508569600000 :=
  sigma_lcmRange_aux 89 (by decide +kernel +revert)
theorem lcmRange_125 :
    lcmRange 125 = 52573842877942565273243107104095419458814459401768000 :=
  lcmRange_aux 125 (by decide +kernel +revert)
theorem sigma_lcmRange_125 :
    σ₁ (lcmRange 125) = 440841516948592182764054142045278420379874885632000000 :=
  sigma_lcmRange_aux 125 (by decide +kernel +revert)
theorem lcmRange_127 :
    lcmRange 127 = 6676878045498705789701874602220118271269436344024536000 :=
  lcmRange_aux 127 (by decide +kernel +revert)
theorem sigma_lcmRange_127 :
    σ₁ (lcmRange 127) = 56427714169419799393798930181795637808623985360896000000 :=
  sigma_lcmRange_aux 127 (by decide +kernel +revert)
theorem lcmRange_128 :
    lcmRange 128 = 13353756090997411579403749204440236542538872688049072000 :=
  lcmRange_aux 128 (by decide +kernel +revert)
theorem sigma_lcmRange_128 :
    σ₁ (lcmRange 128) = 113299741048835030278887615719353445993693828874240000000 :=
  sigma_lcmRange_aux 128 (by decide +kernel +revert)
theorem lcmRange_131 :
    lcmRange 131 = 1749342047920660916901891145781670987072592322134428432000 :=
  lcmRange_aux 131 (by decide +kernel +revert)
theorem sigma_lcmRange_131 :
    σ₁ (lcmRange 131) = 14955565818446223996813165274954654871167585411399680000000 :=
  sigma_lcmRange_aux 131 (by decide +kernel +revert)
theorem lcmRange_137 :
    lcmRange 137 = 239659860565130545615559086972088925228945148132416695184000 :=
  lcmRange_aux 137 (by decide +kernel +revert)
theorem sigma_lcmRange_137 :
    σ₁ (lcmRange 137) = 2063868082945578911560216807943742372221126786773155840000000 :=
  sigma_lcmRange_aux 137 (by decide +kernel +revert)
theorem lcmRange_139 :
    lcmRange 139 = 33312720618553145840562713089120360606823375590405920630576000 :=
  lcmRange_aux 139 (by decide +kernel +revert)
theorem sigma_lcmRange_139 :
    σ₁ (lcmRange 139) = 288941531612381047618430353112123932110957750148241817600000000 :=
  sigma_lcmRange_aux 139 (by decide +kernel +revert)
theorem lcmRange_169 :
    lcmRange 169 =
      41640927904370300154508936603455936348626591748630593262827592445686864000 :=
  lcmRange_aux 169 (by decide +kernel +revert)
theorem sigma_lcmRange_169 :
    σ₁ (lcmRange 169) =
      374867757601140118512603512682984851689582369732924776330622402560000000000 :=
  sigma_lcmRange_aux 169 (by decide +kernel +revert)

end Sage
