/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

public import HighlyAbundant.IsHA.WCertsTactic
public import Mathlib.NumberTheory.Chebyshev

open Nat ArithmeticFunction Lean Elab Tactic Meta

/-! Two ways to pin `σ₁ (lcmUpto n)` to a literal, for measurement: the kernel filtering primes and
taking logarithms itself, against the elaborator supplying the factorisation. -/

namespace Sage

/-- Primes at most `n`, decided in the kernel. -/
@[expose] public noncomputable def primesLEList (n : ℕ) : List ℕ := (List.range (n + 1)).filter Nat.Prime

/-- The divisor sum of `lcmUpto n` as a product over `primesLEList n`. -/
@[expose] public noncomputable def sigmaLcmRangeList (n : ℕ) : ℕ :=
  ((primesLEList n).map fun p ↦ (p ^ (p.log n + 1) - 1) / (p - 1)).foldr (· * ·) 1

public theorem primesLEList_nodup (n : ℕ) : (primesLEList n).Nodup := List.nodup_range.filter _

public theorem primesLEList_toFinset (n : ℕ) : (primesLEList n).toFinset = Nat.primesLE n := by
  ext p
  simp [primesLEList, Nat.primesLE, Nat.primesBelow]

public theorem sigma_lcmUpto_eq (n : ℕ) : σ₁ (lcmUpto n) = sigmaLcmRangeList n := by
  have hcop : ∀ p ∈ Nat.primesLE n, ∀ q ∈ Nat.primesLE n, p ≠ q →
      (p ^ p.log n).Coprime (q ^ q.log n) := fun p hp q hq hpq ↦
    (Nat.Coprime.pow_left _ ((Nat.coprime_primes
      (prime_of_mem_primesLE hp) (prime_of_mem_primesLE hq)).mpr hpq)).pow_right _
  rw [Nat.lcmUpto_eq_prod_pow_log, isMultiplicative_sigma.map_prod _ _ hcop,
    Finset.prod_congr rfl
      (fun p hp ↦ sigma_one_apply_prime_pow' (prime_of_mem_primesLE hp)),
    ← primesLEList_toFinset, List.prod_toFinset _ (primesLEList_nodup _)]
  rfl

/-- Close `σ₁ (lcmUpto n) = sL` by kernel evaluation of the list form. -/
public theorem sigma_of_beq (n : ℕ) {sL : ℕ} (h : (sigmaLcmRangeList n).beq sL) :
    σ₁ (lcmUpto n) = sL := by
  rw [sigma_lcmUpto_eq]; exact Nat.eq_of_beq_eq_true h

/-- Force the kernel-filtering route for a literal `n`. -/
elab "sigma_route_kernel" nStx:num : tactic => do
  let n := nStx.getNat
  let nE := mkNatLit n
  let g := (Sage.lcmUptoValues n).2
  let gE := mkNatLit g
  let app := mkApp2 (mkConst ``Nat.beq) (mkApp (mkConst ``Sage.sigmaLcmRangeList) nE) gE
  let ty := mkApp3 (mkConst ``Eq [.succ .zero]) (mkConst ``Bool) app (mkConst ``Bool.true)
  let _ ← mkAuxLemma [] ty Lean.reflBoolTrue
  liftMetaTactic fun goal => do goal.assign (mkConst ``trivial); pure []

/-- Force the elaborator-supplied-factorisation route for a literal `n`. -/
elab "sigma_route_factor" nStx:num : tactic => do
  let _ ← Sage.proveLcmUptoValues nStx.getNat
  liftMetaTactic fun goal => do goal.assign (mkConst ``trivial); pure []

end Sage

example : True := by sigma_route_kernel 89
