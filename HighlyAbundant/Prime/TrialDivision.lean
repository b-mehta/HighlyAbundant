/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

public section

/-!
# A cheap kernel-reducible primality test for small numbers

`passes` is a trial-division fold, and `Nat.prime_of_passes` certifies that if `n < 23² = 529`
survives trial division by the primes below `23`, then `n` is prime. This gives a fast primality
certificate for the small label primes used by the rank certificates.

## Main statements

* `Nat.primes_below_23`: the primes below `23` are exactly `[2,3,5,7,11,13,17,19]`.
* `Nat.prime_of_passes`: if `2 ≤ n < 529` and `passes n [2,3,5,7,11,13,17,19] = true`, then
  `Nat.Prime n`.
-/

/-- Trial division as a `Bool`-valued fold: `passes x L = true` iff no `i ∈ L` with `i < x`
divides `x`. -/
@[expose] noncomputable def passes (x : ℕ) : List ℕ → Bool :=
  List.rec true (fun i _ r ↦ ((Nat.ble 1 (x.mod i)).or' (x.ble i)).and' r)

@[simp] private theorem passes_nil (x : ℕ) : passes x [] = true := rfl

private theorem passes_cons (x a : ℕ) (t : List ℕ) :
    passes x (a :: t) = ((Nat.ble 1 (x % a)).or' (Nat.ble x a)).and' (passes x t) := rfl

/-- `passes x L = true` exactly when every `i ∈ L` fails to be a proper divisor of `x`: either
`x % i ≠ 0` or `x ≤ i`. -/
private theorem passes_true_iff {x : ℕ} {L : List ℕ} :
    passes x L = true ↔ ∀ i ∈ L, x % i ≠ 0 ∨ x ≤ i := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [passes_cons]
    simp only [Bool.and'_eq_and, Bool.or'_eq_or, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq]
    grind

/-- The primes below `23` are exactly `[2, 3, 5, 7, 11, 13, 17, 19]`. -/
theorem Nat.primes_below_23 (p : ℕ) (hlt : p < 23) (hp : p.Prime) :
    p ∈ [2, 3, 5, 7, 11, 13, 17, 19] := by
  decide +revert +kernel

/-- If every prime below `k` lies in `L`, `2 ≤ n < k²`, and `n` survives trial division by `L`, then
`n` is prime: a proper factor of `n` would have a prime factor below `k`, hence in `L`. -/
theorem Nat.prime_of_passes_lt_sq {n k : ℕ} {L : List ℕ} (hL : ∀ p < k, p.Prime → p ∈ L)
    (h2 : 2 ≤ n) (hk : n < k ^ 2) (hpass : passes n L) : Nat.Prime n := by
  by_contra hnp
  set p := n.minFac with hp
  have hpp : p.Prime := Nat.minFac_prime (by omega)
  have hsq : p ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  have hpltk : p < k := lt_of_pow_lt_pow_left' 2 (by grind)
  have hpmem : p ∈ L := hL p hpltk hpp
  have hpltn : p < n := by nlinarith [hpp.two_le, hsq]
  rcases (passes_true_iff.mp hpass) p hpmem with hmod | hle
  · exact hmod (Nat.dvd_iff_mod_eq_zero.mp (Nat.minFac_dvd n))
  · omega

/-- If `2 ≤ n < 529 = 23²` and `n` survives trial division by the primes below `23`, then `n` is
prime. The `k = 23` case of `Nat.prime_of_passes_lt_sq`. -/
theorem Nat.prime_of_passes (n : ℕ) (h2 : 2 ≤ n) (h529 : n < 529)
    (hpass : passes n [2, 3, 5, 7, 11, 13, 17, 19]) : Nat.Prime n :=
  Nat.prime_of_passes_lt_sq Nat.primes_below_23 h2 (h529.trans_le (by norm_num)) hpass

/-- Kernel `Bool`: `p` is a prime below `529 = 23²`, certified by trial division by the primes below
`23` (`passes`). -/
@[expose] noncomputable def checkPrime (p : ℕ) : Bool :=
  (Nat.ble 2 p).and' ((Nat.ble p 528).and' (passes p [2, 3, 5, 7, 11, 13, 17, 19]))

theorem checkPrime_true {p : ℕ} (h : checkPrime p) : p.Prime := by
  simp only [checkPrime, Bool.and'_eq_and, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨h2, hle, hpass⟩ := h
  exact Nat.prime_of_passes p h2 (by omega) hpass
