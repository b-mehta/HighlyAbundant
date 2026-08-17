/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

public import HighlyAbundant.Basic
public import HighlyAbundant.Prime.TrialDivision

public section

/-!
# The divisor sum of a factorisation

A factorisation is a list of pairs `(p, k)`, read as the product of `p ^ k`. For distinct primes
`p`, the divisor sum of that product is the product of `(p ^ (k + 1) - 1) / (p - 1)`, which is
`sigma_of_factorization`. Each function here is written with `List.rec`, so the kernel evaluates it
on a literal list.
-/

open Nat ArithmeticFunction

namespace Sage

/-! ### Reading a factorisation -/

/-- The product `∏ p ^ k` over a factorisation. -/
@[expose] def prodFactor : List (ℕ × ℕ) → ℕ :=
  List.rec (nat_lit 1) fun pk _ r ↦ (pk.1.pow pk.2).mul r

/-- The product `∏ (p ^ (k + 1) - 1) / (p - 1)` over a factorisation. -/
@[expose] def sigmaFactor : List (ℕ × ℕ) → ℕ :=
  List.rec (nat_lit 1) fun pk _ r ↦
    (((pk.1.pow pk.2.succ).sub (nat_lit 1)).div (pk.1.sub (nat_lit 1))).mul r

/-- The primes of a factorisation. -/
@[expose] def primesFactor : List (ℕ × ℕ) → List ℕ :=
  List.rec [] fun pk _ r ↦ pk.1 :: r

/-- Every prime of a factorisation passes the trial-division check. -/
@[expose] noncomputable def allCheckPrime : List (ℕ × ℕ) → Bool :=
  List.rec true fun pk _ r ↦ (checkPrime pk.1).and' r

@[grind =] theorem prodFactor_cons (pk : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    prodFactor (pk :: t) = pk.1 ^ pk.2 * prodFactor t := rfl

@[grind =] theorem sigmaFactor_cons (pk : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    sigmaFactor (pk :: t) = (pk.1 ^ (pk.2 + 1) - 1) / (pk.1 - 1) * sigmaFactor t := rfl

@[grind =] theorem primesFactor_cons (pk : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    primesFactor (pk :: t) = pk.1 :: primesFactor t := rfl

@[grind =] theorem allCheckPrime_cons (pk : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    allCheckPrime (pk :: t) = (checkPrime pk.1).and' (allCheckPrime t) := rfl

/-- The product of a factorisation, as a product over the mapped list. -/
theorem prodFactor_eq (F : List (ℕ × ℕ)) : prodFactor F = (F.map fun pk ↦ pk.1 ^ pk.2).prod := by
  induction F with
  | nil => rfl
  | cons pk t ih => rw [prodFactor_cons, ih, List.map_cons, List.prod_cons]

/-- The divisor-sum product of a factorisation, as a product over the mapped list. -/
theorem sigmaFactor_eq (F : List (ℕ × ℕ)) :
    sigmaFactor F = (F.map fun pk ↦ (pk.1 ^ (pk.2 + 1) - 1) / (pk.1 - 1)).prod := by
  induction F with
  | nil => rfl
  | cons pk t ih => rw [sigmaFactor_cons, ih, List.map_cons, List.prod_cons]

/-- The primes of a factorisation are the first components. -/
theorem primesFactor_eq (F : List (ℕ × ℕ)) : primesFactor F = F.map Prod.fst := by
  induction F with
  | nil => rfl
  | cons pk t ih => rw [primesFactor_cons, ih, List.map_cons]

/-- The pairs of a factorisation the check accepts have prime first components. -/
theorem forall_prime_of_checkPrime :
    ∀ {F : List (ℕ × ℕ)}, allCheckPrime F → ∀ pk ∈ F, pk.1.Prime
  | [], _ => by simp
  | pk :: t, h => by
    rw [allCheckPrime_cons, Bool.and'_eq_and, Bool.and_eq_true] at h
    intro qk hqk
    rcases List.mem_cons.1 hqk with rfl | hmem
    · exact checkPrime_true h.1
    · exact forall_prime_of_checkPrime h.2 qk hmem

/-! ### The divisor sum -/

/-- `σ₁ (∏ p ^ k) = ∏ (p ^ (k + 1) - 1) / (p - 1)` for a factorisation into distinct primes. -/
theorem sigma_of_factorization {sL : ℕ} (F : List (ℕ × ℕ)) (hp : allCheckPrime F)
    (hd : (primesFactor F).Nodup) (hsig : sigmaFactor F = sL) :
    σ₁ (prodFactor F) = sL := by
  have hpp := forall_prime_of_checkPrime hp
  clear hp
  subst hsig
  simp only [prodFactor_eq, sigmaFactor_eq, primesFactor_eq] at hd ⊢
  induction F with
  | nil => simp
  | cons pk t ih =>
    simp only [List.map_cons, List.prod_cons, List.nodup_cons] at hd ⊢
    obtain ⟨hd1, hd2⟩ := hd
    have hpk : pk.1.Prime := hpp pk (by simp)
    have hcop : (pk.1 ^ pk.2).Coprime (t.map fun pk ↦ pk.1 ^ pk.2).prod := by
      apply Nat.Coprime.pow_left
      rw [Nat.coprime_list_prod_right_iff]
      intro q hq
      obtain ⟨qk, hqk, rfl⟩ := List.mem_map.1 hq
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_primes hpk (hpp qk (List.mem_cons_of_mem _ hqk))]
      exact fun h ↦ absurd (List.mem_map_of_mem hqk) (h ▸ hd1)
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_apply_prime_pow' hpk,
      ih (fun q hq ↦ hpp q (List.mem_cons_of_mem _ hq)) hd2]

/-- `σ₁ (lcmUpto n) = sL` from a factorisation of `lcmUpto n` into distinct primes. -/
theorem sigma_lcmUpto_of_factor {n L sL : ℕ} (F : List (ℕ × ℕ)) (hL : lcmUpto n = L)
    (hprod : prodFactor F = L) (hp : allCheckPrime F) (hd : (primesFactor F).Nodup)
    (hsig : sigmaFactor F = sL) :
    σ₁ (lcmUpto n) = sL := by
  rw [hL, ← hprod]
  exact sigma_of_factorization F hp hd hsig

/-! ### `lcmUpto` as a fold -/

/-- `lcm (1..n)` over the list `[1, …, n]`, which the kernel evaluates on a literal `n`. -/
@[expose] def lcmUptoFoldr (n : ℕ) : ℕ :=
  (List.range' 1 n).rec (nat_lit 1) fun a _ r ↦ a.lcm r

/-- The two forms of `lcm (1..n)` agree. -/
theorem lcmUpto_eq_lcmUptoFoldr (n : ℕ) : lcmUpto n = lcmUptoFoldr n := by
  rw [Nat.lcmUpto, lcmUptoFoldr, Finset.lcm, Finset.fold, Nat.Icc_eq_range']
  change ((List.range' 1 (n + 1 - 1)).map id).foldr GCDMonoid.lcm 1 = _
  simp only [Nat.add_sub_cancel, List.map_id]
  induction List.range' 1 n with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, ih, lcm_eq_nat_lcm]
    rfl

/-- `lcmUpto n = L` from the `Bool` comparison of the fold with `L`. -/
theorem lcmUpto_aux (n : ℕ) {L : ℕ} (h : (lcmUptoFoldr n).beq L) : lcmUpto n = L := by
  rw [lcmUpto_eq_lcmUptoFoldr]; exact Nat.eq_of_beq_eq_true h

/-! ### Values for a literal `n` -/

/-- The factorisation of `lcm (1..n)`: each prime `p ≤ n` with exponent `Nat.log p n`. -/
def factorLcmUptoMeta (n : ℕ) : List (ℕ × ℕ) :=
  (List.range (n + 1)).filterMap fun p ↦ if p.Prime then some (p, Nat.log p n) else none

/-- The pair `(lcm (1..n), σ₁ (lcm (1..n)))` for a literal `n`, as values. -/
def lcmUptoValues (n : ℕ) : ℕ × ℕ :=
  ((List.range' 1 n).foldr Nat.lcm 1,
    (factorLcmUptoMeta n).foldr (fun pk r ↦ (pk.1 ^ (pk.2 + 1) - 1) / (pk.1 - 1) * r) 1)

end Sage
