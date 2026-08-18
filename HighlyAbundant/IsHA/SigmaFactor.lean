/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

public import HighlyAbundant.Basic
public import HighlyAbundant.Prime.TrialDivision

section

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
@[expose] public def prodFactorK : List (ℕ × ℕ) → ℕ :=
  List.rec (nat_lit 1) fun pk _ r ↦ (pk.1.pow pk.2).mul r

/-- The product `∏ (p ^ (k + 1) - 1) / (p - 1)` over a factorisation. -/
@[expose] public def sigmaFactorK : List (ℕ × ℕ) → ℕ :=
  List.rec (nat_lit 1) fun pk _ r ↦
    (((pk.1.pow pk.2.succ).sub (nat_lit 1)).div (pk.1.sub (nat_lit 1))).mul r

/-- The primes of a factorisation. -/
@[expose] public def primesFactorK : List (ℕ × ℕ) → List ℕ :=
  List.rec [] fun pk _ r ↦ pk.1 :: r

/-- The primes of a factorisation increase along the list. -/
public def FactorChain (F : List (ℕ × ℕ)) : Prop := F.IsChain (·.1 < ·.1)

/-- The ordering is decidable, so a literal list settles it. -/
instance {F : List (ℕ × ℕ)} : Decidable (FactorChain F) :=
  inferInstanceAs (Decidable (F.IsChain _))

/-- Every prime of a factorisation passes the trial-division check. -/
@[expose] public noncomputable def allCheckPrimeK : List (ℕ × ℕ) → Bool :=
  List.rec true fun pk _ r ↦ (checkPrime pk.1).and' r

@[grind =] theorem prodFactorK_cons (pk : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    prodFactorK (pk :: t) = pk.1 ^ pk.2 * prodFactorK t := rfl

@[grind =] theorem sigmaFactorK_cons (pk : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    sigmaFactorK (pk :: t) = (pk.1 ^ (pk.2 + 1) - 1) / (pk.1 - 1) * sigmaFactorK t := rfl

@[grind =] theorem primesFactorK_cons (pk : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    primesFactorK (pk :: t) = pk.1 :: primesFactorK t := rfl

@[grind =] theorem allCheckPrimeK_cons (pk : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    allCheckPrimeK (pk :: t) = (checkPrime pk.1).and' (allCheckPrimeK t) := rfl

/-- The product of a factorisation, as a product over the mapped list. -/
theorem prodFactorK_eq (F : List (ℕ × ℕ)) : prodFactorK F = (F.map fun pk ↦ pk.1 ^ pk.2).prod := by
  induction F with
  | nil => rfl
  | cons pk t ih => rw [prodFactorK_cons, ih, List.map_cons, List.prod_cons]

/-- The divisor-sum product of a factorisation, as a product over the mapped list. -/
theorem sigmaFactorK_eq (F : List (ℕ × ℕ)) :
    sigmaFactorK F = (F.map fun pk ↦ (pk.1 ^ (pk.2 + 1) - 1) / (pk.1 - 1)).prod := by
  induction F with
  | nil => rfl
  | cons pk t ih => rw [sigmaFactorK_cons, ih, List.map_cons, List.prod_cons]

/-- The primes of a factorisation are the first components. -/
theorem primesFactorK_eq (F : List (ℕ × ℕ)) : primesFactorK F = F.map Prod.fst := by
  induction F with
  | nil => rfl
  | cons pk t ih => rw [primesFactorK_cons, ih, List.map_cons]

/-- The pairs of a factorisation the check accepts have prime first components. -/
theorem forall_prime_of_checkPrime :
    ∀ {F : List (ℕ × ℕ)}, allCheckPrimeK F → ∀ pk ∈ F, pk.1.Prime
  | [], _ => by simp
  | pk :: t, h => by
    rw [allCheckPrimeK_cons, Bool.and'_eq_and, Bool.and_eq_true] at h
    intro qk hqk
    rcases List.mem_cons.1 hqk with rfl | hmem
    · exact checkPrime_true h.1
    · exact forall_prime_of_checkPrime h.2 qk hmem

/-! ### The divisor sum -/

/-- `σ₁ (∏ p ^ k) = ∏ (p ^ (k + 1) - 1) / (p - 1)` for a factorisation in increasing order. -/
theorem sigma_of_factorization {sL : ℕ} (F : List (ℕ × ℕ)) (hp : allCheckPrimeK F)
    (hc : FactorChain F) (hsig : sigmaFactorK F = sL) :
    σ₁ (prodFactorK F) = sL := by
  have hd : (primesFactorK F).Nodup := by
    rw [primesFactorK_eq]
    exact (hc.pairwise.imp fun h ↦ Nat.ne_of_lt h).map _ (fun _ _ ↦ id)
  have hpp := forall_prime_of_checkPrime hp
  clear hp hc
  subst hsig
  simp only [prodFactorK_eq, sigmaFactorK_eq, primesFactorK_eq] at hd ⊢
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
public theorem sigma_lcmUpto_of_factor {n L sL : ℕ} (F : List (ℕ × ℕ)) (hL : lcmUpto n = L)
    (hprod : prodFactorK F = L) (hp : allCheckPrimeK F) (hc : FactorChain F)
    (hsig : sigmaFactorK F = sL) :
    σ₁ (lcmUpto n) = sL := by
  rw [hL, ← hprod]
  exact sigma_of_factorization F hp hc hsig

/-! ### `lcmUpto` from its factorisation -/

/-- Each pair of `F` contributes its exponent to the factorisation at its own prime. -/
theorem factorization_prodFactorK {F : List (ℕ × ℕ)} (hp : allCheckPrimeK F) {q : ℕ} :
    (prodFactorK F).factorization q = (F.map fun pk ↦ if pk.1 = q then pk.2 else 0).sum := by
  induction F with
  | nil => simp [prodFactorK]
  | cons pk t ih =>
    have hpk : pk.1.Prime := forall_prime_of_checkPrime hp pk List.mem_cons_self
    have ht : allCheckPrimeK t := by
      rw [allCheckPrimeK_cons, Bool.and'_eq_and, Bool.and_eq_true] at hp
      exact hp.2
    have hne : prodFactorK t ≠ 0 := by
      rw [prodFactorK_eq]
      exact List.prod_ne_zero fun h ↦ by
        obtain ⟨qk, hqk, hz⟩ := List.mem_map.1 h
        exact absurd hz (pow_ne_zero _ (forall_prime_of_checkPrime ht qk hqk).pos.ne')
    rw [prodFactorK_cons, Nat.factorization_mul (pow_ne_zero _ hpk.pos.ne') hne,
      Nat.Prime.factorization_pow hpk]
    simp [Finsupp.add_apply, Finsupp.single_apply, ih ht, eq_comm]

/-- The contribution at `q` of a list whose primes are distinct, given a pair at `q`. -/
private theorem sum_map_ite_of_mem {F : List (ℕ × ℕ)} (hd : (F.map Prod.fst).Nodup) {q k : ℕ}
    (h : (q, k) ∈ F) : (F.map fun pk ↦ if pk.1 = q then pk.2 else 0).sum = k := by
  induction F with
  | nil => simp at h
  | cons pk t ih =>
    rw [List.map_cons, List.nodup_cons] at hd
    rcases List.mem_cons.1 h with rfl | hmem
    · have : ∀ qk ∈ t, qk.1 ≠ q := fun qk hqk hq ↦ hd.1 (List.mem_map.2 ⟨qk, hqk, hq⟩)
      simp only [List.map_cons, List.sum_cons]
      rw [List.map_eq_replicate_iff.2 fun qk hqk ↦ if_neg (this qk hqk), List.sum_replicate]
      simp
    · have hne : pk.1 ≠ q := fun hq ↦ hd.1 (List.mem_map.2 ⟨(q, k), hmem, hq.symm⟩)
      simp only [List.map_cons, List.sum_cons, if_neg hne, Nat.zero_add]
      exact ih hd.2 hmem

/-- `lcmUpto n` is the product of the prime powers in `F`, when `F` lists each prime `p ≤ n` once
with an exponent `k` pinned by `p ^ k ≤ n < p ^ (k + 1)`. -/
theorem lcmUpto_eq_prodFactorK {n : ℕ} (F : List (ℕ × ℕ)) (hp : allCheckPrimeK F)
    (hc : FactorChain F)
    (hbound : ∀ pk ∈ F, pk.1 ^ pk.2 ≤ n ∧ n < pk.1 ^ (pk.2 + 1))
    (hcover : ∀ p, p.Prime → p ≤ n → p ∈ primesFactorK F) :
    lcmUpto n = prodFactorK F := by
  have hd : (F.map Prod.fst).Nodup :=
    (hc.pairwise.imp fun h ↦ Nat.ne_of_lt h).map _ (fun _ _ ↦ id)
  rw [primesFactorK_eq] at hcover
  have hne : prodFactorK F ≠ 0 := by
    rw [prodFactorK_eq]
    exact List.prod_ne_zero fun h ↦ by
      obtain ⟨qk, hqk, hz⟩ := List.mem_map.1 h
      exact absurd hz (pow_ne_zero _ (forall_prime_of_checkPrime hp qk hqk).pos.ne')
  have hexp := factorization_lcmUpto_of_bounds (L := F) Prod.fst Prod.snd
    (forall_prime_of_checkPrime hp) hbound
  refine Nat.eq_of_factorization_eq (lcmUpto_ne_zero n) hne fun q ↦ ?_
  by_cases hq : q.Prime
  · rw [factorization_prodFactorK hp]
    rcases le_or_gt q n with hqn | hqn
    · obtain ⟨⟨q', k⟩, hmem, rfl⟩ := List.mem_map.1 (hcover q hq hqn)
      rw [sum_map_ite_of_mem hd hmem, hexp _ hmem]
    · rw [Nat.factorization_lcmUpto n hq, Nat.log_of_lt hqn]
      refine (List.sum_eq_zero fun x hx ↦ ?_).symm
      obtain ⟨⟨p, k⟩, hmem, rfl⟩ := List.mem_map.1 hx
      by_cases hpq : p = q
      · subst hpq
        obtain ⟨h1, -⟩ := hbound _ hmem
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp
        · exact absurd (le_trans (Nat.le_self_pow hk.ne' p) h1) (by lia)
      · simp [hpq]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hq]

/-! ### `lcmUpto` for the kernel -/

/-- `lcm (1..n)` over the list `[1, …, n]`, which the kernel evaluates on a literal `n`. -/
@[expose] public def lcmUptoK (n : ℕ) : ℕ :=
  (List.range' 1 n).rec (nat_lit 1) fun a _ r ↦ a.lcm r

/-- The two forms of `lcm (1..n)` agree. -/
theorem lcmUpto_eq_lcmUptoK (n : ℕ) : lcmUpto n = lcmUptoK n := by
  rw [Nat.lcmUpto, lcmUptoK, Finset.lcm, Finset.fold, Nat.Icc_eq_range']
  change ((List.range' 1 (n + 1 - 1)).map id).foldr GCDMonoid.lcm 1 = _
  simp only [Nat.add_sub_cancel, List.map_id]
  induction List.range' 1 n with
  | nil => rfl
  | cons a l ih => rw [List.foldr_cons, ih, lcm_eq_nat_lcm]

/-- `lcmUpto n = L` from the `Bool` comparison of `lcmUptoK n` with `L`. -/
public theorem lcmUpto_eq_of_beq (n : ℕ) {L : ℕ} (h : (lcmUptoK n).beq L) : lcmUpto n = L := by
  rw [lcmUpto_eq_lcmUptoK]; exact Nat.eq_of_beq_eq_true h

/-! ### Values for a literal `n` -/

/-- The factorisation of `lcm (1..n)`: each prime `p ≤ n` with exponent `Nat.log p n`. -/
public def factorLcmUptoMeta (n : ℕ) : List (ℕ × ℕ) :=
  (List.range (n + 1)).filterMap fun p ↦ if p.Prime then some (p, Nat.log p n) else none

/-- The pair `(lcm (1..n), σ₁ (lcm (1..n)))` for a literal `n`, as values. -/
public def lcmUptoValues (n : ℕ) : ℕ × ℕ :=
  ((List.range' 1 n).foldr Nat.lcm 1,
    (factorLcmUptoMeta n).foldr (fun pk r ↦ (pk.1 ^ (pk.2 + 1) - 1) / (pk.1 - 1) * r) 1)

end Sage
