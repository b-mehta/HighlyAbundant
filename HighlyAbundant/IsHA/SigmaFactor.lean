/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.Basic
import HighlyAbundant.IsHA.Primes

open Nat

open ArithmeticFunction Lean Meta Elab Tactic

namespace Sage

/-- `∏ p^k` over a factorization list. Written with `List.rec` directly (rather
than `List.map`/`List.prod`) so the kernel reduces it through `List.rec` alone. -/
def prodFactor : List (ℕ × ℕ) → ℕ :=
  List.rec 1 (fun pk _ r => pk.1 ^ pk.2 * r)
/-- `∏ (p^(k+1) - 1)/(p - 1)` over a factorization list (the σ₁ closed form). -/
def sigmaFactor : List (ℕ × ℕ) → ℕ :=
  List.rec 1 (fun pk _ r => (pk.1 ^ (pk.2 + 1) - 1) / (pk.1 - 1) * r)
/-- The primes of a factorization list. -/
def primesFactor : List (ℕ × ℕ) → List ℕ :=
  List.rec [] (fun pk _ r => pk.1 :: r)
/-- Every prime in `F` passes the trial-division primality check. -/
noncomputable def allCheckPrime : List (ℕ × ℕ) → Bool :=
  List.rec true (fun pk _ r => (checkPrime pk.1).and' r)

lemma prodFactor_cons (pk : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    prodFactor (pk :: t) = pk.1 ^ pk.2 * prodFactor t := rfl
lemma sigmaFactor_cons (pk : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    sigmaFactor (pk :: t) = (pk.1 ^ (pk.2 + 1) - 1) / (pk.1 - 1) * sigmaFactor t := rfl
lemma primesFactor_cons (pk : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    primesFactor (pk :: t) = pk.1 :: primesFactor t := rfl
lemma allCheckPrime_cons (pk : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    allCheckPrime (pk :: t) = (checkPrime pk.1).and' (allCheckPrime t) := rfl

lemma prodFactor_eq (F : List (ℕ × ℕ)) : prodFactor F = (F.map (fun pk => pk.1 ^ pk.2)).prod := by
  induction F with
  | nil => rfl
  | cons pk t ih => rw [prodFactor_cons, ih, List.map_cons, List.prod_cons]

lemma sigmaFactor_eq (F : List (ℕ × ℕ)) :
    sigmaFactor F = (F.map (fun pk => (pk.1 ^ (pk.2 + 1) - 1) / (pk.1 - 1))).prod := by
  induction F with
  | nil => rfl
  | cons pk t ih => rw [sigmaFactor_cons, ih, List.map_cons, List.prod_cons]

lemma primesFactor_eq (F : List (ℕ × ℕ)) : primesFactor F = F.map Prod.fst := by
  induction F with
  | nil => rfl
  | cons pk t ih => rw [primesFactor_cons, ih, List.map_cons]

lemma forall_prime_of_checkPrime :
    ∀ {F : List (ℕ × ℕ)}, allCheckPrime F = true → ∀ pk ∈ F, pk.1.Prime
  | [], _ => by simp
  | pk :: t, h => by
    rw [allCheckPrime_cons, Bool.and'_eq_and, Bool.and_eq_true] at h
    intro qk hqk
    rcases List.mem_cons.1 hqk with rfl | hmem
    · exact checkPrime_true h.1
    · exact forall_prime_of_checkPrime h.2 qk hmem

/-- `σ₁ (∏ p^k) = ∏ (p^(k+1)-1)/(p-1)` when the `p` are distinct primes. -/
lemma sigma_of_factorization {sL : ℕ} (F : List (ℕ × ℕ))
    (hp : allCheckPrime F = true) (hd : (primesFactor F).Nodup) (hsig : sigmaFactor F = sL) :
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
    have hcop : (pk.1 ^ pk.2).Coprime (t.map (fun pk => pk.1 ^ pk.2)).prod := by
      apply Nat.Coprime.pow_left
      rw [Nat.coprime_list_prod_right_iff]
      intro q hq
      obtain ⟨qk, hqk, rfl⟩ := List.mem_map.1 hq
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_primes hpk (hpp qk (List.mem_cons_of_mem _ hqk))]
      exact fun h => absurd (List.mem_map_of_mem hqk) (h ▸ hd1)
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_apply_prime_pow' hpk,
      ih (fun q hq => hpp q (List.mem_cons_of_mem _ hq)) hd2]

/-- Bridge from a factorization of `L = lcmUpto n` to `σ₁ (lcmUpto n)`. -/
lemma sigma_lcm_bridge {n L sL : ℕ} (F : List (ℕ × ℕ))
    (hL : lcmUpto n = L) (hprod : prodFactor F = L)
    (hp : allCheckPrime F = true) (hd : (primesFactor F).Nodup) (hsig : sigmaFactor F = sL) :
    σ₁ (lcmUpto n) = sL := by
  rw [hL, ← hprod]
  exact sigma_of_factorization F hp hd hsig

/-- Meta-side factorization of `lcmUpto n`: primes `≤ n` with exponent `Nat.log p n`. -/
def factorLcmUptoMeta (n : ℕ) : List (ℕ × ℕ) :=
  (List.range (n + 1)).filterMap fun p => if p.Prime then some (p, Nat.log p n) else none

/-- `sigma_lcm hL` proves `σ₁ (lcmUpto n) = sL` given `hL : lcmUpto n = L`. The
factorization is computed meta-side; the kernel only verifies `∏ p^k = L`, `∏ σ = sL`
(via `Nat.beq`/`reflBoolTrue`), primality by trial division, and distinctness. -/
elab "sigma_lcm" hLStx:ident : tactic => do
  let hLName ← resolveGlobalConstNoOverload hLStx
  let hLexpr := mkConst hLName
  let hLty ← inferType hLexpr
  let some (_, lhs, LExpr) := hLty.eq?
    | throwError "sigma_lcm: argument must prove `lcmUpto n = L`"
  let_expr Nat.lcmUpto nExpr := lhs
    | throwError "sigma_lcm: LHS must be `lcmUpto n`"
  let some nVal := nExpr.nat? | throwError "sigma_lcm: n not a literal"
  liftMetaFinishingTactic fun g => do
    let some (_, _, sLExpr) := (← g.getType).eq?
      | throwError "sigma_lcm: goal must be `σ₁ (lcmUpto n) = sL`"
    let natTy := mkConst ``Nat
    let prodTy := mkApp2 (mkConst ``Prod [.zero, .zero]) natTy natTy
    let mut FExpr := mkApp (mkConst ``List.nil [.zero]) prodTy
    for (p, k) in (factorLcmUptoMeta nVal).reverse do
      let pairE := mkApp4 (mkConst ``Prod.mk [.zero, .zero]) natTy natTy (mkNatLit p) (mkNatLit k)
      FExpr := mkApp3 (mkConst ``List.cons [.zero]) prodTy pairE FExpr
    let factorsE ← mkAuxDefinition (← mkAuxDeclName `factors)
      (mkApp (mkConst ``List [.zero]) prodTy) FExpr (compile := false)
    let boolTy := mkConst ``Bool
    let trueE := mkConst ``Bool.true
    let boolCert (b : Expr) : MetaM Expr := do
      return mkConst (← mkAuxLemma [] (mkApp3 (mkConst ``Eq [.succ .zero]) boolTy b trueE)
        Lean.reflBoolTrue)
    let prodApp := mkApp (mkConst ``Sage.prodFactor) factorsE
    let hprod := mkApp3 (mkConst ``Nat.eq_of_beq_eq_true) prodApp LExpr
      (← boolCert (mkApp2 (mkConst ``Nat.beq) prodApp LExpr))
    let hp ← boolCert (mkApp (mkConst ``Sage.allCheckPrime) factorsE)
    let hd ← mkDecideProof (mkApp2 (mkConst ``List.Nodup [.zero]) natTy
      (mkApp (mkConst ``Sage.primesFactor) factorsE))
    let sigApp := mkApp (mkConst ``Sage.sigmaFactor) factorsE
    let hsig := mkApp3 (mkConst ``Nat.eq_of_beq_eq_true) sigApp sLExpr
      (← boolCert (mkApp2 (mkConst ``Nat.beq) sigApp sLExpr))
    g.assign <| mkAppN (mkConst ``Sage.sigma_lcm_bridge)
      #[nExpr, LExpr, sLExpr, factorsE, hLexpr, hprod, hp, hd, hsig]

end Sage
