import HighlyAbundant.Basic
import HighlyAbundant.IsHA.Primes

open ArithmeticFunction Lean Meta Elab Tactic

namespace Sage

/-- `∏ p^k` over a factorization list. -/
def prodFactor (F : List (ℕ × ℕ)) : ℕ := (F.map (fun pk => pk.1 ^ pk.2)).prod
/-- `∏ (p^(k+1) - 1)/(p - 1)` over a factorization list (the σ₁ closed form). -/
def sigmaFactor (F : List (ℕ × ℕ)) : ℕ := (F.map (fun pk => (pk.1 ^ (pk.2 + 1) - 1) / (pk.1 - 1))).prod
/-- The primes of a factorization list. -/
def primesFactor (F : List (ℕ × ℕ)) : List ℕ := F.map Prod.fst
/-- Every prime in `F` passes the trial-division primality check. -/
noncomputable def allCheckPrime (F : List (ℕ × ℕ)) : Bool := F.all (fun pk => ECCompute.checkPrime pk.1)

lemma forall_prime_of_checkPrime {F : List (ℕ × ℕ)} (h : allCheckPrime F = true) :
    ∀ pk ∈ F, pk.1.Prime := by
  unfold allCheckPrime at h
  intro pk hpk
  exact ECCompute.checkPrime_true (List.all_eq_true.1 h pk hpk)

/-- `σ₁ (∏ p^k) = ∏ (p^(k+1)-1)/(p-1)` when the `p` are distinct primes. -/
lemma sigma_of_factorization {sL : ℕ} (F : List (ℕ × ℕ))
    (hp : allCheckPrime F = true) (hd : (primesFactor F).Nodup) (hsig : sigmaFactor F = sL) :
    σ₁ (prodFactor F) = sL := by
  have hpp := forall_prime_of_checkPrime hp
  clear hp
  subst hsig
  unfold prodFactor sigmaFactor primesFactor at *
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
      ih hd2 (fun q hq => hpp q (List.mem_cons_of_mem _ hq))]

/-- Bridge from a factorization of `L = lcmRange n` to `σ₁ (lcmRange n)`. -/
lemma sigma_lcm_bridge {n L sL : ℕ} (F : List (ℕ × ℕ))
    (hL : lcmRange n = L) (hprod : prodFactor F = L)
    (hp : allCheckPrime F = true) (hd : (primesFactor F).Nodup) (hsig : sigmaFactor F = sL) :
    σ₁ (lcmRange n) = sL := by
  rw [hL, ← hprod]
  exact sigma_of_factorization F hp hd hsig

/-- Meta-side factorization of `lcmRange n`: primes `≤ n` with exponent `Nat.log p n`. -/
def factorLcmRangeMeta (n : ℕ) : List (ℕ × ℕ) :=
  (List.range (n + 1)).filterMap fun p => if p.Prime then some (p, Nat.log p n) else none

/-- `sigma_lcm hL` proves `σ₁ (lcmRange n) = sL` given `hL : lcmRange n = L`. The
factorization is computed meta-side; the kernel only verifies `∏ p^k = L`, `∏ σ = sL`
(via `Nat.beq`/`reflBoolTrue`), primality by trial division, and distinctness. -/
elab "sigma_lcm" hLStx:ident : tactic => do
  let hLName ← resolveGlobalConstNoOverload hLStx
  let hLexpr := mkConst hLName
  let hLty ← inferType hLexpr
  let some (_, lhs, LExpr) := hLty.eq?
    | throwError "sigma_lcm: argument must prove `lcmRange n = L`"
  let_expr lcmRange nExpr := lhs
    | throwError "sigma_lcm: LHS must be `lcmRange n`"
  let some nVal := nExpr.nat? | throwError "sigma_lcm: n not a literal"
  liftMetaFinishingTactic fun g => do
    let some (_, _, sLExpr) := (← g.getType).eq?
      | throwError "sigma_lcm: goal must be `σ₁ (lcmRange n) = sL`"
    let natTy := mkConst ``Nat
    let prodTy := mkApp2 (mkConst ``Prod [.zero, .zero]) natTy natTy
    let mut FExpr := mkApp (mkConst ``List.nil [.zero]) prodTy
    for (p, k) in (factorLcmRangeMeta nVal).reverse do
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
