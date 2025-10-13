/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum.PowMod

/-!
# Proof-producing evaluation of `a ^ b % n`

Note that `Mathlib.Tactic.NormNum.PowMod` contains a similar tactic, but that runs significantly
slower and less efficiently than the one here.
-/

open Nat

/-- The pow-mod function, named explicitly to allow more precise control of reduction. -/
def powMod (a b n : ℕ) : ℕ := a ^ b % n
/-- The pow-mod auxiliary function, named explicitly to allow more precise control of reduction. -/
def powModAux (a b c n : ℕ) : ℕ := (a ^ b * c) % n

lemma powModAux_zero_eq {a c n m : ℕ} (hm : c % n = m) : powModAux a 0 c n = m := by
  simpa [powModAux]

lemma powModAux_one_eq {a c n m : ℕ} (hm : (a * c) % n = m) : powModAux a 1 c n = m := by
  simp_all [powModAux]

lemma powModAux_even_eq {a a' b b' c n m : ℕ}
    (ha' : a * a % n = a') (hb' : b' <<< 1 = b)
    (h : powModAux a' b' c n = m) :
    powModAux a b c n = m := by
  rw [← ha', powModAux, mul_mod] at h
  rw [Nat.shiftLeft_eq, mul_comm, pow_one] at hb'
  rw [← hb', powModAux, pow_mul, mul_mod, pow_two, pow_mod, h]

lemma powModAux_odd_eq {a a' b b' c c' n m : ℕ}
    (hb' : 2 * b' + 1 = b) (ha' : a * a % n = a') (hc' : a * c % n = c')
    (h : powModAux a' b' c' n = m) :
    powModAux a b c n = m := by
  rw [← ha', ← hc', powModAux, mul_mod, mod_mod] at h
  rw [← hb', powModAux, pow_succ, pow_mul, mul_assoc, mul_mod, pow_mod, pow_two, h]

lemma powMod_eq (a : ℕ) {a' b n m : ℕ} (h : powModAux a' b 1 n = m) (ha : a % n = a') :
    powMod a b n = m := by
  rwa [powModAux, mul_one, ← ha, pow_mod, mod_mod, ← pow_mod] at h

lemma powMod_ne {a b n m : ℕ} (m' : ℕ) (hm : bne m' m) (h : powMod a b n = m') :
    powMod a b n ≠ m := by
  simp_all

noncomputable def powModTR (a b n : Nat) : Nat :=
  aux (b + 1) (a % n) b 1
where
  aux : Nat → ((a b c : Nat) → Nat) :=
    Nat.rec (fun _ _ _ => 0)
      (fun _ r a b c =>
        (b.beq 0).rec
          ((b.beq 1).rec
            (((b.mod 2).beq 0).rec
                (r ((a.mul a).mod n) (b.div 2) ((a.mul c).mod n))
                (r ((a.mul a).mod n) (b.div 2) c))
            ((a.mul c).mod n))
          (c.mod n))

def powModTR' (a b n : ℕ) : ℕ :=
  aux (a % n) b 1
  where aux (a b c : ℕ) : ℕ :=
    if b = 0 then c % n
    else if b = 1 then (a * c) % n
    else if b % 2 = 0 then
      aux (a * a % n) (b / 2) c
    else
      aux (a * a % n) (b / 2) (a * c % n)
    partial_fixpoint

lemma Bool.rec_eq_ite {α : Type*} {b : Bool} {t f : α} : b.rec f t = if b then t else f := by
  cases b <;> simp

@[simp] lemma Nat.mod_eq_mod {a b : ℕ} : a.mod b = a % b := rfl
@[simp] lemma Nat.div_eq_div {a b : ℕ} : a.div b = a / b := rfl

@[simp] lemma powModTR_aux_zero_eq {n a b c : ℕ} :
    powModTR.aux n 0 a b c = 0 := rfl

lemma powModTR_aux_succ_eq {n a b c fuel : ℕ} :
    powModTR.aux n (fuel + 1) a b c =
      (b.beq 0).rec (true := c % n)
      ((b.beq 1).rec (true := (a * c) % n)
      (((b % 2).beq 0).rec
          (powModTR.aux n fuel (a * a % n) (b / 2) (a * c % n))
          (powModTR.aux n fuel (a * a % n) (b / 2) c))) := by
  rfl

lemma powModTR_aux_succ_eq' {n a b c fuel : ℕ} :
    powModTR.aux n (fuel + 1) a b c =
      if b = 0 then c % n else
      if b = 1 then a * c % n else
      if b % 2 = 0 then powModTR.aux n fuel (a * a % n) (b / 2) c
      else powModTR.aux n fuel (a * a % n) (b / 2) (a * c % n) := by
  simp only [powModTR_aux_succ_eq, Bool.rec_eq_ite, beq_eq]

lemma powModTR_aux_eq (n a b c fuel) (hfuel : b < fuel) :
    powModTR.aux n fuel a b c = powModAux a b c n := by
  induction fuel generalizing a b c with
  | zero => omega
  | succ fuel ih =>
    rw [powModTR_aux_succ_eq']
    split
    case isTrue hb0 => rw [hb0, powModAux_zero_eq rfl]
    split
    case isTrue hb1 => rw [hb1, powModAux_one_eq rfl]
    split
    case isTrue hb0 hb1 hbe =>
      rw [ih _ _ _ (by omega)]
      exact (powModAux_even_eq rfl (by omega) rfl).symm
    case isFalse hb0 hb1 hbo =>
      rw [ih _ _ _ (by omega)]
      exact (powModAux_odd_eq (by omega) rfl rfl rfl).symm

lemma powModTR_eq (a b n : ℕ) : powModTR a b n = powMod a b n := by
  rw [powModTR, powModTR_aux_eq _ _ _ _ _ (by omega)]
  exact (powMod_eq _ rfl rfl).symm

lemma powMod_eq_of_powModTR (a b n m : ℕ) (h : (powModTR a b n).beq m) : powMod a b n = m := by
  rwa [powModTR_eq, beq_eq] at h

namespace Tactic.powMod

open Lean Meta Elab Tactic

/-- Given `a, b, c, n : ℕ`, return `(m, ⊢ ℕ, ⊢ powModAux a b c n = m)`. -/
partial def mkPowModAuxEq (a b c n : ℕ) (aE bE cE nE : Expr) : MetaM (ℕ × Expr × Expr) :=
  if b = 0 then do
    let m : ℕ := c % n
    let mE : Expr := mkNatLit m
    let hm : Expr ← mkEqRefl mE
    return (m, mE, mkApp5 (mkConst ``powModAux_zero_eq []) aE cE nE mE hm)
  else if b = 1 then do
    let m : ℕ := (a * c) % n
    let mE : Expr := mkNatLit m
    let hm : Expr ← mkEqRefl mE
    return (m, mE, mkApp5 (mkConst ``powModAux_one_eq []) aE cE nE mE hm)
  else if Even b then do
    let b' := b / 2
    let a' := a * a % n
    let a'E := mkNatLit a'
    let b'E := mkNatLit b'
    let ha' : Expr ← mkEqRefl a'E
    let hb' : Expr ← mkEqRefl bE
    let (m, mE, eq) ← mkPowModAuxEq a' b' c n a'E b'E cE nE
    return (m, mE, mkApp10 (mkConst ``powModAux_even_eq []) aE a'E bE b'E cE nE mE ha' hb' eq)
  else do
    let a' := a * a % n
    let b' := b / 2
    let c' := a * c % n
    let a'E := mkNatLit a'
    let b'E := mkNatLit b'
    let c'E := mkNatLit c'
    let hb' : Expr ← mkEqRefl bE
    let ha' : Expr ← mkEqRefl a'E
    let hc' : Expr ← mkEqRefl c'E
    let (m, mE, eq) ← mkPowModAuxEq a' b' c' n a'E b'E c'E nE
    return (m, mE,
      mkApp5 (mkApp7 (mkConst ``powModAux_odd_eq []) aE a'E bE b'E cE c'E nE) mE hb' ha' hc' eq)

/-- Given `a, b, n : ℕ`, return `(m, ⊢ powMod a b n = m)`. -/
def mkPowModEq (a b n : ℕ) (aE bE nE : Expr) : MetaM (ℕ × Expr × Expr) := do
  let a' := a % n
  let a'E := mkNatLit a'
  let (m, mE, eq) ← mkPowModAuxEq a' b 1 n a'E bE (mkNatLit 1) nE
  return (m, mE, ← mkAppM ``powMod_eq #[aE, eq, ← mkEqRefl a'E])

/-- Given `a, b, n : ℕ`, return `(m, ⊢ powMod a b n = m)`. -/
def mkPowModEq' (a b n : ℕ) (aE bE nE : Expr) : MetaM (ℕ × Expr × Expr) := do
  let m := powModTR' a b n
  let mE := mkNatLit m
  return (m, mE, mkApp5 (mkConst ``powMod_eq_of_powModTR) aE bE nE mE eagerReflBoolTrue)

/-- Given `a, b, n, m : ℕ`, if `powMod a b n = m` then return a proof of that fact. -/
def provePowModEq (a b n m : ℕ) (aE bE nE : Expr) : MetaM Expr := do
  let (m', _, eq) ← mkPowModEq a b n aE bE nE
  unless m = m' do throwError "attempted to prove {a} ^ {b} % {n} = {m} but it's actually {m'}"
  return eq

/-- Given `a, b, n, m : ℕ`, if `powMod a b n ≠ m` then return a proof of that fact. -/
def provePowModNe (a b n m : ℕ) (aE bE nE mE : Expr) : MetaM Expr := do
  let (m', m'E, eq) ← mkPowModEq a b n aE bE nE
  if m = m' then throwError "attempted to prove {a} ^ {b} % {n} ≠ {m} but it is {m'}"
  let ne := eagerReflBoolTrue
  return mkApp7 (mkConst ``powMod_ne []) aE bE nE mE m'E ne eq

/-- Given `a, b, n, m : ℕ`, if `powMod a b n = m` then return a proof of that fact. -/
def provePowModEq' (a b n m : ℕ) (aE bE nE : Expr) : MetaM Expr := do
  let (m', _, eq) ← mkPowModEq' a b n aE bE nE
  unless m = m' do throwError "attempted to prove {a} ^ {b} % {n} = {m} but it's actually {m'}"
  return eq

/-- Given `a, b, n, m : ℕ`, if `powMod a b n ≠ m` then return a proof of that fact. -/
def provePowModNe' (a b n m : ℕ) (aE bE nE mE : Expr) : MetaM Expr := do
  let (m', m'E, eq) ← mkPowModEq' a b n aE bE nE
  if m = m' then throwError "attempted to prove {a} ^ {b} % {n} ≠ {m} but it is {m'}"
  let ne := eagerReflBoolTrue
  return mkApp7 (mkConst ``powMod_ne []) aE bE nE mE m'E ne eq

def prove_pow_mod_tac (g : MVarId) : MetaM Unit := do
  let t : Expr ← g.getType
  match_expr t with
  | Eq ty lhsE rhsE =>
    unless (← whnfR ty).isConstOf ``Nat do throwError "not an equality of naturals"
    let some rhs := rhsE.nat? | throwError "rhs is not a numeral"
    let some (aE, bE, nE) := lhsE.app3? ``powMod | throwError "lhs is not a pow-mod"
    let some a := aE.nat? | throwError "base is not a numeral"
    let some b := bE.nat? | throwError "exponent is not a numeral"
    let some n := nE.nat? | throwError "modulus is not a numeral"
    let pf ← provePowModEq a b n rhs aE bE nE
    g.assign pf
  | Ne ty lhsE rhsE =>
    unless (← whnfR ty).isConstOf ``Nat do throwError "not an equality of naturals"
    let some rhs := rhsE.nat? | throwError "rhs is not a numeral"
    let some (aE, bE, nE) := lhsE.app3? ``powMod | throwError "lhs is not a pow-mod"
    let some a := aE.nat? | throwError "base is not a numeral"
    let some b := bE.nat? | throwError "exponent is not a numeral"
    let some n := nE.nat? | throwError "modulus is not a numeral"
    let pf ← provePowModNe a b n rhs aE bE nE rhsE
    g.assign pf
  | _ => throwError "not an accepted expression"

def prove_pow_mod_tac' (g : MVarId) : MetaM Unit := do
  let t : Expr ← g.getType
  match_expr t with
  | Eq ty lhsE rhsE =>
    unless (← whnfR ty).isConstOf ``Nat do throwError "not an equality of naturals"
    let some rhs := rhsE.nat? | throwError "rhs is not a numeral"
    let some (aE, bE, nE) := lhsE.app3? ``powMod | throwError "lhs is not a pow-mod"
    let some a := aE.nat? | throwError "base is not a numeral"
    let some b := bE.nat? | throwError "exponent is not a numeral"
    let some n := nE.nat? | throwError "modulus is not a numeral"
    let pf ← provePowModEq' a b n rhs aE bE nE
    g.assign pf
  | Ne ty lhsE rhsE =>
    unless (← whnfR ty).isConstOf ``Nat do throwError "not an equality of naturals"
    let some rhs := rhsE.nat? | throwError "rhs is not a numeral"
    let some (aE, bE, nE) := lhsE.app3? ``powMod | throwError "lhs is not a pow-mod"
    let some a := aE.nat? | throwError "base is not a numeral"
    let some b := bE.nat? | throwError "exponent is not a numeral"
    let some n := nE.nat? | throwError "modulus is not a numeral"
    let pf ← provePowModNe' a b n rhs aE bE nE rhsE
    g.assign pf
  | _ => throwError "not an accepted expression"

elab "prove_pow_mod" : tactic => liftMetaFinishingTactic prove_pow_mod_tac
elab "prove_pow_mod'" : tactic => liftMetaFinishingTactic prove_pow_mod_tac'

end Tactic.powMod

-- #time
-- example :
--     powMod 2
--       131715931587485903133664770501783872901180735752961173191222502260846184802138117218820246495979164495762424017769215925882581565859513559697500346853208717730048481311930278737221764046227216650748207028546755348290341925152606053939920784122173626831732721956717186562885471376983969828398653806056
--       131715931587485903133664770501783872901180735752961173191222502260846184802138117218820246495979164495762424017769215925882581565859513559697500346853208717730048481311930278737221764046227216650748207028546755348290341925152606053939920784122173626831732721956717186562885471376983969828398653806057 =
--       1 := by
--   prove_pow_mod

-- #time
-- example :
--     powMod 2
--       131715931587485903133664770501783872901180735752961173191222502260846184802138117218820246495979164495762424017769215925882581565859513559697500346853208717730048481311930278737221764046227216650748207028546755348290341925152606053939920784122173626831732721956717186562885471376983969828398653806056
--       131715931587485903133664770501783872901180735752961173191222502260846184802138117218820246495979164495762424017769215925882581565859513559697500346853208717730048481311930278737221764046227216650748207028546755348290341925152606053939920784122173626831732721956717186562885471376983969828398653806057 =
--       1 := by
--   prove_pow_mod'

-- #eval powModTR' 2 (31 ^ 100) (31 ^ 100 + 7)

-- #eval 68700266508534171304139668405538781983844090880155308447315415736868121904417993012859336490047417444352793669286109720181816751709874535850447534937862879222650085866396891801700313186135778700458822 / 2
