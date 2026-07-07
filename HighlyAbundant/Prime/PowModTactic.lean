/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

public import HighlyAbundant.Prime.PowMod
meta import HighlyAbundant.Prime.PowMod

/-!
# The `prove_pow_mod` tactic

A proof-producing tactic closing goals `powMod a b n = m` / `powMod a b n ≠ m` for literals.
The value is computed at elaboration time by `powModTR'` (kept as an ordinary definition in
`HighlyAbundant.Prime.PowMod` and brought into the meta phase by `meta import`), and the kernel
verifies it via `powMod_eq_of_powModTR`.
-/

public section

namespace Tactic.powMod

open Lean Meta Elab Tactic

/-- Given `a, b, n : ℕ`, return `(m, ⊢ powMod a b n = m)`. -/
meta def mkPowModEq' (a b n : ℕ) (aE bE nE : Expr) : MetaM (ℕ × Expr × Expr) := do
  let m := powModTR' a b n
  let mE := mkNatLit m
  return (m, mE, mkApp5 (mkConst ``powMod_eq_of_powModTR) aE bE nE mE eagerReflBoolTrue)

/-- Given `a, b, n, m : ℕ`, if `powMod a b n = m` then return a proof of that fact. -/
meta def provePowModEq' (a b n m : ℕ) (aE bE nE : Expr) : MetaM Expr := do
  let (m', _, eq) ← mkPowModEq' a b n aE bE nE
  unless m = m' do throwError "attempted to prove {a} ^ {b} % {n} = {m} but it's actually {m'}"
  return eq

/-- Given `a, b, n, m : ℕ`, if `powMod a b n ≠ m` then return a proof of that fact. -/
meta def provePowModNe' (a b n m : ℕ) (aE bE nE mE : Expr) : MetaM Expr := do
  let m' := powModTR' a b n
  if m = m' then throwError "attempted to prove {a} ^ {b} % {n} ≠ {m} but it is {m'}"
  return mkApp5 (mkConst ``powMod_ne_of_powModTR) aE bE nE mE eagerReflBoolFalse

meta def prove_pow_mod_tac (g : MVarId) : MetaM Unit := do
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
