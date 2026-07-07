/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

public import Mathlib.Tactic.NormNum.Prime
public import Batteries.Tactic.NoMatch
public import Lean.Message
public import Mathlib.Data.Nat.Factors

/-!
# Pure data and computation for Pratt certificates

The certificate data types and the pure functions that compute and reshape them. These carry no
`Expr`/`Syntax`, so they are ordinary (non-`meta`) definitions; the tactic module imports them at
both phases and only its proof-term construction is `meta`.
-/

@[expose] public section

open Nat

namespace Tactic.Prime

inductive MPrattCertificate : Type
  | small (n : ℕ)
  | big (n : ℕ) (root : ℕ) (factors : List MPrattCertificate)
  deriving Repr, BEq, Lean.ToExpr

inductive PrattEntry : Type
  | small (n : ℕ)
  | big (n : ℕ) (root : ℕ) (factors : List ℕ)
  deriving Repr, BEq, Lean.ToExpr, Lean.FromJson

def PrattCertificate : Type := List PrattEntry
  deriving Repr, BEq, Lean.ToExpr, Lean.FromJson

def MPrattCertificate.out : MPrattCertificate → ℕ
  | .small n => n
  | .big n _ _ => n

def reformatAux : MPrattCertificate → Std.TreeMap ℕ PrattEntry
  | .small n => {(n, .small n)}
  | .big n root factors =>
      if n ≤ 11 then {(n, .small n)} else
      (factors.map reformatAux).foldl (.mergeWith (fun _ a _ => a))
      {(n, .big n root (factors.map (·.out)))}

def reformat : MPrattCertificate → PrattCertificate := Std.TreeMap.values ∘ reformatAux

def extractFactor.acc (p q i : ℕ) (hq : 1 < q) : ℕ × ℕ :=
  if hp₀ : p = 0 then (0, i)
  else if p % q = 0 then
    have : p / q < p := Nat.div_lt_self (by omega) hq
    acc (p / q) q (i + 1) hq
  else (p, i)

/--
Given `p q : ℕ`, find the unique `r k : ℕ` such that `r * q ^ k = p` and `r` is not divisible by `q`
-/
def extractFactor (p q : ℕ) : ℕ × ℕ :=
  if hq : q ≤ 1 then (p, 0) else extractFactor.acc p q 0 (lt_of_not_ge hq)

def powMod (a b n : ℕ) : ℕ :=
  powModAux (a % n) b 1 where
  powModAux (a b c : ℕ) : ℕ :=
    if b = 0 then c % n
    else if b = 1 then (a * c) % n
    else if b % 2 = 0 then
      powModAux (a * a % n) (b / 2) c
    else
      powModAux (a * a % n) (b / 2) (a * c % n)
    partial_fixpoint

def testPrimitiveRoot (n a : ℕ) (facs : List ℕ) : Bool :=
  facs.all fun q ↦ powMod a ((n - 1) / q) n ≠ 1

def makePrimitiveRoot (n : ℕ) (facs : List ℕ) : Except String ℕ :=
  go 2 where
  go (a : ℕ) : Except String ℕ :=
    if a.gcd n > 1 then .error s!"composite: found factor {a}" else
    if a < n then
      if powMod a (n - 1) n ≠ 1 then .error s!"composite: fails fermat test at {a}"
      else if testPrimitiveRoot n a facs
        then .ok a
        else go (a + 1)
    else .error "no primitive root found"

def factorList (n : ℕ) : List ℕ := Nat.primeFactorsList n

/-- The name under which the cached primality proof of `n` is stored. -/
def toName (n : ℕ) : Lean.Name := .mkStr4 "Tactic" "Prime" "Nat" (s!"prime_{n}")

end Tactic.Prime
