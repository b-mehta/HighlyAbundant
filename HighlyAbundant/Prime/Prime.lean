/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import HighlyAbundant.Prime.Pratt
import Batteries.Tactic.NoMatch
import Lean.Message
import Mathlib.Tactic.NormNum.Prime

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

section

open Lean Elab Meta Tactic Qq

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

structure PrattProofEntry : Type where
  metaVar : Expr
  uses : Std.TreeSet ℕ
  pf : Expr
  deriving Repr

def processEntryAux (m : Std.TreeMap ℕ PrattProofEntry) (p p' root : ℕ) (pE rootE : Expr)
    (factors : List ℕ) :
    MetaM (ℕ × Std.TreeSet ℕ × Expr) := do
  let mut t : ℕ := 1
  let mut res : ℕ := p'
  -- cur * res = p'
  let mut pf ← mkAppM ``pratt_axiom #[pE, rootE]
  -- pf will be a proof of `pratt_predicate p root t`
  let mut uses : Std.TreeSet ℕ := ∅
  for q in factors do
    let (spare, k) := extractFactor res q -- r * q ^ k = res
    if k = 0 then logWarning m!"unused factor {q} in factorization {factors} of {p - 1}"
    let r := t
    t := t * q ^ k
    res := spare
    let tE : Expr := mkNatLit t
    let qE : Expr := mkNatLit q
    let o : ℕ := (p - 1) / q
    let oE : Expr := mkNatLit o
    let some entry := m.get? q | throwError s!"purported prime {q} not in certificate"
    let hpow ← Tactic.powMod.provePowModNe root o p 1 rootE oE pE (mkNatLit 1)
    pf ← mkAppM ``prove_prime_step #[pE, rootE, qE, oE, tE, mkNatLit r, mkNatLit k,
      ← mkEqRefl oE, entry.metaVar, ← mkEqRefl tE, hpow, pf]
    uses := insert q (uses.insertMany entry.uses)
  return (t, uses, pf)

section

open Command

syntax "mk_tiny_primes" num : command
elab_rules : command
  | `(mk_tiny_primes $j) => do
    let j := j.getNat
    for i in [2:j+1] do
      if Nat.Prime i then
        let nm := mkIdent (.mkStr2 "Nat" (s!"prime_{i}"))
        let cmd ← `(command| def $nm : Nat.Prime $(Syntax.mkNatLit i) := by norm_num)
        elabCommand cmd

mk_tiny_primes 1000

end

def toName (n : ℕ) : Name := .mkStr4 "Tactic" "Prime" "Nat" (s!"prime_{n}")

def processEntry (m : Std.TreeMap ℕ PrattProofEntry) :
    PrattEntry → MetaM (Std.TreeMap ℕ PrattProofEntry)
  | .small p => do
    unless p < 1000 ∧ Nat.Prime p do
      throwError "{p} is not a recognised small prime"
    let nm := toName p
    let mv ← mkFreshExprMVar
      (some (← mkAppM ``Nat.Prime #[mkNatLit p]))
      (userName := .mkSimple s!"prime_{p}")
    let pf := mkConst nm
    return insert (p, ⟨mv, ∅, pf⟩) m
  | .big p root factors => do
    unless p ≥ 2 do
      throwError "error 4"
    let p' : ℕ := p - 1
    let pE : Expr := mkNatLit p
    let p'E : Expr := mkNatLit p'
    let rootE : Expr := mkNatLit root
    let (last, uses, pf) ← processEntryAux m p (p - 1) root pE rootE factors
    unless last = p - 1 do
      throwError "bad factorization {factors} of {p - 1} (missing {(p - 1) / last})"
    let hpow ← Tactic.powMod.provePowModEq root p' p 1 rootE p'E pE
    let pf ← mkAppM ``prove_prime_end #[p'E, rootE, ← mkEqRefl pE, hpow, pf]
    let i ← mkFreshExprMVar
      (some (← mkAppM ``Nat.Prime #[pE]))
      (userName := .mkSimple s!"prime_{p}")
    return insert (p, ⟨i, uses, pf⟩) m

def prove_prime (cert : PrattCertificate) (n : ℕ) : MetaM Expr := do
  let data ← cert.foldlM processEntry ∅
  let some ent := data.get? n | throwError "the certificate doesn't prove {n} is prime"
  ent.uses.foldrM (init := ent.pf) fun q pf => do
    let some entq := data.get? q | throwError "internal error 1"
    entq.metaVar.mvarId! |>.assign entq.pf
    return pf

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

partial def makeNativeCertificate (n : ℕ) : MetaM MPrattCertificate := do
  if n < 100 then return .small n else
  let facs := (factorList (n - 1)).destutter (· ≠ ·)
  match makePrimitiveRoot n facs with
  | .ok a => return .big n a (← facs.mapM makeNativeCertificate)
  | .error e => throwError e

def makeCertificate (n : ℕ) : MetaM PrattCertificate := reformat <$> makeNativeCertificate n

syntax "prime" Parser.Tactic.optConfig ppSpace : tactic

def mkPrimalityProof (n : ℕ) : MetaM Expr := do
  let cert ← makeCertificate n
  prove_prime cert n

elab_rules : tactic
  | `(tactic| prime) => do
    liftMetaFinishingTactic fun goal ↦ do
      let t := (← goal.getType'').consumeMData
      let some nE := t.app1? ``Nat.Prime | throwError "goal for `prime` not a primality test"
      let some n := nE.nat? | throwError "not a numeral"
      let pf ← mkPrimalityProof n
      goal.assign pf

end

end Tactic.Prime

example : Nat.Prime 59 := by prime

example : Nat.Prime 214499 := by prime

example : Nat.Prime 6602975023 := by prime
example : Nat.Prime 6602975053 := by prime
example : Nat.Prime 6602975069 := by prime
example : Nat.Prime 8840291989 := by prime
example : Nat.Prime 8840292001 := by prime
example : Nat.Prime 8840292047 := by prime

--   divs := [6602975023, 6602975053, 6602975069]
--   divs := [8840291989, 8840292001, 8840292047]
