/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import HighlyAbundant.IsNotHA.Prime.Pratt
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

open Lean Elab

declare_syntax_cat pratt_certificate
declare_syntax_cat bpratt_certificate
declare_syntax_cat bpratt_entry

syntax bpratt_certificate : pratt_certificate
syntax "[" bpratt_entry,* "]" : bpratt_certificate
syntax num : bpratt_entry
syntax "(" num "," ppSpace num "," ppSpace "[" num,* "]" ")" : bpratt_entry

partial def PrattEntry.ofSyntax : TSyntax `bpratt_entry → MetaM PrattEntry
  | `(bpratt_entry| $n:num) => return .small n.getNat
  | `(bpratt_entry| ( $n:num, $root:num, [ $[$nums],* ] )) => do
      let n := n.getNat
      let root := root.getNat
      let nums := nums.map (·.getNat)
      return .big n root nums.toList
  | e => throwError "Invalid builder Pratt entry syntax {e}"

partial def PrattCertificate.ofSyntaxAux : TSyntax `bpratt_certificate → MetaM PrattCertificate
  | `(bpratt_certificate| [ $[$entries],* ] ) => do
    let entries ← entries.mapM PrattEntry.ofSyntax
    return entries.toList
  | e => throwError "Invalid builder Pratt certificate syntax {e}"

partial def PrattCertificate.ofSyntax : TSyntax `pratt_certificate → MetaM PrattCertificate
  | `(pratt_certificate| $n:bpratt_certificate) => PrattCertificate.ofSyntaxAux n
  | e => throwError "Invalid Pratt certificate syntax {e}"

partial def PrattEntry.toSyntax : PrattEntry → MetaM (TSyntax `bpratt_entry)
  | .small n => do
      let n := Lean.Syntax.mkNatLit n
      `(bpratt_entry| $n:num)
  | .big n root factors => do
      let n := Lean.Syntax.mkNatLit n
      let root := Lean.Syntax.mkNatLit root
      let factors := factors.toArray.map Lean.Syntax.mkNatLit
      `(bpratt_entry| ($n:num, $root:num, [ $[$factors],* ]))

partial def PrattCertificate.toSyntax (i : PrattCertificate) :
    MetaM (TSyntax `bpratt_certificate) := do
  let j ← i.toArray.mapM (·.toSyntax)
  `(bpratt_certificate| [ $[$j],* ] )

end


section

open Lean Elab Command

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

def processEntryAux (m : Std.TreeMap ℕ PrattProofEntry) (p p' : ℕ) (pE rootE : Expr)
    (factors : List ℕ) :
    MetaM (ℕ × Std.TreeSet ℕ × Expr) := do
  let mut t : ℕ := 1
  let mut res : ℕ := p'
  -- cur * res = p'
  let mut pf := mkApp2 (mkConst ``pratt_axiom) pE rootE
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
    let pf1 := mkApp7 (mkConst ``prove_prime_step) pE rootE qE oE tE (mkNatLit r) (mkNatLit k)
    pf := mkApp5 pf1 reflBoolTrue entry.metaVar reflBoolTrue reflBoolFalse pf
    uses := insert q (uses.insertMany entry.uses)
  return (t, uses, pf)

def toName (n : ℕ) : Name := .mkStr4 "Tactic" "Prime" "Nat" (s!"prime_{n}")

def processEntry (m : Std.TreeMap ℕ PrattProofEntry) :
    PrattEntry → MetaM (Std.TreeMap ℕ PrattProofEntry)
  | .small p => do
    if p ∈ m then return m
    unless p < 1000 ∧ Nat.Prime p do
      throwError "{p} is not a recognised small prime"
    let nm := toName p
    let mv ← mkFreshExprMVar
      (some (mkApp (mkConst ``Nat.Prime) (mkNatLit p)))
      (userName := .mkSimple s!"prime_{p}")
    let pf := mkConst nm
    return insert (p, ⟨mv, ∅, pf⟩) m
  | .big p root factors => do
    if p ∈ m then return m
    unless p ≥ 2 do
      throwError "error 4"
    let p' : ℕ := p - 1
    let pE : Expr := mkNatLit p
    let p'E : Expr := mkNatLit p'
    let rootE : Expr := mkNatLit root
    let (last, uses, pf) ← processEntryAux m p (p - 1) pE rootE factors
    unless last = p - 1 do
      throwError "bad factorization {factors} of {p - 1} (missing {(p - 1) / last})"
    let pf := mkApp6 (mkConst ``prove_prime_end) pE p'E rootE reflBoolTrue pf reflBoolTrue
    let i ← mkFreshExprMVar
      (some (mkApp (mkConst ``Nat.Prime) (mkNatLit p)))
      (userName := .mkSimple s!"prime_{p}")
    return insert (p, ⟨i, uses, pf⟩) m

def prove_prime (cert : PrattCertificate) (n : ℕ) : MetaM Expr := do
  let data ← cert.foldlM processEntry ∅
  let some ent := data.get? n | throwError "the certificate doesn't prove {n} is prime"
  ent.uses.foldrM (init := ent.pf) fun q pf => do
    let some entq := data.get? q | throwError "internal error 1"
    -- let e ← mkLetFVars #[entq.metaVar] pf (binderInfoForMVars := .default)
    -- return mkApp e entq.pf
    entq.metaVar.mvarId! |>.assign entq.pf
    return pf

elab "pratt" ppSpace certificate:pratt_certificate : tactic => liftMetaFinishingTactic fun goal ↦ do
  match certificate with
  | `(pratt_certificate| $cert:pratt_certificate) =>
    let cert ← PrattCertificate.ofSyntax cert
    let t := (← goal.getType'').consumeMData
    let some nE := t.app1? ``Nat.Prime | throwError "goal for `pratt` not a primality test"
    let some n := nE.nat? | throwError "not a numeral"
    let pf ← prove_prime cert n
    goal.assign pf

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

def mkCachedPrimalityProof (n : ℕ) : TacticM Expr := do
  let e ← getEnv
  let nm := toName n
  bif e.constants.contains nm then
    return mkConst nm
  else
    throwError s!"cached proof for {n} not found"

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
