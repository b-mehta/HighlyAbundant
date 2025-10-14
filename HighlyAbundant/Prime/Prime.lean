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

example : Nat.Prime 7484205022627358832362038205823524567570018795761675368007 := by pratt
  [2, 3, 5, 7, 11, 13, 17, 23, 31, 37, 101, 227, 463, 557, 641, 797, 947, (1259, 2, [2, 17, 37]), (2393, 3, [2, 13, 23]), (3847, 5, [2, 3, 641]), (4787, 2, [2, 2393]), (5557, 2, [2, 3, 463]), (10949, 2, [2, 7, 17, 23]), (183871, 7, [2, 3, 5, 227]), (382589, 2, [2, 101, 947]), (722411, 2, [2, 5, 13, 5557]), (1444823, 5, [2, 722411]), (203421667, 3, [2, 3, 7, 1259, 3847]), (627053183, 5, [2, 7, 31, 1444823]), (64477539101, 2, [2, 5, 13, 797, 4787]), (120272246927083, 2, [2, 3, 10949, 203421667]), (249657031399073, 3, [2, 11, 64477539101]), (481088987708333, 2, [2, 120272246927083]), (1439421901384723, 2, [2, 3, 382589, 627053183]), (13073870015348242727214147396923554289, 3, [2, 37, 183871, 249657031399073, 481088987708333]), (7484205022627358832362038205823524567570018795761675368007, 3, [2, 3, 7, 17, 557, 1439421901384723, 13073870015348242727214147396923554289])]

example : Nat.Prime 21888242871839275222246405745257275088696311157297823662689037894645226208583 := by
  pratt [2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 67, 73, 89, (109, 6, [2, 3]), (127, 3, [2, 3, 7]), (229, 6, [2, 3, 19]), (233, 3, [2, 29]), (271, 6, [2, 3, 5]), (311, 17, [2, 5, 31]), (491, 2, [2, 5, 7]), (911, 17, [2, 5, 7, 13]), (983, 5, [2, 491]), (1231, 3, [2, 3, 5, 41]), (2221, 2, [2, 3, 5, 37]), (3557, 2, [2, 7, 127]), (3691, 2, [2, 3, 5, 41]), (4999, 3, [2, 3, 7, 17]), (5501, 2, [2, 5, 11]), (11003, 2, [2, 5501]), (13327, 3, [2, 3, 2221]), (327599, 19, [2, 19, 37, 233]), (1853641, 17, [2, 3, 5, 19, 271]), (4562087, 5, [2, 17, 109, 1231]), (173171039, 13, [2, 73, 89, 13327]), (405928799, 22, [2, 11, 3691, 4999]), (1263766531, 10, [2, 3, 5, 13, 911, 3557]), (11465965001, 3, [2, 5, 7, 327599]), (35385462869, 2, [2, 7, 1263766531]), (2480874801745591, 6, [2, 3, 5, 19, 41, 35385462869]), (13427688667394608761327070753331941386769, 17, [2, 3, 7, 11, 1853641, 4562087, 173171039, 2480874801745591]), (21888242871839275222246405745257275088696311157297823662689037894645226208583, 3, [2, 3, 13, 29, 67, 229, 311, 983, 11003, 405928799, 11465965001, 13427688667394608761327070753331941386769])]

example : Nat.Prime 57896044618658097711785492504343953926634992332820282019728792003956564819949 := by
  pratt [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 83, 97, (103, 5, [2, 3, 17]), (107, 2, [2, 53]), (127, 3, [2, 3, 7]), (131, 2, [2, 5, 13]), (173, 2, [2, 43]), (223, 3, [2, 3, 37]), (239, 7, [2, 7, 17]), (353, 3, [2, 11]), (419, 2, [2, 11, 19]), (479, 13, [2, 239]), (487, 3, [2, 3]), (991, 6, [2, 3, 5, 11]), (1723, 3, [2, 3, 7, 41]), (2437, 2, [2, 3, 7, 29]), (3727, 3, [2, 3, 23]), (4153, 5, [2, 3, 173]), (9463, 3, [2, 3, 19, 83]), (32573, 2, [2, 17, 479]), (37853, 2, [2, 9463]), (57467, 2, [2, 59, 487]), (65147, 2, [2, 32573]), (75707, 2, [2, 37853]), (132049, 26, [2, 3, 7, 131]), (430751, 17, [2, 5, 1723]), (569003, 2, [2, 7, 97, 419]), (1923133, 2, [2, 3, 43, 3727]), (8574133, 2, [2, 3, 7, 103, 991]), (2773320623, 5, [2, 2437, 569003]), (72106336199, 7, [2, 13, 2773320623]), (1919519569386763, 2, [2, 3, 7, 19, 47, 127, 8574133]), (31757755568855353, 10, [2, 3, 31, 107, 223, 4153, 430751]), (75445702479781427272750846543864801, 7, [2, 3, 5, 75707, 72106336199, 1919519569386763]), (74058212732561358302231226437062788676166966415465897661863160754340907, 2, [2, 3, 353, 57467, 132049, 1923133, 31757755568855353, 75445702479781427272750846543864801]), (57896044618658097711785492504343953926634992332820282019728792003956564819949, 2, [2, 3, 65147, 74058212732561358302231226437062788676166966415465897661863160754340907])]

example : Nat.Prime 726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439 := by
  pratt [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 59, 61, 67, 109, 137, 149, 151, 197, 223, 229, 271, 443, 463, 593, 613, 641, 727,
  (1481, 3, [2, 5, 37]),
  (1549, 2, [2, 3, 43]),
  (1979, 2, [2, 23, 43]),
  (2437, 2, [2, 3, 7, 29]),
  (2531, 2, [2, 5, 11, 23]),
  (2683, 2, [2, 3, 149]),
  (2963, 2, [2, 1481]),
  (6197, 2, [2, 1549]),
  (9749, 2, [2, 2437]),
  (17449, 14, [2, 3, 727]),
  (18287, 5, [2, 41, 223]),
  (47497, 5, [2, 3, 1979]),
  (116989, 10, [2, 3, 9749]),
  (189989, 2, [2, 47497]),
  (196687, 3, [2, 3, 7, 223]),
  (217003, 3, [2, 3, 59, 613]),
  (379979, 2, [2, 189989]),
  (411743, 10, [2, 29, 31, 229]),
  (1466449, 7, [2, 3, 137, 223]),
  (1609403, 2, [2, 23, 59, 593]),
  (2916841, 13, [2, 3, 5, 109, 223]),
  (6700417, 5, [2, 3, 17449]),
  (36753053, 2, [2, 7, 443, 2963]),
  (1255525949, 2, [2, 2683, 116989]),
  (1335912079, 6, [2, 3, 19, 31, 61, 6197]),
  (1764234391, 3, [2, 3, 5, 271, 217003]),
  (3402277943, 5, [2, 7, 151, 1609403]),
  (32061889897, 10, [2, 3, 1335912079]),
  (25136521679249, 3, [2, 7, 32061889897]),
  (97859369123353, 5, [2, 3, 67, 197, 271, 379979]),
  (34741861125639557, 13, [2, 7, 31, 463, 1764234391]),
  (36131535570665139281, 3, [2, 5, 13, 34741861125639557]),
  (1469495262398780123809, 17, [2, 3, 7, 223, 411743, 3402277943]),
  (167773885276849215533569, 17, [2, 3, 7, 2531, 97859369123353]),
  (596242599987116128415063, 5, [2, 37, 223, 36131535570665139281]),
  (37414057161322375957408148834323969, 23, [2, 3, 7, 36753053, 1255525949, 25136521679249]),
  (726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439, 7, [2, 641, 18287, 196687, 1466449, 2916841, 6700417, 1469495262398780123809, 167773885276849215533569, 596242599987116128415063, 37414057161322375957408148834323969])]
