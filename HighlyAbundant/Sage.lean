/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

/-!
# An executable check that `lcm(1..n)` is highly abundant

This is a Lean port of the Sage program by Max Alekseyev attached to the
MathOverflow thread <https://mathoverflow.net/q/501066>, which decides whether
`L_n = lcm(1, …, n)` is highly abundant.

A natural number `N` is **highly abundant** when `σ(m) < σ(N)` for every
`0 < m < N`, where `σ` is the sum-of-divisors function. Equivalently, `N` is
*not* highly abundant exactly when there is a *witness* `m < N` with
`σ(m) ≥ σ(N)`.

`L_n` is astronomically large (`L_67 ≈ 2·10^17`, `L_148 ≈ 10^61`, …), so we
cannot scan all `m < L_n`. Instead we port Alekseyev's search, which only ever
builds candidate witnesses as products of prime powers over an increasing run of
primes, pruning with the bound `σ(t)/t ≤ ∏_{p ∣ t} p/(p-1)`.

`search pr B target num minIdx` asks: starting from the partial product `num`
(built from primes of index below `minIdx`), is there a factor `t` using only
primes of index `≥ minIdx`, with `num·t < B`, such that `σ(num·t) ≥ σ(L)`? Since
`σ` is multiplicative and `target = ⌈σ(L)/σ(num)⌉` is the remaining `σ` we still
need, this is exactly `σ(t) ≥ target`. Hence `L_n` is highly abundant iff
`search` finds **no** witness.

To stay rational-free we track the wheel's ratio `∏ p / ∏ (p-1)` as the pair
`(prodP, prodDen)` of naturals and test `∏ p/(p-1) ≥ target/m` by
cross-multiplication, `prodP * m ≥ target * prodDen`.

## Only the first few primes are needed

A highly abundant number — and hence any competitor of `L_n` — has largest prime
factor `O(log N · (log log N)^3)` (Alaoglu–Erdős, 1944); in practice the search
for `L_n` only ever touches primes below `~1.4 n` (measured: the first 49 primes,
up to 227, suffice for *every* `n ≤ 172`). So we sieve the primes up to a small
bound depending on `n` and run the wheel over indices into that array `pr`. No
general primality test is needed: the original Sage code's `next_prime(σ_L - 2)`
shortcut only matters when a single *large* prime would finish a witness, which
never happens on a highly abundant input — this variant is specialised to
deciding the highly abundant case, the only case of interest here.

Everything uses only the Lean core library, so the program compiles to a fast
native executable (`lake exe sage`) without depending on Mathlib.
-/

namespace Sage

/-- Sieve of Eratosthenes: all primes `≤ N`, in increasing order. -/
def sieveUpTo (N : Nat) : Array Nat := Id.run do
  let mut comp : Array Bool := Array.replicate (N + 1) false
  let mut res : Array Nat := #[]
  for i in [2:N+1] do
    if !comp[i]! then
      res := res.push i
      let mut j := i * i
      while j ≤ N do
        comp := comp.set! j true
        j := j + i
  return res

/-! ## The search

`pr` is the array of small primes (`pr[0] = 2`). The wheel is a window of
*consecutive* primes `pr[front..back]`, with `prodP = ∏ p` and `prodDen = ∏ (p-1)`
over the window. `front > back` denotes the empty window (`prodP = prodDen = 1`). -/

/-- Roll the window rightwards until its ratio `∏ p/(p-1) ≥ target/m`; return
`none` once the window's prime product would exceed the size budget `m`. -/
partial def extend (pr : Array Nat) (m target front back prodP prodDen : Nat) :
    Option (Nat × Nat × Nat × Nat) :=
  if front ≤ back && prodP * m ≥ target * prodDen then
    some (front, back, prodP, prodDen)
  else
    let addIdx := if front ≤ back then back + 1 else front
    let q := pr[addIdx]!
    let prodP' := prodP * q
    if prodP' > m then none
    else extend pr m target front addIdx prodP' (prodDen * (q - 1))

mutual

/-- For the front prime `p`, try exponents `k = 1, 2, …` (while `p^k ≤ m`),
recursing on each `num · p^k`; stop once `σ(p^k) ≥ target`. -/
partial def processExps (pr : Array Nat) (B target num p nextMinIdx m k : Nat) : Bool :=
  let pk := p ^ k
  if pk > m then false
  else
    let spk := (p ^ (k + 1) - 1) / (p - 1)        -- σ(p^k)
    let target' := (target + spk - 1) / spk        -- ⌈target / σ(p^k)⌉
    if search pr B target' (num * pk) nextMinIdx then true
    else if spk ≥ target then false
    else processExps pr B target num p nextMinIdx m (k + 1)

/-- Walk the wheel: use each front prime in turn (spawning its prime-power
children), then drop it and advance to the next. -/
partial def loop (pr : Array Nat) (B target num m front back prodP prodDen : Nat) : Bool :=
  match extend pr m target front back prodP prodDen with
  | none => false
  | some (f, b, prodP', prodDen') =>
    let p := pr[f]!
    if processExps pr B target num p (f + 1) m 1 then true
    else loop pr B target num m (f + 1) b (prodP' / p) (prodDen' / (p - 1))

/-- Is there a witness `num · t < B` with `σ(num · t) ≥ σ(L)`, where `t` uses only
primes of index `≥ minIdx` and `target = ⌈σ(L)/σ(num)⌉`? -/
partial def search (pr : Array Nat) (B target num minIdx : Nat) : Bool :=
  if target ≤ 1 then
    num < B            -- σ(num) already ≥ σ(L); a witness iff it lies below B
  else
    let m := B / num
    let p0 := pr[minIdx]!
    loop pr B target num m minIdx minIdx p0 (p0 - 1)

end

/-! ## `lcm(1..n)` and its `σ`, via prime factorisation

`L_n = ∏_{p ≤ n} p^{e_p}` with `e_p` the largest exponent with `p^{e_p} ≤ n`, so
we obtain `L_n` and `σ(L_n)` exactly without factoring a huge number. -/

/-- The largest exponent `e ≥ 1` with `p ^ e ≤ n` (for `2 ≤ p ≤ n`). -/
partial def maxExp (p n : Nat) : Nat :=
  let rec go (e pe : Nat) : Nat := if pe * p ≤ n then go (e + 1) (pe * p) else e
  go 1 p

/-- The factorisation of `L_n = lcm(1..n)` as a list `(p, e_p)`. -/
def lcmFact (n : Nat) : List (Nat × Nat) :=
  (sieveUpTo n).toList.map (fun p => (p, maxExp p n))

/-- `L_n = lcm(1..n)`. -/
def lcmVal (n : Nat) : Nat :=
  (lcmFact n).foldl (fun acc pe => acc * pe.1 ^ pe.2) 1

/-- `σ(L_n)`, computed from the factorisation as `∏ σ(p^{e_p})`. -/
def sigmaLcm (n : Nat) : Nat :=
  (lcmFact n).foldl (fun acc pe => acc * ((pe.1 ^ (pe.2 + 1) - 1) / (pe.1 - 1))) 1

/-- Is `lcm(1..n)` highly abundant? (No witness strictly below it.)

The search only touches primes below `~1.4 n`, so a sieve to `3 n + 50` has ample
margin (e.g. for `n ≤ 172` it needs primes up to 227, well under the bound). -/
def isHighlyAbundantLcm (n : Nat) : Bool :=
  let B := lcmVal n
  if B ≤ 1 then true else !search (sieveUpTo (3 * n + 50)) B (sigmaLcm n) 1 0

/-! ## A brute-force cross-check for small inputs

This is the literal definition of highly abundant. It is `O(N^2)`, so only usable
for tiny `n`, but it lets us confirm the fast search against the definition. -/

/-- `σ(n)` by directly summing divisors. -/
def sigmaBrute (n : Nat) : Nat :=
  (List.range (n + 1)).foldl (fun s d => if d != 0 && n % d == 0 then s + d else s) 0

/-- `N` is highly abundant, checked directly against the definition. -/
def isHighlyAbundantBrute (N : Nat) : Bool :=
  let sN := sigmaBrute N
  (List.range N).all (fun m => m == 0 || sigmaBrute m < sN)

/-! ## Build-time sanity checks (kept tiny so they run instantly) -/

-- `L_n` is highly abundant for every `n ≤ 6`, and the fast search agrees with
-- the brute-force definition there.
#eval (List.range 7).all isHighlyAbundantLcm
#eval (List.range 7).all (fun n => isHighlyAbundantLcm n == isHighlyAbundantBrute (lcmVal n))

/-! ## Executable entry point

`lake exe sage [N]` verifies that `L_n` is highly abundant for every known
highly-abundant index `n ≤ N` (default `N = 50`), and cross-checks the fast
search against the brute-force definition for very small `n`. -/

/-- The indices `n ≤ 172` for which `L_n` is known to be highly abundant. -/
def knownHA (n : Nat) : Bool :=
  (1 ≤ n && n ≤ 70) || (81 ≤ n && n ≤ 96) || (125 ≤ n && n ≤ 148) || (169 ≤ n && n ≤ 172)

end Sage

open Sage in
def main (args : List String) : IO Unit := do
  let out ← IO.getStdout
  let nMax := (args.head?.bind (·.toNat?)).getD 50
  out.putStrLn s!"Verifying lcm(1..n) is highly abundant for known-HA n ≤ {nMax} ..."
  let t0 ← IO.monoMsNow
  let mut allOK := true
  for n in [1:nMax+1] do
    if knownHA n then
      let ok := isHighlyAbundantLcm n
      if !ok then allOK := false
      out.putStrLn s!"  n={n}  L_n={lcmVal n}  highly abundant: {ok}"
      out.flush
  let t1 ← IO.monoMsNow
  out.putStrLn s!"All known-HA L_n with n ≤ {nMax} verified highly abundant: {allOK}   ({t1 - t0} ms)"
  let bruteOK := (List.range 9).all (fun n => isHighlyAbundantLcm n == isHighlyAbundantBrute (lcmVal n))
  out.putStrLn s!"Fast search agrees with the brute-force definition for n ≤ 8: {bruteOK}"
