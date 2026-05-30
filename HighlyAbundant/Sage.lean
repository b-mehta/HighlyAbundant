/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

/-!
# An executable check that `lcm(1..n)` is highly abundant

This is a direct, deliberately *simple* Lean port of the Sage program by
Max Alekseyev attached to the MathOverflow thread
<https://mathoverflow.net/q/501066>, which decides whether `L_n = lcm(1, …, n)`
is highly abundant.

A natural number `N` is **highly abundant** when `σ(m) < σ(N)` for every
`0 < m < N`, where `σ` is the sum-of-divisors function. Equivalently, `N` is
*not* highly abundant exactly when there is a *witness* `m < N` with
`σ(m) ≥ σ(N)`.

`L_n` is astronomically large (`L_67 ≈ 2·10^17`, `L_148 ≈ 10^61`, …), so we
cannot scan all `m < L_n`. Instead we port Alekseyev's search, which only ever
builds candidate witnesses as products of prime powers over an increasing run of
primes, pruning with the bound `σ(t)/t ≤ ∏_{p ∣ t} p/(p-1)`.

`search B target num minp` asks: starting from the partial product `num` (built
from primes `< minp`), is there a factor `t` using only primes `≥ minp`, with
`num·t < B`, such that `σ(num·t) ≥ σ(L)`?  Since `σ` is multiplicative and
`target = ⌈σ(L)/σ(num)⌉` is the remaining `σ` we still need, this is exactly
`σ(t) ≥ target`. Hence `L_n` is highly abundant iff `search` finds **no** witness.

The single shortcut Alekseyev describes is included: a prime `q ≥ σ_L - 1`
satisfies `σ(q) = q + 1 ≥ σ_L`, so `num·q` is an immediate witness whenever it
is `< B`; this is the `just_any = True` variant, which stops at the first witness.
(We do not implement the parallelism or the rolling-deque micro-optimisation in
the original — efficiency is not the point here, readability is.)

To stay rational-free we track the wheel's ratio `∏ p / ∏ (p-1)` as the pair
`(prodP, prodDen)` of naturals and test `∏ p/(p-1) ≥ target/m` by
cross-multiplication, `prodP * m ≥ target * prodDen`.

Everything uses only the Lean core library, so the program compiles to a fast
native executable (`lake exe sage`) without depending on Mathlib. Run-time grows
quickly with `n` (the candidate trees and the big integers both grow), so this is
intended for sanity-checking small `n`; `lake exe sage 50` verifies every highly
abundant `L_n` with `n ≤ 50` in a few seconds.
-/

namespace Sage

/-! ## Primality and primes

We use Miller–Rabin so that primality of the huge values of `σ(L_n)` is cheap;
the chosen bases make it deterministic well beyond the sizes that occur here. -/

/-- `a ^ b mod n`. -/
partial def powMod (a b n : Nat) : Nat :=
  if b == 0 then 1 % n
  else
    let h := powMod (a * a % n) (b / 2) n
    if b % 2 == 1 then h * a % n else h

/-- Write `m = d · 2^r` with `d` odd, returning `(d, r)` (starting from `r`). -/
partial def factor2 (m r : Nat) : Nat × Nat :=
  if m % 2 == 0 then factor2 (m / 2) (r + 1) else (m, r)

/-- The square-and-check half of one Miller–Rabin round. -/
partial def mrSquare (n x i : Nat) : Bool :=
  if i == 0 then false
  else
    let x2 := x * x % n
    if x2 == n - 1 then true else mrSquare n x2 (i - 1)

/-- One Miller–Rabin round for base `a`, where `n - 1 = d · 2^r` with `d` odd. -/
def mrPass (n d r a : Nat) : Bool :=
  let x := powMod a d n
  if x == 1 || x == n - 1 then true else mrSquare n x (r - 1)

/-- Deterministic Miller–Rabin with the bases below: this is correct for all
`n < 3.3·10^24`, comfortably past the sizes used here. -/
def isPrime (n : Nat) : Bool :=
  if n < 2 then false
  else if n == 2 || n == 3 then true
  else if n % 2 == 0 then false
  else
    let (d, r) := factor2 (n - 1) 0
    [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37].all (fun a => a % n == 0 || mrPass n d r a)

/-- The smallest prime strictly greater than `n`. -/
partial def nextPrime (n : Nat) : Nat :=
  if isPrime (n + 1) then n + 1 else nextPrime (n + 1)

/-- The smallest prime `≥ n`. -/
def nextPrimeGE (n : Nat) : Nat :=
  if n ≤ 2 then 2 else if isPrime n then n else nextPrime n

/-! ## The search -/

/-- Roll the wheel of consecutive primes (the window `P`, with `prodP = ∏ p` and
`prodDen = ∏ (p-1)`, `lastP` the largest prime seen) until its ratio
`∏ p/(p-1) ≥ target/m`. Returns `none` when the window product already exceeds the
size budget `m` (no candidate can lie down this branch). -/
partial def extend (m target : Nat) :
    List Nat → Nat → Nat → Nat → Option (List Nat × Nat × Nat × Nat)
  | P, prodP, prodDen, lastP =>
    if !P.isEmpty && prodP * m ≥ target * prodDen then
      some (P, prodP, prodDen, lastP)
    else
      let q := nextPrime lastP
      let prodP' := prodP * q
      if prodP' > m then none
      else extend m target (P ++ [q]) prodP' (prodDen * (q - 1)) q

mutual

/-- For the front prime `p`, try exponents `k = 1, 2, …` (while `p^k ≤ m`),
recursing on each `num · p^k`. We stop once `σ(p^k) ≥ target`, since larger
exponents only yield larger candidates. -/
partial def processExps (B target num p nextMinp m k : Nat) : Bool :=
  let pk := p ^ k
  if pk > m then false
  else
    let spk := (p ^ (k + 1) - 1) / (p - 1)        -- σ(p^k)
    let target' := (target + spk - 1) / spk        -- ⌈target / σ(p^k)⌉
    if search B target' (num * pk) nextMinp then true
    else if spk ≥ target then false
    else processExps B target num p nextMinp m (k + 1)

/-- Walk the wheel: use each front prime in turn (spawning its prime-power
children), then drop it and advance to the next. -/
partial def loop (B target num m : Nat) :
    List Nat → Nat → Nat → Nat → Bool
  | P, prodP, prodDen, lastP =>
    match extend m target P prodP prodDen lastP with
    | none => false
    | some (P', prodP', prodDen', lastP') =>
      match P' with
      | [] => false   -- unreachable: `extend` returns a nonempty window
      | p :: rest =>
        let nextMinp := match rest with | [] => nextPrime p | q :: _ => q
        if processExps B target num p nextMinp m 1 then true
        else loop B target num m rest (prodP' / p) (prodDen' / (p - 1)) lastP'

/-- Is there a witness `num · t < B` with `σ(num · t) ≥ σ(L)`, where `t` uses only
primes `≥ minp` and `target = ⌈σ(L)/σ(num)⌉`? -/
partial def search (B target num minp : Nat) : Bool :=
  if target ≤ 1 then
    num < B            -- σ(num) already ≥ σ(L); a witness iff it lies below B
  else
    let m := B / num
    -- Shortcut: the prime `q ≥ max(minp, target-1)` has `σ(q) = q+1 ≥ target`,
    -- so `num · q` is a witness as soon as it is below `B`.
    let q := if target - 1 > minp then nextPrimeGE (target - 1) else minp
    if num * q < B then true
    else loop B target num m [minp] minp (minp - 1) minp

end

/-! ## `lcm(1..n)` and its `σ`, via prime factorisation

`L_n = ∏_{p ≤ n} p^{e_p}` with `e_p` the largest exponent with `p^{e_p} ≤ n`, so
we obtain `L_n` and `σ(L_n)` exactly without factoring a huge number. -/

/-- The primes `≤ n`. -/
def primesUpTo (n : Nat) : List Nat :=
  (List.range (n + 1)).filter isPrime

/-- The largest exponent `e ≥ 1` with `p ^ e ≤ n` (for `2 ≤ p ≤ n`). -/
partial def maxExp (p n : Nat) : Nat :=
  let rec go (e pe : Nat) : Nat := if pe * p ≤ n then go (e + 1) (pe * p) else e
  go 1 p

/-- The factorisation of `L_n = lcm(1..n)` as a list `(p, e_p)`. -/
def lcmFact (n : Nat) : List (Nat × Nat) :=
  (primesUpTo n).map (fun p => (p, maxExp p n))

/-- `L_n = lcm(1..n)`. -/
def lcmVal (n : Nat) : Nat :=
  (lcmFact n).foldl (fun acc pe => acc * pe.1 ^ pe.2) 1

/-- `σ(L_n)`, computed from the factorisation as `∏ σ(p^{e_p})`. -/
def sigmaLcm (n : Nat) : Nat :=
  (lcmFact n).foldl (fun acc pe => acc * ((pe.1 ^ (pe.2 + 1) - 1) / (pe.1 - 1))) 1

/-- Is `lcm(1..n)` highly abundant? (No witness strictly below it.) -/
def isHighlyAbundantLcm (n : Nat) : Bool :=
  let B := lcmVal n
  if B ≤ 1 then true else !search B (sigmaLcm n) 1 2

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
highly-abundant index `n ≤ N` (default `N = 40`), and cross-checks the fast
search against the brute-force definition for very small `n`. -/

/-- The indices `n ≤ 172` for which `L_n` is known to be highly abundant. -/
def knownHA (n : Nat) : Bool :=
  (1 ≤ n && n ≤ 70) || (81 ≤ n && n ≤ 96) || (125 ≤ n && n ≤ 148) || (169 ≤ n && n ≤ 172)

end Sage

open Sage in
def main (args : List String) : IO Unit := do
  let out ← IO.getStdout
  let nMax := (args.head?.bind (·.toNat?)).getD 40
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
