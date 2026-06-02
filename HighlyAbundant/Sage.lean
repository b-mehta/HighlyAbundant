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

`search B target num minIdx` asks: starting from the partial product `num` (built
from primes of index below `minIdx`), is there a factor `t` using only primes of
index `≥ minIdx`, with `num·t < B`, such that `σ(num·t) ≥ σ(L)`? Since `σ` is
multiplicative and `target = ⌈σ(L)/σ(num)⌉` is the remaining `σ` we still need,
this is exactly `σ(t) ≥ target`. Hence `L_n` is highly abundant iff `search`
finds **no** witness.

To stay rational-free we track the wheel's ratio `∏ p / ∏ (p-1)` as the pair
`(prodP, prodDen)` of naturals and test `∏ p/(p-1) ≥ target/m` by
cross-multiplication, `prodP * m ≥ target * prodDen`.

## Only the first few primes are needed

A highly abundant number — and hence any competitor of `L_n` — has largest prime
factor `O(log N · (log log N)^3)` (Alaoglu–Erdős, 1944); in practice the search
for `L_n` only ever touches primes below `~1.4 n` (measured: the first 49 primes,
up to 227, suffice for *every* `n ≤ 172`). So instead of any primality test we
just keep a short hard-coded table `primes` of the first 100 primes (up to 541)
and run the wheel over indices into it. This supports `n` up to roughly `380`,
covering the whole known highly-abundant range `n ≤ 172` with plenty of room.

Everything uses only the Lean core library, so the program compiles to a fast
native executable (`lake exe sage`) without depending on Mathlib.
-/

namespace Sage

/-- The first 100 primes (up to 541). Every prime the search touches for the
supported range (`n ≲ 380`) lies in this table. -/
def primes : Array Nat := #[
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
    59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
    137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
    227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311,
    313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
    419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
    509, 521, 523, 541]

/-! ## The search

The wheel is a window of *consecutive* primes `primes[front..back]`. Within one
search node `m` and `target` are fixed, so rather than recompute the big products
`prodP·m` and `target·prodDen` on every window step we carry them and update them
incrementally by small factors:

* `lhs = prodP · m`   (`prodP = ∏ p` over the window),
* `rhs = target · prodDen`   (`prodDen = ∏ (p-1)`),

with the empty window being `prodP = prodDen = 1`, i.e. `lhs = m`, `rhs = target`.
The feasibility test `∏ p/(p-1) ≥ target/m` is then just `lhs ≥ rhs`, and the size
test `prodP > m` is `lhs > m²` (passing `m2 = m·m`). Every per-step update is a
multiplication by a tiny prime, never a product of two huge numbers. -/

/-- Roll the window rightwards until it is feasible (`lhs ≥ rhs`); return `none`
once the window's prime product would exceed the budget (`lhs > m2`, i.e.
`prodP > m`) or the prime table is exhausted (never, within the supported range).

Total: each step moves the window's right end strictly rightward, stopping at the
end of `primes`. -/
def extend (m2 front back lhs rhs : Nat) : Option (Nat × Nat × Nat × Nat) :=
  if h2 : front ≤ back then
    if lhs ≥ rhs then
      some (front, back, lhs, rhs)                 -- feasible window
    else if h : back + 1 < primes.size then
      let q := primes[back + 1]
      let lhs' := lhs * q
      if lhs' > m2 then none                        -- prodP·m > m² ⟺ prodP > m
      else extend m2 front (back + 1) lhs' (rhs * (q - 1))
    else none
  else                                              -- empty window (lhs = m, rhs = target)
    if h : front < primes.size then
      let q := primes[front]
      let lhs' := lhs * q
      if lhs' > m2 then none
      else extend m2 front front lhs' (rhs * (q - 1))
    else none
  termination_by primes.size - back
  decreasing_by all_goals omega

mutual

/-- For the front prime `p`, try exponents `k = 1, 2, …` (while `p^k ≤ m`),
recursing on each `num · p^k`; stop once `σ(p^k) ≥ target`.

`partial`: termination is the genuine content of the search (the remaining
`target` strictly drops on each recursive `search`), which is not structural, so
we do not prove it here — this is an executable check, not a verified lemma. -/
partial def processExps (B target num p nextMinIdx m k : Nat) : Bool :=
  let pk := p ^ k
  if pk > m then false
  else
    let spk := (p ^ (k + 1) - 1) / (p - 1)        -- σ(p^k)
    let target' := (target + spk - 1) / spk        -- ⌈target / σ(p^k)⌉
    if search B target' (num * pk) nextMinIdx then true
    else if spk ≥ target then false
    else processExps B target num p nextMinIdx m (k + 1)

/-- Walk the wheel: use each front prime in turn (spawning its prime-power
children), then drop it and advance to the next. -/
partial def loop (B target num m m2 front back lhs rhs : Nat) : Bool :=
  match extend m2 front back lhs rhs with
  | none => false
  | some (f, b, lhs', rhs') =>
    let p := primes[f]!
    if processExps B target num p (f + 1) m 1 then true
    else loop B target num m m2 (f + 1) b (lhs' / p) (rhs' / (p - 1))

/-- Is there a witness `num · t < B` with `σ(num · t) ≥ σ(L)`, where `t` uses only
primes of index `≥ minIdx` and `target = ⌈σ(L)/σ(num)⌉`? -/
partial def search (B target num minIdx : Nat) : Bool :=
  if target ≤ 1 then
    num < B            -- σ(num) already ≥ σ(L); a witness iff it lies below B
  else
    let m := B / num
    let p0 := primes[minIdx]!
    -- seed the one-prime window {p0}: lhs = p0·m, rhs = target·(p0-1), m2 = m²
    loop B target num m (m * m) minIdx minIdx (p0 * m) (target * (p0 - 1))

end

/-! ## `lcm(1..n)` and its `σ`, via prime factorisation

`L_n = ∏_{p ≤ n} p^{e_p}` with `e_p = ⌊log_p n⌋` the largest exponent with
`p^{e_p} ≤ n`, so we get `L_n` and `σ(L_n)` exactly without factoring. -/

/-- The largest exponent `e` with `p ^ e ≤ n` (i.e. `⌊log_p n⌋`), for `2 ≤ p`. -/
def maxExp (p n : Nat) : Nat := Id.run do
  let mut e := 0
  let mut pe := 1
  while pe * p ≤ n do
    pe := pe * p
    e := e + 1
  return e

/-- `(L_n, σ(L_n))` computed together from the factorisation of `L_n = lcm(1..n)`. -/
def lcmData (n : Nat) : Nat × Nat :=
  (primes.toList.takeWhile (· ≤ n)).foldl
    (fun (acc : Nat × Nat) p =>
      let e := maxExp p n
      (acc.1 * p ^ e, acc.2 * ((p ^ (e + 1) - 1) / (p - 1)))) (1, 1)

/-- `L_n = lcm(1..n)`. -/
def lcmVal (n : Nat) : Nat := (lcmData n).1

/-- Is `lcm(1..n)` highly abundant? (No witness strictly below it.) -/
def isHighlyAbundantLcm (n : Nat) : Bool :=
  let (B, sL) := lcmData n
  if B ≤ 1 then true else !search B sL 1 0

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
