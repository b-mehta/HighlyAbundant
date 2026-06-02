/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Nat.Log

/-!
# Deciding whether `lcm(1..n)` is highly abundant

`N` is *highly abundant* if `σ(m) < σ(N)` for every `0 < m < N`, where `σ` is the
sum of divisors. So `L = lcm(1..n)` fails to be highly abundant exactly when some
`m < L` has `σ(m) ≥ σ(L)`; we call such an `m` a *witness*.

`L` is enormous, so we cannot scan `m < L`. Following Alekseyev
(<https://mathoverflow.net/q/501066>) we hunt for a witness by building candidates
as products of prime powers over an increasing run of primes. Writing `num` for
the partial product (using primes below index `minIdx`) and `target = ⌈σ(L)/σ(num)⌉`
for the sum of divisors still required, a witness extending `num` is a `t` using
only primes of index `≥ minIdx` with `num·t < L` and `σ(t) ≥ target` (as `σ` is
multiplicative). `search` looks for one.

Two ingredients keep the search finite:

* **The wheel.** For the next prime factor we consider a window of consecutive
  primes `primes[front..back]`. Since `σ(t)/t ≤ ∏_{p ∣ t} p/(p-1)`, such a window
  can only produce a witness once `∏ p/(p-1) ≥ target/m` with `m = L/num`; we grow
  the window until that holds and abandon the branch once the window's own product
  exceeds `m`. To avoid multiplying huge numbers we carry the scaled products
  `lhs = (∏ p)·m` and `rhs = target·(∏ (p-1))`, so the feasibility test is just
  `lhs ≥ rhs` and the budget test is `lhs > m·m`.

* **A fixed prime table.** Every prime a witness can use is small (the largest
  prime factor of a highly abundant number is `O(log N · (log log N)³)`,
  Alaoglu–Erdős 1944; empirically `< 1.4 n`). We keep the first 100 primes, and
  rather than *prove* the table always suffices, the search returns `none` the
  moment it would need a prime beyond it. A result of `some _` is then a
  self-contained certificate that the table was large enough for that run, so no
  size bound need be assumed.

`highlyAbundantLcm? n` returns `some true` (highly abundant), `some false` (a
witness exists), or `none` (the table was too small — enlarge `primes`).

Every definition is total, so the search can be reasoned about; the intended
soundness theorem is `highlyAbundantLcm? n = some true → IsHighlyAbundant L`.
Depends only on `Mathlib.Data.Nat.Log`.
-/

namespace Sage

/-- The first 100 primes (up to 541). The search reports `none` if it ever needs a
prime beyond this table, so its size never has to be assumed correct. -/
def primes : Array Nat := #[
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
    59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
    137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
    227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311,
    313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
    419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
    509, 521, 523, 541]

/-- The outcome of growing the wheel's prime window. -/
inductive Wheel where
  /-- Needed a prime beyond `primes`; the search is inconclusive. -/
  | exhaustedTable
  /-- The window's prime product exceeded the budget `m`: this branch has no
  witness (a sound "no"). -/
  | overBudget
  /-- A feasible window `primes[front..back]`, with `lhs = (∏ p)·m`,
  `rhs = target·(∏ (p-1))`. -/
  | window (back lhs rhs : Nat)

/-- Grow the window's right end until it is feasible (`lhs ≥ rhs`), reporting
`overBudget` if the window product first exceeds `m` (tested as `lhs > m·m`, i.e.
`∏ p > m`), or `exhaustedTable` if it runs off the end of `primes`. `front` is
unchanged so it is not returned. -/
def extend (m2 front back lhs rhs : Nat) : Wheel :=
  if h2 : front ≤ back then
    if lhs ≥ rhs then .window back lhs rhs
    else if h : back + 1 < primes.size then
      let q := primes[back + 1]
      let lhs' := lhs * q
      if lhs' > m2 then .overBudget else extend m2 front (back + 1) lhs' (rhs * (q - 1))
    else .exhaustedTable
  else  -- empty window (lhs = m, rhs = target): seed it with primes[front]
    if h : front < primes.size then
      let q := primes[front]
      let lhs' := lhs * q
      if lhs' > m2 then .overBudget else extend m2 front front lhs' (rhs * (q - 1))
    else .exhaustedTable
  termination_by primes.size - back
  decreasing_by all_goals omega

/-! The three search functions are mutually recursive and total. Each returns
`Option Bool`: `some true` = a witness exists, `some false` = no witness,
`none` = the prime table was too small to decide. Termination uses the
lexicographic measure `(primes.size - primeIndex, phase, fuel)`: the prime index
strictly advances on the deep recursion, the `phase` tag (`search 1`, `loop 0`,
`processExps 2`) orders same-index edges, and `fuel = ⌊log_p m⌋ + 1` bounds the
exponent loop. -/

/-- A uniform bound on the exponent of any prime in any candidate `≤ B`: since
every prime is `≥ 2`, `p^k ≤ B` forces `k ≤ ⌊log₂ B⌋`. Computing this once (from
the fixed `B`) lets `processExps` take it as fuel without recomputing a logarithm
of a huge number on every wheel step. -/
@[inline] def expBound (B : Nat) : Nat := Nat.log 2 B + 1

mutual

/-- Try exponents `k = 1, 2, …` of the front prime `p` (while `p^k ≤ m`), recursing
on each `num · p^k`; stop once `σ(p^k) ≥ target`. `fb = expBound B` is the constant
fuel that bounds this loop and is forwarded to `search`. -/
def processExps (B target num p nextMinIdx m fb fuel k : Nat) : Option Bool :=
  if fuel = 0 then none
  else
    let pk := p ^ k
    if pk > m then some false
    else
      let spk := (p ^ (k + 1) - 1) / (p - 1)        -- σ(p^k)
      let target' := (target + spk - 1) / spk        -- ⌈target / σ(p^k)⌉
      match search B target' (num * pk) nextMinIdx fb with
      | none => none
      | some true => some true
      | some false =>
        if spk ≥ target then some false
        else processExps B target num p nextMinIdx m fb (fuel - 1) (k + 1)
  termination_by (primes.size - nextMinIdx, 2, fuel)

/-- Use each front prime of the wheel in turn, then drop it and advance. -/
def loop (B target num m m2 front back lhs rhs fb : Nat) : Option Bool :=
  match extend m2 front back lhs rhs with
  | .exhaustedTable => none
  | .overBudget => some false
  | .window b lhs' rhs' =>
    if hf : front < primes.size then
      let p := primes[front]
      match processExps B target num p (front + 1) m fb fb 1 with
      | none => none
      | some true => some true
      | some false => loop B target num m m2 (front + 1) b (lhs' / p) (rhs' / (p - 1)) fb
    else none
  termination_by (primes.size - front, 0, 0)

/-- Is there a witness `num · t < B` with `σ(num · t) ≥ σ(L)`, where `t` uses only
primes of index `≥ minIdx` and `target = ⌈σ(L)/σ(num)⌉`? `fb = expBound B`. -/
def search (B target num minIdx fb : Nat) : Option Bool :=
  if target ≤ 1 then
    some (decide (num < B))   -- σ(num) ≥ σ(L) already; `num` is a witness iff `num < B`
  else if h : minIdx < primes.size then
    let m := B / num
    let p0 := primes[minIdx]
    -- seed the one-prime window {p0}: lhs = p0·m, rhs = target·(p0-1), budget m2 = m²
    loop B target num m (m * m) minIdx minIdx (p0 * m) (target * (p0 - 1)) fb
  else none
  termination_by (primes.size - minIdx, 1, 0)

end

/-- `(L_n, σ(L_n))`, from `L_n = ∏_{p ≤ n} p^{⌊log_p n⌋}`. -/
def lcmData (n : Nat) : Nat × Nat :=
  (primes.toList.takeWhile (· ≤ n)).foldl
    (fun (acc : Nat × Nat) p =>
      let e := Nat.log p n
      (acc.1 * p ^ e, acc.2 * ((p ^ (e + 1) - 1) / (p - 1)))) (1, 1)

/-- Whether `lcm(1..n)` is highly abundant: `some true` (yes), `some false` (no,
a witness exists), or `none` (the prime table was too small — enlarge `primes`). -/
def highlyAbundantLcm? (n : Nat) : Option Bool :=
  let (B, sL) := lcmData n
  if B ≤ 1 then some true else (search B sL 1 0 (expBound B)).map (!·)

/-- Indices `n ≤ 172` for which `L_n` is known to be highly abundant. -/
def knownHA (n : Nat) : Bool :=
  (1 ≤ n && n ≤ 70) || (81 ≤ n && n ≤ 96) || (125 ≤ n && n ≤ 148) || (169 ≤ n && n ≤ 172)

-- Sanity: `L_n` is highly abundant for every `n ≤ 12`.
#eval (List.range 13).all (highlyAbundantLcm? · == some true)

end Sage

open Sage in
/-- `lake exe sage n₁ n₂ …` reports `highlyAbundantLcm?` (with timing) for each
given `n`; with no arguments it checks every known highly-abundant `n ≤ 50`. -/
def main (args : List String) : IO Unit := do
  let out ← IO.getStdout
  let ns := if args.isEmpty then (List.range 51).filter knownHA else args.filterMap (·.toNat?)
  for n in ns do
    let t0 ← IO.monoMsNow
    let r := highlyAbundantLcm? n
    out.putStr s!"  n={n}  highly abundant: {r}"   -- forces `r` before reading the clock
    out.flush
    let t1 ← IO.monoMsNow
    out.putStrLn s!"   ({t1 - t0} ms)"
