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
as products of prime powers over an increasing run of primes. Writing `num` for a
partial product (using primes below index `minIdx`) and `target = ⌈σ(L)/σ(num)⌉`
for the sum of divisors still required, a witness extending `num` is a `t` using
only primes of index `≥ minIdx` with `num·t < L` and `σ(t) ≥ target` (as `σ` is
multiplicative).

The search is a depth-first search over a stack of subproblems, driven by a single
self-recursive `step` (no mutual recursion). A *node* `(target, num, minIdx)`
stands for: find `t`, a product of prime powers using only primes of index
`≥ minIdx`, with `num·t < L` and `σ(t) ≥ target`; then `num·t` is a witness (since
`target = ⌈σ(L)/σ(num)⌉` makes `σ(t) ≥ target ↔ σ(num·t) ≥ σ(L)`).

* `children` expands one node into its child subproblems: for each front prime `p`
  the wheel deems feasible and each exponent `k ≥ 1` with `p^k ≤ m = L/num`, the
  child `(⌈target/σ(p^k)⌉, num·p^k, idx(p)+1)`, stopping the exponents once
  `σ(p^k) ≥ target`. Feasibility uses the wheel `extend`: slide a window of
  consecutive primes `primes[front..back]`; since `σ(t)/t ≤ ∏_{p ∣ t} p/(p-1)`,
  the window can only yield a witness once `∏ p/(p-1) ≥ target/m`, and yields none
  once `∏ p > m`. To avoid multiplying huge numbers `extend` carries
  `lhs = (∏ p)·m` and `rhs = target·(∏ (p-1))`: feasibility is `lhs ≥ rhs`, the
  budget test is `lhs > m·m`. (`σ(p^k) = (p^k·p − 1)/(p−1)` reuses `p^k`.)
* `step` pops a node: if `target ≤ 1` it is a witness iff `num < L` (the case
  `t = 1`); otherwise it pushes that node's `children` and continues. A stack thus
  denotes the union of its nodes' subtrees, and `step` answers whether any of them
  contains a witness — so independent subtrees can be verified separately and the
  results combined (`step (s₁ ++ s₂)` splits along `++`).

Two finite resources keep everything terminating and self-certifying: the prime
table (the search returns `none` if it would read past it) and the `fuel` bound on
the number of nodes (`none` if it runs out). A `some _` result certifies both
sufficed, so neither bound has to be proved correct in advance.

`highlyAbundantLcm? n` returns `some true` (highly abundant), `some false` (a
witness exists), or `none` (enlarge `primes` or `fuel`).
-/

namespace Sage

/-- The first 49 primes (up to 227). This is the shortest table for which every
known highly-abundant `L_n` (`n ≤ 172`) is decided: the search reads it only via
`primes[i]?` (returning `none` past the end), so it reports `none` rather than a
wrong answer if it would ever need more, and the table size never has to be
assumed correct. Enlarge it (e.g. with the rest of the first 100 primes) for
larger `n`. -/
def primes : Array Nat := #[
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
    59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
    137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
    227]

/-- The result of growing the wheel's prime window: it ran off the table, or its
product exceeded the budget (no witness down this branch), or it is feasible
(`primes[front..back]`, with `lhs = (∏ p)·m`, `rhs = target·(∏ (p-1))`). -/
inductive Wheel where
  | exhaustedTable
  | overBudget
  | window (back lhs rhs : Nat)

/-- Grow the window's right end until it is feasible (`lhs ≥ rhs`), reporting
`overBudget` once the product exceeds the budget (`∏ p > m`, tested `lhs > m·m`) or
`exhaustedTable` past the end of `primes`. `front` is unchanged, so not returned.
`fuel ≥ primes.size` always suffices (the window cannot exceed the table).
Structurally recursive on `fuel`, so it is a plain terminating helper, not part of
the search's recursion. -/
def extend (fuel m2 front back lhs rhs : Nat) : Wheel :=
  match fuel with
  | 0 => .exhaustedTable
  | fuel + 1 =>
    if front ≤ back then
      if lhs ≥ rhs then .window back lhs rhs
      else match primes[back + 1]? with
        | none => .exhaustedTable
        | some q =>
          let lhs' := lhs * q
          if lhs' > m2 then .overBudget else extend fuel m2 front (back + 1) lhs' (rhs * (q - 1))
    else  -- empty window (lhs = m, rhs = target): seed it with primes[front]
      match primes[front]? with
      | none => .exhaustedTable
      | some q =>
        let lhs' := lhs * q
        if lhs' > m2 then .overBudget else extend fuel m2 front front lhs' (rhs * (q - 1))

/-- Readable, well-founded twin of `extend`, written to make the algorithm clear:
it recurses directly on the window growing toward the end of the table
(`termination_by primes.size - back`) rather than on a fuel counter. It is the
specification `extend` implements — the two agree whenever `fuel ≥ primes.size`
(then `extend` never hits its `fuel = 0` case before this one hits the table edge).
`extend` is used by the search because the fuel form reduces in the kernel; this
form is here only to be read and to prove `extend` against. -/
def extendWF (m2 front back lhs rhs : Nat) : Wheel :=
  if front ≤ back then
    if lhs ≥ rhs then .window back lhs rhs
    else if h : back + 1 < primes.size then
      let q := primes[back + 1]
      let lhs' := lhs * q
      if lhs' > m2 then .overBudget else extendWF m2 front (back + 1) lhs' (rhs * (q - 1))
    else .exhaustedTable
  else  -- empty window (lhs = m, rhs = target): seed it with primes[front]
    if h : front < primes.size then
      let q := primes[front]
      let lhs' := lhs * q
      if lhs' > m2 then .overBudget else extendWF m2 front front lhs' (rhs * (q - 1))
    else .exhaustedTable
  termination_by primes.size - back
  decreasing_by all_goals omega

/-- Exponent children of the front prime `p` (`pk = p^k`, starting at `k = 1`):
for each `k ≥ 1` with `p^k ≤ m`, prepend the child `(⌈target/σ(p^k)⌉, num·p^k,
nextMinIdx)`, stopping once `σ(p^k) ≥ target`. Structural on `fuel` (`fuel ≥
⌊log_p m⌋ + 1` suffices; `m + 1` does). -/
def expChildren (fuel target num nextMinIdx m p pk : Nat)
    (acc : List (Nat × Nat × Nat)) : List (Nat × Nat × Nat) :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
    if pk > m then acc
    else
      let spk := (pk * p - 1) / (p - 1)              -- σ(p^k), reusing pk (pk·p = p^(k+1))
      let target' := (target + spk - 1) / spk         -- ⌈target / σ(p^k)⌉
      let acc := (target', num * pk, nextMinIdx) :: acc
      if spk ≥ target then acc
      else expChildren fuel target num nextMinIdx m p (pk * p) acc

/-- Accumulate the children of node `(target, num, minIdx)` (budget `m = B/num`):
the wheel `extend` slides over feasible front primes and each contributes its
`expChildren`. `none` if the prime table is exhausted. Structural on `fuel`
(`fuel ≥ primes.size` suffices). -/
def wheelChildren (fuel m2 m target num front back lhs rhs : Nat)
    (acc : List (Nat × Nat × Nat)) : Option (List (Nat × Nat × Nat)) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match extend (primes.size + 1) m2 front back lhs rhs with
    | .exhaustedTable => none
    | .overBudget => some acc
    | .window b lhs' rhs' =>
      match primes[front]? with
      | none => none
      | some p =>
        wheelChildren fuel m2 m target num (front + 1) b (lhs' / p) (rhs' / (p - 1))
          (expChildren (m + 1) target num (front + 1) m p p acc)

/-- The child subproblems of node `(target, num, minIdx)`: the `(prime, exponent)`
one-step extensions the search would explore. `none` iff a needed prime lies past
the table. This is the explicit subtree structure of the search. -/
def children (B target num minIdx : Nat) : Option (List (Nat × Nat × Nat)) :=
  match primes[minIdx]? with
  | none => none
  | some p0 =>
    let m := B / num
    wheelChildren (primes.size + 1) (m * m) m target num minIdx minIdx (p0 * m) (target * (p0 - 1)) []

/-- A generous bound on the number of nodes the search visits; `none` is returned
(rather than a wrong answer) if it is ever too small. -/
def searchFuel : Nat := 1000000000

/-- Depth-first search over a stack of node subproblems `(target, num, minIdx)`.
Returns `some true` if some node on the stack has a witness, `some false` if none
does (stack emptied), `none` if a resource (prime table or `fuel`) ran out.
Self-recursive and structural on `fuel`; `children` is a plain helper, so there is
no mutual recursion. -/
def step (B : Nat) : Nat → List (Nat × Nat × Nat) → Option Bool
  | 0, _ => none
  | _, [] => some false
  | fuel + 1, (target, num, minIdx) :: rest =>
    if target ≤ 1 then
      if num < B then some true else step B fuel rest   -- t = 1 is a witness iff num < B
    else match children B target num minIdx with
      | none => none
      | some cs => step B fuel (cs ++ rest)

/-- `(L_n, σ(L_n))`, from `L_n = ∏_{p ≤ n} p^{⌊log_p n⌋}`. -/
def lcmData (n : Nat) : Nat × Nat :=
  (primes.toList.takeWhile (· ≤ n)).foldl
    (fun (acc : Nat × Nat) p =>
      let e := Nat.log p n
      (acc.1 * p ^ e, acc.2 * ((p ^ (e + 1) - 1) / (p - 1)))) (1, 1)

/-- Whether `lcm(1..n)` is highly abundant: `some true` (yes), `some false` (no, a
witness exists), or `none` (a resource ran out — enlarge `primes` or `searchFuel`). -/
def highlyAbundantLcm? (n : Nat) : Option Bool :=
  let (B, sL) := lcmData n
  if B ≤ 1 then some true else (step B searchFuel [(sL, 1, 0)]).map (!·)

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
