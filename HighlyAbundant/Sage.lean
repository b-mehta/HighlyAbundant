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

The search is an explicit-stack depth-first search: a single recursive function
`step` consuming a stack of `Frame`s (no mutual recursion, so it is easy to run
and to reason about). The frames are:

* `node target num minIdx` — a subproblem: look for a witness extending `num`
  using primes of index `≥ minIdx`. If `target ≤ 1` then `σ(num) ≥ σ(L)` already,
  so `num` is a witness iff `num < L`; otherwise expand it into a `wheel`.
* `wheel … front back lhs rhs` — choosing the next prime factor. We slide a window
  of consecutive primes `primes[front..back]`; since `σ(t)/t ≤ ∏_{p ∣ t} p/(p-1)`,
  a window can only yield a witness once `∏ p/(p-1) ≥ target/m` (`m = L/num`), and
  is hopeless once its product exceeds `m`. To avoid multiplying huge numbers we
  carry `lhs = (∏ p)·m` and `rhs = target·(∏ (p-1))`: feasibility is `lhs ≥ rhs`
  and the budget test is `lhs > m·m`. A feasible window emits an `exps` frame for
  its front prime and a `wheel` frame for the window with that prime dropped.
* `exps … p pk` — the exponents of the front prime `p`, with `pk = p^k`. It emits
  the child `node` for `num·p^k` and, unless `σ(p^k) ≥ target`, an `exps` frame for
  `k+1` (carrying `pk·p`, reusing `pk` so no power is recomputed).

Two finite resources keep everything terminating and self-certifying: a fixed
table of the first 100 primes (the search returns `none` if it would read past it)
and a `fuel` budget on the number of steps (`none` if it runs out). A `some _`
result therefore certifies that both sufficed, so neither bound has to be proved
correct in advance.

`highlyAbundantLcm? n` returns `some true` (highly abundant), `some false` (a
witness exists), or `none` (enlarge `primes` or `fuel`).
-/

namespace Sage

/-- The first 100 primes (up to 541). The search reads this only via `primes[i]?`,
returning `none` past the end, so its size never has to be assumed correct. -/
def primes : Array Nat := #[
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
    59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
    137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
    227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311,
    313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
    419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
    509, 521, 523, 541]

/-- A pending task in the depth-first search (see the module docstring). `B = L` is
fixed throughout, so it is not stored in frames. -/
inductive Frame where
  | node (target num minIdx : Nat)
  | wheel (target num m m2 front back lhs rhs : Nat)
  | exps (target num nextMinIdx m p pk : Nat)

/-- One step of the search. Returns `some true` if a witness exists, `some false`
if the stack empties with none found, and `none` if a resource (prime table or
`fuel`) is exhausted. Structurally recursive on `fuel`. -/
def step (B : Nat) : Nat → List Frame → Option Bool
  | 0, _ => none
  | _, [] => some false
  | fuel + 1, .node target num minIdx :: rest =>
    if target ≤ 1 then
      if num < B then some true else step B fuel rest
    else match primes[minIdx]? with
      | none => none
      | some p0 =>
        let m := B / num
        step B fuel (.wheel target num m (m * m) minIdx minIdx (p0 * m) (target * (p0 - 1)) :: rest)
  | fuel + 1, .wheel target num m m2 front back lhs rhs :: rest =>
    if front ≤ back then
      if lhs ≥ rhs then  -- feasible window: use front prime, keep sliding from front+1
        match primes[front]? with
        | none => none
        | some p =>
          step B fuel (.exps target num (front + 1) m p p ::
            .wheel target num m m2 (front + 1) back (lhs / p) (rhs / (p - 1)) :: rest)
      else  -- grow the window
        match primes[back + 1]? with
        | none => none
        | some q =>
          let lhs' := lhs * q
          if lhs' > m2 then step B fuel rest  -- over budget: this node has no witness
          else step B fuel (.wheel target num m m2 front (back + 1) lhs' (rhs * (q - 1)) :: rest)
    else  -- empty window (lhs = m, rhs = target): seed it with primes[front]
      match primes[front]? with
      | none => none
      | some q =>
        let lhs' := lhs * q
        if lhs' > m2 then step B fuel rest
        else step B fuel (.wheel target num m m2 front front lhs' (rhs * (q - 1)) :: rest)
  | fuel + 1, .exps target num nextMinIdx m p pk :: rest =>
    if pk > m then step B fuel rest  -- p^k > m: exponents of p exhausted
    else
      let spk := (pk * p - 1) / (p - 1)            -- σ(p^k), reusing pk (pk·p = p^(k+1))
      let target' := (target + spk - 1) / spk       -- ⌈target / σ(p^k)⌉
      let child : Frame := .node target' (num * pk) nextMinIdx
      if spk ≥ target then step B fuel (child :: rest)  -- larger exponents only enlarge num
      else step B fuel (child :: .exps target num nextMinIdx m p (pk * p) :: rest)

/-- A generous bound on the number of search steps; `none` is returned (rather than
a wrong answer) if it is ever too small. -/
def searchFuel : Nat := 1000000000

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
  if B ≤ 1 then some true else (step B searchFuel [.node sL 1 0]).map (!·)

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
