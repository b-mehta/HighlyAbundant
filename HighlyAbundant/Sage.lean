/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Nat.Log

/-!
# Deciding whether `lcm(1..n)` is highly abundant

`σ` denotes the sum-of-divisors function. `N` is *highly abundant* if `σ m < σ N`
for every `m` with `0 < m < N`. Hence `L = lcm(1..n)` is highly abundant iff there
is no `m` with `1 ≤ m < L` and `σ m ≥ σ L`.

Following Alekseyev (<https://mathoverflow.net/q/501066>) we search over numbers
written as products of prime powers, taking primes in increasing order. Notation
used throughout (and assuming `primes` lists the primes in increasing order, so
`primes[i]` is the `i`-th prime, `primes[0] = 2`):

* `P j := { t : ℕ | 1 ≤ t ∧ ∀ prime q, q ∣ t → primes[j] ≤ q }`
  (the naturals `≥ 1` all of whose prime factors have index `≥ j`; note `1 ∈ P j`).
* A *node* is a triple `(target, num, minIdx)`. Its *witness set* is
  `W target num minIdx := { t ∈ P minIdx | num * t < B ∧ target ≤ σ t }`,
  where `B = L`. Under the standing meaning `target = ⌈σ L / σ num⌉` with `num` a
  product of primes of index `< minIdx`, multiplicativity of `σ` gives
  `target ≤ σ t ↔ σ L ≤ σ (num * t)`, so each `t ∈ W target num minIdx` makes
  `num * t` an `m` with `1 ≤ m < L` and `σ L ≤ σ m`.

The pieces (full pre/postconditions are on each definition):

* `extend` examines the primes `primes[front], …` and decides, for the size limit
  `m`, whether some product of them can reach the required `σ`-ratio.
* `children` maps a node to a list `cs` of child nodes such that the node has a
  witness `t ≠ 1` iff some child in `cs` has a witness. (Every `t ∈ P minIdx` with
  `t ≠ 1` equals `primes[i]^k * t'` with `i ≥ minIdx` the index of its least prime
  factor, `k ≥ 1`, `t' ∈ P (i+1)`, and `target ≤ σ t ↔ ⌈target/σ(primes[i]^k)⌉ ≤
  σ t'`; the child for `(i,k)` is `(⌈target/σ(primes[i]^k)⌉, num*primes[i]^k, i+1)`.)
* `step` searches a list (used as a stack) of nodes: `some true` if every node on
  the list has an empty witness set, `some false` if some node has a witness,
  `none` if a limit is reached (exact postcondition on `step`). `step` runs one
  shared `fuel` over the whole list, so `step B f (s₁ ++ s₂)` is not determined
  by `step B f s₁` and `step B f s₂`; subtrees are combined through their witness
  sets `W`, not through `step` on appended lists. See *Partial verification*.

`extend`, `children`, `step` are total. They read the table only through
`primes[i]?`, so an index `≥ primes.size` yields the result `none` rather than a
wrong answer; and each recurses on a `Nat` that bounds its number of recursive
calls, yielding `none` at `0`. Thus a `some _` result is valid for any table
length and any sufficiently large bound.

## Partial verification

To prove `lcm (1..n)` highly abundant from results about subtrees (instead of one
evaluation of the whole search), let `(B, sL) = lcmData n` and assume `2 ≤ B`:

1. Evaluate `children B sL 1 0`. If it is `none`, enlarge `primes`. Otherwise it
   is `some cs`, and `cs` is the list of the root node's children.
2. For each `c ∈ cs`, obtain `step B searchFuel [c] = some true` (each is a
   separate, smaller evaluation). By the postcondition of `step`, this gives
   `W c.1 c.2.1 c.2.2 = ∅`.
3. `1 ∉ W sL 1 0`, because `σ 1 = 1 < sL`. The postcondition of `children`, negated,
   states `(∀ t ∈ W sL 1 0, t = 1) ↔ (∀ c ∈ cs, W c.1 c.2.1 c.2.2 = ∅)`; its right
   side holds by step 2, and `W sL 1 0 = ∅ ↔ (1 ∉ W sL 1 0 ∧ ∀ t ∈ W sL 1 0, t = 1)`,
   so `W sL 1 0 = ∅`.
4. `W sL 1 0 = ∅` is, by definition, `¬ ∃ m, 1 ≤ m ∧ m < B ∧ sL ≤ σ m`. With
   `B = lcm (1..n)` and `sL = σ B`, this is exactly: `lcm (1..n)` is highly abundant.

The only facts used are the postconditions of `step` and `children` stated below;
the full root is never evaluated.
-/

namespace Sage

/-- The first 49 primes, `2` to `227`, in increasing order, read only through
`primes[i]?`. This is the least length for which `highlyAbundantLcm? n ≠ none` for
all `n ≤ 172`; extend it for larger `n`. -/
def primes : Array Nat := #[
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
    59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
    137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
    227]

/-- Ceiling division `⌈a / b⌉`, equal to `(a + b - 1) / b` when `b ≠ 0`. -/
def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- Result of `extend` (its three cases are specified in `extend`).
* `window back lhs rhs`: the index `back` and the two products `lhs`, `rhs`.
* `tooLarge`: no admissible product of `primes[front], …` reaches the ratio.
* `exhaustedTable`: an index `≥ primes.size` was reached. -/
inductive Wheel where
  | exhaustedTable
  | tooLarge
  | window (back lhs rhs : Nat)

/-- Let `m, target` be the naturals with `m2 = m * m`, and for `front ≤ b` write
`Π b = ∏ i ∈ [front, b], primes[i]` and `Π' b = ∏ i ∈ [front, b], (primes[i] - 1)`.

Call invariant: `m2 = m * m`, `fuel ≥ primes.size + 1 - back`, and either
`front ≤ back` with `lhs = m * Π back` and `rhs = target * Π' back`, or
`front = back + 1` (the range is empty) with `lhs = m` and `rhs = target`.

Output, under the invariant:
* `window b lhs' rhs'`: `b` is the least index `≥ back` with `Π b ≤ m` and
  `target * Π' b ≤ m * Π b`; and `lhs' = m * Π b`, `rhs' = target * Π' b`.
* `tooLarge`: no index `b ≥ back` has both `Π b ≤ m` and `target * Π' b ≤ m * Π b`;
  equivalently `σ t < target` for every `t ∈ P front` with `t ≤ m`.
* `exhaustedTable`: deciding between the two above would read an index `≥
  primes.size`.

`front` is never changed, so it is not returned. `extend` is used by the search
because it recurses on `fuel` (a `Nat`), which reduces in the kernel. It equals
`extendWF` whenever `fuel ≥ primes.size + 1 - back`. -/
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
          if lhs' > m2 then .tooLarge else extend fuel m2 front (back + 1) lhs' (rhs * (q - 1))
    else  -- front = back + 1: the range is empty; start it at index front
      match primes[front]? with
      | none => .exhaustedTable
      | some q =>
        let lhs' := lhs * q
        if lhs' > m2 then .tooLarge else extend fuel m2 front front lhs' (rhs * (q - 1))

/-- Well-founded form of `extend` with the same input/output specification, written
to be read: it recurses on the index `back` increasing toward `primes.size`
(`termination_by primes.size - back`) and reads `primes[i]` under a proof `i <
primes.size` instead of via `primes[i]?` and a `fuel`. Not used by the search;
kept as the reference `extend` is proved against. The two are equal when
`fuel ≥ primes.size + 1 - back`. -/
def extendWF (m2 front back lhs rhs : Nat) : Wheel :=
  if front ≤ back then
    if lhs ≥ rhs then .window back lhs rhs
    else if h : back + 1 < primes.size then
      let q := primes[back + 1]
      let lhs' := lhs * q
      if lhs' > m2 then .tooLarge else extendWF m2 front (back + 1) lhs' (rhs * (q - 1))
    else .exhaustedTable
  else
    if h : front < primes.size then
      let q := primes[front]
      let lhs' := lhs * q
      if lhs' > m2 then .tooLarge else extendWF m2 front front lhs' (rhs * (q - 1))
    else .exhaustedTable
  termination_by primes.size - back
  decreasing_by all_goals omega

/-- Call invariant: `pk = p ^ k` for the current `k ≥ 1`, and `m`, `target`, `num`,
`nextMinIdx` are fixed. Returns the list of nodes `(⌈target / σ(p^k)⌉, num * p^k,
nextMinIdx)` for `k` running from its initial value upward, for each `k` with
`p^k ≤ m`, stopping after the first `k` with `σ(p^k) ≥ target`
(using `σ(p^k) = (p^k * p - 1)/(p - 1)`). `fuel` must be at least the number of
such `k` (e.g. `fuel = m + 1`). -/
def expChildren (fuel target num nextMinIdx m p pk : Nat) : List (Nat × Nat × Nat) :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    if pk > m then []
    else
      let spk := (pk * p - 1) / (p - 1)              -- σ(p^k); pk * p = p^(k+1)
      let child := (ceilDiv target spk, num * pk, nextMinIdx)
      if spk ≥ target then [child]
      else child :: expChildren fuel target num nextMinIdx m p (pk * p)

/-- Call invariant: the `extend` invariant for `(m2, front, back, lhs, rhs)` with
this `m` and `target`, and `fuel ≥ primes.size + 1 - front`. Returns `none` if
`extend` reaches an index `≥ primes.size`; otherwise returns `some` of the list
consisting of, for every index `i ≥ front` at which `extend` returns a `window`,
the `expChildren` of `primes[i]` (the nodes
`(⌈target/σ(primes[i]^k)⌉, num*primes[i]^k, i+1)` for `k ≥ 1` with `primes[i]^k ≤
m`, stopping after `σ(primes[i]^k) ≥ target`). Helper for `children`.
It equals `wheelChildrenWF` whenever `fuel ≥ primes.size + 1 - front`. -/
def wheelChildren (fuel m2 m target num front back lhs rhs : Nat)
    (acc : List (Nat × Nat × Nat)) : Option (List (Nat × Nat × Nat)) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match extend (primes.size + 1) m2 front back lhs rhs with
    | .exhaustedTable => none
    | .tooLarge => some acc
    | .window b lhs' rhs' =>
      match primes[front]? with
      | none => none
      | some p =>
        wheelChildren fuel m2 m target num (front + 1) b (lhs' / p) (rhs' / (p - 1))
          (expChildren (m + 1) target num (front + 1) m p p ++ acc)

/-- Well-founded form of `wheelChildren` with the same specification, written to be
read: it recurses on `primes.size - front` and uses `extendWF` instead of `extend`
with fuel. Not used by the search; kept as the reference `wheelChildren` is proved
against. The two are equal when `fuel ≥ primes.size + 1 - front`. -/
def wheelChildrenWF (m2 m target num front back lhs rhs : Nat) :
    Option (List (Nat × Nat × Nat)) :=
  if h : front ≥ primes.size then none
  else
    match extendWF m2 front back lhs rhs with
    | .exhaustedTable => none
    | .tooLarge => some []
    | .window b lhs' rhs' =>
      let p := primes[front]
      match wheelChildrenWF m2 m target num (front + 1) b (lhs' / p) (rhs' / (p - 1)) with
      | none => none
      | some rest => some (expChildren (m + 1) target num (front + 1) m p p ++ rest)
  termination_by primes.size - front
  decreasing_by omega

/-- The child nodes of node `(target, num, minIdx)` (with `m = B / num`):
* `children B target num minIdx = none` iff deciding the node would read an index
  `≥ primes.size`;
* `children B target num minIdx = some cs` with each `c ∈ cs` of the form
  `(⌈target/σ(primes[i]^k)⌉, num*primes[i]^k, i+1)` for some `i ≥ minIdx`, `k ≥ 1`
  with `primes[i]^k ≤ m`, such that
  `(∃ t ∈ W target num minIdx, t ≠ 1) ↔ (∃ c ∈ cs, W c.1 c.2.1 c.2.2 ≠ ∅)`.

The initial call to `wheelChildren` starts with the range [minIdx..minIdx] already
seeded (lhs = m * primes[minIdx], rhs = target * (primes[minIdx] - 1)), because
starting in the empty-range state would require `back = minIdx - 1`, which
underflows for `minIdx = 0`. -/
def children (B target num minIdx : Nat) : Option (List (Nat × Nat × Nat)) :=
  match primes[minIdx]? with
  | none => none
  | some p0 =>
    let m := B / num
    wheelChildren (primes.size + 1) (m * m) m target num minIdx minIdx (p0 * m) (target * (p0 - 1)) []

/-- A `Nat` at least the number of nodes the search visits; `step` returns `none`
if it is too small, never a wrong answer. Experimentally determined to be the
minimum value for which `highlyAbundantLcm? n ≠ none` for all `n ≤ 172` (the
hardest cases, n = 169–172, each visit between 6.3M and 6.4M nodes). -/
def searchFuel : Nat := 6400000

/-- Searches `stack`, a list of nodes, for a witness (`B = L`):
* `step B fuel stack = some true` ⟹ every `(target, num, minIdx) ∈ stack` has
  `W target num minIdx = ∅` (no witness exists);
* `step B fuel stack = some false` ⟹ some `(target, num, minIdx) ∈ stack` has
  `W target num minIdx ≠ ∅` (a witness exists);
* `step B fuel stack = none` ⟹ `fuel` reached `0`, or `children` read an index
  `≥ primes.size`.

Removing the head node `(target, num, minIdx)`: if `target ≤ 1` then `t = 1` is a
witness for it iff `num < B`; otherwise its witnesses with `t ≠ 1` are those of its
`children`, which replace it. Self-recursive and structural on `fuel`; `children`
does not call `step`, so there is no mutual recursion. -/
def step (B : Nat) : Nat → List (Nat × Nat × Nat) → Option Bool
  | 0, _ => none
  | _, [] => some true
  | fuel + 1, (target, num, minIdx) :: rest =>
    if target ≤ 1 then
      if num < B then some false else step B fuel rest   -- t = 1 is a witness iff num < B
    else match children B target num minIdx with
      | none => none
      | some cs => step B fuel (cs ++ rest)

/-- `lcmData n = (lcm (1..n), σ (lcm (1..n)))`, computed as
`(∏ p^{⌊log_p n⌋}, ∏ σ(p^{⌊log_p n⌋}))` over the primes `p ≤ n`. Correct for
`n ≤ 227` (so every prime `≤ n` is in the table). -/
def lcmData (n : Nat) : Nat × Nat :=
  (primes.toList.takeWhile (· ≤ n)).foldl
    (fun (acc : Nat × Nat) p =>
      let e := Nat.log p n
      (acc.1 * p ^ e, acc.2 * ((p ^ (e + 1) - 1) / (p - 1)))) (1, 1)

/-- Decides whether `lcm (1..n)` is highly abundant:
* `some true` ⟹ `lcm (1..n)` is highly abundant (no `m` with `1 ≤ m < L`,
  `σ L ≤ σ m`);
* `some false` ⟹ such an `m` exists;
* `none` ⟹ the table or `searchFuel` was too small (enlarge and retry). -/
def highlyAbundantLcm? (n : Nat) : Option Bool :=
  let (B, sL) := lcmData n
  if B ≤ 1 then some true else step B searchFuel [(sL, 1, 0)]

/-- The indices `n ≤ 172` for which `lcm (1..n)` is known to be highly abundant. -/
def knownHA (n : Nat) : Bool :=
  (1 ≤ n && n ≤ 70) || (81 ≤ n && n ≤ 96) || (125 ≤ n && n ≤ 148) || (169 ≤ n && n ≤ 172)

-- `lcm (1..n)` is highly abundant for every `n ≤ 12`.
#eval (List.range 13).all (highlyAbundantLcm? · == some true)

-- Isolate whether Nat.log is the kernel reduction blocker.
example : Nat.log 2 2 = 1 := by decide
-- Kernel reduction tests: `by decide` asks the kernel to reduce the closed term.
example : highlyAbundantLcm? 2 = some true := by decide
example : highlyAbundantLcm? 3 = some true := by decide
example : highlyAbundantLcm? 5 = some true := by decide

end Sage

open Sage in
/-- `lake exe sage n₁ n₂ …` prints `highlyAbundantLcm?` (with timing) for each given
`n`; with no arguments it does so for every known highly-abundant `n ≤ 50`. -/
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
