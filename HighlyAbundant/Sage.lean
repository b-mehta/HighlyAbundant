/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

/-!
# Decider for "is `lcm (1..n)` highly abundant?"

Following Alekseyev (<https://mathoverflow.net/q/501066>), code to search candidate
counterexamples `m < B` for `sL ≤ σ m`, taking `m` as a product of prime powers
in increasing-prime order. With `(B, sL) = (lcm (1..n), σ (lcm (1..n)))`, a
`some true` answer certifies that `lcm (1..n)` is highly abundant; correctness proofs
to that statement lives in `HighlyAbundant.SageSpec`.

A *node* is a triple `(target, num, minIdx)` representing the subproblem
"find `t ≥ 1` whose prime factors all sit at index `≥ minIdx` in `primes`, with
`num * t < B` and `target ≤ σ t`". The standing meaning is
`target = ⌈sL / σ num⌉` with `num` a product of prime powers at indices
`< minIdx`; multiplicativity of `σ` then reduces witness search at a node to
witness search at its children. `extend` slides a prime window for one node,
`expChildren` emits the prime-power children at one index, `children` collects
all children, and `step` runs a stack-machine over them.

`extend`, `children`, `step` are total: they read the table only through
`primes[i]?` (out-of-range ⟹ `none`) and recurse on `Nat` fuel that bottoms out
at `0` to `none`. So a `some _` result is valid for any sufficiently large
table and bound. The witness-set `W` and the correctness theorems against it
live in `HighlyAbundant.SageSpec`.
-/

namespace Sage

/-- The first 49 primes, `2` to `227`, in increasing order, read only through
`primes[i]?`. This is the least length for which `highlyAbundantLcm? B sL ≠ none`
on the `lcm (1..n)` inputs `(B, sL)` for all `n ≤ 172`; extend it for larger `n`. -/
def primes : Array Nat := #[
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
    59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
    137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
    227]

/-- Ceiling division `⌈a / b⌉`, equal to `(a + b - 1) / b` when `b ≠ 0`. -/
def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- Result of `extend`; see `extend` for the meaning of each case. -/
inductive Wheel where
  | exhaustedTable
  | tooLarge
  | window (back lhs rhs : Nat)

/-- Grow a prime window `[front, b]` to find the least `b ≥ back` with
`∏ primes[i] ≤ m` and `target * ∏ (primes[i] - 1) ≤ m * ∏ primes[i]`. Products
are threaded as `lhs` and `rhs`. Writing `Π b = ∏ i ∈ [front, b], primes[i]`
and `Π' b = ∏ i ∈ [front, b], (primes[i] - 1)`:

* call invariant: `m2 = m * m`, `fuel ≥ primes.size + 1 - back`, and either
  `front ≤ back` with `lhs = m * Π back`, `rhs = target * Π' back`, or
  `front = back + 1` (empty window) with `lhs = m`, `rhs = target`;
* `.window b lhs' rhs'`: the least such `b ≥ back`, with `lhs' = m * Π b` and
  `rhs' = target * Π' b`;
* `.tooLarge`: no such `b` exists with `Π b ≤ m` (equivalently, every
  `t ∈ P front` with `t ≤ m` has `σ t < target`);
* `.exhaustedTable`: a verdict would require reading past `primes.size`.

Recurses on `fuel` (kernel-reducible); equals `extendWF` when
`fuel ≥ primes.size + 1 - back`. -/
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

/-- Well-founded form of `extend` (same I/O spec). Recurses on `primes.size - back`
and reads `primes[i]` under `i < primes.size` instead of via `primes[i]?` + fuel.
Not used by the search; kept as the reference `extend` is proved against. -/
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

/-- Emit the nodes `(⌈target / σ(p^k)⌉, num * p^k, nextMinIdx)` for `k = 1, 2, …`
with `p^k ≤ m`, stopping after the first `k` with `σ(p^k) ≥ target`. Call
invariant: `pk = p ^ k` for the current `k ≥ 1`; `fuel` is at least the number
of such `k` (e.g. `m + 1`). Uses `σ(p^k) = (p^k * p - 1)/(p - 1)`. -/
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

/-- Iterate `extend` from index `front` onward, collecting `expChildren` of
`primes[i]` at every index `i ≥ front` where `extend` returns `.window`.
Returns `none` if any call needs an index `≥ primes.size`. Call invariant: the
`extend` invariant on `(m2, front, back, lhs, rhs)` with this `m, target`, and
`fuel ≥ primes.size + 1 - front`. Helper for `children`; equals `wheelChildrenWF`
when `fuel ≥ primes.size + 1 - front`. -/
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

/-- Well-founded form of `wheelChildren` (same spec). Recurses on
`primes.size - front` and uses `extendWF`. Not used by the search; kept as the
reference `wheelChildren` is proved against. -/
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

/-- Children of node `(target, num, minIdx)` (with `m = B / num`):
* `none` iff deciding the node would read an index `≥ primes.size`;
* `some cs` with each `c ∈ cs` of the form
  `(⌈target/σ(primes[i]^k)⌉, num*primes[i]^k, i+1)` for some `i ≥ minIdx`,
  `k ≥ 1`, `primes[i]^k ≤ m`. The node has a non-trivial witness iff some
  `c ∈ cs` has a witness (see `children_spec` in `SageSpec`).

The initial `wheelChildren` call seeds the range `[minIdx, minIdx]` directly
(`lhs = m * primes[minIdx]`, `rhs = target * (primes[minIdx] - 1)`), since the
empty-range state would underflow `back = minIdx - 1` at `minIdx = 0`. -/
def children (B target num minIdx : Nat) : Option (List (Nat × Nat × Nat)) :=
  match primes[minIdx]? with
  | none => none
  | some p0 =>
    let m := B / num
    wheelChildren (primes.size + 1) (m * m) m target num minIdx minIdx (p0 * m) (target * (p0 - 1)) []

/-- Upper bound on nodes visited by the search; `step` returns `none` if it is
too small, never a wrong answer. Experimentally minimal for which
`highlyAbundantLcm? B sL ≠ none` on the `lcm (1..n)` inputs for all `n ≤ 172`
(the hardest cases, `n = 169–172`, each visit 6.3M–6.4M nodes). -/
def searchFuel : Nat := 6400000

/-- Stack-machine witness search:
* `some true` ⟹ no node on `stack` has a witness;
* `some false` ⟹ some node on `stack` has a witness;
* `none` ⟹ `fuel` reached `0`, or `children` read an index `≥ primes.size`.

Popping the head `(target, num, minIdx)`: if `target ≤ 1`, `t = 1` is a witness
iff `num < B`; otherwise the non-trivial witnesses are those of its `children`,
which replace the head. Structural on `fuel`; no mutual recursion. -/
def step (B : Nat) : Nat → List (Nat × Nat × Nat) → Option Bool
  | 0, _ => none
  | _, [] => some true
  | fuel + 1, (target, num, minIdx) :: rest =>
    if target ≤ 1 then
      if num < B then some false else step B fuel rest   -- t = 1 is a witness iff num < B
    else match children B target num minIdx with
      | none => none
      | some cs => step B fuel (cs ++ rest)

/-- Decide whether no `m` with `1 ≤ m < B` has `sL ≤ σ m`:
* `some true` ⟹ no such `m`;
* `some false` ⟹ such an `m` exists;
* `none` ⟹ the prime table or `searchFuel` was too small.

With `(B, sL) = (lcm (1..n), σ (lcm (1..n)))`, `some true` certifies that
`lcm (1..n)` is highly abundant. -/
def highlyAbundantLcm? (B sL : Nat) : Option Bool :=
  if B ≤ 1 then some true else step B searchFuel [(sL, 1, 0)]

end Sage
