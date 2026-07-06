/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import Lean.Data.RArray

/-!
# Decider for "is `lcm (1..n)` highly abundant?"

Following Alekseyev (<https://mathoverflow.net/q/501066>), searches for `m < B`
with `sL ≤ σ m` as products of prime powers in increasing-prime order. With
`(B, sL) = (lcm (1..n), σ (lcm (1..n)))`, a `some true` answer certifies that
`lcm (1..n)` is highly abundant. Correctness lives in `HighlyAbundant.SageSpec`.
-/

namespace Sage

/-- The first 49 primes, `2` to `227`. Read only through `primes[i]?` so the
table can be extended for larger `n` without invalidating proofs. -/
def primes : Array Nat := #[
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
    59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
    137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
    227]

def primesRArray : Lean.RArray Nat :=
  .branch (nat_lit 24)
    (.branch (nat_lit 12)
      (.branch (nat_lit 6)
        (.branch (nat_lit 3)
          (.branch (nat_lit 1) (.leaf (nat_lit 2)) (.branch (nat_lit 2) (.leaf (nat_lit 3)) (.leaf (nat_lit 5))))
          (.branch (nat_lit 4) (.leaf (nat_lit 7)) (.branch (nat_lit 5) (.leaf (nat_lit 11)) (.leaf (nat_lit 13)))))
        (.branch (nat_lit 9)
          (.branch (nat_lit 7) (.leaf (nat_lit 17)) (.branch (nat_lit 8) (.leaf (nat_lit 19)) (.leaf (nat_lit 23))))
          (.branch (nat_lit 10) (.leaf (nat_lit 29)) (.branch (nat_lit 11) (.leaf (nat_lit 31)) (.leaf (nat_lit 37))))))
      (.branch (nat_lit 18)
        (.branch (nat_lit 15)
          (.branch (nat_lit 13) (.leaf (nat_lit 41)) (.branch (nat_lit 14) (.leaf (nat_lit 43)) (.leaf (nat_lit 47))))
          (.branch (nat_lit 16) (.leaf (nat_lit 53)) (.branch (nat_lit 17) (.leaf (nat_lit 59)) (.leaf (nat_lit 61)))))
        (.branch (nat_lit 21)
          (.branch (nat_lit 19) (.leaf (nat_lit 67)) (.branch (nat_lit 20) (.leaf (nat_lit 71)) (.leaf (nat_lit 73))))
          (.branch (nat_lit 22) (.leaf (nat_lit 79)) (.branch (nat_lit 23) (.leaf (nat_lit 83)) (.leaf (nat_lit 89)))))))
    (.branch (nat_lit 36)
      (.branch (nat_lit 30)
        (.branch (nat_lit 27)
          (.branch (nat_lit 25) (.leaf (nat_lit 97)) (.branch (nat_lit 26) (.leaf (nat_lit 101)) (.leaf (nat_lit 103))))
          (.branch (nat_lit 28) (.leaf (nat_lit 107)) (.branch (nat_lit 29) (.leaf (nat_lit 109)) (.leaf (nat_lit 113)))))
        (.branch (nat_lit 33)
          (.branch (nat_lit 31) (.leaf (nat_lit 127)) (.branch (nat_lit 32) (.leaf (nat_lit 131)) (.leaf (nat_lit 137))))
          (.branch (nat_lit 34) (.leaf (nat_lit 139)) (.branch (nat_lit 35) (.leaf (nat_lit 149)) (.leaf (nat_lit 151))))))
      (.branch (nat_lit 42)
        (.branch (nat_lit 39)
          (.branch (nat_lit 37) (.leaf (nat_lit 157)) (.branch (nat_lit 38) (.leaf (nat_lit 163)) (.leaf (nat_lit 167))))
          (.branch (nat_lit 40) (.leaf (nat_lit 173)) (.branch (nat_lit 41) (.leaf (nat_lit 179)) (.leaf (nat_lit 181)))))
        (.branch (nat_lit 45)
          (.branch (nat_lit 43) (.leaf (nat_lit 191)) (.branch (nat_lit 44) (.leaf (nat_lit 193)) (.leaf (nat_lit 197))))
          (.branch (nat_lit 47)
            (.branch (nat_lit 46) (.leaf (nat_lit 199)) (.leaf (nat_lit 211)))
            (.branch (nat_lit 48) (.leaf (nat_lit 223)) (.leaf (nat_lit 227)))))))

theorem primesRArray_get_eq_primes_get (i : Nat) (hi : i < 49) :
    primesRArray.get i = primes[i] := by
  change primesRArray[i] = primes[i]
  decide +kernel +revert

/-- Ceiling division `⌈a / b⌉`, equal to `(a + b - 1) / b` when `b ≠ 0`. -/
def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- Result of `extend`. -/
inductive Wheel where
  | exhaustedTable
  | tooLarge
  | window (back lhs rhs : Nat)

/-- Grow a prime window from `back` forward, threading `lhs = m * ∏ primes[i]`
and `rhs = target * ∏ (primes[i] - 1)`. Returns `.window b lhs' rhs'` at the least
`b ≥ back` with `lhs ≥ rhs`; `.tooLarge` if the next prime would push `lhs > m2`;
`.exhaustedTable` if fuel or the table runs out. -/
def extend (fuel m2 front back lhs rhs : Nat) : Wheel :=
  match fuel with
  | 0 => .exhaustedTable
  | fuel + 1 =>
    if front ≤ back then
      if lhs ≥ rhs then .window back lhs rhs
      else if back + 1 < 49 then
        let q := primesRArray.get (back + 1)
        let lhs' := lhs * q
        if lhs' > m2 then .tooLarge else extend fuel m2 front (back + 1) lhs' (rhs * (q - 1))
      else .exhaustedTable
    else  -- front = back + 1: the range is empty; start it at index front
      if front < 49 then
        let q := primesRArray.get front
        let lhs' := lhs * q
        if lhs' > m2 then .tooLarge else extend fuel m2 front front lhs' (rhs * (q - 1))
      else .exhaustedTable

/-- Well-founded form of `extend`. Not used by the search; kept as a spec-level
reference equivalent to `extend` when fuel is sufficient. -/
def extendWF (m2 front back lhs rhs : Nat) : Wheel :=
  if front ≤ back then
    if lhs ≥ rhs then .window back lhs rhs
    else if back + 1 < 49 then
      let q := primesRArray.get (back + 1)
      let lhs' := lhs * q
      if lhs' > m2 then .tooLarge else extendWF m2 front (back + 1) lhs' (rhs * (q - 1))
    else .exhaustedTable
  else
    if front < 49 then
      let q := primesRArray.get front
      let lhs' := lhs * q
      if lhs' > m2 then .tooLarge else extendWF m2 front front lhs' (rhs * (q - 1))
    else .exhaustedTable
  termination_by 49 - back
  decreasing_by all_goals omega

/-- Emit children `(⌈target / σ(p^k)⌉, num * p^k, next)` for `k ≥ 1` with
`p^k ≤ m`, stopping after the first `k` with `σ(p^k) ≥ target`. -/
def expChildren (fuel target num next m p pk : Nat) : List (Nat × Nat × Nat) :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    if pk > m then []
    else
      let spk := (pk * p - 1) / (p - 1)              -- σ(p^k); pk * p = p^(k+1)
      let child := (ceilDiv target spk, num * pk, next)
      if spk ≥ target then [child]
      else child :: expChildren fuel target num next m p (pk * p)

/-- Iterate `extend` from `front` onward, collecting `expChildren` at every
`.window` index. Returns `none` if an index `≥ 49` is read. -/
def wheelChildren (fuel m2 m target num front back lhs rhs : Nat)
    (acc : List (Nat × Nat × Nat)) : Option (List (Nat × Nat × Nat)) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match extend 50 m2 front back lhs rhs with
    | .exhaustedTable => none
    | .tooLarge => some acc
    | .window b lhs' rhs' =>
      if front < 49 then
        let p := primesRArray.get front
        wheelChildren fuel m2 m target num (front + 1) b (lhs' / p) (rhs' / (p - 1))
          (expChildren (m + 1) target num (front + 1) m p p ++ acc)
      else none

/-- Well-founded form of `wheelChildren`. Not used by the search; kept as a
spec-level reference. -/
def wheelChildrenWF (m2 m target num front back lhs rhs : Nat) :
    Option (List (Nat × Nat × Nat)) :=
  if front ≥ 49 then none
  else
    match extendWF m2 front back lhs rhs with
    | .exhaustedTable => none
    | .tooLarge => some []
    | .window b lhs' rhs' =>
      let p := primesRArray.get front
      match wheelChildrenWF m2 m target num (front + 1) b (lhs' / p) (rhs' / (p - 1)) with
      | none => none
      | some rest => some (rest ++ expChildren (m + 1) target num (front + 1) m p p)
  termination_by 49 - front
  decreasing_by omega

/-- Children of node `(target, num, minIdx)` with `m = B / num`. Each `c ∈ cs` is
`(⌈target/σ(primes[i]^k)⌉, num * primes[i]^k, i + 1)` for some `i ≥ minIdx` and
`k ≥ 1` with `primes[i]^k ≤ m`. Returns `none` if the search needs an index
`≥ 49`. -/
def children (B target num minIdx : Nat) : Option (List (Nat × Nat × Nat)) :=
  if minIdx < 49 then
    let p0 := primesRArray.get minIdx
    let m := B / num
    wheelChildren 50 (m * m) m target num minIdx minIdx (p0 * m) (target * (p0 - 1)) []
  else none

/-- Upper bound on nodes visited by `step`. Experimentally minimal for
`highlyAbundantLcm? B sL ≠ none` on `lcm (1..n)` for `n ≤ 172`. -/
def searchFuel : Nat := 6400000

/-- Stack-machine witness search. `some true`: no node on `stack` has a witness.
`some false`: some node has a witness. `none`: fuel exhausted or `children` read
an index `≥ 49`. -/
def step (B : Nat) : Nat → List (Nat × Nat × Nat) → Option Bool
  | 0, _ => none
  | _, [] => some true
  | fuel + 1, (target, num, minIdx) :: rest =>
    if target ≤ 1 then
      if num < B then some false else step B fuel rest   -- t = 1 is a witness iff num < B
    else match children B target num minIdx with
      | none => none
      | some cs => step B fuel (cs ++ rest)

/-- Decide whether no `m` with `1 ≤ m < B` has `sL ≤ σ m`. With
`(B, sL) = (lcm (1..n), σ (lcm (1..n)))`, `some true` certifies that
`lcm (1..n)` is highly abundant. -/
def highlyAbundantLcm? (B sL : Nat) : Option Bool :=
  if B ≤ 1 then some true else step B searchFuel [(sL, 1, 0)]

end Sage
