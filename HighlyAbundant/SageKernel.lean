/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.Sage

/-!
# Kernel-friendly versions of the decider functions

These mirror the definitions in `HighlyAbundant.Sage` but are written using
`Nat.rec`, `Bool.rec`, `Nat.ble`, `Nat.blt`, etc. — primitives the kernel can
reduce without unfolding `Decidable` instances. Equivalence with the original
definitions lives in `HighlyAbundant.SageKernelEquiv`.
-/

namespace Sage

/-- Ceiling division `⌈a / b⌉`, equal to `(a + b - 1) / b` when `b ≠ 0`. -/
def ceilDivK (a b : Nat) : Nat := ((a.add b).sub 1).div b

/-- Grow a prime window from `back` forward, threading `lhs = m * ∏ primes[i]`
and `rhs = target * ∏ (primes[i] - 1)`. Returns `.window b lhs' rhs'` at the least
`b ≥ back` with `lhs ≥ rhs`; `.tooLarge` if the next prime would push `lhs > m2`;
`.exhaustedTable` if fuel or the table runs out. -/
noncomputable def extendK (fuel m2 front : Nat) : Nat → Nat → Nat → Wheel :=
  fuel.rec (fun _ _ _ ↦ .exhaustedTable) fun _ r back lhs rhs ↦
    (front.ble back).rec
      ((front.ble 48).rec .exhaustedTable <|
        let q := primesRArray.get front
        let lhs' := lhs.mul q
        (m2.blt lhs').rec (r front lhs' (rhs.mul (q.sub 1))) .tooLarge)
      ((rhs.ble lhs).rec
        ((back.ble 47).rec .exhaustedTable <|
          let q := primesRArray.get back.succ
          let lhs' := lhs.mul q
          (m2.blt lhs').rec (r back.succ lhs' (rhs.mul (q.sub 1))) .tooLarge)
        (.window back lhs rhs))

  -- match fuel with
  -- | 0 => .exhaustedTable
  -- | fuel + 1 =>
  --   if front ≤ back then
  --     if lhs ≥ rhs then .window back lhs rhs
  --     else if back + 1 < 49 then
  --       let q := primesRArray.get (back + 1)
  --       let lhs' := lhs * q
  --       if lhs' > m2 then .tooLarge else extend fuel m2 front (back + 1) lhs' (rhs * (q - 1))
  --     else .exhaustedTable
  --   else  -- front = back + 1: the range is empty; start it at index front
  --     if front < 49 then
  --       let q := primesRArray.get front
  --       let lhs' := lhs * q
  --       if lhs' > m2 then .tooLarge else extend fuel m2 front front lhs' (rhs * (q - 1))
  --     else .exhaustedTable

-- /-- Well-founded form of `extend`. Not used by the search; kept as a spec-level
-- reference equivalent to `extend` when fuel is sufficient. -/
-- def extendWF (m2 front back lhs rhs : Nat) : Wheel :=
--   if front ≤ back then
--     if lhs ≥ rhs then .window back lhs rhs
--     else if back + 1 < 49 then
--       let q := primesRArray.get (back + 1)
--       let lhs' := lhs * q
--       if lhs' > m2 then .tooLarge else extendWF m2 front (back + 1) lhs' (rhs * (q - 1))
--     else .exhaustedTable
--   else
--     if front < 49 then
--       let q := primesRArray.get front
--       let lhs' := lhs * q
--       if lhs' > m2 then .tooLarge else extendWF m2 front front lhs' (rhs * (q - 1))
--     else .exhaustedTable
--   termination_by 49 - back
--   decreasing_by all_goals omega
--
-- /-- Emit children `(⌈target / σ(p^k)⌉, num * p^k, next)` for `k ≥ 1` with
-- `p^k ≤ m`, stopping after the first `k` with `σ(p^k) ≥ target`. -/
-- def expChildren (fuel target num next m p pk : Nat) : List (Nat × Nat × Nat) :=
--   match fuel with
--   | 0 => []
--   | fuel + 1 =>
--     if pk > m then []
--     else
--       let spk := (pk * p - 1) / (p - 1)              -- σ(p^k); pk * p = p^(k+1)
--       let child := (ceilDiv target spk, num * pk, next)
--       if spk ≥ target then [child]
--       else child :: expChildren fuel target num next m p (pk * p)
--
-- /-- Iterate `extend` from `front` onward, collecting `expChildren` at every
-- `.window` index. Returns `none` if an index `≥ 49` is read. -/
-- def wheelChildren (fuel m2 m target num front back lhs rhs : Nat)
--     (acc : List (Nat × Nat × Nat)) : Option (List (Nat × Nat × Nat)) :=
--   match fuel with
--   | 0 => none
--   | fuel + 1 =>
--     match extend 50 m2 front back lhs rhs with
--     | .exhaustedTable => none
--     | .tooLarge => some acc
--     | .window b lhs' rhs' =>
--       if front < 49 then
--         let p := primesRArray.get front
--         wheelChildren fuel m2 m target num (front + 1) b (lhs' / p) (rhs' / (p - 1))
--           (expChildren (m + 1) target num (front + 1) m p p ++ acc)
--       else none
--
-- /-- Well-founded form of `wheelChildren`. Not used by the search; kept as a
-- spec-level reference. -/
-- def wheelChildrenWF (m2 m target num front back lhs rhs : Nat) :
--     Option (List (Nat × Nat × Nat)) :=
--   if front ≥ 49 then none
--   else
--     match extendWF m2 front back lhs rhs with
--     | .exhaustedTable => none
--     | .tooLarge => some []
--     | .window b lhs' rhs' =>
--       let p := primesRArray.get front
--       match wheelChildrenWF m2 m target num (front + 1) b (lhs' / p) (rhs' / (p - 1)) with
--       | none => none
--       | some rest => some (rest ++ expChildren (m + 1) target num (front + 1) m p p)
--   termination_by 49 - front
--   decreasing_by omega
--
-- /-- Children of node `(target, num, minIdx)` with `m = B / num`. Each `c ∈ cs` is
-- `(⌈target/σ(primes[i]^k)⌉, num * primes[i]^k, i + 1)` for some `i ≥ minIdx` and
-- `k ≥ 1` with `primes[i]^k ≤ m`. Returns `none` if the search needs an index
-- `≥ 49`. -/
-- def children (B target num minIdx : Nat) : Option (List (Nat × Nat × Nat)) :=
--   if minIdx < 49 then
--     let p0 := primesRArray.get minIdx
--     let m := B / num
--     wheelChildren 50 (m * m) m target num minIdx minIdx (p0 * m) (target * (p0 - 1)) []
--   else none
--
-- /-- Upper bound on nodes visited by `step`. Experimentally minimal for
-- `highlyAbundantLcm? B sL ≠ none` on `lcm (1..n)` for `n ≤ 172`. -/
-- def searchFuel : Nat := 6400000
--
-- /-- Stack-machine witness search. `some true`: no node on `stack` has a witness.
-- `some false`: some node has a witness. `none`: fuel exhausted or `children` read
-- an index `≥ 49`. -/
-- def step (B : Nat) : Nat → List (Nat × Nat × Nat) → Option Bool
--   | 0, _ => none
--   | _, [] => some true
--   | fuel + 1, (target, num, minIdx) :: rest =>
--     if target ≤ 1 then
--       if num < B then some false else step B fuel rest   -- t = 1 is a witness iff num < B
--     else match children B target num minIdx with
--       | none => none
--       | some cs => step B fuel (cs ++ rest)
--
-- /-- Decide whether no `m` with `1 ≤ m < B` has `sL ≤ σ m`. With
-- `(B, sL) = (lcm (1..n), σ (lcm (1..n)))`, `some true` certifies that
-- `lcm (1..n)` is highly abundant. -/
-- def highlyAbundantLcm? (B sL : Nat) : Option Bool :=
--   if B ≤ 1 then some true else step B searchFuel [(sL, 1, 0)]

end Sage
