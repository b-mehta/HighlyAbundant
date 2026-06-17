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

/-- Kernel-friendly list append using `List.rec` directly, avoiding the
brecOn/match_1 machinery that `List.append` would unfold. -/
noncomputable def appendK {α : Type _} (xs ys : List α) : List α :=
  xs.rec ys fun x _ ih ↦ x :: ih

/-- Ceiling division `⌈a / b⌉`, equal to `(a + b - 1) / b` when `b ≠ 0`. -/
def ceilDivK (a b : Nat) : Nat := ((a.add b).sub (nat_lit 1)).div b

/-- Grow a prime window from `back` forward, threading `lhs = m * ∏ primes[i]`
and `rhs = target * ∏ (primes[i] - 1)`. Returns `.window b lhs' rhs'` at the least
`b ≥ back` with `lhs ≥ rhs`; `.tooLarge` if the next prime would push `lhs > m2`;
`.exhaustedTable` if fuel or the table runs out. -/
noncomputable def extendK (fuel m2 front : Nat) : Nat → Nat → Nat → Wheel :=
  fuel.rec (fun _ _ _ ↦ .exhaustedTable) fun _ r back lhs rhs ↦
    (front.ble back).rec
      ((front.ble (nat_lit 48)).rec .exhaustedTable <|
        let q := primesRArray.get front
        let lhs' := lhs.mul q
        (lhs'.ble m2).rec .tooLarge (r front lhs' (rhs.mul (q.sub (nat_lit 1)))))
      ((rhs.ble lhs).rec
        ((back.ble (nat_lit 47)).rec .exhaustedTable <|
          let q := primesRArray.get back.succ
          let lhs' := lhs.mul q
          (lhs'.ble m2).rec .tooLarge (r back.succ lhs' (rhs.mul (q.sub (nat_lit 1)))))
        (.window back lhs rhs))

/-- Emit children `(⌈target / σ(p^k)⌉, num * p^k, next)` for `k ≥ 1` with
`p^k ≤ m`, stopping after the first `k` with `σ(p^k) ≥ target`. -/
noncomputable def expChildrenK (fuel target num next m p : Nat) :
    Nat → List (Nat × Nat × Nat) :=
  fuel.rec (fun _ ↦ []) fun _ r pk ↦
    (pk.ble m).rec []
      (let spk := ((pk.mul p).sub (nat_lit 1)).div (p.sub (nat_lit 1))
       let child := (ceilDivK target spk, num.mul pk, next)
       (target.ble spk).rec (child :: r (pk.mul p)) [child])

/-- Iterate `extend` from `front` onward, collecting `expChildren` at every
`.window` index. Returns `none` if an index `≥ 49` is read. -/
noncomputable def wheelChildrenK (fuel m2 m target num : Nat) :
    Nat → Nat → Nat → Nat → List (Nat × Nat × Nat) → Option (List (Nat × Nat × Nat)) :=
  fuel.rec (fun _ _ _ _ _ ↦ none) fun _ r front back lhs rhs acc ↦
    (extendK (nat_lit 50) m2 front back lhs rhs).rec
      none
      (some acc)
      (fun b lhs' rhs' ↦
        (front.ble (nat_lit 48)).rec none <|
          let p := primesRArray.get front
          r front.succ b (lhs'.div p) (rhs'.div (p.sub (nat_lit 1)))
            (appendK (expChildrenK m.succ target num front.succ m p p) acc))

/-- Children of node `(target, num, minIdx)` with `m = B / num`. Each `c ∈ cs` is
`(⌈target/σ(primes[i]^k)⌉, num * primes[i]^k, i + 1)` for some `i ≥ minIdx` and
`k ≥ 1` with `primes[i]^k ≤ m`. Returns `none` if the search needs an index
`≥ 49`. -/
noncomputable def childrenK (B target num minIdx : Nat) :
    Option (List (Nat × Nat × Nat)) :=
  (minIdx.ble (nat_lit 48)).rec none <|
    let p0 := primesRArray.get minIdx
    let m := B.div num
    wheelChildrenK (nat_lit 50) (m.mul m) m target num minIdx minIdx (p0.mul m)
      (target.mul (p0.sub (nat_lit 1))) []

/-- Stack-machine witness search. `some true`: no node on `stack` has a witness.
`some false`: some node has a witness. `none`: fuel exhausted or `children` read
an index `≥ 49`. -/
noncomputable def stepK (B : Nat) : Nat → List (Nat × Nat × Nat) → Option Bool :=
  fun fuel ↦ fuel.rec (fun _ ↦ none) fun _ r stack ↦
    stack.rec (some true) fun node rest _ ↦
      let target := node.1
      let num := node.2.1
      let minIdx := node.2.2
      (target.ble (nat_lit 1)).rec
        ((childrenK B target num minIdx).rec none (fun cs ↦ r (appendK cs rest)))
        ((B.ble num).rec (some false) (r rest))

/-- Decide whether no `m` with `1 ≤ m < B` has `sL ≤ σ m`. With
`(B, sL) = (lcm (1..n), σ (lcm (1..n)))`, `some true` certifies that
`lcm (1..n)` is highly abundant. -/
noncomputable def highlyAbundantLcmK? (B sL : Nat) : Option Bool :=
  (B.ble (nat_lit 1)).rec (stepK B searchFuel [(sL, nat_lit 1, nat_lit 0)]) (some true)

end Sage
