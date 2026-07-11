/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

public import HighlyAbundant.IsHA.Sage

public section

/-!
# Kernel-reducible versions of the decider functions

These mirror the `HighlyAbundant.Sage` definitions using primitives the kernel reduces directly:
`Nat.rec`, `Bool.rec`, `Nat.ble`. `SageKernelEquiv` proves they agree with the spec versions.

Nodes here use a flat `SageNode` struct, one `SageNode.rec` per node, where the spec side on
`Nat × Nat × Nat` takes two nested `Prod.rec`.
-/

namespace Sage

/-- A search node as a flat struct, so the kernel destructures it with a single `SageNode.rec`. -/
structure SageNode where
  target : Nat
  num : Nat
  minIdx : Nat

/-- Convert a kernel-side `SageNode` back to a spec-side `(Nat × Nat × Nat)`. -/
def fromSageNode (n : SageNode) : Nat × Nat × Nat := (n.target, n.num, n.minIdx)

/-- Append on `List SageNode`, written with `List.rec` so the kernel reduces it directly. -/
@[expose] noncomputable def appendK (xs ys : List SageNode) : List SageNode :=
  xs.rec ys fun x _ ih ↦ x :: ih

/-- Ceiling division `⌈a / b⌉`, equal to `(a + b - 1) / b` when `b ≠ 0`. -/
@[expose] def ceilDivK (a b : Nat) : Nat := ((a.add b).sub (nat_lit 1)).div b

/-- Grow a prime window forward from `back`, where `lhs = m * ∏ primes[i]` and
`rhs = target * ∏ (primes[i] - 1)`. Returns `.window b lhs' rhs'` at the least `b ≥ back` with
`lhs ≥ rhs`, `.tooLarge` if the next prime pushes `lhs > m2`, and `.exhaustedTable` if fuel or the
table runs out. -/
@[expose] noncomputable def extendK (fuel m2 front : Nat) : Nat → Nat → Nat → Wheel :=
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

/-- Emit children `⟨⌈target / σ(p^k)⌉, num * p^k, next⟩` for `k ≥ 1` with `p^k ≤ m`, up to and
including the first `k` where `σ(p^k) ≥ target`. -/
@[expose] noncomputable def expChildrenK (fuel target num next m p : Nat) :
    Nat → List SageNode :=
  fuel.rec (fun _ ↦ []) fun _ r pk ↦
    (pk.ble m).rec []
      (let spk := ((pk.mul p).sub (nat_lit 1)).div (p.sub (nat_lit 1))
       let child : SageNode := ⟨ceilDivK target spk, num.mul pk, next⟩
       (target.ble spk).rec (child :: r (pk.mul p)) [child])

/-- Iterate `extend` from `front` onward and gather `expChildren` at each `.window` index. Returns
`none` if it reads an index `≥ 49`. -/
@[expose] noncomputable def wheelChildrenK (fuel m2 m target num : Nat) :
    Nat → Nat → Nat → Nat → List SageNode → Option (List SageNode) :=
  fuel.rec (fun _ _ _ _ _ ↦ none) fun _ r front back lhs rhs acc ↦
    (extendK (nat_lit 50) m2 front back lhs rhs).rec
      none
      (some acc)
      (fun b lhs' rhs' ↦
        (front.ble (nat_lit 48)).rec none <|
          let p := primesRArray.get front
          r front.succ b (lhs'.div p) (rhs'.div (p.sub (nat_lit 1)))
            (appendK (expChildrenK m.succ target num front.succ m p p) acc))

/-- Children of node `⟨target, num, minIdx⟩` with `m = B / num`. Each `c ∈ cs` is
`⟨⌈target/σ(primes[i]^k)⌉, num * primes[i]^k, i + 1⟩` for some `i ≥ minIdx` and
`k ≥ 1` with `primes[i]^k ≤ m`. Returns `none` if the search needs an index
`≥ 49`. -/
@[expose] noncomputable def childrenK (B target num minIdx : Nat) :
    Option (List SageNode) :=
  (minIdx.ble (nat_lit 48)).rec none <|
    let p0 := primesRArray.get minIdx
    let m := B.div num
    wheelChildrenK (nat_lit 50) (m.mul m) m target num minIdx minIdx (p0.mul m)
      (target.mul (p0.sub (nat_lit 1))) []

/-- Stack-machine witness search. Returns `some true` if no node on `stack` has a witness,
`some false` if some node does, and `none` if fuel runs out or `children` reads an index `≥ 49`. -/
@[expose] noncomputable def stepK (B : Nat) : Nat → List SageNode → Option Bool :=
  fun fuel ↦ fuel.rec (fun _ ↦ none) fun _ r stack ↦
    stack.rec (some true) fun node rest _ ↦
      node.rec fun target num minIdx ↦
        (target.ble (nat_lit 1)).rec
          ((childrenK B target num minIdx).rec none (fun cs ↦ r (appendK cs rest)))
          ((B.ble num).rec (some false) (r rest))

/-- Decide whether no `m` with `1 ≤ m < B` has `sL ≤ σ m`. With
`(B, sL) = (lcm (1..n), σ (lcm (1..n)))`, `some true` certifies that
`lcm (1..n)` is highly abundant. -/
@[expose] noncomputable def highlyAbundantLcmK? (B sL : Nat) : Option Bool :=
  (B.ble (nat_lit 1)).rec (stepK B searchFuel [⟨sL, nat_lit 1, nat_lit 0⟩]) (some true)

end Sage
