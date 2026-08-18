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

The `Bool` certificate forms at the end state a search result as an equality `Nat.beq` closes, which
`Lean.reflBoolTrue` proves in one kernel reduction.
-/

namespace Sage

/-- A search node as a flat struct, so the kernel destructures it with a single `SageNode.rec`. -/
structure SageNode where
  goal : Nat
  cand : Nat
  i : Nat

/-- Append on `List SageNode`, written with `List.rec` so the kernel reduces it directly. -/
@[expose] noncomputable def appendK (xs ys : List SageNode) : List SageNode :=
  xs.rec ys fun x _ ih ↦ x :: ih

/-- Ceiling division `⌈a / b⌉`, equal to `(a + b - 1) / b` when `b ≠ 0`. -/
@[expose] def ceilDivK (a b : Nat) : Nat := ((a.add b).sub (nat_lit 1)).div b

/-- The window-growing loop, entered with `back` inside the window so the phase test is settled.
Returns `.window b lhs' rhs'` at the least `b ≥ back` with `lhs ≥ rhs`, `.tooLarge` if the next
prime pushes `lhs > m2`, and `.exhaustedTable` if fuel or the table runs out. -/
@[expose] noncomputable def extendKLoop (fuel m2 : Nat) : Nat → Nat → Nat → Wheel :=
  fuel.rec (fun _ _ _ ↦ .exhaustedTable) fun _ r back lhs rhs ↦
    (rhs.ble lhs).rec
      ((back.ble (nat_lit 47)).rec .exhaustedTable <|
        let q := primesRArray.get back.succ
        let lhs' := lhs.mul q
        (lhs'.ble m2).rec .tooLarge (r back.succ lhs' (rhs.mul (q.sub (nat_lit 1)))))
      (.window back lhs rhs)

/-- Grow a prime window forward from `back`, where `lhs = m * ∏ primes[i]` and
`rhs = goal * ∏ (primes[i] - 1)`. Settles the empty-range case once, then runs `extendKLoop`. -/
@[expose] noncomputable def extendK (fuel m2 front : Nat) : Nat → Nat → Nat → Wheel :=
  fuel.rec (fun _ _ _ ↦ .exhaustedTable) fun n _ back lhs rhs ↦
    (front.ble back).rec
      ((front.ble (nat_lit 48)).rec .exhaustedTable <|
        let q := primesRArray.get front
        let lhs' := lhs.mul q
        (lhs'.ble m2).rec .tooLarge (extendKLoop n m2 front lhs' (rhs.mul (q.sub (nat_lit 1)))))
      (extendKLoop n.succ m2 back lhs rhs)

/-- Emit children `⟨⌈goal / σ(p^k)⌉, cand * p^k, next⟩` for `k ≥ 1` with `p^k ≤ m`, up to and
including the first `k` where `σ(p^k) ≥ goal`. -/
@[expose] noncomputable def expChildrenK (fuel goal cand next m p : Nat) :
    Nat → List SageNode :=
  fuel.rec (fun _ ↦ []) fun _ r pk ↦
    (pk.ble m).rec []
      (let spk := ((pk.mul p).sub (nat_lit 1)).div (p.sub (nat_lit 1))
       ⟨ceilDivK goal spk, cand.mul pk, next⟩ :: (goal.ble spk).rec (r (pk.mul p)) [])

/-- Iterate `extend` from `front` onward and gather `expChildren` at each `.window` index. Returns
`none` if it reads an index `≥ 49`. -/
@[expose] noncomputable def wheelChildrenK (fuel m2 m goal cand : Nat) :
    Nat → Nat → Nat → Nat → List SageNode → Option (List SageNode) :=
  fuel.rec (fun _ _ _ _ _ ↦ none) fun _ r front back lhs rhs acc ↦
    (extendK (nat_lit 50) m2 front back lhs rhs).rec
      none
      (some acc)
      (fun b lhs' rhs' ↦
        (front.ble (nat_lit 48)).rec none <|
          let p := primesRArray.get front
          r front.succ b (lhs'.div p) (rhs'.div (p.sub (nat_lit 1)))
            (appendK (expChildrenK m.succ goal cand front.succ m p p) acc))

/-- Children of node `⟨goal, cand, i⟩` with `m = B / cand`. Each `c ∈ cs` is
`⟨⌈goal/σ(primes[j]^k)⌉, cand * primes[j]^k, j + 1⟩` for some `j ≥ i` and
`k ≥ 1` with `primes[j]^k ≤ m`. Returns `none` if the search needs an index
`≥ 49`. -/
@[expose] noncomputable def childrenK (B goal cand i : Nat) :
    Option (List SageNode) :=
  (i.ble (nat_lit 48)).rec none <|
    let p0 := primesRArray.get i
    let m := B.div cand
    wheelChildrenK (nat_lit 50) (m.mul m) m goal cand i i (p0.mul m)
      (goal.mul (p0.sub (nat_lit 1))) []

/-- Stack-machine witness search. Returns `some true` if no node on `stack` has a witness,
`some false` if some node does, and `none` if fuel runs out or `children` reads an index `≥ 49`. -/
@[expose] noncomputable def stepK (B : Nat) : Nat → List SageNode → Option Bool :=
  fun fuel ↦ fuel.rec (fun _ ↦ none) fun _ r stack ↦
    stack.rec (some true) fun node rest _ ↦
      node.rec fun goal cand i ↦
        (goal.ble (nat_lit 1)).rec
          ((childrenK B goal cand i).rec none (fun cs ↦ r (appendK cs rest)))
          ((B.ble cand).rec (some false) (r rest))

/-- Decide whether no `m` with `1 ≤ m < B` has `sL ≤ σ m`. With
`(B, sL) = (lcm (1..n), σ (lcm (1..n)))`, `some true` certifies that
`lcm (1..n)` is highly abundant. -/
@[expose] noncomputable def highlyAbundantLcmK? (B sL : Nat) : Option Bool :=
  (B.ble (nat_lit 1)).rec (stepK B searchFuel [⟨sL, nat_lit 1, nat_lit 0⟩]) (some true)

/-! ### Certificates as `Bool` -/

/-- Structural `beq` on `SageNode` from `Nat.beq` and `Bool.and'`. -/
@[expose] noncomputable def SageNode.beq (a b : SageNode) : Bool :=
  (a.goal.beq b.goal).and' ((a.cand.beq b.cand).and' (a.i.beq b.i))

/-- Pointwise `SageNode.beq` on two lists, written with `List.rec`. -/
@[expose] noncomputable def sageListBeq : List SageNode → List SageNode → Bool :=
  fun xs ↦ xs.rec
    (fun ys ↦ ys.rec true (fun _ _ _ ↦ false))
    fun x _ ih ys ↦ ys.rec false fun y ys' _ ↦ (x.beq y).and' (ih ys')

/-- `Bool` form of the leaf certificate `stepK B fuel [c] = some true`. -/
@[expose] noncomputable def stepKSingletonBeqCert (B fuel : Nat) (c : SageNode) : Bool :=
  (stepK B fuel [c]).elim false fun b ↦ b

/-- `Bool` form of the `childrenK` certificate, phrased on `Option.elim` so the metaprogram builds
it from literal arguments. -/
@[expose] noncomputable def childrenKBeqCert (B goal cand i : Nat) (cs : List SageNode) :
    Bool :=
  (childrenK B goal cand i).elim false fun cs' ↦ sageListBeq cs' cs

end Sage
