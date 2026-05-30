/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import HighlyAbundant.Basic
import HighlyAbundant.Sage
import Mathlib.Data.Nat.Log

/-!
# Correctness of the `lcm (1..n)` HA-decider

Spec of the search in `HighlyAbundant.Sage`; proofs are `sorry`. Notation:

* `P j := { t ≥ 1 | every prime factor of t occurs in primes at index ≥ j }`;
* `W B target num minIdx := { t ∈ P minIdx | num * t < B ∧ target ≤ σ₁ t }`
  is the witness set of a node `(target, num, minIdx)` for bound `B`;
* `lcmData n := (∏ p^⌊log_p n⌋, ∏ σ(p^⌊log_p n⌋))` over primes `p ≤ n` in the
  table; agrees with `(lcmRange n, σ₁ (lcmRange n))` for `n ≤ 227` (`lcmData_eq`).

## Partial verification

`step`'s shared fuel does not factor over `++`, so the root evaluation
`step B searchFuel [(sL, 1, 0)]` does not decompose into per-child evaluations.
To prove `lcm (1..n)` highly abundant from per-subtree results, let
`(B, sL) = lcmData n` with `2 ≤ B`:

1. Evaluate `children B sL 1 0 = some cs` (enlarge `primes` on `none`).
2. For each `c ∈ cs`, obtain `step B searchFuel [c] = some true` separately;
   `step_true` gives `W B c.1 c.2.1 c.2.2 = ∅`.
3. `1 ∉ W B sL 1 0` since `σ₁ 1 = 1 < sL`. Negating `children_spec` gives
   `(∀ t ∈ W B sL 1 0, t = 1) ↔ (∀ c ∈ cs, W B c.1 c.2.1 c.2.2 = ∅)`; the right
   side holds by step 2, so combined with step 3 we get `W B sL 1 0 = ∅`.
4. `W B sL 1 0 = ∅` unfolds to `¬ ∃ m, 1 ≤ m ∧ m < B ∧ sL ≤ σ₁ m`, which with
   `B = lcm (1..n)` and `sL = σ₁ B` is highly-abundance of `lcm (1..n)`.

Only `children_spec` and `step_true` are used; the full root is never evaluated.
-/

namespace Sage

/-- `P j`: naturals `≥ 1` all of whose prime factors occur in `primes` at index `≥ j`. -/
def P (j : Nat) : Set Nat :=
  { t | 1 ≤ t ∧ ∀ q : Nat, q.Prime → q ∣ t → ∃ i, primes[i]? = some q ∧ j ≤ i }

/-- The witness set of a node `(target, num, minIdx)` for bound `B`. -/
def W (B target num minIdx : Nat) : Set Nat :=
  { t | t ∈ P minIdx ∧ num * t < B ∧ target ≤ σ₁ t }

/-- `lcmData n = (lcm (1..n), σ₁ (lcm (1..n)))`, computed as
`(∏ p^{⌊log_p n⌋}, ∏ σ(p^{⌊log_p n⌋}))` over the primes `p ≤ n`. Correct for
`n ≤ 227` (so every prime `≤ n` is in the table); see `lcmData_eq`. -/
def lcmData (n : Nat) : Nat × Nat :=
  (primes.toList.takeWhile (· ≤ n)).foldl
    (fun (acc : Nat × Nat) p =>
      let e := Nat.log p n
      (acc.1 * p ^ e, acc.2 * ((p ^ (e + 1) - 1) / (p - 1)))) (1, 1)

/-- For `n ≤ 227`, the prime table contains every prime `≤ n`, so `lcmData n`
agrees with the canonical `(lcmRange n, σ₁ (lcmRange n))`. -/
theorem lcmData_eq {n : Nat} (hn : n ≤ 227) :
    lcmData n = (lcmRange n, σ₁ (lcmRange n)) := sorry

/-- The fuel-based and well-founded forms of `extend` agree once fuel is large enough. -/
theorem extend_eq_extendWF {fuel m2 front back lhs rhs : Nat}
    (h : primes.size + 1 - back ≤ fuel) :
    extend fuel m2 front back lhs rhs = extendWF m2 front back lhs rhs := sorry

/-- The fuel-based and well-founded forms of `wheelChildren` agree once fuel is large
enough. `wheelChildrenWF` returns `some []` where `wheelChildren` returns `some acc`. -/
theorem wheelChildren_eq_wheelChildrenWF
    {fuel m2 m target num front back lhs rhs : Nat}
    (h : primes.size + 1 - front ≤ fuel) (acc : List (Nat × Nat × Nat)) :
    wheelChildren fuel m2 m target num front back lhs rhs acc =
      (wheelChildrenWF m2 m target num front back lhs rhs).map (· ++ acc) := sorry

/-- `children` reduces nontrivial witnesses of a node to witnesses of its children. -/
theorem children_spec {B target num minIdx : Nat} {cs : List (Nat × Nat × Nat)}
    (h : children B target num minIdx = some cs) :
    (∃ t ∈ W B target num minIdx, t ≠ 1) ↔
      ∃ c ∈ cs, W B c.1 c.2.1 c.2.2 ≠ ∅ := sorry

/-- `step = some true` ⟹ every node on the stack has an empty witness set. -/
theorem step_true {B fuel : Nat} {stack : List (Nat × Nat × Nat)}
    (h : step B fuel stack = some true) :
    ∀ node ∈ stack, W B node.1 node.2.1 node.2.2 = ∅ := sorry

/-- `step = some false` ⟹ some node on the stack has a nonempty witness set. -/
theorem step_false {B fuel : Nat} {stack : List (Nat × Nat × Nat)}
    (h : step B fuel stack = some false) :
    ∃ node ∈ stack, W B node.1 node.2.1 node.2.2 ≠ ∅ := sorry

/-- Top-level correctness: a `some true` answer on `lcmData n` certifies that
`lcm (1..n)` is highly abundant (for `n` within the prime-table range). -/
theorem highlyAbundantLcm_correct {n : Nat} (hn : n ≤ 227)
    (h : highlyAbundantLcm? (lcmData n).1 (lcmData n).2 = some true) :
    IsHighlyAbundant (lcmRange n) := sorry

end Sage
