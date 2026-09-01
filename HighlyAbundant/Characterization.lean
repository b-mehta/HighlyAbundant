/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.Basic
import HighlyAbundant.IsNotHA.ClimbLadder
import HighlyAbundant.IsHA.HAComposeSmall
import HighlyAbundant.IsHA.HACompose125
import HighlyAbundant.IsHA.HACompose127
import HighlyAbundant.IsHA.HACompose137
import HighlyAbundant.IsHA.HACompose139
import HighlyAbundant.IsHA.HACompose169

/-!
# Characterization of highly abundant `lcmUpto n` for `1 ≤ n ≤ 10 ^ 40`

`lcmUpto n` is highly abundant iff `n` lies in the explicit set listed in the README.
-/

open Nat

/-- Logic core: given all anchor HA facts and all chunk non-HA facts as hypotheses, the
characterization follows by the block-transfer lemma and arithmetic. -/
private theorem iff_of_facts {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 10 ^ 40)
    (h1 : IsHighlyAbundant (lcmUpto 1))
    (h2 : IsHighlyAbundant (lcmUpto 2))
    (h3 : IsHighlyAbundant (lcmUpto 3))
    (h4 : IsHighlyAbundant (lcmUpto 4))
    (h5 : IsHighlyAbundant (lcmUpto 5))
    (h7 : IsHighlyAbundant (lcmUpto 7))
    (h8 : IsHighlyAbundant (lcmUpto 8))
    (h9 : IsHighlyAbundant (lcmUpto 9))
    (h11 : IsHighlyAbundant (lcmUpto 11))
    (h13 : IsHighlyAbundant (lcmUpto 13))
    (h16 : IsHighlyAbundant (lcmUpto 16))
    (h17 : IsHighlyAbundant (lcmUpto 17))
    (h19 : IsHighlyAbundant (lcmUpto 19))
    (h23 : IsHighlyAbundant (lcmUpto 23))
    (h25 : IsHighlyAbundant (lcmUpto 25))
    (h27 : IsHighlyAbundant (lcmUpto 27))
    (h29 : IsHighlyAbundant (lcmUpto 29))
    (h31 : IsHighlyAbundant (lcmUpto 31))
    (h32 : IsHighlyAbundant (lcmUpto 32))
    (h37 : IsHighlyAbundant (lcmUpto 37))
    (h41 : IsHighlyAbundant (lcmUpto 41))
    (h43 : IsHighlyAbundant (lcmUpto 43))
    (h47 : IsHighlyAbundant (lcmUpto 47))
    (h49 : IsHighlyAbundant (lcmUpto 49))
    (h53 : IsHighlyAbundant (lcmUpto 53))
    (h59 : IsHighlyAbundant (lcmUpto 59))
    (h61 : IsHighlyAbundant (lcmUpto 61))
    (h64 : IsHighlyAbundant (lcmUpto 64))
    (h67 : IsHighlyAbundant (lcmUpto 67))
    (h81 : IsHighlyAbundant (lcmUpto 81))
    (h83 : IsHighlyAbundant (lcmUpto 83))
    (h89 : IsHighlyAbundant (lcmUpto 89))
    (h125 : IsHighlyAbundant (lcmUpto 125))
    (h127 : IsHighlyAbundant (lcmUpto 127))
    (h128 : IsHighlyAbundant (lcmUpto 128))
    (h131 : IsHighlyAbundant (lcmUpto 131))
    (h137 : IsHighlyAbundant (lcmUpto 137))
    (h139 : IsHighlyAbundant (lcmUpto 139))
    (h169 : IsHighlyAbundant (lcmUpto 169))
    (c1 : ∀ i, 71 ≤ i → i ≤ 80 → ¬ IsHighlyAbundant (lcmUpto i))
    (c2 : ∀ i, 97 ≤ i → i ≤ 124 → ¬ IsHighlyAbundant (lcmUpto i))
    (c3 : ∀ i, 149 ≤ i → i ≤ 168 → ¬ IsHighlyAbundant (lcmUpto i))
    (c4 : ∀ i, 173 ≤ i → i ≤ 10029542461709537120579603199949529595648 →
      ¬ IsHighlyAbundant (lcmUpto i)) :
    IsHighlyAbundant (lcmUpto n) ↔
      n ∈ Finset.Icc 1 70 ∪ Finset.Icc 81 96 ∪ Finset.Icc 125 148 ∪ Finset.Icc 169 172 := by
  have blk : ∀ (q e : ℕ), IsHighlyAbundant (lcmUpto q) →
      (∀ x ∈ Finset.Ioc q e, ¬ IsPrimePow x) →
      ∀ k, q ≤ k → k ≤ e → IsHighlyAbundant (lcmUpto k) :=
    fun q e hq hgap k hk1 hk2 => isHighlyAbundant_lcmUpto_of_no_primePow_Ioc hk1
      (fun x hx => hgap x (Finset.mem_Ioc.2
        ⟨(Finset.mem_Ioc.1 hx).1, le_trans (Finset.mem_Ioc.1 hx).2 hk2⟩)) hq
  have b1 := blk 1 1 h1 (by decide +kernel)
  have b2 := blk 2 2 h2 (by decide +kernel)
  have b3 := blk 3 3 h3 (by decide +kernel)
  have b4 := blk 4 4 h4 (by decide +kernel)
  have b5 := blk 5 6 h5 (by decide +kernel)
  have b7 := blk 7 7 h7 (by decide +kernel)
  have b8 := blk 8 8 h8 (by decide +kernel)
  have b9 := blk 9 10 h9 (by decide +kernel)
  have b11 := blk 11 12 h11 (by decide +kernel)
  have b13 := blk 13 15 h13 (by decide +kernel)
  have b16 := blk 16 16 h16 (by decide +kernel)
  have b17 := blk 17 18 h17 (by decide +kernel)
  have b19 := blk 19 22 h19 (by decide +kernel)
  have b23 := blk 23 24 h23 (by decide +kernel)
  have b25 := blk 25 26 h25 (by decide +kernel)
  have b27 := blk 27 28 h27 (by decide +kernel)
  have b29 := blk 29 30 h29 (by decide +kernel)
  have b31 := blk 31 31 h31 (by decide +kernel)
  have b32 := blk 32 36 h32 (by decide +kernel)
  have b37 := blk 37 40 h37 (by decide +kernel)
  have b41 := blk 41 42 h41 (by decide +kernel)
  have b43 := blk 43 46 h43 (by decide +kernel)
  have b47 := blk 47 48 h47 (by decide +kernel)
  have b49 := blk 49 52 h49 (by decide +kernel)
  have b53 := blk 53 58 h53 (by decide +kernel)
  have b59 := blk 59 60 h59 (by decide +kernel)
  have b61 := blk 61 63 h61 (by decide +kernel)
  have b64 := blk 64 66 h64 (by decide +kernel)
  have b67 := blk 67 70 h67 (by decide +kernel)
  have b81 := blk 81 82 h81 (by decide +kernel)
  have b83 := blk 83 88 h83 (by decide +kernel)
  have b89 := blk 89 96 h89 (by decide +kernel)
  have b125 := blk 125 126 h125 (by decide +kernel)
  have b127 := blk 127 127 h127 (by decide +kernel)
  have b128 := blk 128 130 h128 (by decide +kernel)
  have b131 := blk 131 136 h131 (by decide +kernel)
  have b137 := blk 137 138 h137 (by decide +kernel)
  have b139 := blk 139 148 h139 (by decide +kernel)
  have b169 := blk 169 172 h169 (by decide +kernel)
  constructor
  · intro hHA
    by_contra hmem
    simp only [Finset.mem_union, Finset.mem_Icc] at hmem
    rcases (by omega : (71 ≤ n ∧ n ≤ 80) ∨ (97 ≤ n ∧ n ≤ 124) ∨
        (149 ≤ n ∧ n ≤ 168) ∨ 173 ≤ n) with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | a
    · exact c1 n a b hHA
    · exact c2 n a b hHA
    · exact c3 n a b hHA
    · exact c4 n a (le_trans hn (by norm_num)) hHA
  · intro hmem
    simp only [Finset.mem_union, Finset.mem_Icc] at hmem
    rcases hmem with ((⟨ha, hb⟩ | ⟨ha, hb⟩) | ⟨ha, hb⟩) | ⟨ha, hb⟩
    · rcases (by omega :
        (1 ≤ n ∧ n ≤ 1) ∨ (2 ≤ n ∧ n ≤ 2) ∨ (3 ≤ n ∧ n ≤ 3) ∨ (4 ≤ n ∧ n ≤ 4) ∨ (5 ≤ n ∧ n ≤ 6) ∨
        (7 ≤ n ∧ n ≤ 7) ∨ (8 ≤ n ∧ n ≤ 8) ∨ (9 ≤ n ∧ n ≤ 10) ∨ (11 ≤ n ∧ n ≤ 12) ∨
        (13 ≤ n ∧ n ≤ 15) ∨ (16 ≤ n ∧ n ≤ 16) ∨ (17 ≤ n ∧ n ≤ 18) ∨ (19 ≤ n ∧ n ≤ 22) ∨
        (23 ≤ n ∧ n ≤ 24) ∨ (25 ≤ n ∧ n ≤ 26) ∨ (27 ≤ n ∧ n ≤ 28) ∨ (29 ≤ n ∧ n ≤ 30) ∨
        (31 ≤ n ∧ n ≤ 31) ∨ (32 ≤ n ∧ n ≤ 36) ∨ (37 ≤ n ∧ n ≤ 40) ∨ (41 ≤ n ∧ n ≤ 42) ∨
        (43 ≤ n ∧ n ≤ 46) ∨ (47 ≤ n ∧ n ≤ 48) ∨ (49 ≤ n ∧ n ≤ 52) ∨ (53 ≤ n ∧ n ≤ 58) ∨
        (59 ≤ n ∧ n ≤ 60) ∨ (61 ≤ n ∧ n ≤ 63) ∨ (64 ≤ n ∧ n ≤ 66) ∨ (67 ≤ n ∧ n ≤ 70)) with
        ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ |
        ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ |
        ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩
      · exact b1 n l r
      · exact b2 n l r
      · exact b3 n l r
      · exact b4 n l r
      · exact b5 n l r
      · exact b7 n l r
      · exact b8 n l r
      · exact b9 n l r
      · exact b11 n l r
      · exact b13 n l r
      · exact b16 n l r
      · exact b17 n l r
      · exact b19 n l r
      · exact b23 n l r
      · exact b25 n l r
      · exact b27 n l r
      · exact b29 n l r
      · exact b31 n l r
      · exact b32 n l r
      · exact b37 n l r
      · exact b41 n l r
      · exact b43 n l r
      · exact b47 n l r
      · exact b49 n l r
      · exact b53 n l r
      · exact b59 n l r
      · exact b61 n l r
      · exact b64 n l r
      · exact b67 n l r
    · rcases (by omega :
        (81 ≤ n ∧ n ≤ 82) ∨ (83 ≤ n ∧ n ≤ 88) ∨ (89 ≤ n ∧ n ≤ 96)) with
        ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩
      · exact b81 n l r
      · exact b83 n l r
      · exact b89 n l r
    · rcases (by omega :
        (125 ≤ n ∧ n ≤ 126) ∨ (127 ≤ n ∧ n ≤ 127) ∨ (128 ≤ n ∧ n ≤ 130) ∨ (131 ≤ n ∧ n ≤ 136) ∨
        (137 ≤ n ∧ n ≤ 138) ∨ (139 ≤ n ∧ n ≤ 148)) with
        ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩ | ⟨l, r⟩
      · exact b125 n l r
      · exact b127 n l r
      · exact b128 n l r
      · exact b131 n l r
      · exact b137 n l r
      · exact b139 n l r
    · rcases (by omega :
        (169 ≤ n ∧ n ≤ 172)) with
        ⟨l, r⟩
      · exact b169 n l r

/-- For `1 ≤ n ≤ 10 ^ 40`, `lcmUpto n` is highly abundant iff `n` lies in the explicit
finite set of the README (the union of four intervals of admissible indices). -/
theorem isHighlyAbundant_lcmUpto_iff {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 10 ^ 40) :
    IsHighlyAbundant (lcmUpto n) ↔
      n ∈ Finset.Icc 1 70 ∪ Finset.Icc 81 96 ∪ Finset.Icc 125 148 ∪ Finset.Icc 169 172 :=
  iff_of_facts hn1 hn
    (by
      have h : lcmUpto 1 = 1 := by decide
      intro m hm hlt
      omega)
    Sage.isHighlyAbundant_lcmUpto_2 Sage.isHighlyAbundant_lcmUpto_3
    Sage.isHighlyAbundant_lcmUpto_4 Sage.isHighlyAbundant_lcmUpto_5
    Sage.isHighlyAbundant_lcmUpto_7 Sage.isHighlyAbundant_lcmUpto_8
    Sage.isHighlyAbundant_lcmUpto_9 Sage.isHighlyAbundant_lcmUpto_11
    Sage.isHighlyAbundant_lcmUpto_13 Sage.isHighlyAbundant_lcmUpto_16
    Sage.isHighlyAbundant_lcmUpto_17 Sage.isHighlyAbundant_lcmUpto_19
    Sage.isHighlyAbundant_lcmUpto_23 Sage.isHighlyAbundant_lcmUpto_25
    Sage.isHighlyAbundant_lcmUpto_27 Sage.isHighlyAbundant_lcmUpto_29
    Sage.isHighlyAbundant_lcmUpto_31 Sage.isHighlyAbundant_lcmUpto_32
    Sage.isHighlyAbundant_lcmUpto_37 Sage.isHighlyAbundant_lcmUpto_41
    Sage.isHighlyAbundant_lcmUpto_43 Sage.isHighlyAbundant_lcmUpto_47
    Sage.isHighlyAbundant_lcmUpto_49 Sage.isHighlyAbundant_lcmUpto_53
    Sage.isHighlyAbundant_lcmUpto_59 Sage.isHighlyAbundant_lcmUpto_61
    Sage.isHighlyAbundant_lcmUpto_64 Sage.isHighlyAbundant_lcmUpto_67
    Sage.isHighlyAbundant_lcmUpto_81 Sage.isHighlyAbundant_lcmUpto_83
    Sage.isHighlyAbundant_lcmUpto_89 Sage.isHighlyAbundant_lcmUpto_125
    Sage.isHighlyAbundant_lcmUpto_127 Sage.isHighlyAbundant_lcmUpto_128
    Sage.isHighlyAbundant_lcmUpto_131 Sage.isHighlyAbundant_lcmUpto_137
    Sage.isHighlyAbundant_lcmUpto_139 Sage.isHighlyAbundant_lcmUpto_169
    chunk1 chunk2 chunk3 chunk4
