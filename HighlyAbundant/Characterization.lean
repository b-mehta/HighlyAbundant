/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import HighlyAbundant.Basic
import HighlyAbundant.LcmRangeConstant
import HighlyAbundant.ClimbLadder
import HighlyAbundant.HACompose2
import HighlyAbundant.HACompose3
import HighlyAbundant.HACompose4
import HighlyAbundant.HACompose5
import HighlyAbundant.HACompose7
import HighlyAbundant.HACompose8
import HighlyAbundant.HACompose9
import HighlyAbundant.HACompose11
import HighlyAbundant.HACompose13
import HighlyAbundant.HACompose16
import HighlyAbundant.HACompose17
import HighlyAbundant.HACompose19
import HighlyAbundant.HACompose23
import HighlyAbundant.HACompose25
import HighlyAbundant.HACompose27
import HighlyAbundant.HACompose29
import HighlyAbundant.HACompose31
import HighlyAbundant.HACompose32
import HighlyAbundant.HACompose37
import HighlyAbundant.HACompose41
import HighlyAbundant.HACompose43
import HighlyAbundant.HACompose47
import HighlyAbundant.HACompose49
import HighlyAbundant.HACompose53
import HighlyAbundant.HACompose59
import HighlyAbundant.HACompose61
import HighlyAbundant.HACompose64
import HighlyAbundant.HACompose67
import HighlyAbundant.HACompose81
import HighlyAbundant.HACompose83
import HighlyAbundant.HACompose89
import HighlyAbundant.HACompose125
import HighlyAbundant.HACompose127
import HighlyAbundant.HACompose128
import HighlyAbundant.HACompose131
import HighlyAbundant.HACompose137
import HighlyAbundant.HACompose139
import HighlyAbundant.HACompose169

/-!
# Characterization of highly abundant `lcmRange n` for `1 ≤ n ≤ 10 ^ 40`

`lcmRange n` is highly abundant iff `n` lies in the explicit set listed in the README.
-/

open Nat

/-- Logic core: given all anchor HA facts and all chunk non-HA facts as hypotheses, the
characterization follows by the block-transfer lemma and arithmetic. -/
private theorem iff_of_facts {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 10 ^ 40)
    (h1 : IsHighlyAbundant (lcmRange 1))
    (h2 : IsHighlyAbundant (lcmRange 2))
    (h3 : IsHighlyAbundant (lcmRange 3))
    (h4 : IsHighlyAbundant (lcmRange 4))
    (h5 : IsHighlyAbundant (lcmRange 5))
    (h7 : IsHighlyAbundant (lcmRange 7))
    (h8 : IsHighlyAbundant (lcmRange 8))
    (h9 : IsHighlyAbundant (lcmRange 9))
    (h11 : IsHighlyAbundant (lcmRange 11))
    (h13 : IsHighlyAbundant (lcmRange 13))
    (h16 : IsHighlyAbundant (lcmRange 16))
    (h17 : IsHighlyAbundant (lcmRange 17))
    (h19 : IsHighlyAbundant (lcmRange 19))
    (h23 : IsHighlyAbundant (lcmRange 23))
    (h25 : IsHighlyAbundant (lcmRange 25))
    (h27 : IsHighlyAbundant (lcmRange 27))
    (h29 : IsHighlyAbundant (lcmRange 29))
    (h31 : IsHighlyAbundant (lcmRange 31))
    (h32 : IsHighlyAbundant (lcmRange 32))
    (h37 : IsHighlyAbundant (lcmRange 37))
    (h41 : IsHighlyAbundant (lcmRange 41))
    (h43 : IsHighlyAbundant (lcmRange 43))
    (h47 : IsHighlyAbundant (lcmRange 47))
    (h49 : IsHighlyAbundant (lcmRange 49))
    (h53 : IsHighlyAbundant (lcmRange 53))
    (h59 : IsHighlyAbundant (lcmRange 59))
    (h61 : IsHighlyAbundant (lcmRange 61))
    (h64 : IsHighlyAbundant (lcmRange 64))
    (h67 : IsHighlyAbundant (lcmRange 67))
    (h81 : IsHighlyAbundant (lcmRange 81))
    (h83 : IsHighlyAbundant (lcmRange 83))
    (h89 : IsHighlyAbundant (lcmRange 89))
    (h125 : IsHighlyAbundant (lcmRange 125))
    (h127 : IsHighlyAbundant (lcmRange 127))
    (h128 : IsHighlyAbundant (lcmRange 128))
    (h131 : IsHighlyAbundant (lcmRange 131))
    (h137 : IsHighlyAbundant (lcmRange 137))
    (h139 : IsHighlyAbundant (lcmRange 139))
    (h169 : IsHighlyAbundant (lcmRange 169))
    (c1 : ∀ i, 71 ≤ i → i ≤ 80 → ¬ IsHighlyAbundant (lcmRange i))
    (c2 : ∀ i, 97 ≤ i → i ≤ 124 → ¬ IsHighlyAbundant (lcmRange i))
    (c3 : ∀ i, 149 ≤ i → i ≤ 168 → ¬ IsHighlyAbundant (lcmRange i))
    (c4 : ∀ i, 173 ≤ i → i ≤ 10029542461709537120579603199949529595648 →
      ¬ IsHighlyAbundant (lcmRange i)) :
    IsHighlyAbundant (lcmRange n) ↔
      n ∈ Finset.Icc 1 70 ∪ Finset.Icc 81 96 ∪ Finset.Icc 125 148 ∪ Finset.Icc 169 172 := by
  have blk : ∀ (q e : ℕ), IsHighlyAbundant (lcmRange q) →
      (∀ x ∈ Finset.Ioc q e, ¬ IsPrimePow x) →
      ∀ k, q ≤ k → k ≤ e → IsHighlyAbundant (lcmRange k) :=
    fun q e hq hgap k hk1 hk2 => isHighlyAbundant_lcmRange_of_no_primePow_Ioc hk1
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

/-- For `1 ≤ n ≤ 10 ^ 40`, `lcmRange n` is highly abundant iff `n` lies in the explicit
finite set of the README (the union of four intervals of admissible indices). -/
theorem isHighlyAbundant_lcmRange_iff {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 10 ^ 40) :
    IsHighlyAbundant (lcmRange n) ↔
      n ∈ Finset.Icc 1 70 ∪ Finset.Icc 81 96 ∪ Finset.Icc 125 148 ∪ Finset.Icc 169 172 :=
  iff_of_facts hn1 hn
    (by
      have h : lcmRange 1 = 1 := by decide
      intro m hm hlt
      omega)
    Sage.isHighlyAbundant_lcmRange_2 Sage.isHighlyAbundant_lcmRange_3
    Sage.isHighlyAbundant_lcmRange_4 Sage.isHighlyAbundant_lcmRange_5
    Sage.isHighlyAbundant_lcmRange_7 Sage.isHighlyAbundant_lcmRange_8
    Sage.isHighlyAbundant_lcmRange_9 Sage.isHighlyAbundant_lcmRange_11
    Sage.isHighlyAbundant_lcmRange_13 Sage.isHighlyAbundant_lcmRange_16
    Sage.isHighlyAbundant_lcmRange_17 Sage.isHighlyAbundant_lcmRange_19
    Sage.isHighlyAbundant_lcmRange_23 Sage.isHighlyAbundant_lcmRange_25
    Sage.isHighlyAbundant_lcmRange_27 Sage.isHighlyAbundant_lcmRange_29
    Sage.isHighlyAbundant_lcmRange_31 Sage.isHighlyAbundant_lcmRange_32
    Sage.isHighlyAbundant_lcmRange_37 Sage.isHighlyAbundant_lcmRange_41
    Sage.isHighlyAbundant_lcmRange_43 Sage.isHighlyAbundant_lcmRange_47
    Sage.isHighlyAbundant_lcmRange_49 Sage.isHighlyAbundant_lcmRange_53
    Sage.isHighlyAbundant_lcmRange_59 Sage.isHighlyAbundant_lcmRange_61
    Sage.isHighlyAbundant_lcmRange_64 Sage.isHighlyAbundant_lcmRange_67
    Sage.isHighlyAbundant_lcmRange_81 Sage.isHighlyAbundant_lcmRange_83
    Sage.isHighlyAbundant_lcmRange_89 Sage.isHighlyAbundant_lcmRange_125
    Sage.isHighlyAbundant_lcmRange_127 Sage.isHighlyAbundant_lcmRange_128
    Sage.isHighlyAbundant_lcmRange_131 Sage.isHighlyAbundant_lcmRange_137
    Sage.isHighlyAbundant_lcmRange_139 Sage.isHighlyAbundant_lcmRange_169
    chunk1 chunk2 chunk3 chunk4