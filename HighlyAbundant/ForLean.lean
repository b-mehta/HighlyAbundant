/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

public import Init.Prelude

public section

/-!
# Lemmas belonging upstream

General facts about core definitions, stated here until they live in Lean itself.
-/

@[simp, grind =] theorem Nat.div_eq_div {a b : Nat} : a.div b = a / b := rfl
@[simp, grind =] theorem Nat.mod_eq_mod {a b : Nat} : a.mod b = a % b := rfl

attribute [grind =] Bool.and'_eq_and
