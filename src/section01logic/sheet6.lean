/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/

-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.

variables (P Q R S : Prop)

example : P → P ∨ Q :=
begin
  intro hp,
  left,
  exact hp,
end

example : Q → P ∨ Q :=
begin
  intro hq,
  right,
  exact hq,
end

example : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  intro hpq,
  intro hpr,
  intro hqr,
  cases hpq with hp hq,
  apply hpr,
  exact hp,
  apply hqr,
  apply hq,
end

-- symmetry of `or`
example : P ∨ Q → Q ∨ P :=
begin
  intro hpq,
  cases hpq with hp hq,
  right,
  exact hp,
  left,
  exact hq,
end

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
begin
  split,
  intro hpqr,
  cases hpqr with a b,
  cases a with aa ab,
  left,
  exact aa,
  right,
  left, 
  exact ab,
  right,
  right,
  exact b,
  intro hpqr2,
  cases hpqr2 with ha hb,
  left,
  left,
  exact ha,
  cases hb with hba hbb,
  left,
  right,
  exact hba,
  right,
  exact hbb,
end

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  intro hpr,
  intro hqs,
  intro hpq,
  cases hpq with hp hq,
  left,
  apply hpr,
  exact hp,
  right,
  apply hqs,
  exact hq,
end

example : (P → Q) → P ∨ R → Q ∨ R :=
begin
  intro hpq,
  intro hpr,
  cases hpr with hp hr,
  left,
  apply hpq,
  exact hp,
  right,
  exact hr,
end

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
begin
  intro hpr,
  intro hqs,
  cases hpr,
  cases hqs,
  split,
  intro hpq,
  cases hpq with hp hq,
  left,apply hpr_mp,exact hp,
  right,apply hqs_mp,exact hq,
  intro hrs,
  cases hrs with hr hs,
  left, apply hpr_mpr, exact hr,
  right, apply hqs_mpr,exact hs,
end

-- de Morgan's laws
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
  exact not_or_distrib,
  sorry,
end

example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  sorry
end
