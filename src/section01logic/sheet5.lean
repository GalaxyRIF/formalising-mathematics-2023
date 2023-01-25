/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

-/

variables (P Q R S : Prop)

example : P ↔ P :=
begin
  refl,
end

example : (P ↔ Q) → (Q ↔ P) :=
begin
  intro hpq,
  rw hpq,
end

example : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split,
  intro hpq,
  rw hpq,
  intro hqp,
  rw hqp,
end

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intro hpq,
  intro hqr,
  rw hpq,
  exact hqr,
end

example : P ∧ Q ↔ Q ∧ P :=
begin
  split,
  intro hpq,
  cases hpq,
  split,
  exact hpq_right,
  exact hpq_left,
  intro hqp,
  cases hqp,
  split,
  exact hqp_right,
  exact hqp_left,

end

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
begin
  split,
  -- (→) 
  intro h1,
  cases h1,
  cases h1_left,
  split,
  exact h1_left_left,
  split,
  exact h1_left_right,
  exact h1_right,
  -- (←)
  intro h2,
  cases h2,
  cases h2_right,
  split,
  split,
  exact h2_left,
  exact h2_right_left,
  exact h2_right_right,
end

example : P ↔ (P ∧ true) :=
begin
  split,
  intro hp,
  split,
  exact hp,
  triv,
  intro hpt,
  cases hpt,
  exact hpt_left,
end

example : false ↔ (P ∧ false) :=
begin
  split,
  intro hf,
  split,
  exfalso,
  triv,
  triv,
  intro hpf,
  cases hpf,
  triv,
end

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
begin
  intro hpq,
  intro hrs,
  cases hpq,
  cases hrs,
  split,

  intro hpr,
  cases hpr,
  split,

  apply hpq_mp,
  exact hpr_left,

  apply hrs_mp,
  exact hpr_right,


  intro hqs,
  cases hqs,
  split,

  apply hpq_mpr,
  exact hqs_left ,

  apply hrs_mpr,
  exact hqs_right,
end

example : ¬ (P ↔ ¬ P) :=
begin
  simp,
  sorry,
end
