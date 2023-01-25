/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2023/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : ¬ true → false :=
begin
  intro ht,
  change  true → false at ht,
  apply ht,
  triv,
end

example : false → ¬ true :=
begin
  intro hf,
  triv,
end

example : ¬ false → true :=
begin
  intro hf,
  change false → false at hf,
  triv,
end

example : true → ¬ false :=
begin
  intro ht,
  triv,
end

example : false → ¬ P :=
begin
  intro hf,
  exfalso,
  apply hf,
end

example : P → ¬ P → false :=
begin
  intro hp,
  intro hnp,
  change P → false at hnp,
  apply hnp,
  apply hp,
end

example : P → ¬ (¬ P) :=
begin
  intro hP,
  triv,
end

example : (P → Q) → (¬ Q → ¬ P) :=
begin
  intro hpq,
  intro hnq,
  change Q → false at hnq,
  by_contra,
  apply hnq,
  apply hpq,
  apply h,
end

example : ¬ ¬ false → false :=
begin
  intro hnnf,
  by_contra hnf,
  apply hnnf,
  exact hnf,
  -- A simple 'simp,' would also work
end

example : ¬ ¬ P → P :=
begin
  intro hnnp,
  by_contra hnp,
  apply hnnp,
  exact hnp,
  -- A simple 'simp,' would also work
end

example : (¬ Q → ¬ P) → (P → Q) :=
begin
sorry,
end