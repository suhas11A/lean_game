import Game.Metadata
import Mathlib.Data.Set.Defs
import Mathlib.Tactic.ApplyAt

World "Functions"
Level 5
Title "Characteristic functions"

Introduction "
Here, we will introduce characteristic functions and prove Theorem
3.1.25 together.

In Lean, the notation we will use for the characteristic function of a
set $A$ is `χ A`.  (You can type the letter `χ` with `\\chi`.)  For
instance, if `A` is the set of even natural numbers, then `χ A 8` will
equal 1, while `χ A 17` will equal 0.  You may also use the notation
`characteristic_function` in place of `χ`.

The characteristic function is fully characterized by three theorems,
which we have proven for you:
- `characteristic_function_0`, which says that $χ_A(x) = 0$ is
  equivalent to $x ∉ A$,
- `characteristic_function_1`, which says that $χ_A(x) = 1$ is
  equivalent to $x ∈ A$,
- `characteristic_function_value`, which says that $χ_A(x)$ is always
  either $0$ or $1$.

Following the argument in the book, use these facts to prove Theorem
3.1.25.
"

-- Could not find a definition of this in mathlib.  This requires
-- classical reasoning, as we need membership in A to be decidable.
noncomputable def characteristic_function {X : Type} (A : Set X) (x : X) : ℕ :=
  match Classical.propDecidable (x ∈ A) with
    | isTrue _ => 1
    | isFalse _ => 0

noncomputable abbrev χ {X : Type} := @characteristic_function X

-- Theorems for reasoning with characteristic_function.

theorem characteristic_function_0 {X : Type} (A : Set X) (x : X) :
  χ A x = 0 ↔ x ∉ A := by
  unfold χ
  unfold characteristic_function
  constructor
  · intro hchi
    split at hchi
    · contradiction
    · assumption
  · intro hx
    split
    · contradiction
    · trivial

theorem characteristic_function_1 {X : Type} (A : Set X) (x : X) :
  χ A x = 1 ↔ x ∈ A := by
  unfold χ
  unfold characteristic_function
  constructor
  · intro hchi
    split at hchi
    · assumption
    · contradiction
  · intro hx
    split
    · trivial
    · contradiction

theorem characteristic_function_value {X : Type} (A : Set X) (x : X) :
  χ A x = 0 ∨ χ A x = 1 := by
  unfold χ
  unfold characteristic_function
  split
  · right; trivial
  · left; trivial

/-- Let $X$ be a set and $U,V ⊆ X$.  Then $U = V$ if and only if $χ_U = χ_V$.
 -/
Statement (X : Type) (U V : Set X) : U = V ↔ χ U = χ V := by
  Hint "Start off by using `constructor` to split the goal into two subgoals."
  constructor
  · Hint "The forward direction is a straightforward substitution."
    intro huv
    rw [huv]
  · Hint "
    In the backwards direction, your goal is to prove equality of
    sets, so you will need to use `ext` and show containment in both
    directions.
    "
    intro hchi
    ext
    constructor
    · intro hxu
      Hint "
      Our first step is to show that the value of $χ_U({x})$ is $1$.
      Is there a property of $χ$ that would be helpful to use at `{hxu}`?
      "
      apply (characteristic_function_1 U x).mpr at hxu
      Hint "Now, we need to deduce that $χ_{V}({x})=1$."
      rw [hchi] at hxu
      Hint "Finally, we must show that $x∈V$."
      apply (characteristic_function_1 V x).mp
      assumption
    · Hint "
      Proving that $V⊆U$ is essentially the same as proving $U⊆V$,
      just with the variables switched around.  Just follow the same
      steps as before.
      "
      intro hxv
      apply (characteristic_function_1 V x).mpr at hxv
      rw [← hchi] at hxv
      apply (characteristic_function_1 U x).mp
      assumption

Conclusion "
In my proof, I only used `characteristic_function_1`, but the other
two theorems will be helpful for the next exercises, where we will
relate set operations to operations in the natural numbers through
characteristic functions.  Make sure you understand them!
"

NewTactic assumption
NewTheorem characteristic_function_0 characteristic_function_1 characteristic_function_value
