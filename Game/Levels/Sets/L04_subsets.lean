import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 4
Title "Subset Trasitivity"

Introduction "
This example is inspired from Proposition 2.1.20 in Infinite Descent.

From this level we will be talking of objects being of a general type `U`, and set of these objects being of type `Set U`.
"
open Set
/-- Suppose A ⊆ B, B ⊆ C. Then A ⊆ C. -/
Statement (U : Type)(A B C : Set U)(ha : A ⊆ B)(hb : B ⊆ C): A ⊆ C := by
  Hint "We now know how we can prove a goal of form `A ⊆ B`, proceed."
  intro x hx
  Hint "What does it mean when you have `ha : A ⊆ B`?? It means that every element of A is also a mem of B.
   Thus `ha: A ⊆ B` is the proof of `x ∈ A → x ∈ B`."
  Hint "Unfold the definition of Subset at `ha` and `hb` using theorem `subset_def`."
  rw [subset_def] at ha
  rw [subset_def] at hb
  Hint "`ha : ∀ x ∈ A, x ∈ B` is same as `ha : x ∈ A → x ∈ B`, we can eliminate ∀ in `ha` and make it into `x ∈ A → x ∈ B` using the tactic `forall_elim`.
   Similarly do the same for `hb`."
  forall_elim ha of x into h2
  forall_elim hb of x into h3
  Hint "We now know enough about implications and related tactics, you can take it from here."
  imp_elim h2 with hx into conc1
  imp_elim h3 with conc1 into conc2
  exact conc2

Conclusion "We are now familiar with proof strategies to prove a goal of form `A ⊆ B` and to use a hypotheses of form `A ⊆ B`."
