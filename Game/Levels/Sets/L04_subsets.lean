import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 4
Title "Subset Transitivity"

Introduction "
From this level we will be talking of objects being of a general type `U`, and set of these objects being of type `Set U`.
"
open Set
/-- Suppose A ⊆ B, B ⊆ C. Then A ⊆ C. -/
Statement (U : Type)(A B C : Set U)(h1 : A ⊆ B)(h2 : B ⊆ C): A ⊆ C := by
  Hint "We now know how we can prove a goal of form `A ⊆ B`, proceed."
  intro x hx
  Hint "What does it mean when you have a hypotheses `{h1} : A ⊆ B`?? It means that every element of A is also a mem of B.
   Thus `{h1}: A ⊆ B` is the proof of `∀ x ∈ A, x ∈ B`."
  Hint "Unfold the definition of Subset at `{h1}` and `{h2}` using theorem `subset_def`."
  rw [subset_def] at h1
  rw [subset_def] at h2
  Hint "`{h1} : ∀ x ∈ A, x ∈ B` is same as `{h1} : x ∈ A → x ∈ B`, use the appropriate tactic to proceed with simplifying {h1}."
  forall_elim h1 of x into h3
  Hint "You know enough about implications, quantifiers and related tactics, you can finish it from here."
  forall_elim h2 of x into h4
  apply h4
  apply h3
  exact hx

Conclusion ""
