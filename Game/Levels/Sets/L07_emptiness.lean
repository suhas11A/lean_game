import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 7
Title "A non trivial example"

Introduction "
This example is inspired from Exercise 2.1.31 from infinite descent.
"
open Set
/-- Let a,b ∈ R. Prove that [a, b] is empty if and only if a > b. -/
Statement (a b : ℝ): Icc a b = ∅ ↔ a > b := by
  iff_intro
  intro h1
  by_contra h
  push_neg at h
  have h_ : a = a := rfl
  have h_a_eq : a ≤ a := le_of_eq h_
  have h_and : a ≤ a ∧ a ≤ b := And.intro h_a_eq h
  rw[← mem_Icc] at h_and
  rw [h1] at h_and
  cases h_and
  intro h
  ext x
  iff_intro
  intro hx
  and_elim hx into h1, h2
  have h3 := le_trans h1 h2
  exact not_le_of_gt h h3
  intro
  cases x_1

Conclusion ""

NewTheorem le_trans not_le_of_gt le_of_eq le_of_lt
