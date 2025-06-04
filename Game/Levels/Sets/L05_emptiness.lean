import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 5
Title "Basic example in intervals"

Introduction "
Following along with Proposition 2.1.20.

To prove tha goal
"
open Set
/-- Let a,b ∈ R. Prove that [a,b] is empty if and only if a > b. -/
Statement (a b : ℕ): Icc a b = ∅ ↔ a > b := by
  constructor
  intro h1
  have h_ : a = a := rfl
  have h_a_eq : a ≤ a := le_of_eq h_
  cases lt_trichotomy a b
  have h_a_le : a ≤ b := le_of_lt h
  have h_and : a ≤ a ∧ a ≤ b := And.intro h_a_eq h_a_le
  rw[← mem_Icc] at h_and
  rw [h1] at h_and
  cases h_and
  cases h
  have h_b_eq : a ≤ b := le_of_eq h_1
  have h_and : a ≤ a ∧ a ≤ b := And.intro h_a_eq h_b_eq
  rw[← mem_Icc] at h_and
  rw [h1] at h_and
  cases h_and
  exact h_1
  intro h
  ext x
  constructor
  intro hx
  rw[mem_Icc] at hx
  have h1 := hx.1
  have h2 := hx.2
  have h3 := le_trans h1 h2
  exfalso
  exact not_le_of_gt h h3
  intro
  exfalso
  cases a_1

Conclusion "
--conc--
"

NewTactic exact rw intro
