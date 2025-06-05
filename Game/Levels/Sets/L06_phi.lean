import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 6
Title "Basic example in intervals"

Introduction "
Following along with Proposition 2.1.20.

To prove tha goal
"
open Set
/-- Let X be a set. Prove that ∅ ⊆ X -/
Statement (U :Type)(X : Set U): ∅ ⊆ X := by
  intro x hx
  cases hx

Conclusion "
--conc--
"

NewTactic cases
