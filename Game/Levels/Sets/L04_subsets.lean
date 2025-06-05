import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 4
Title "Basic example in intervals"

Introduction "
Following along with Proposition 2.1.20.

To prove tha goal
"
open Set
/-- Suppose A⊆B, B⊆C, and x∈A. Then x∈C. -/
Statement (U : Type)(A B C : Set U)(ha : A ⊆ B)(hb : B ⊆ C): A ⊆ C := by
  intro x h1
  have h2 : x ∈ B := ha h1
  have h3 : x ∈ C := hb h2
  exact h3 -- or do `exact hb h2`, both mean the same

Conclusion "--conc--"
