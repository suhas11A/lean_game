import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 3
Title "Basic example in intervals"

Introduction "
Following along with Proposition 2.1.20.

To prove tha goal
"
open Set
/-- Suppose A⊆B, B⊆C, and x∈A. Then x∈C. -/
Statement (U : Type)(A : Set U)(B : Set ℕ): 0 = 0 := by
  -- just a place holder level toexplain types vs sets
  rfl

Conclusion "--conc--"

NewTactic rfl «have»
