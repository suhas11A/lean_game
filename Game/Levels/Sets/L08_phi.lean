import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 8
Title "Basic example in intervals"

Introduction "
Following along with Proposition 2.1.20.

To prove tha goal
"
open Set
/-- Let a,b ∈ R. Prove that [a,b] is empty if and only if a > b. -/
Statement (U : Type)(X : Set U): ∅ ⊆ X := by
  intro x hx
  cases hx

Conclusion "
Using this we can prove any 2 empty sets are equal. Say A and B are empty sets, from the above proof A ⊆ B and B ⊆ A, and from
definition of eqaualit in sets, A = B.
"

