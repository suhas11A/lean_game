import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 6
Title "Basic example in intervals"

Introduction "
We will now prove a very simple yet important result in Sets.
"
open Set
/-- Let X be a set. Prove that ∅ ⊆ X -/
Statement (U :Type)(X : Set U): ∅ ⊆ X := by
  intro x hx
  Hint "When there is hypotheses `x ∈ ∅` any goal is trivially true. To prove this execute `cases hx`."
  cases hx

Conclusion "
Using this we can prove any 2 empty sets are equal. Say A and B are empty sets, from the above proof A ⊆ B and B ⊆ A, and from
definition of eqauality in sets, A = B.
"

NewTactic cases
