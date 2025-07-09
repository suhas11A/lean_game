import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 6
Title "Concept of Empty Set(∅)"

Introduction "
We will now prove a very simple yet important result in Sets.
"
open Set
/-- Let X be a set. Prove that ∅ ⊆ X -/
Statement (U :Type)(X : Set U): ∅ ⊆ X := by
  intro x hx
  Hint "When there is hypotheses `x ∈ ∅` (which is not possible as no such x exists) any goal is trivially true (Recall from Chapter 1 that from a false assumption anything can be shown). To prove this in LEAN execute we use the tactic `contradiction `."
  contradiction

Conclusion "
Using this we can prove any 2 empty sets (of same type) are equal. Say A and B are empty sets, from the above proof A ⊆ B and B ⊆ A, and from
definition of equality of sets, A = B.
"
