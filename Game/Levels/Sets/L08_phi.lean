import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 8
Title "Basic example in intervals"

Introduction "
This example is imspired from Exercise 2.1.32 from infinite descent.
"
open Set
/-- Let a,b ∈ R. Prove that [a,b] is empty if and only if a > b. -/
Statement (U : Type)(p : U → Prop): ∀ x ∈ (∅ : Set U), p x := by
  Hint "This is a simple proof, you are on your own."
  intro x hx
  cases hx

Conclusion "
This exercise is a logical technicality, which is counterintuitive for the same reason
that makes the principle of explosion (If a contradiction is assumed, any consequence may be derived) difficult to grasp. However, it
is extremely useful for proving facts about the empty set.
"
