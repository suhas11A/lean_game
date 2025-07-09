import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 8
Title "Triviality"

Introduction ""
open Set
/-- If p is proposition in x. Show that ∀ x ∈ ∅, p(x) is true. -/
Statement (U : Type)(p : U → Prop): ∀ x ∈ (∅ : Set U), p x := by
  Hint "This is a simple proof, you are on your own. We believe in you, less gooo..."
  fix x
  assume h
  contradiction

Conclusion "
This exercise is a logical technicality, which is counterintuitive for the same reason
that makes the principle of explosion (If a contradiction is assumed, any consequence may be derived) difficult to grasp. However, it
is extremely useful for proving facts about the empty set.
"
