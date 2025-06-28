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
  Hint "When there is hypotheses `x ∈ ∅` (which is not possible as no such x exists) any goal is trivially true (Recall from Chapter 1 that from a false assumption anything can be shown). To prove this in LEAN execute `cases hx`."
  Hint "`cases` is a tactic that can be used to split a hypotheses into cases."
  Hint "If we have `hx : x ∈ Set(a,b)`, then `cases hx` would split the tactic state into 2 tactic states (with goals same as the original goal) but with diff hypotheses: `hx : x = a` in the first state and `hx : x = b` in the second state."
  cases hx

Conclusion "
Using this we can prove any 2 empty sets are equal. Say A and B are empty sets, from the above proof A ⊆ B and B ⊆ A, and from
definition of equality in sets, A = B.
"

NewTactic cases
