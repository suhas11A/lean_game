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
  Hint "When there is hypotheses `x ∈ ∅` any goal is trivially true (Recall from Chapter 1). To prove this in LEAN execute `cases hx`."
  Hint "`cases` is a tactic used to split a hypotheses into cases."
  Hint "If we have `hx : x ∈ Set(a,b)`, then `cases hx` would change the tactic state into 2 goals(same as original goal) with diff hypotheses: `hx : x ∈ A` in the first goal and `hx : x ∈ B` in the second goal."
  cases hx

Conclusion "
Using this we can prove any 2 empty sets are equal. Say A and B are empty sets, from the above proof A ⊆ B and B ⊆ A, and from
definition of eqauality in sets, A = B.
"

NewTactic cases
