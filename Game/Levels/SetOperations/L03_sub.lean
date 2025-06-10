import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "SetOperations"
Level 3
Title "Basic example in intervals"

Introduction "
This example is inspired from Exercise 2.2.30 from infinite descent.

Here the goal is of form `↔`. First we need to split the goal into 2 sub-goals.
"
open Set
/-- Let X and Y be sets. Prove that X ⊆ Y if and only if X∩Y = X. -/
Statement (U : Type)(X Y : Set U): X ⊆ Y ↔ (X ∩ Y = X) := by
  Hint "Recall which Theorem is used to split an `↔` goal."
  apply Iff.intro
  Hint "To prove a result of type `p → q` we need to assume `p` and show `q`."
  intro h
  Hint "To prove that 2 Sets are equal it suffices to show ..."
  apply Subset.antisymm
  Hint "To show `A ⊆ B` it is enough to show ..."
  intro a
  intro a_1
  rw[mem_inter_iff] at a_1
  exact a_1.1
  intro a
  intro a_1
  Hint "To prove `x ∈ A ∩ B` we need to show `x ∈ A` and `x ∈ B`."
  rw[mem_inter_iff]
  have h4 := h a_1
  exact And.intro a_1 h4
  intro h
  intro a
  intro a_1
  rw[← h] at a_1
  rw[mem_inter_iff] at a_1
  exact a_1.2



Conclusion "--conc--"


NewTheorem Set.mem_inter_iff Set.Subset.antisymm
NewTactic symm apply
