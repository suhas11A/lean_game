import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "SetOperations"
Level 3
Title "Exercise involving Intersection and Iff"

Introduction "
This example is inspired from Exercise 2.2.30 from infinite descent.

Here the goal is of form `↔`. First we need to split the goal into 2 sub-goals.
"
open Set
/-- Let X and Y be sets. Prove that X ⊆ Y if and only if X∩Y=X. -/
Statement (U : Type)(X Y : Set U): X ⊆ Y ↔ (X ∩ Y = X) := by
  Hint "Recall which tactic is used to split an `↔` goal."
  iff_intro
  Hint "To prove a result of type `p → q` we need to assume `p` and show `q`."
  imp_intro h
  Hint "To prove that 2 Sets are equal it suffices to show ..."
  apply Subset.antisymm
  Hint "To show `A ⊆ B` it is enough to show ..."
  intro a a_1
  Hint "Recall first level in this world"
  exact a_1.1
  intro a a_1
  Hint "To prove `x ∈ A ∩ B` we need to show `x ∈ A` and `x ∈ B`. To rewrite the goal `{a} ∈ X ∩ Y` into `{a} ∈ X ∧ {a} ∈ Y` we use a theorem we have previously learned."
  rw[mem_inter_iff]
  and_intro
  exact a_1
  exact h a_1
  Hint "We now prove the second part of the iff goal first presented."
  imp_intro h
  intro a a_1
  Hint "Since we have `{h} : X ∩ Y = X` we can replace `X` in `{a_1}` with `X ∩ Y`."
  rw[← h] at a_1
  rw[mem_inter_iff] at a_1
  exact a_1.2



Conclusion "We now go on to prove the famous De Morgans laws for Sets."

