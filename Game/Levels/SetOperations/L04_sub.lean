import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "SetOperations"
Level 4
Title "Exercise involving Intersection and Iff"

Introduction "
Here the goal is of form `↔`. First we need to split the goal into 2 sub-goals.
"
open Set
/-- Let X and Y be sets. Prove that X ⊆ Y if and only if X∩Y=X. -/
Statement (U : Type)(X Y : Set U): X ⊆ Y ↔ (X ∩ Y = X) := by
  Hint "You will be using tactics and theorems you have previously learnt, go ahead and try to prove this on your own."
  iff_intro
  assume h
  apply Subset.antisymm
  intro a a_1
  exact a_1.1
  intro a a_1
  rw[mem_inter_iff]
  and_intro
  exact a_1
  exact h a_1
  Hint "We now prove the second part of the iff goal first presented."
  assume h
  intro a a_1
  Hint "Since we have `{h} : X ∩ Y = X` we can replace `X` in `{a_1}` with `X ∩ Y`."
  rw[← h] at a_1
  rw[mem_inter_iff] at a_1
  exact a_1.2



Conclusion "We now go on to prove the famous De Morgans laws for Sets."
