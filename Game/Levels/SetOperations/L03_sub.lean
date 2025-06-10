import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "SetOperations"
Level 3
Title "Basic example in intervals"

Introduction "
Following along with Example 2.1.17.

To prove the goal
"
open Set
/-- Let X and Y be sets. Prove that X ⊆ Y if and only if X∩Y = X. -/
Statement (U : Type)(X Y : Set U): X ⊆ Y ↔ (X ∩ Y = X) := by
  constructor
  intro h
  apply Subset.antisymm
  intro
  intro
  rw[mem_inter_iff] at a_1
  exact a_1.1
  intro
  intro
  rw[mem_inter_iff]
  have h4 := h a_1
  exact And.intro a_1 h4
  intro h
  intro a
  intro h_1
  symm at h
  rw[h] at h_1
  rw[mem_inter_iff] at h_1
  exact h_1.2



Conclusion "--conc--"


NewTheorem Set.mem_inter_iff Set.Subset.antisymm
NewTactic symm apply
