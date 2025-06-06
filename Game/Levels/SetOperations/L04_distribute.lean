import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Basic

World "SetOperations"
Level 4
Title "Basic example in intervals"

Introduction "
Following along with Example 2.1.17.

To prove the goal
"
open Set
/-- Let X, Y and Z be sets. Prove that X∩(Y∪Z) = (X∩Y)∪(X∩Z). -/
Statement (U : Type)(X Y Z : Set U): X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) := by
  ext x
  rw[mem_inter_iff]
  rw[mem_union]
  rw[mem_union]
  rw[mem_inter_iff]
  constructor
  intro
  have a_1 := a.1
  have a_2 := a.2
  cases a_2
  left
  exact And.intro a_1 h
  right
  exact And.intro a_1 h
  intro
  cases a
  rw[and_or_left]
  left
  exact h
  rw[and_or_left]
  right
  exact h




Conclusion "--conc--"


NewTheorem and_or_left
