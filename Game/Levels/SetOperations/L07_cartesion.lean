import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Basic

World "SetOperations"
Level 7
Title "Basic example in intervals"

Introduction "
Following along with Example 2.1.17.

To prove the goal
"

open Set
/--  Let X be a set. Prove that X×∅ = ∅. -/
Statement (U : Type)(X: Set U): X ×ˢ (∅ : Set U) = ∅ := by
  apply Subset.antisymm
  intro a ha
  rw[mem_prod] at ha
  cases ha.2
  intro a ha
  cases ha


Conclusion "--conc--"


NewTheorem Set.mem_prod
