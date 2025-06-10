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
  ext x
  rw[mem_prod]
  apply Iff.intro
  intro h
  cases h.2
  intro
  cases a




Conclusion "--conc--"


NewTheorem Set.mem_prod
