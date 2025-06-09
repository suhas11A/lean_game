import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith

World "SetOperations"
Level 8
Title "Basic example in intervals"

Introduction "
Following along with Example 2.1.17.

To prove the goal
"

open Set
/--  Let X be a set. Prove that X×∅ = ∅. -/
Statement : (⋂ n : ℕ, Ico (0 : ℝ) (1 + 1 / (n + 1))) = Icc 0 1 := by
  ext x
  simp[mem_Ico, mem_Icc, mem_inter]
  constructor
  intro h
  have hx0 : 0 ≤ x := (h 0).1
  constructor
  exact hx0
  by_contra hx
  apply lt_of_not_ge at hx
  sorry
  sorry


Conclusion "--conc--"
