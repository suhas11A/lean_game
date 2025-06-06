import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 2
Title "Basic example in intervals"

Introduction "
Following along with Example 2.1.17.

To prove tha goal
"
open Set
/-- Suppose A is a set. Then A⊆A. -/
Statement (a b c d : ℝ)(ha : a < c)(hc : d < b): Icc c d ⊆ Ioo a b := by
  intro x hx
  rw [mem_Icc] at hx
  have h1 := hx.1
  have h2 := hx.2
  have h3 := lt_of_lt_of_le ha h1
  have h4 := lt_of_le_of_lt h2 hc
  have h : a < x ∧ x < b := And.intro h3 h4
  rw [← mem_Ioo] at h
  exact h

Conclusion "--conc--"


NewTactic rw intro And.intro
NewTheorem Set.mem_Icc Set.mem_Ioo lt_of_lt_of_le lt_of_le_of_lt Set.Icc Set.Ioo
