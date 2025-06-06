import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "SetOperations"
Level 1
Title "Basic example in intervals"

Introduction "
Following along with Example 2.1.17.

To prove tha goal
"
open Set
/-- Suppose x∈A∩B. Then x∈B. -/
Statement (U : Type)(x : U)(A B : Set U)(h : x ∈ A ∩ B): x ∈ B := by
  rw[mem_inter_iff] at h
  exact h.2

Conclusion "--conc--"


NewTheorem Set.mem_inter_iff
