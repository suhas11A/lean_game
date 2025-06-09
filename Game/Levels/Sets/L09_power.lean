import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 9
Title "Basic example in intervals"

Introduction "
This example is imspired from Example 2.1.37 from infinite descent.
"
open Set
/-- Suppose A = {a,b}. Then P(A) = {∅, {a}, {b}, {a,b}}. -/
Statement (E : Type)(a b : E): {∅, {a}, {b}, {a, b}} ⊆ Set.powerset ({a, b}) := by
  intro x hx
  rw[mem_powerset_iff]
  cases hx
  rw[h]
  simp
  cases h
  rw[h_1]
  simp
  cases h_1
  rw[h]
  simp
  simp[mem_singleton] at h
  rw[h]

Conclusion "--conc--"


NewTheorem Set.mem_singleton Set.mem_powerset_iff
NewTactic simp
