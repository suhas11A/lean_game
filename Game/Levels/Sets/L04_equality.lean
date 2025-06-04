import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 4
Title "Basic example in intervals"

Introduction "
Following along with Proposition 2.1.20.

To prove tha goal
"
open Set
/-- Suppose A is a set. Then (Aᶜ)ᶜ= A. -/
Statement (A : Set ℕ): (Aᶜ)ᶜ = A := by
  apply Subset.antisymm
  intro a a_1
  rw[mem_compl_iff] at a_1
  rw[mem_compl_iff] at a_1
  push_neg at a_1
  exact a_1
  intro a a_1
  rw[mem_compl_iff]
  rw[mem_compl_iff]
  push_neg
  exact a_1

Conclusion "--conc--"

NewTactic exact rw intro
