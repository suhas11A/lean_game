import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "SetOperations"
Level 1
Title "Basic example in intervals"

Introduction "
Let us prove a basic result involving intersection(`∩`) to get a better understanding.
"
open Set
/-- Suppose x∈A∩B. Then x∈B. -/
Statement (U : Type)(x : U)(A B : Set U)(h : x ∈ A ∩ B): x ∈ B := by
  Hint "Read and use the theorom `mem_inter_iff` (member of intersection if and only if)."
  rw[mem_inter_iff] at h
  exact h.2

Conclusion "Directly executing `exact h.2` will also close the goal, but it is important to understand what `x ∈ A ∩ B` means."


NewTheorem Set.mem_inter_iff Set.mem_inter
NewTactic exact rw
NewDefinition Set
