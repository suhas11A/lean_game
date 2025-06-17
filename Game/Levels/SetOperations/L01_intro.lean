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
  Hint "`x ∈ A ∩ B` means that the element x is a member of both A and B."
  Hint "Read and use the theorem `mem_inter_iff` (member of intersection if and only if) to rewrite `x ∈ A ∩ B` into `x ∈ A ∧ x ∈ B`."
  rw[mem_inter_iff] at h
  exact h.2

Conclusion "Directly executing `exact h.2` will also close the goal, but it is important to understand what `x ∈ A ∩ B` means."


/-- If `A` and `B` are sets, then `A ∩ B` is the intersection of `A` and `B`.
To enter the symbol `∩`, type `\inter` or `\cap`. -/
DefinitionDoc inter as "∩"


NewTheorem Set.mem_inter_iff Set.mem_inter
NewTactic exact rw
NewDefinition Set  inter
