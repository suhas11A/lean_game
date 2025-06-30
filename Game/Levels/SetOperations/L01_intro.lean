import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "SetOperations"
Level 1
Title "Intro to Intersection of 2 sets"

Introduction "
Let us prove a basic result involving intersection(`∩`) to get a better understanding. Click on `∩` to know more about it.
"
open Set
/-- Suppose x∈A∩B. Then x∈B. -/
Statement (U : Type)(x : U)(A B : Set U)(h : x ∈ A ∩ B): x ∈ B := by
  Hint "`x ∈ A ∩ B` is equivalent to saying that the element x is a member of both A and B."
  Hint "Read and use the theorem `mem_inter_iff` (member of intersection if and only if) to rewrite `x ∈ A ∩ B` into `x ∈ A ∧ x ∈ B`."
  rw[mem_inter_iff] at h
  Hint "if `p ∧ q` is assumed then `p` can be proved, recall how."
  exact h.2

Conclusion "Directly executing `and_elim h into ha, hb` without rewriting with `mem_inter_iff` will also change the hypotheses, but it is important to understand what `x ∈ A ∩ B` means."


/-- If `A` and `B` are sets, then `A ∩ B` is the intersection of `A` and `B`.
To enter the symbol `∩`, type `\inter` or `\cap`. -/
DefinitionDoc inter as "∩"


NewTheorem Set.mem_inter_iff
NewDefinition inter
