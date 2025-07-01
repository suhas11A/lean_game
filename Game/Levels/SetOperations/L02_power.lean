import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic


World "Set Operations"
Level 2
Title "Power Set"

Introduction "
This example is inspired from Example 2.1.37 from infinite descent.
"
open Set
/-- Suppose A and B are Sets. Then P(A ∩ B) = P(A) ∩ P(B). -/
Statement (U : Type)(A B : Set U): powerset (A ∩ B) = powerset (A) ∩ powerset (B) := by
  Hint "We now know which proof strategy to use to prove 2 sets are equal."
  apply Subset.antisymm
  intro x hx
  Hint "An element `{x}` is a member of `𝒫(A)` if and only if `{x} ⊆ A`.
   Theorem `mem_powerset_iff` can be used to rewrite `{x} ∈ 𝒫(A)` into `{x} ⊆ A`."
  rw[mem_powerset_iff] at hx
  Hint "Open the definition of intersection in the goal and split into two tactic states using the tactic `and_intro`."
  and_intro
  Hint "Using `mem_powerset_iff`, rewrite the goal."
  rw[mem_powerset_iff]
  Hint "We know that `A ∩ B ⊆ A` and having this as a hypotheses will bring us a step closer to closing the goal. Recall the tactic `have`."
  have hh : A ∩ B ⊆ A
  Hint "You know how to prove this, go ahead."
  intro a ha
  exact ha.1
  exact subset_trans hx hh
  Hint "This is similar to previous goal and includes same series of steps."
  rw[mem_powerset_iff]
  have hh : A ∩ B ⊆ B
  intro a ha
  exact ha.2
  exact subset_trans hx hh
  Hint "We have shown one direction of subset, we wil now show the other direction as well."
  intro x hx
  Hint "Rewrite the goal and {hx} using the definitions of \" member of a power set\" and intersection and finish this proof from here."
  rw[mem_inter_iff] at hx
  and_elim hx into h5, h6
  rw[mem_powerset_iff] at h5
  rw[mem_powerset_iff] at h6
  rw[mem_powerset_iff]
  intro a aa
  and_intro
  exact h5 aa
  exact h6 aa


Conclusion "We are now familiar with the basics of Sets, let's move on to the next world to know more about them."


NewTheorem Set.mem_powerset_iff
