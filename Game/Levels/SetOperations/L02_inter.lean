import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "SetOperations"
Level 2
Title "Basic example in intervals"

Introduction "
This example is inspired from Exercise 2.2.14 from infinite descent.

`Ico a b` represent the interval [a,b) in LEAN.
"
open Set
/-- Suppose a < c < b < d. Then show that [a,b) ∩ [c,d) = [c,b). -/
Statement (a b c d : ℝ)(h1 : a < c)(h3 : b < d): (Ico a b) ∩ (Ico c d) = Ico c b := by
  Hint "There are 2 ways you can prove `A = B`, first one being splitting goal into `A ⊆ B` and `B ⊆ A` or second strategy being
  using the tactic `ext` to change the goal into `x ∈ A ↔ x ∈ B`. Here I will be using `apply Subset.antisymm` but you can use either to close the goal."
  Hint "There is tactic named `clear` that will clear any hypotheses or variable if you think its not useful anymore."
  Hint "Read and learn theorems `le_of_lt`, `lt_trans` and `mem_Ico` as they will be useful."
  apply Subset.antisymm
  Hint "Recall how to solve a goal of type `A ⊆ B`."
  intro x h
  Hint "`rw[mem_Ico]` only works when the goal or hypotheses is of form `h : x ∈ Ico a b`, but if it's of the form `h : x ∈ Ico a b ∩ Ico c d` then `rw` will fail."
  Hint "Use `simp[mem_Ico] at h` to rewrite both the `∈ Ico`."
  simp[mem_Ico] at h
  Hint "It is better to first rewrite all terms that contain `Ico` because now you only have to work with inequalities."
  rw[mem_Ico]
  Hint "Recall that exact can be used to close goal that don't directly match one of the hypotheses."
  Hint "`exact And.intro h.2.1 h.1.2` can close the goal here."
  exact And.intro h.2.1 h.1.2
  intro x h
  Hint "First rewrite all `x ∈ Interval` into inequalities."
  rw[mem_Ico] at h
  simp [mem_Ico]
  Hint "Now use theorems `lt_trans`, `le_of_lt`, etc. to get required inequalities."
  Hint "Look into the tactic `have` as it might be useful."
  have hd : x < d := lt_trans h.2 h3
  have ha : a ≤ x := le_of_lt (lt_of_lt_of_le h1 h.1)
  apply And.intro
  exact And.intro ha h.2
  exact And.intro h.1 hd



Conclusion "--conc--"


NewTheorem Set.mem_inter_iff Set.mem_Ico And.intro lt_trans le_of_lt lt_of_lt_of_le Iff.intro
NewTactic clear «have» ext intro apply split
