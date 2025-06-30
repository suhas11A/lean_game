import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "SetOperations"
Level 3
Title "An Example involving intervals"

Introduction "
This example is inspired from Exercise 2.2.14 from infinite descent.

`Ico a b` represent the interval [a,b) in LEAN.
"
open Set
/-- Suppose a < c < b < d. Then show that [a,b) ∩ [c,d) = [c,b). -/
Statement (a b c d : ℝ)(h1 : a < c)(h3 : b < d): (Ico a b) ∩ (Ico c d) = Ico c b := by
  Hint "There are 2 ways you can prove `A = B`, first one being splitting goal into `A ⊆ B` and `B ⊆ A` or second strategy being
   changing the goal into `x ∈ A ↔ x ∈ B`. Here I will be using `apply Subset.antisymm` since it gives us clearer understanding of the concept of equality."
  Hint "There is tactic named `clear` that will clear any hypotheses or variable that you think its not useful anymore."
  Hint "Read and learn theorems `le_of_lt`, `lt_trans` and `mem_Ico` as they will be useful."
  apply Subset.antisymm
  Hint "Recall how to solve a goal of type `A ⊆ B` from previous world."
  intro x h
  Hint "`rw[mem_Ico]` only works when the goal or hypotheses is of form `{h} : x ∈ Ico a b`, but if it's of the form `h : x ∈ Ico a b ∩ Ico c d` then `rw[mem_Ico]` will fail.
   We need to first expand the definition of intersection and then use `mem_Ico` twice to completely expand {h}."
  rw[mem_inter_iff, mem_Ico, mem_Ico] at h
  Hint "It is better to first rewrite all terms that contain `Ico` (In both goal and hypotheses) because then you'd only have to work with inequalities."
  rw[mem_Ico]
  Hint "Recall how to show a goal of form `p ∧ q`."
  and_intro
  exact h.2.1
  exact h.1.2
  intro x h
  Hint "First rewrite all `x ∈ Interval` into inequalities in goal and hypotheses."
  rw[mem_Ico] at h
  rw[mem_inter_iff, mem_Ico, mem_Ico]
  Hint "Eliminate and in {h} so that we can work with the inequalities separately."
  and_elim h into hc, hb
  Hint "Now use theorems `lt_trans`, `le_of_lt` to get required inequalities.
   Executing `have hd : x < d := lt_trans {hb} {h3}` will create a new hypotheses `hd : x < d `.
   Similarly try to get a new hypotheses `ha : a ≤ x` using known theorems related to comparison."
  have hd : x < d := lt_trans hb h3
  have ha : a ≤ x := le_of_lt (lt_of_lt_of_le h1 hc)
  and_intro
  exact ha
  exact hb
  exact hc
  exact hd



Conclusion "Nice! You now have a solid understanding of intervals and intersection."


NewTheorem Set.mem_Ico lt_trans le_of_lt lt_of_lt_of_le
NewHiddenTactic clear
