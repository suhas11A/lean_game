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
/-- Suppose x∈A∩B. Then x∈B. -/
Statement (a b c d : ℝ)(h1 : a < c)(h2 : c < b)(h3 : b < d): (Ico a b) ∩ (Ico c d) = Ico c b := by
  Hint "There are 2 ways you can prove `A = B`, first one being splitting goal into `A ⊆ B` and `B ⊆ A` or second strategy being
  using the tactic `ext` to chage the goal into `x ∈ A ↔ x ∈ B`. Here I will be using `ext` tactic but you can use either to close the goal."
  Hint "There is tactic named `clear` that will clear any hypotheses or variable if you feel like its not usefull anymore."
  Hint "Read and learn theorems `le_of_lt`, `lt_trans` and `mem_Ico` as they will be usefull."
  ext x
  Hint "Recall how to solve `↔` goals"
  apply Iff.intro
  intro h
  have ha := h.1
  have hb := h.2
  clear h
  rw[mem_Ico] at ha hb
  rw[mem_Ico]
  exact And.intro hb.1 ha.2
  intro h
  rw[mem_Ico] at h
  rw[mem_inter_iff]
  have hc := h.1
  have hb := h.2
  have hd : x < d := lt_trans hb h3
  have ha : a ≤ x := le_of_lt (lt_of_lt_of_le h1 hc)
  apply And.intro
  rw[mem_Ico]
  exact And.intro ha hb
  rw[mem_Ico]
  exact And.intro hc hd



Conclusion "--conc--"


NewTheorem Set.mem_inter_iff Set.mem_Ico And.intro lt_trans le_of_lt lt_of_lt_of_le Iff.intro
NewTactic clear «have» ext intro apply split
