import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "SetOperations"
Level 2
Title "Basic example in intervals"

Introduction "
Following along with Example 2.1.17.

To prove the goal
"
open Set
/-- Suppose x∈A∩B. Then x∈B. -/
Statement (a b c d : ℝ)(h1 : a < c)(h2 : c < b)(h3 : b < d): (Ico a b) ∩ (Ico c d) = Ico c b := by
  ext x
  constructor
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
  constructor
  rw[mem_Ico]
  exact And.intro ha hb
  rw[mem_Ico]
  exact And.intro hc hd



Conclusion "--conc--"


NewTheorem Set.mem_inter_iff Set.mem_Ico
NewTactic clear
