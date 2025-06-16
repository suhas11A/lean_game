import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 2
Title "Basic example in intervals"

Introduction "
This example is inspired from Example 2.1.17 from infinite descent.

We will be proving a simple result involving intervals.

In LEAN the interval [a,b] is represented as `Icc a b` (Interval closed closed a b).
"
open Set
/-- Suppose a < c and d < b. Show that [c, d] ⊆ (a,b). -/
Statement (a b c d : ℝ)(ha : a < c)(hc : d < b): Icc c d ⊆ Ioo a b := by
  intro x hx
  Hint "If `a ∈ Icc x y` it means two things, `a ≥ x` and `a ≤ y`. Use theorem `mem_Icc` to rewrite `x ∈ Icc c d` to `c ≤ x ∧ x ≤ d`."
  rw [mem_Icc] at hx
  Hint "When `a < b` and `b ≤ c`, it is obvious that `a < c`, but how does lean know that. Well there are theoroms that we can use!"
  Hint "See theorems `lt_of_lt_of_le` and `lt_of_le_of_lt` and how to use them."
  and_elim hx into h1 h2
  have h3 := lt_of_lt_of_le ha h1
  have h4 := lt_of_le_of_lt h2 hc
  Hint "Recall `And.intro` from first World."
  have h : a < x ∧ x < b := And.intro h3 h4
  Hint "Use theorem `mem_Ioo` (mem of Interval open open)."
  rw [← mem_Ioo] at h
  exact h

Conclusion "--conc--"


NewTactic rw intro And.intro «have»
NewTheorem Set.mem_Icc Set.mem_Ioo lt_of_lt_of_le lt_of_le_of_lt Set.Icc Set.Ioo
