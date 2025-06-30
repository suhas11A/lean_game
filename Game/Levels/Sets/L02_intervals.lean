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

Closed interval [a,b] is the set of all values x that satisfies `x ≥ a ∧ x ≤ b`.
 In LEAN the interval [a,b] is represented as `Icc a b` (Interval closed closed a b).
"
open Set
/-- Suppose a < c and d < b. Show that [c, d] ⊆ (a,b). -/
Statement (a b c d : ℝ)(ha : a < c)(hc : d < b): Icc c d ⊆ Ioo a b := by
  Hint "We have seen how to prove a goal of form `A ⊆ B`, and it requires us to assume `x ∈ A` and
   show `x ∈ B`. Now that we know  what exactly it  means for a Set to be a subset of another set,
   we will be using `intro` tactic to  directly change a goal of form `A ⊆ B` into a new hypotheses
   `hx : x ∈ A` and goal `x ∈ B`. Execute `intro x hx` to do this."
  intro x hx
  Hint "If `a ∈ Icc x y` it means two things, `a ≥ x` and `a ≤ y`. Use tactic `rw` and theorem `mem_Icc` to rewrite `x ∈ Icc c d` to `c ≤ x ∧ x ≤ d`."
  rw [mem_Icc] at hx
  Hint "If `a ∈ Ioo x y` it means two things, `a > x` and `a < y`. Similarly use theorem `mem_Ioo` to rewrite `x ∈ Ioo a b` to `a < x ∧ x < b`."
  rw [mem_Ioo]
  Hint "Use `and_elim to proceed further."
  and_elim hx into h1, h2
  Hint "When `a < b` and `b ≤ c`, it is obvious that `a < c`, but how does lean know that. Well there are theorems that we can use!"
  Hint "See theorems `lt_of_lt_of_le` and `lt_of_le_of_lt` and how to use them."
  Hint "Recall `have` from previous world, we use `have` to introduce a new hypotheses from known results and hypotheses.
   Theorem `lt_of_lt_of_le` says that `a < b → b ≤ c → a < c` which can be interpreted as `(a < b ∧ b ≤ c) → a < c`.
   `have h_ax := lt_of_lt_of_le {ha} {h1}` will adds the hypotheses `h_ax : a < x` into our tactic state.
   Similarly try to show `x < b` using the same idea."
  and_intro
  have h_ax := lt_of_lt_of_le ha h1
  exact h_ax
  have h_xb := lt_of_le_of_lt h2 hc
  exact h_xb

Conclusion "We will now go on to learn how LEAN treats Sets and what are Types that we first talked about at the beginning of this world."


NewTactic rw intro And.intro «have»
NewTheorem Set.mem_Icc Set.mem_Ioo lt_of_lt_of_le lt_of_le_of_lt Set.Icc Set.Ioo
