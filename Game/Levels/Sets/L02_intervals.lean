import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 2
Title "Basic example in intervals"

Introduction "
A closed interval $[a,b]$ is the set of all values $x$ that satisfy $x ≥ a ∧ x ≤ b$.
In Lean the interval [a,b] is represented as `Icc a b` (Interval closed closed a b) and the interval (a,b) is represented as `Ioo a b` (Interval open open a b)

In the previous level, we start with a goal `A ⊆ B` and rewrite using `subset_def`.
Now that we know what it  means for a Set to be a subset of another set,
we will be using `intro` tactic to directly change a goal of form `A ⊆ B` into a new hypotheses
`hx : x ∈ A` and the goal changed to `x ∈ B`. Execute `intro x hx` to do this.
"
open Set
/-- Suppose a < c and d < b. Show that [c, d] ⊆ (a,b). -/
Statement (a b c d : ℝ) (h1 : a < c) (h2 : d < b): Icc c d ⊆ Ioo a b := by
  intro x hx
  Hint "
  The statement $a ∈ [x,y]$ is equivalent to $x ≤ a ≤ y$. We will now learn a few theorems to help us deal with inequalities and intervals.  
    
  ```
  mem_Ioo : x ∈ Ioo a b ↔ a < x ∧ x < b
  mem_Icc : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b
  mem_Ico : x ∈ Icc a b ↔ a ≤ x ∧ x < b
  mem_Ioc : x ∈ Icc a b ↔ a < x ∧ x ≤ b
  le_trans : a ≤ b → b ≤ c → a ≤ c
  lt_trans : a < b → b < c → a < c
  lt_of_lt_of_le : a < b → b ≤ c → a < c
  lt_of_le_of_lt : a ≤ b → b < c → a < c
  ```
  "
  Hint "
  Note : Theorem `lt_of_lt_of_le` says that `a < b → b ≤ c → a < c` which can also be interpreted as `(a < b ∧ b ≤ c) → a < c`.  
    
  Using these theorems, we should be able to finish this level. In general it is easier to deal with inequalities than intervals, so first rewrite `Ico` and `Ioo` into inequalities.
  "
  rw [mem_Icc] at hx
  rw [mem_Ioo]
  and_elim hx into h_1, h_2
  and_intro
  Hint "When `a < b` and `b ≤ c`, it is obvious that `a < c`, but you need to write this out explicitly in LEAN using one of the theorems introduced above."
  Hint "Recall `have` from previous world, we use `have` to introduce a new hypotheses from existing hypotheses and known theorems.
   Theorem `lt_of_lt_of_le` can be used to add the hypotheses `h_a{x} : a < {x}` into our tactic state."
  have h_ax := lt_of_lt_of_le h1 h_1
  exact h_ax
  have h_xb := lt_of_le_of_lt h_2 h2
  exact h_xb

Conclusion ""


NewTactic rw intro «have»
NewTheorem Set.mem_Icc Set.mem_Ioo lt_of_lt_of_le lt_of_le_of_lt Set.Icc Set.Ioo
