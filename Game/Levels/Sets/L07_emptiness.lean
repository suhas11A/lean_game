import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 7
Title "A non trivial example"

Introduction "
This example is inspired from Exercise 2.1.31 from infinite descent.
"
open Set
/-- Let a,b ∈ R. Prove that [a, b] is empty if and only if a > b. -/
Statement (a b : ℝ): Icc a b = ∅ ↔ a > b := by
  iff_intro
  imp_intro h1
  Hint "We use the strategy \"Proof by Contradiction\", to do this apply `by_contra` tactic."
  by_contra h
  Hint "`{h} : ¬a > b` is same as `{h} : a ≤ b`, to do this use the tactic `push_neg` at {h}."
  push_neg at h
  Hint "we can prove this in many ways, we will go ahead by showing that if `a ≤ b` then `a ∈ Icc a b`.
   To do this we first need to show `a ≤ a ∧ a ≤ b`, we already have `a ≤ b` as one of our hypotheses, so we need to show `a ≤ a` i.e have a new hypotheses `haa : a ≤ a`.
   Recall the tactic `have`. We know `have` needs to be given a new hypotheses to be introduced and a proof of that hypotheses in the same line. But we can also use have with just the hypotheses and give the proof of this later.
   Try executing `have haa : a ≤ a`, this will first ask you to prove this hypotheses as a goal and after you prove, it then becomes a hypotheses that we can use in our proof."
  have haa : a ≤ a
  Hint "We can close this trivially using `trivial`."
  trivial
  Hint "We need to show `a ∈ Icc a b`, use `have` to first prove this and then have it as a hypotheses."
  have hi : a ∈ Icc a b
  Hint "Close this goal on your own"
  and_intro
  exact haa
  exact h
  Hint "We have `{h1} : Icc a b = ∅` and `{hi} : {a} ∈ Icc a b`, which means `{a} ∈ ∅`. We know we can close any goal when we have a false hypotheses."
  rw[h1] at hi
  cases hi
  imp_intro h
  apply Subset.antisymm
  intro x hx
  Hint "Rewrite the definition of Icc at {hx}."
  rw[mem_Icc] at hx
  Hint "using {hx}, we can deduce `a ≤ b`. Use theorem `le_trans` to show that."
  and_elim hx into jk, kl
  have hh : a ≤ b := le_trans jk kl
  Hint "Have a new hypotheses `¬ (a>b)` (which can be derived from {hh}) so that we can use the tactic `contradiction`."
  have kk : ¬ (a>b)
  push_neg
  exact hh
  contradiction
  intro x hx
  cases hx

Conclusion ""

NewTheorem le_trans
