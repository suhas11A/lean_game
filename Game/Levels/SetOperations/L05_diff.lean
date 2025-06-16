import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Basic

World "SetOperations"
Level 5
Title "Basic example in intervals"

Introduction "
This example is inspired from Example 2.2.27, We use this exercise to understand the concept of relative complement
"
def evens : Set ℕ := { n | n % 2 =0 }
def odds : Set ℕ := { n | n % 2 = 1 }

open Set
/-- Let evens and odds be set of even and odd Natural numbers. Prove that univ \ evens = odds. -/
Statement : Set.univ \ evens = odds := by
  apply Subset.antisymm
  intro n hn
  Hint "`A \\ B` is the set of all elements in A that are not membors of B."
  Hint "Theorem `mem_diff` can be used to rewrite ` x ∈ A \\ B` into `x ∈ A ∧ x ∉ B`."
  rw[mem_diff] at hn
  Hint "Any Natural number is either odd or even, in other wordds `n % 2 = 0 ∨ n % 2 = 1`. Theorem `Nat.mod_two_eq_zero_or_one n` tells exaactly that."
  Hint "`have hh := Nat.mod_two_eq_zero_or_one n` is used to create a new hypotheses saying exactly that."
  have hh := Nat.mod_two_eq_zero_or_one n
  cases hh
  Hint "If `n % 2 = 0` then `n ∈ evens` and in LEAN both are definitionally equal."
  Hint "You can have a new hypotheses `have h1 : n ∈ evens := h` but since both are definitionally equal, wherever you need `n ∈ evens` you can use `h` instead."
  Hint "Hypotheses are contradicting each other hence irrespective of the goal, the goal can be closed."
  have h1 : n ∈ evens := h
  have a_1 := hn.2
  trivial
  exact h
  intro n hn
  Hint "There are many ways to close this goal, one of the ways is to use `1 ≠ 0`. Theorem `Nat.one_ne_zero` says `1 ≠ 0`."
  Hint "`have h2 := Nat.one_ne_zero` will create a new hypotheses `h2 : 1 ≠ 0`."
  have h1 : n % 2 = 1 := hn
  have h2 := Nat.one_ne_zero
  rw[← h1] at h2
  rw[mem_diff]
  have h3 : n ∉ evens := h2
  and_intro
  trivial
  exact h3


Conclusion "--conc--"


NewTheorem Set.mem_union lt_trans and_or_left Nat.mod_two_eq_zero_or_one Set.mem_diff Set.univ Nat.one_ne_zero
NewTactic trivial
