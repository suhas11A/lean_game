import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Basic

World "SetOperations"
Level 6
Title "Basic example in intervals"

Introduction "
We use this exercise to understand the concept of relative complement(`\\`)  
$A \\ B$ is the set of all elements in $A$ that are not members of $B$.
"
def evens : Set ℕ := { n | n % 2 =0 }
def odds : Set ℕ := { n | n % 2 = 1 }

open Set
/-- Let evens and odds be set of even and odd Natural numbers. Prove that univ \ evens = odds. -/
Statement : Set.univ \ evens = odds := by
  apply Subset.antisymm
  intro n hn
  Hint "Theorem `mem_diff` can be used to rewrite ` x ∈ A \\ B` into `x ∈ A ∧ x ∉ B`."
  rw[mem_diff] at hn
  Hint "Any Natural number is either odd or even, in other words `n % 2 = 0 ∨ n % 2 = 1`. Theorem `Nat.mod_two_eq_zero_or_one n` tells exactly that.
   `have h := Nat.mod_two_eq_zero_or_one n` is used to create a new hypotheses `h : n % 2 = 0 ∨ n % 2 = 1`."
  have h := Nat.mod_two_eq_zero_or_one n
  Hint "Split `{h}` into two cases by using appropriate tactic (Hint :- It's `or_elim`)"
  or_elim h into h, h
  Hint "If `n % 2 = 0` then `n ∈ evens` and in LEAN both are definitionally equal.
   You can have a new hypotheses `have h1 : n ∈ evens := {h}` but since both are definitionally equal, wherever you need `n ∈ evens` you can use `{h}` instead."
  Hint "Hypotheses are contradicting each other hence irrespective of the what the goal is, it can be closed."
  have h1 : n ∈ evens := h
  Hint "Eliminate `∧` in `{hn}` to have 2 contradicting hypotheses."
  have a_1 := hn.2
  Hint "Now we can use the tactic `contradiction` to close the goal."
  contradiction
  exact h
  intro n hn
  Hint "There are many ways to close this goal, one of the ways is to use the strategy \"Proof by Contradiction\"."
  by_contra h
  Hint "Use `mem_diff` to rewrite {h}."
  rw[mem_diff] at h
  Hint "Push the negation inside using the tactic `push_neg`."
  push_neg at h
  Hint "n is obviously a member of `univ`, use `have` and `trivial` to get a new hypotheses `hj : n ∈ univ`."
  have hj : n ∈ univ := trivial
  Hint "we can now use `apply` to show `n ∈ evens` from {h} and {hj}."
  apply h at hj
  Hint "Using `have` try to get 2 new hypotheses, `h1 : n % 2 = 0` and `h2 : n % 2 = 1`."
  have h1 : n%2 =0 := hj
  have h2 : n%2 =1 := hn
  rw[h1] at h2
  trivial



Conclusion "Let us try one more exercise on relative compliment."

/-- If `A` and `B` are sets, then `A / B` is the relative compliment of `A` with respect to `B`. -/
DefinitionDoc diff as "/"

NewTheorem Set.mem_union lt_trans and_or_left Nat.mod_two_eq_zero_or_one Set.mem_diff Set.univ Nat.one_ne_zero
NewDefinition diff
