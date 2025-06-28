import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 9
Title "Power Set"

Introduction "
This example is inspired from Example 2.1.37 from infinite descent.
"
open Set
/-- Suppose A = {a,b}. Then P(A) = {∅, {a}, {b}, {a,b}}. -/
Statement (E : Type)(a b : E): {∅, {a}, {b}, {a, b}} ⊆ Set.powerset ({a, b}) := by
  intro x hx
  Hint "An element `x` is a member of `𝒫(A)` if and only if `x ⊆ A`.
   Theorem `mem_powerset_iff` can be used to rewrite `x ∈ 𝒫(A)` into `x ⊆ A`."
  rw[mem_powerset_iff]
  Hint "When we have `x ∈ Set(a,b,c)` it means that `x` is either `a` or `b` or `c`, in other words `x = a ∨ x ∈ Set(b,c)`."
  Hint "We have discussed earlier that executing `cases` tactic on `h : x ∈ Set(a,b)` will convert it into 2 separate Tactic states with `h : x = a` in the first and `h : x = b` in the second."
  Hint "Similarly `cases` can be executed on `h : x ∈ Set(a,b,c,d)`."
  cases hx
  Hint "We now have `{h} : x = ∅` and we have to prove `x ⊆ Set(a,b)`, use `rw` to rewrite `x` into `∅` in the goal."
  rw[h]
  Hint "In this state we need to prove `∅ ⊆ Set(a,b)` and its obviously true, in such cases use the tactic `simp`."
  simp
  Hint "Continue executing `cases` to split h into different cases."
  cases h
  rw[h_1]
  Hint "`simp` can be used to close the goal"
  simp
  cases h_1
  rw[h]
  simp
  cases h
  Hint "Any set is subset of itself and it is trivially true, we can use `trivial` tactic to close this goal."
  trivial

Conclusion "We are now familiar with the basics of Sets, let's move on to the next world to know more about them."


NewTheorem Set.mem_powerset_iff
