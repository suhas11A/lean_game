import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 5
Title "Basic example in intervals"

Introduction "
In order to prove `X = Y`, it suffices to prove `X ⊆ Y` and `X ⊇ Y`.
"
open Set
/-- Suppose A is a set. Then (Aᶜ)ᶜ= A. -/
Statement (U : Type)(A : Set U): (Aᶜ)ᶜ = A := by
  Hint "`A = B` means every element of A is also and element of B and every element of B is also an element of A."
  Hint "More precicely `A = B` means `A ⊆ B ∧ B ⊆ A`."
  Hint "You could also look at it this way `x ∈ A ↔ x ∈ B` (but we avoid this for now)."
  Hint "`apply Subset.antisymm` to the goal to split it into 2 goals `(Aᶜ)ᶜ ⊆ A` and `A ⊆ (Aᶜ)ᶜ`"
  apply Subset.antisymm
  intro a a_1
  Hint "Aᶜ is the Set of all elements that are not members of A, what this means is that `x ∈ Aᶜ` is equivalent to `¬a ∈ A`"
  Hint "Read `mem_compl_iff` and use the theorem to rewrite `a ∈ Aᶜ` into `a ∉ A`."
  Hint "Note:- `a ∉ A` is equivalent to `¬a ∈ A`"
  rw[mem_compl_iff] at a_1
  rw[mem_compl_iff] at a_1
  Hint "We have seen that `a ∉ A` is equivalent to `¬a ∈ A` so what does `¬a ∉ A` mean??"
  Hint "`¬a ∉ A` is negation of `a ∉ A` i.e negation of `¬a ∈ A` which in turn is `a ∈ A`."
  Hint "this `¬a ∉ A` means that a is an element of A"
  Hint "Learn new Tactic `push_neg` to push the negation inside"
  push_neg at a_1
  exact a_1
  Hint "You can take it from here!!"
  intro a a_1
  rw[mem_compl_iff]
  rw[mem_compl_iff]
  push_neg
  exact a_1

Conclusion "--conc--"

NewTactic push_neg apply
NewTheorem Set.mem_compl_iff Set.Subset.antisymm
