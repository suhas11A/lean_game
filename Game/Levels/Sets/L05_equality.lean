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
  Hint "`apply Subset.antisymm` to split the goal into 2 goals `(Aᶜ)ᶜ ⊆ A` and `A ⊆ (Aᶜ)ᶜ`"
  apply Subset.antisymm
  intro a a_1
  Hint "Read `mem_compl_iff` and rewrite `a ∈ Aᶜ` into `a ∉ A`."
  Hint "Note:- `a ∉ A` is equivalent to `¬a ∈ A`"
  rw[mem_compl_iff] at a_1
  rw[mem_compl_iff] at a_1
  Hint "Learn new Tactic `push_neg`"
  push_neg at a_1
  exact a_1
  intro a a_1
  rw[mem_compl_iff]
  rw[mem_compl_iff]
  push_neg
  exact a_1

Conclusion "--conc--"

NewTactic push_neg apply
NewTheorem Set.mem_compl_iff Set.Subset.antisymm
