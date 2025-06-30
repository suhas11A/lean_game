import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 5
Title "Equality of 2 Sets"

Introduction "
In order to prove `X = Y`, it suffices to prove `X ⊆ Y` and `X ⊇ Y`.
"
open Set
/-- Suppose A is a set. Then (Aᶜ)ᶜ = A. -/
Statement (U : Type)(A : Set U): (Aᶜ)ᶜ = A := by
  Hint "`A = B` means every element of A is an element of B and every element of B is an element of A.
   More precisely, the equality `A = B` holds if and only if `A ⊆ B ∧ B ⊆ A`.
   You could also look at `A = B` this way `x ∈ A ↔ x ∈ B` (but we avoid this for now).
   `apply Subset.antisymm` to the goal to split it into 2 goals `(Aᶜ)ᶜ ⊆ A` and `A ⊆ (Aᶜ)ᶜ`"
  apply Subset.antisymm
  Hint "We have to prove a goal of form `A ⊆ B`, you know what to do..."
  intro a a_1
  Hint "Aᶜ is the Set of all elements that are not members of A, what this means is that `{a} ∈ Aᶜ` is equivalent to `¬{a} ∈ A`.
  Read `mem_compl_iff` and use this theorem to rewrite `{a} ∈ Aᶜ` into `{a} ∉ A`."
  Hint "Note:- `a ∉ A` is equivalent to `¬a ∈ A`"
  rw[mem_compl_iff] at a_1
  Hint "We still have `{a} ∉ Aᶜ`, and we need to rewrite this again using the correct theorem as above."
  rw[mem_compl_iff] at a_1
  Hint "We have seen that `a ∉ A` is equivalent to `¬a ∈ A` so what does `¬a ∉ A` mean??
   `¬a ∉ A` is negation of `a ∉ A` i.e negation of `¬a ∈ A` which in turn is `a ∈ A` (by Law of double negation).
   So `¬a ∉ A` means that a is an element of A."
  Hint "Recall Tactic `push_neg` to push the negation inside. Try executing `push_neg at a_1` to push the negation."
  push_neg at a_1
  exact a_1
  Hint "You can take it from here!!"
  intro a a_1
  rw[mem_compl_iff]
  rw[mem_compl_iff]
  push_neg
  exact a_1

Conclusion "We have now learned what it means for 2 Sets to be equal and how to use a new Tactic `push_neg`."

/-- `A = B` means that every element of `A` is an element of `B` and vice-versa. What it means is that `A ⊆ B` and `B ⊆ A`. -/
DefinitionDoc Set.eq as "="

/-- If `A` is a set, then `Aᶜ` is the complement of `A`.
To enter the symbol `ᶜ`, type `\compl` or `\^c`. -/
DefinitionDoc compl as "ᶜ"

DefinitionDoc inter as "∩"

NewTactic push_neg
NewTheorem Set.mem_compl_iff Set.Subset.antisymm
NewDefinition Set.eq compl
