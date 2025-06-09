import Game.Metadata
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Game.Levels.Functions.L05_characteristic_functions

World "Functions"
Level 13
Title "Every function to the booleans is a characteristic function"

Introduction "
The way that this theorem is stated in Lean differs slightly from the
book.  Because the characteristic function's codomain is $ℤ$, to prove
that $f$ equals the characteristic function, we need $f$’s codomain to
be $ℤ$.  So, we add an extra hypothesis that states that the range of
$f$ is $\\{0,1\\}$.
"

open Set

/-- Every function $f:X→\{0,1\}$ is the characteristic function of the
    subset $f^{-1}[\{1\}]⊆X$.
 -/
Statement (X : Type) (f : X → Int) : (∀ x : X, f x = 0 ∨ f x = 1) →
  f = χ (f ⁻¹' (singleton 1)) := by
  intro hf
  ext
  specialize hf x
  cases hf with
  | inl hf =>
  · rw [hf]
    Hint "
    The goal seems to suggest using `characteristic_function_0`, but
    the equality is the wrong way around; you should use `symm` to
    exchange both sides of the goal here.
    "
    symm
    rw [characteristic_function_0]
    rw [mem_preimage]
    rw [hf]
    rw [mem_singleton_iff]
    intro contra
    contradiction
  | inr hf =>
  · rw [hf]
    symm
    rw [characteristic_function_1]
    rw [mem_preimage]
    rw [hf]
    apply mem_singleton

Conclusion "

"

NewTheorem Set.mem_preimage Set.mem_singleton_iff Set.mem_singleton
NewTactic symm
