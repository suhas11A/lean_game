import Game.Metadata
import Game.Levels.Functions.L05_characteristic_functions
import Mathlib.Tactic.Ring

World "Functions"
Level 8
Title "Characteristic functions: Complement"

Introduction "
Try proving Theorem 3.1.27(c) on your own!
"

open Set

/-- Let $X$ be a set and $U ⊆ X$.  Then $χ_{X∖U}(a) = 1 - χ_U(a)$ for all $a∈X$.
 -/
Statement (X : Type) (U : Set X) (a : X) : χ Uᶜ a = 1 - χ U a := by
  have hu := characteristic_function_value U a
  cases hu with
  | inl hu =>
    rw [hu]
    simp
    apply (characteristic_function_1 Uᶜ a).mpr
    simp
    intro ha
    apply (characteristic_function_0 U a).mp at hu
    contradiction
  | inr hu =>
    rw [hu]
    simp
    apply (characteristic_function_0 Uᶜ a).mpr
    simp
    apply (characteristic_function_1 U a).mp
    assumption

Conclusion "
"

NewTheorem Set.mem_union
