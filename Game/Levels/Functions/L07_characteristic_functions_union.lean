import Game.Metadata
import Game.Levels.Functions.L05_characteristic_functions
import Mathlib.Tactic.Ring

World "Functions"
Level 7
Title "Characteristic functions: Union"

Introduction "
Try proving Theorem 3.1.27(b) on your own!
"

open Set

/-- Let $X$ be a set and $U,V ⊆ X$.  Then $χ_{U∪V}(a) = χ_U(a)+χ_V(a)-χ_U(a)χ_V(a)$ for all $a∈X$.
 -/
Statement (X : Type) (U V : Set X) (a : X) : χ (U ∪ V) a = (χ U a) + (χ V a) - (χ U a) * (χ V a) := by
  have hu := characteristic_function_value U a
  have hv := characteristic_function_value V a
  cases hu with
  | inl hu =>
    cases hv with
    | inl hv =>
      rw [hu, hv]
      simp
      apply (characteristic_function_0 (U ∪ V) a).mpr
      apply (characteristic_function_0 U a).mp at hu
      apply (characteristic_function_0 V a).mp at hv
      intro h
      cases h <;> contradiction
    | inr hv =>
      rw [hv]
      simp
      apply (characteristic_function_1 (U ∪ V) a).mpr
      right
      apply (characteristic_function_1 V a).mp
      assumption
  | inr hu =>
    rw [hu]
    simp
    apply (characteristic_function_1 (U ∪ V) a).mpr
    left
    apply (characteristic_function_1 U a).mp
    assumption

Conclusion "
"

NewTheorem Set.mem_union
NewTactic left right
