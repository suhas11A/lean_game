import Game.Metadata
import Game.Levels.Functions.L05_characteristic_functions
import Mathlib.Tactic.Ring

World "Functions"
Level 6
Title "Characteristic functions: Intersection"

Introduction "
This follows Theorem 3.1.27(a) in the book.  We won't follow the steps of
the proof exactly how they are described in the book, since that proof
is fairly high level.  Instead, let's work through this step by step.

To begin, we need to do case analysis on the value of the
characteristic function for either $U$ or $V$.  Let's pick $U$.  Use
the `have` tactic and one of the properties of the characteristic
function to introduce a hypothesis that describes the possible values
of $χ_U(a)$.
"

open Set

/-- Let $X$ be a set and $U,V ⊆ X$.  Then $χ_{U∩V}(a) = χ_U(a)χ_V(a)$ for all $a∈X$.
 -/
Statement characteristic_function_inter (X : Type) (U V : Set X) (a : X) : χ (U ∩ V) a = (χ U a) * (χ V a) := by
  have hu := characteristic_function_value U a
  Hint "
  Now, we can use the cases tactic to examine each possibility individually.
  "
  cases hu with
  | inl hu =>
    Hint "
    In the case where $χ_{U}({a})=0$, we can figure out the value of
    $χ_{U}({a})χ_{V}({a})$.  Rewrite with the new equality and
    simplify the goal with `simp`.
    "
    rw [hu]
    simp
    Hint "
    Now we know what $χ_\{{U} ∩ {V}}({a})$ should be.  What theorem
    can we use to prove this goal?
    "
    apply (characteristic_function_0 (U ∩ V) a).mpr
    Hint "
    The hypothesis `{hu}` tells us, with the help of a property of
    $χ$, that ${a}∉{U}$.  The rest of this case is just set theory.
    "
    intro ⟨hu', hv⟩
    apply (characteristic_function_0 U a).mp at hu
    contradiction
  | inr hu =>
    Hint "
    In the case where $χ_{U}({a})=1$, we need to know the value of
    $χ_{V}({a})$ to deduce what $χ_\{{U}∩{V}}$ is.  Do this the same
    way we did in the previous case.
    "
    have hv := characteristic_function_value V a
    cases hv with
    | inl hv =>
      Hint "
      In this case, the proof will follow similar to when $χ_{U}(a)$
      was $0$.  Simplify the right-hand side of the goal, and then
      prove that ${a} ∉ {U} ∩ {V}$.
      "
      rw [hv]
      simp
      apply (characteristic_function_0 (U ∩ V) a).mpr
      intro ⟨hu', hv'⟩
      apply (characteristic_function_0 V a).mp at hv
      contradiction
    | inr hv =>
      Hint "
      Here, we know that both $χ_{U}({a})$ and $χ_{V}({a})$ are $1$,
      so by rewriting with `{hu}` and `{hv}` and simplifying with
      `simp`, we can show that $χ_\{{U} ∩ {V}}({a})$ is $1$ as
      well.
      "
      rw [hu, hv]
      simp
      Hint "
      Now, which of our theorems will allow us to prove the current
      goal?
      "
      apply (characteristic_function_1 (U ∩ V) a).mpr
      Hint "
      Use the same theorem to prove that ${a}∈{U}$ and ${a}∈{V}$, and
      then the rest is just set theory.
      "
      apply mem_inter
      · apply (characteristic_function_1 U a).mp at hu
        assumption
      · apply (characteristic_function_1 V a).mp at hv
        assumption

Conclusion "
  In the next two levels, you'll be proving parts (b) and (c) on your
  own.  Remember to use `simp` whenever you need to simplify your
  arithmetic!
"

NewTactic simp contradiction
NewTheorem Set.mem_inter
