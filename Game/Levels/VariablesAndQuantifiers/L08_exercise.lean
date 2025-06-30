/-
one more concerete and not so trivial example
take formulas from 1.3.34 (c,d) or 1.3.38
or its negation and ask sudents to prove on their own
-/

import Game.Metadata
import GameServer.Commands
import Mathlib.Data.Real.Basic

World "VariablesAndQuantifiers"
Level 8
Title "Exercise"

Introduction "Try the exercise below."

-- maybe i should be naming my levels
-- and also give the prompt from the exercise instead of just "try the exercise"
-- what is the precedence of ¬ operator? binds to ∀ or should have parentheses around everything

/-
h1: ∀ x ≥ 0, ∃ y ∈ ℝ, y^2=x → False
∀ y ∈ ℝ, y^2 ≠ 2
-/

import Mathlib



example : ∀ x : ℝ, x>1 → (∃y : ℝ, x<y ∧ ¬(x^2 ≤ y)) := by
  intro x
  intro h
  use (x+x^2)/2
  simp [h]
  constructor
  · rw [div_eq_mul_inv, lt_mul_inv_iff₀', two_mul]
    simp
    nth_rw 1 [← one_mul x]
    rw [pow_two]
    apply mul_lt_mul <;> try simp [h]
    · apply lt_trans (b := 1) <;> simp [h]
    · apply le_trans (b := 1) <;> try simp [h]
      ·

Statement : ∀ x : ℝ, x>1 → (∃y : ℝ, x<y ∧ ¬(x^2 ≤ y)) := by
  forall_intro x'
  imp_intro h
  exists_intro (x+x^2)/2
  and_intro
  calc x>1 x^2>x x^2+x>2x (x^2+x)/2>x
  unfold Not
  imp_intro h'
  -- x^2≤(x^2+x)/2 → 2x^2≤x^2+x → x^2≤x → x ≤ 1
  contradiction


-- example (U : Type) (p : U → U → Prop): (¬∀ x : U, ∃ y : U, p x y) ↔ (∃ x : U, ∀ y : U, ¬p x y) := by
--   iff_intro
--   imp_intro h1
--   unfold Not at h1
-- TODO: finish proof, maybe choose different one

NewTactic

Conclusion ""
