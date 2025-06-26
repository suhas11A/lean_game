/-
one more concerete and not so trivial example
take formulas from 1.3.34 (c,d) or 1.3.38
or its negation and ask sudents to prove on their own
-/

import Game.Metadata
import GameServer.Commands

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

TODO: finish pf

-/

Statement : (¬∀ x ≥ 0, ∃ y ∈ ℝ, y^2=x) ↔ (∃ x ≥ 0, ∀ y ∈ ℝ, y^2 ≠ x) := by
  iff_intro -- split goal into proving each of the two directions
  intro h1
  unfold Not at h1
  -- how to handle negation in the hypothesis?
  exists_intro 2
  forall_elim h1 of 2, hx





NewTactic

Conclusion ""
