import Game.Metadata
import GameServer.Commands

World "LogicalEquivalence"
Level 8
Title "Proof by Counterexample"


Introduction "Use the `push_neg` tactic to invoke deMorgan's laws and begin the proof."

-- Statement : ¬(∀x:ℝ, x>3) := by
--   push_neg
--   use 3

Statement : ¬(∀ (a b : ℕ), a * b + a + b ≠ 11) := by
  push_neg
  use 5
  use 1

Conclusion ""
