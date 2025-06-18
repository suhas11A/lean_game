import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 9
Title "Negation in the Goal"

Introduction "
As the Natural Numbers Game says, `False` is a goal which cannot be
deduced from a consistent set of assumptions. If the goal is `False`, the
hypothesis should be contradictory. The logical formula ¬p is actually defined as the implication p → False,
so we can use `imp_intro` and `imp_elim` as before when negation appears in the goal and hypotheses,
respectively.

Definition 1.1.37 gives the introduction
and elimination rules of the negation operator ¬ as follows:

(¬I) If a contradiction can be derived from the assumption that p is true, then ¬p is true.
(¬E) If ¬p and p are both true, then a contradiction may be derived.

Try using `imp_intro` with the correct syntax to begin the proof.
"

Statement (h1: x=3) : ¬(x=4) := by
  imp_intro h2
  Hint "Try using `rw` with the correct syntax to do the next step of the proof."
  rw [h1] at h2
  Hint "Theorem Proving in Lean 4 states the `contradiction` tactic searches for a contradiction
  among the hypotheses of the current goal. Since 3=4 is a contradiction, we can use the
  `contradiction` tactic to complete the proof."
  contradiction

NewTactic contradiction

Conclusion ""
