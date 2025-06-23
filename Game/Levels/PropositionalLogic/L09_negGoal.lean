import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 9
Title "Negation in the Goal"

Introduction "
`False` is a goal which cannot be
deduced from a consistent set of assumptions. If the goal is `False`, the
hypotheses should be contradictory. The logical formula `¬p` is actually defined as the implication
`p → False`,
so we can use `imp_intro` and `imp_elim` as before when negation appears in the goal and hypotheses,
respectively.

The introduction rule for ¬ is
(¬I) If a contradiction can be derived from the assumption that p is true, then ¬p is true.
This means that to *prove a goal* of the form ¬p, it suffices
to assume p is true and derive a contradiction.

When we have a goal of the form `¬p`, we can use `imp_intro h` to invoke ¬I and introduce assumption
`h: p` and change the goal to `False`, which means we must derive a contradiction from the hypotheses.
Try using `imp_intro` with the correct syntax to begin the proof.
"

Statement : ¬(2=3) := by
  imp_intro h2
  Hint "The `contradiction` tactic searches for a contradiction
  among the hypotheses of the current goal. Since 2=3 is a contradiction, we can use the
  `contradiction` tactic to complete the proof."
  contradiction

NewTactic contradiction

Conclusion ""
