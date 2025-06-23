import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 10
Title "Negation in the Hypothesis"

Introduction "
The elimination rule for ¬ is
(¬E) If ¬p and p are both true, then a contradiction may be derived.
¬E is invoked using the `contradiction` tactic, which was described in the previous level.
"

Statement (h1:¬(x=1)) (h2: x=1) : False := by
  contradiction

NewTactic

Conclusion ""
