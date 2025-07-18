import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 10
Title "Negation in the Hypothesis"

Introduction "
The elimination rule for negation (¬) is

(¬E) If ¬p and p are both true, then a contradiction may be derived.

When we have an **assumption** of the form `h: ¬p`, we can invoke ¬E
using the `contradiction` tactic, which was described in the previous level.
"

Statement (h1:¬(x=1)) (h2: x=1) : False := by
  contradiction


Conclusion ""
