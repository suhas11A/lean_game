import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 9
Title "Negation in the Goal"

Introduction "
In Lean, negation (¬) is defined by declaring ¬p
to mean p → False, where False is a contradiction.

The introduction rule for negation (¬) is

(¬I) If a contradiction can be derived from the assumption that p is true, then ¬p is true.

This means that to **prove a goal** of the form ¬p, it suffices
to assume p is true and derive a contradiction.

When we have a goal of the form `¬p`, we can use `imp_intro h` to invoke ¬I and introduce assumption
`h: p` and change the goal to `False`, which means we must derive a contradiction from the hypotheses.
Try using `imp_intro` with the correct syntax to begin the proof.
"

Statement : ¬(2=3) := by
  -- unfold Not
  imp_intro h
  Hint "The `contradiction` tactic searches for a contradiction
  among the assumptions.

  Since 2=3 is a contradiction, we can use the
  `contradiction` tactic to complete the proof."
  contradiction

DefinitionDoc Not as "Not / ¬"

NewTactic contradiction
NewDefinition Not

-- two ways a contradiction can happen:
-- assumptions contradict each other, or assumption is false

Conclusion ""
