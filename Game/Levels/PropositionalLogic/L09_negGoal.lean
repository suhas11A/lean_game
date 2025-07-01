import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 9
Title "Negation in the Goal"

Introduction "
In standard mathematics, a negated proposition $¬p$ ($¬$ is written
`\\neg`) is defined to be a proposition that is true whenever $p$ is
false, and vice versa.  In Lean, $¬p$ is defined to be $p →
\\rm{False}$.  $\\rm{False}$ is the trivially false proposition; by
definition, you can’t prove it.

The introduction rule for negation (¬) is:

(¬I) *If a contradiction can be derived from the assumption that $p$ is true, then $¬p$ is true.*

This means that to **prove a goal** of the form $¬p$, it suffices
to assume $p$ is true and derive a contradiction.  We can do this using
the `by_contra` tactic.  By typing `by_contra h`, $p$ will be assumed
and the assumption will be given the name `h`, and the goal will
change to `False`.
"

Statement : ¬(2=3) := by
  by_contra h
  Hint "We can’t prove the goal (False) directly.  Instead, we have to
  use our assumptions to find a contradiction.  Once we have found a
  contradiction, the proof will close automatically.

  The `contradiction` tactic searches for a contradiction
  among the assumptions.  A contradiction can be either two
  assumptions which contradict each other, i.e., $p$ and $¬p$, or one
  assumption that is trivially false.

  Since 2=3 is trivially false, we can use the `contradiction` tactic
  to complete the proof.
  "
  contradiction

DefinitionDoc Not as "Not / ¬"

NewTactic contradiction
NewDefinition Not

-- two ways a contradiction can happen:
-- assumptions contradict each other, or assumption is false

Conclusion ""
