import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 10
Title "Negation in the Hypothesis"

Introduction "Use your knowledge of the conjunction and disjunction operators to begin
the proof!"

Statement (h:(x=3 ∨ y=5) ∧ ¬(x=3)) : y=5 := by
  and_elim h into h1, h2
  or_elim h1 into hx, hy
  Hint "When the hypotheses are contradictory, use the `exfalso` tactic
  to make your goal into `False`. `exfalso` is short for \"ex falso sequitur quodlibet,\"
  which is a Latin phrase meaning \"from false, anything follows\"."
  exfalso
  Hint "Now that we have contradictory hypotheses and our goal is `False`, we can use the
  `contradiction` tactic to complete the first case of the proof."
  contradiction
  Hint "Finish off the proof!"
  exact hy

NewTactic exfalso

Conclusion ""
