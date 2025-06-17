import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 8
Title "Biconditional in the Hypothesis"

Introduction "In this level, we learn to handle a biconditional
in a hypothesis using the `iff_elim` tactic. Use the syntax `iff_elim h into h1, h2` to split
the biconditional in hypothesis h: p ↔ q into two separate hypotheses h1: p → q and h2: q → p."

Statement (h:x=3 ↔ y=5) : (x=3 → y=5) ∧ (y=5 → x=3) := by
  iff_elim h into h1, h2
  Hint "Next, recall how to invoke the introduction rule for the
  conjunction operator from Level 1 of this world."
  and_intro
  Hint "Finish off the proof!"
  exact h1
  exact h2

NewTactic iff_elim

Conclusion ""
