import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 8
Title "Biconditional in the Hypothesis"

Introduction "
When we have an **assumption** of the form `h: p ↔ q`, use `iff_elim h into h1, h2` to invoke
the biconditional elimination rule and split h into two separate hypotheses `h1: p → q` and `h2: q → p`.
Try using `iff_elim` with the correct syntax to begin the proof."

Statement (h:x=3 ↔ y=5) : (x=3 → y=5) ∧ (y=5 → x=3) := by
  iff_elim h into h1, h2
  Hint "Notice that the goal is of the form p ∧ q. Recall how to invoke the introduction rule for ∧ to complete the next step of the proof."
  and_intro
  Hint "Finish off the proof!"
  exact h1
  exact h2

NewTactic iff_elim

Conclusion ""
