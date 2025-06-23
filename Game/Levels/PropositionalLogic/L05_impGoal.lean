import Game.Metadata
import GameServer.Commands

World "PropositionalLogic"
Level 5
Title "Implication in the Goal"

Introduction "
The introduction rule for → is
(→I) If q can be derived from the assumption that p is true, then p → q is true
This means that to *prove a goal* of the form p → q, it suffices
to assume p is true and derive that q is true.

In this level, our goal is indeed of the form
p → q. We invoke →I with `imp_intro h` which will change the goal of proving
n=1 → n+1=2 into n+1=2 and add `h: n=1` as a hypothesis. Try using `imp_intro` with
the correct syntax to begin the proof."

Statement (n:ℕ) n=1 → n+1=2 := by
  imp_intro h
  Hint "Use the `rw` and `trivial` tactics to complete the proof."
  rw [h]
  trivial

NewTactic imp_intro

Conclusion ""
