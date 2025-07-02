import Game.Metadata
import GameServer.Commands

World "PropositionalLogic"
Level 5
Title "Implication in the Goal"

Introduction "
The introduction rule for implication (→) is

(→I) If q can be derived from the assumption that p is true, then p → q is true.

This means that to **prove a goal** of the form p → q, it suffices
to assume p is true and derive that q is true.

In this level, our goal is indeed of the form p → q. We invoke →I with
`assume h` which will change the goal of proving n=1 → n+1=2 into
n+1=2 and add `h: n=1` as a hypothesis. Try using `assume` with the
correct syntax to begin the proof.
"

Statement (n:ℕ) : n=1 → n+1=2 := by
  assume h
  Hint "Use the `rewrite` and `trivial` tactics to complete the proof."
  rewrite [h]
  trivial

NewTactic assume

Conclusion ""
