import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 4
Title "Disjunction in the Hypothesis"

Introduction "
The elimination rule for ∨ is
(∨E) If p ∨ q is true, and if r can be derived from p and from q, then r is true
This means that if our *assumption* is of the form p ∨ q, then we
must prove the goal assuming p is true but not necessarily q, and we must also
prove the goal assuing q is true but not necessarily p.

When we have an assumption of the form `h: p ∨ q`, we can invoke ∨E
and separate the proof into two cases, one assuming `h1: p` and one assuming `h2: q`, by typing `or_elim h into h1, h2`.
Try using `or_elim` with the correct syntax to begin the proof.
"

Statement (h:x=0 ∨ x=1) : x*x=x := by
  or_elim h into h1, h2
  Hint "Use the `rw` and `trivial` tactics to complete the proof."
  rw [h]
  trivial
  rw [h]
  trivial

NewTactic or_elim

Conclusion ""
