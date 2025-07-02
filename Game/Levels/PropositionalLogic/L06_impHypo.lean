import Game.Metadata
import GameServer.Commands

World "PropositionalLogic"
Level 6
Title "Implication in the Hypothesis"

Introduction "
The elimination rule for implication (→) is

(→E) If p → q is true and p is true, then q is true.

This means that if our **assumption** is of the form `h: p → q` and we have goal q, then it is sufficient
to prove p is true. We use `apply h` to turn the goal into proving p is true.
Alternatively, if our *assumption* is of the form `h: p → q` and we have assumption `h1: p`, then
we can deduce that q is true. We use `apply h at h1` to change `h1` to be a proof of `q`.

Try using `apply` with the correct syntax to begin the proof.
"

Statement (n:ℕ) (h1:n=1 → n+1=2) (h2:n=1) : n+1=2 := by
  apply h1 at h2
  Hint "Use the `exact` tactic to finish the proof."
  exact h2

NewTactic imp_elim

Conclusion ""
