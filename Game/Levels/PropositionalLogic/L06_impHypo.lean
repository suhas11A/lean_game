import Game.Metadata
import GameServer.Commands

World "PropositionalLogic"
Level 6
Title "Implication in the Hypothesis"

Introduction "
The elimination rule for implication (→) is
(→E) If p → q is true and p is true, then q is true.
This means that if our *assumption* is of the form `h: p → q` and we have goal q, then it is sufficient
to prove p is true. We use `imp_elim h` to turn the goal into proving p is true.
Alternatively, if our *assumption* is of the form `h: p → q` and we have assumption `h1: p`, then
we can deduce that q is true. We use `imp_elim h with h1 into h2` to add the hypothesis `h2: q`.

Try using `imp_elim` with the correct syntax to begin the proof.
"

Statement (n:ℕ) (h1:n=1 → n+1=2) (h2:n=1) : n+1=2 := by
  imp_elim h1 with h2 into h3
  Hint "Use the `exact` tactic to finish the proof."
  exact h3

NewTactic imp_elim

Conclusion ""
