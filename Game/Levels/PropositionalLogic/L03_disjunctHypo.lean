import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 3
Title "Disjunction in the Hypothesis"

Introduction "Definition 1.1.12 gives the two introduction rules and
one elimination rule of the disjunction operator. The elimination rule is as follows:

(∨E) If p ∨ q is true, and if r can be derived from p and from q, then r is true

In this level, we invoke ∨E using `or_elim`. If we have a hypothesis
of the form h: p ∨ q, we write `or_elim h into h1, h2`
to separate our proof into two cases, one where we assume
p is true (and have hypothesis h1: p) and one where we assume q is true
(and have hypothesis h2: q). Try using `or_elim` with the correct syntax to begin the proof.
"

Statement (h:x=3 ∨ x=3) : x=3 := by
  or_elim h into h1, h2
  Hint "Use `exact` like in the last two levels to complete the proof."
  exact h1
  exact h2

NewTactic or_elim

Conclusion ""
