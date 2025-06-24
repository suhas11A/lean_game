import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 2
Title "Conjunction in the Hypothesis"

Introduction "
The elimination rules for conjunction (∧) are

(∧E₁) If p ∧ q is true, then p is true.

(∧E₂) If p ∧ q is true, then q is true.

This means that if our **assumption** is of the form p ∧ q, then we
can deduce that p is true and that q is true.

When we have an assumption of the form `h: p ∧ q`, we can invoke ∧E₁ and ∧E₂
and produce new assumptions `h1: p` and `h2: q` by typing `and_elim h into h1, h2`.
Try using `and_elim` with the correct syntax to begin the proof."

Statement (h:2+2=4 ∧ 3<5) : 2+2=4 := by
  and_elim h into h1, h2
  Hint "Now that we have the hypotheses `2+2=4` and `3<5`, our goal matches one of these
  hypotheses exactly. Use `exact h'` where h' is the name of the hypothesis that matches
  the goal to finish the proof."
  exact h1

NewTactic and_elim exact
NewHiddenTactic  «into»

Conclusion ""
