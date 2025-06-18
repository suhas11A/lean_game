import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 2
Title "Conjunction in the Hypothesis"

Introduction "The two elimination rules of the conjunction operator given by Definition 1.1.4 are
as follows:

(∧E₁) If p ∧ q is true, then p is true.
(∧E₂) If p ∧ q is true, then q is true.

In this level, we invoke ∧E₂ with the tactic `and_elim`.
When a hypothesis of our proof has a conjunction ∧ as its outermost operator, we write
`and_elim h into h1, h2` to separate hypothesis h: p ∧ q into two separate hypotheses, h1: p and h2: q.
Try using `and_elim` with the correct syntax to start the proof.

Note: `and_intro` and `and_elim` are the
introduction and elimination rules for the conjunction (AKA and) operator. Other tactics like
`or_intro` and `or_elim` in the next few levels follow similar naming conventions."

Statement (h:x=3 ∧ y=5) : y=5 := by
  and_elim h into h1, h2
  Hint "Now that we have the hypotheses `h1: x=3` and `h2: y=5`, our goal matches one of these
  hypotheses exactly. Use the `exact` tactic like in the previous level to finish the proof."

  exact h2

NewTactic and_elim

Conclusion ""
