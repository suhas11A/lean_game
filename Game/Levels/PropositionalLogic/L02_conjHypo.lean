import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 2
Title "Conjunction in the Hypothesis"

Introduction "In this level, we will learn to handle conjunction operations in the hypothesis,
which can be done using the `and_elim` tactic. Notice that `and_intro` and `and_elim` are the
introduction and elimination rules for the conjunction (AKA and) operator. Other tactics like
`or_intro` and `or_elim` in the next few levels follow similar naming conventions
In Definition 1.1.4, the second and third properties of the conjunction operator are:
(2) If p ∧ q, then p is true; (3) If p ∧ q, then q is true. The `and_elim` tactic invokes
these two properties. If we have p ∧ q in hypothesis h, use `and_elim h into h1 h2` to
separate h into two separate hypotheses: `h1: p` and `h2: q`. Try using this as the first
step of the proof."

Statement (h:x=3 ∧ y=5) : y=5 := by
  and_elim h into h1, h2
  Hint "Now that we have the hypotheses `h1: x=3` and `h2: y=5`, our goal matches one of these
  hypotheses exactly. Use the `exact` tactic like in the previous level to finish the proof."

  exact h2

NewTactic and_elim

Conclusion ""
