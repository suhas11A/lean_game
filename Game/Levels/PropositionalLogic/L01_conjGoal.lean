import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 1
Title "Conjunction in the Goal"

Introduction "Definition 1.1.4 gives the one introduction rule (∧I) and two elimination rules of
the conjunction operator (∧E₁ and ∧E₂). Introduction rules are used when the operator (or
quantifier, as seen in the next world) appears in the goal. Elimination rules are used when the
operator or quantifier is in a hypothesis.

(∧I) If p is true and q is true, then p ∧ q is true.

In this level, we invoke ∧I with the tactic `and_intro`.
When the goal of our proof has a conjunction ∧ as its outermost operator, we use the `and_intro`
tactic to separate the goal of proving p ∧ q is true into two separate goals, proving p is true
and proving q is true. Try using `and_intro` to start the proof."

Statement (h1:x=3) (h2:y=5) : x=3 ∧ y=5 := by
  and_intro
  Hint "Next, we can use the `exact` tactic to resolve a goal that exactly matches one of the
  hypotheses. Since the goal x=3 exactly matches hypothesis h1, we can use `exact h1` to resolve
  this goal."

  exact h1
  Hint "Do something similar to resolve the goal y=5."

  exact h2

NewTactic and_intro exact

Conclusion ""
