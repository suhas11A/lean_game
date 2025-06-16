import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 1
Title "Conjunction in the Goal"

Introduction "Definition 1.1.4 gives the three properties of the conjunction operator.
In this level, we will invoke the first property: If p is true and q is true, then p ∧ q is true.
When the goal of our proof has a conjunction ∧ as its outermost operator, we use the `and_intro`
tactic to separate the goal into two separate goals. If we want to prove p ∧ q, we must prove
p and q separately. Try typing `and_intro` and pressing Enter."

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
