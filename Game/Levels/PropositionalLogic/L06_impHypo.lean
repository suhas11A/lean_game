import Game.Metadata
import GameServer.Commands

World "PropositionalLogic"
Level 6
Title "Implication in the Hypothesis"

Introduction "Definition 1.1.21 gives the two properties of the implication operator.
In this level, we will use the second property: If p → q is true and p is true, then q is true.
When we want to invoke this property of implication, we use the `apply` tactic. If we have
hypotheses h1: p → q and h: p, then `apply h1 at h` means to invoke the second property of
implications mentioned above to transform hypothesis h into h: q. If instead we have hypothesis
h1: p → q and the goal is q, we can use `apply h1` to transform the goal into p. This is because
if we know that p → q, proving p is true would in turn prove q is true. Therefore, it suffices
to show p is true which is why the goal transforms from q to p. Try typing `apply h at h1` to
begin the proof."

Statement (h: x=3 → y=5) (h1: x=3) : y=5 := by
  imp_elim h at h1
  Hint "Use the `exact` tactic to finish the proof."
  exact h1

NewTactic apply

Conclusion ""
