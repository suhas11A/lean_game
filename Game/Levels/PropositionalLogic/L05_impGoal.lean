import Game.Metadata
import GameServer.Commands

World "PropositionalLogic"
Level 5
Title "Implication in the Goal"

Introduction "
Here is a brief summary of what we've learned in this world so far:
· When conjunction ∧ appears in the goal, invoke the introduction rule with `and_intro`
· When conjunction ∧ appears in a hypothesis, invoke the elimination rule with `and_elim h into h1, h2`
· When disjunction ∨ appears in the goal, invoke the introduction rule with `or_intro p`
· When disjunction ∨ appears in a hypothesis, invoke the elimination rule with `or_elim h into h1, h2`

Definition 1.1.21 states the implication operator →
has introduction and elimination rules as follows:

(→I) If q can be derived from the assumption that p is true, then p → q is true
     · If the goal is p → q, we use `imp_intro h` to add h: p as a hypothesis
      and make the goal to prove q is true.

(→E) If p → q is true and p is true, then q is true
     · If we have hypothesis h: p → q and goal q, proving p is true is sufficient to prove q is true.
      We use `imp_elim h` to turn the goal into proving p is true.
     · If we have hypotheses h1: p → q and h2: p, we use `imp_elim h1 at h2` to turn
      h2: p into h2: q.

Based on the information provided above, try completing this proof on your own!"

Statement : x=3 → x=3 := by
  imp_intro h
  Hint "Use the `exact` tactic to finish the proof."
  exact h

NewTactic imp_intro

Conclusion ""
