import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 1
Title "Conjunction in the Goal"

Introduction "
The introduction rule for conjunction (∧) is
(∧I) If p is true and q is true, then p ∧ q is true.
This means that to *prove a goal* of the form p ∧ q, it suffices
to prove p and (separately) q.

In this level, our goal is indeed of the form
p ∧ q. We invoke ∧I with the tactic `and_intro` which will split
the goal of proving (2+2=4) ∧ (3<5) into two separate goals: proving 2+2=4
is true and proving 3<5 is true. Try using `and_intro` to split the goal."

Statement : (2+2=4) ∧ (3<5) := by
  and_intro
  Hint "Notice that we now have two separate goals.
  For simple arithmetic like proving 2+2=4, we can use `trivial` tactic."
  trivial
  Hint "Your first use of `trivial` resolved the goal 2+2=4. Use it once more to
  prove 3<5."
  trivial

NewTactic and_intro trivial

Conclusion ""
