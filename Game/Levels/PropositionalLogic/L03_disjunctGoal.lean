import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 3
Title "Disjunction in the Goal"

Introduction "
The introduction rules for ∨ are
(∨I₁) If p is true, then p ∨ q is true.
(∨I₂) If q is true, then p ∨ q is true.
This means that to *prove a goal* of the form p ∨ q, it suffices
to either prove p is true or prove q is true.

When we have a goal of the form
`h: p ∨ q`, we can use either `or_intro p` to invoke ∨I₁ or `or_intro q` to invoke ∨I₂.
Note that we should be careful whether we choose to prove p or q, as one
might be more difficult and require us to go back and prove the other.
Try using either `or_intro 3<2` or `or_intro 2+2=4` to begin the proof.
"

Statement : 2+2=4 ∨ 3<2 := by
  or_intro 2+2=4
  Hint "Use the `trivial` tactic to finish the proof."
  trivial

NewTactic or_intro

Conclusion ""
