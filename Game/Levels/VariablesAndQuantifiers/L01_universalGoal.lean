import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 1
Title "Universal Quantifier in the Goal"


Introduction "
Let p(x) be a logical formula with free variable x with range X.
The introduction rule of the universal quantifier (∀) is
(∀I) If p(x) can be derived from the assumption that x is an arbitrary
element of X, then ∀x ∈ X, p(x).
The expression `∀x ∈ X, p(x)` represents \"for all x ∈ X, p(x)\".
This means that to **prove a goal** of the form `∀x ∈ X, p(x)`, it suffices to take
an arbitrary y ∈ X and prove p(y) is true.

In this level, we have goal `∀x ∈ ℤ, x<x+1`. `forall_intro y` invokes ∀I by taking y to be an
arbitrary element of ℤ and changing the goal to proving y<y+1 is true. Try using `forall_intro`
with the correct syntax to begin the proof.
"

Statement : ∀x:ℤ, x<x+1 := by
  forall_intro y
  -- TODO: finish writing the proof
  simp




NewTactic forall_intro
Conclusion
