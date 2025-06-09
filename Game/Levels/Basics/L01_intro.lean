import GameServer.Commands

World "Basics"
Level 1
Title "Introduction to Proofs in Lean"

Introduction "
Let’s get started by proving some very basic theorems within Lean, to
get you familiar with how Lean works and what it lets you do.

In the middle of the screen is a log of your entire proof.  Right now,
it contains the proposition you need to prove, written in plain
English, as well as a “Goal”, which displays the same information in
Lean’s syntax.  There is also a textbox where you can insert commands,
called tactics, that Lean will follow to advance the proof.

This first theorem looks obvious, but we do need to tell Lean one
thing in order to finish the proof; that it is true because of
reflexivity of equality, i.e., because any number is equal to itself.

To tell Lean to apply reflexivity of equality, use the tactic `rfl`.
Type `rfl` in the box.
"

/-- $0$ is equal to $0$. -/
Statement : 0 = 0 := by
  rfl

/-- `rfl` solves a goal of the form `e = e`.  Both sides of the equality must be exactly the same. -/
TacticDoc rfl

NewTactic rfl

Conclusion "
Good, you’ve written your first proof in Lean!

On the right side of the screen, you can see an inventory of all the
tactics and theorems you have learned so far and are able to use.  You
can click on the name of a tactic or theorem to pull up a window
explaining what it does.

Onto the next level!
"
