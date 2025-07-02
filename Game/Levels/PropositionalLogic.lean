import Game.Levels.PropositionalLogic.L01_conjGoal
import Game.Levels.PropositionalLogic.L02_conjHypo
import Game.Levels.PropositionalLogic.L04_disjunctHypo
import Game.Levels.PropositionalLogic.L03_disjunctGoal
import Game.Levels.PropositionalLogic.L05_impGoal
import Game.Levels.PropositionalLogic.L06_impHypo
import Game.Levels.PropositionalLogic.L07_bicondGoal
import Game.Levels.PropositionalLogic.L08_bicondHypo
import Game.Levels.PropositionalLogic.L09_negGoal
import Game.Levels.PropositionalLogic.L10_negHypo

World "PropositionalLogic"
Title "Chapter 1: Propositional Logic"

Introduction "
Consider the following two propositions:

· If c divides b and b divides a, then c divides a.

· If n > 2 and n is prime, then n is odd.

Both share the same _logical form_: `If P and Q, then R`, where P, Q, and R
are _propositional variables_. A proposition's logical
form tells us which proof strategies we should use to prove it
(or to use it as an assumption), and the same strategies apply to all
propositions with that form.

In this world, we begin our study of the logical forms
that propositions can take by considering _propositional formulas_,
the simplest kinds of logical form. These are built from propositional
variables using _logical operators_ or _logical connectives_:
conjunction, disjunction, implication, biconditional, and negation.

Each logical operator is defined by introduction and elimination rules:

· Introduction rules explain how to **prove a goal** when that operator
  appears as the outermost logical connective in the goal.

· Elimination rules explain how to **use an assumption** when that operator
  appears as the outermost logical connective in the assumption.

We'll explore the proof strategies associated to the introduction
and elimination rules for each operator in turn.
"
