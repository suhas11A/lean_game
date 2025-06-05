import Game.Levels.Functions.L01_extensionality
import Game.Levels.Functions.L02_graphs
import Game.Levels.Functions.L03_identity_and_composition
import Game.Levels.Functions.L04_associativity_of_composition
import Game.Levels.Functions.L05_characteristic_functions

World "Functions"
Title "Chapter 3: Functions"

Introduction "
In this world, we will follow Chapter 3 of Infinite Descent, which
focuses on functions.  Functions in Lean are defined slightly
differently from the way they are defined in the textbook; they are
given as algorithms rather than lists of inputs and outputs, but the
relevant theorems are all the same.

In Lean, the type of a function with domain $X$ and codomain $Y$ is `X
→ Y`.  So, if you have a line that says `f : ℤ → ℕ` in the Objects
section of a proof you are doing, then you know that $f$ is a function
from the integers to the natural numbers.

To write the value of a function at a point, just write the function
name followed by the argument; for instance, `f 2` denotes the
mathematical expression $f(2)$.  You can use parentheses if needed;
for instance, `f (2 + 2)` denotes $f(2+2)$.
"
