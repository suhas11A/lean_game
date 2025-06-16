import Game.Levels.Sets.L01_intro
import Game.Levels.Sets.L02_intervals
import Game.Levels.Sets.L03_types
import Game.Levels.Sets.L04_subsets
import Game.Levels.Sets.L05_equality
import Game.Levels.Sets.L06_phi
import Game.Levels.Sets.L07_emptiness
import Game.Levels.Sets.L08_phi
import Game.Levels.Sets.L09_power

World "Sets"
Title "Section 2.1: Sets"

Introduction "
Welcome to Set World!

To specify that an object `x` belongs to the set of Natural Numbers `ℕ`, we write `x : ℕ`.
To specify that `A` is a set of objects from `ℕ`, we write `A : Set ℕ`.
(The terminology used in Lean is that `x` has type `ℕ` and `A` has type `Set ℕ`).

To say that `x` is an element of `A`, we write `x ∈ A`.

The notation A ⊆ B means that A is a subset of B.

Click on 'Start' below to get started.
"
