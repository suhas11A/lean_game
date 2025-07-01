import Game.Metadata
import GameServer.Commands
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

/-
(1) strat - indirect pf by contradiction (double negation)
    a,b,c non-neg reals s.t. a^2+b^2=c^2
    prove a+b \geq c
(2) strat - proof by contraposition
    fix naturals n, m. mn>64 \imp m > 8 or n > 8
    (prove the contrapositive)
(3) (deMorgan's laws for logical operators)
(4) (deMorgan's laws for quantifiers)
(5) strat - pf by counterexample (for quantifiers)
    not every integer is divisible by a prime number
    not every rational can be expressed as a/b, a even and b odd
(6) strat - assuming tautologies

exercises: proofs in natural numbers
-/

World "LogicalEquivalence"
Level 2
Title "Proof by Contraposition"

Introduction ""

-- fix naturals n, m. mn>64 → m > 8 or n > 8

Statement (n m : ℕ) : m*n > 64 → m > 8 ∨ n > 8 := by


NewTactic

Conclusion ""
