import Game.Metadata
import GameServer.Commands
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

World "LogicalEquivalence"
Level 3
Title "Proof by Contraposition"

Introduction ""

-- fix naturals n, m. mn>64 → m > 8 or n > 8

Statement (n m : ℕ) : m*n > 64 → m > 8 ∨ n > 8 := by


NewTactic

Conclusion ""
