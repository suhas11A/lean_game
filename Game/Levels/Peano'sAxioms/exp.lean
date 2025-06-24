import Mathlib.Init.Data.Nat.Basic
import Game.Metadata
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic
World "Peano'sAxioms"
Level 1
Title "--title--"

Introduction "
--intro--
"
theorem Nat.of_le_succ{m n : ℕ} : m ≤ n.succ → m ≤ n ∨ m = n.succ :=
  sorry
def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  rfl

theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
  induction' n with n ih
  · exact absurd ipos (not_lt_of_ge ile)
  rw [fac]
  rcases Nat.of_le_succ ile with h | h
  · apply dvd_mul_of_dvd_right (ih h)
  rw [h]
  apply dvd_mul_right

/-- Suppose x∈A∩B. Then x∈B. -/
Statement {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
  induction' n with n hn
  sorry
  sorry

Conclusion "--conc--"
