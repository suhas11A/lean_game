import Game.Metadata
World "Weak Induction"
Level 1
Title "--title--"

Introduction "
--intro--
"

/-- Suppose x∈A∩B. Then x∈B. -/
Statement (x : ℕ): x = x := by
  Hint "This level aims at introducing Peano's Axioms"
  rfl

Conclusion "--conc--"
