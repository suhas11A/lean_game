import Game.Metadata
import Mathlib.Data.Set.Defs

World "Functions"
Level 12
Title "Preimage of the codomain"

Introduction "
Recall that `univ` here refers to the sets $X$ and $Y$ themselves;
the goal in this theorem states that the preimage of the
codomain-universe (the whole set $Y$) is the domain-universe (the
whole set $X$f.)
"

open Set

/-- For all functions $f : X → Y$, $f^{-1}[Y] = X$.
 -/
Statement (X Y : Type) (f : X → Y) : f ⁻¹' univ = univ := by
  ext
  rw [mem_preimage]
  trivial

Conclusion "

"

NewTheorem Set.mem_preimage
