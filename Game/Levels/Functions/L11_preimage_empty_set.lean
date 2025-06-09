import Game.Metadata
import Mathlib.Data.Set.Defs

World "Functions"
Level 11
Title "Preimage of the empty set"

Introduction "
In Lean, we write the preimage of $A$ under $f$, where $f$ is a function
and $A$ a set in its domain, as `f ⁻¹' A`.  To write `⁻¹`, type `\\-1`.
"

open Set

/-- For all functions $f : X → Y$, $f^{-1}[∅] = ∅$.
 -/
Statement (X Y : Type) (f : X → Y) : f ⁻¹' ∅ = ∅ := by
  ext
  constructor
  · intro h
    rw [mem_preimage] at h
    contradiction
  · intro h
    contradiction

Conclusion "

"

NewTheorem Set.mem_preimage
