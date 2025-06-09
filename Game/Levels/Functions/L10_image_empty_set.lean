import Game.Metadata
import Mathlib.Data.Set.Defs

World "Functions"
Level 10
Title "Image of the empty set"

Introduction "
In Lean, we write the image of $A$ under $f$, where $f$ is a function
and $A$ a set in its domain, as `f '' A`—that’s two apostrophes, not a
double quote.
"

open Set

/-- For all functions $f : X → Y$, $f[∅] = ∅$.
 -/
Statement (X Y : Type) (f : X → Y) : f '' ∅ = ∅ := by
  ext
  constructor
  · intro h
    rw [mem_image] at h
    cases h with
    | intro w h =>
      cases h
      contradiction
  · intro h
    contradiction

Conclusion "

"

NewTheorem Set.mem_image
