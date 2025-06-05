import Game.Metadata

World "Functions"
Level 4
Title "Associativity of composition"

Introduction "
You’re on your own for this one—but don’t worry, the proof is pretty
short.
"

/-- If $f : X → Y$, $g : Y → Z$, and $h : Z → W$ are functions, then

$$h ∘ (g ∘ f) = (h ∘ g) ∘ f : X → W.$$
 -/
Statement (X Y Z W : Type) (f : X → Y) (g : Y → Z) (h : Z → W) : h ∘ (g ∘ f) = (h ∘ g) ∘ f := by
  funext
  rfl

Conclusion "
Lean took care of basically everything for you in this proof, so it
would be a good idea to try writing the proof out on your own as well.
"
