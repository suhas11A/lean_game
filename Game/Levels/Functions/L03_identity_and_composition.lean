import Game.Metadata

World "Functions"
Level 3
Title "The identity function and composition"

Introduction "
In Lean, the identity function on any type $X$ is written `id`.  You
don't need to specify the type yourself; Lean will figure it out
automatically.

The composition of two functions is written with the `∘` symbol, which
you can type using `\\circ`.  For instance, if we have a function `f :
A → B` and a function `g : B → C`, then we can write their
composition, $g ∘ f$, as `g ∘ f`.

Let's prove Example 3.1.20.  In Lean, the argument is straightforward;
just split this proof into its two cases, use function
extensionality in each goal, and then solve each goal using `rfl`.
Lean is able to compute with the identity function and composition
automatically.
"

/-- Let $f : X → Y$ be any function.  Then

$$id_Y ∘ f = f = f ∘ id_X.$$
 -/
Statement (X Y : Type) (f : X → Y) : (id ∘ f = f) ∧ (f ∘ id = f) := by
  constructor
  -- Actually, both of these cases can be trivially solved without funext, but
  -- let's pretend Lean isn't that smart :)
  · funext x
    rfl
  · funext x
    rfl

NewDefinition id Function.comp

Conclusion "Great! Now we can move onto proving associativity of composition."
