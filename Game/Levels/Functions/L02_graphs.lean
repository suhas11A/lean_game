import Game.Metadata
import Mathlib

open Set

World "Functions"
Level 2
Title "The graph of a function"

Introduction "
This proof is long and complicated.  The backward direction in
particular may be too much for this course, so we may remove it.  No
hints just yet.
"

-- This lemma is from mathlib, but it doesn't look like Lean 4.7.0 has it.
-- Should double check later.
lemma mem_graphOn : x ∈ graphOn f s ↔ x.1 ∈ s ∧ f x.1 = x.2 := by aesop (add simp graphOn)

/-- Let $X$ and $Y$ be sets.  A subset $G ⊆ X×Y$ is the graph of a function if and only if:

$∀ x∈X, ∃! y∈Y, (x,y)∈G.$
 -/
Statement (X Y : Type) (G : Set (X × Y)) :
  (∃ f : X → Y, G = graphOn f univ) ↔ (∀ x : X, ∃! y : Y, (x, y) ∈ G) := by
  constructor
  · intro ⟨f, hg⟩ x
    use f x
    Hint "
    The goal might look scary, but remember you can use `dsimp`.
    "
    dsimp
    rw [hg]
    constructor
    · apply mem_graphOn.mpr
      constructor
      · apply mem_univ
      · rfl
    · intro y
      intro h
      apply mem_graphOn.mp at h
      cases h
      rw [right]
  · intro h
    let f : X → Y := fun x ↦ (h x).exists.choose
    have hf : ∀ (x : X), (x, f x) ∈ G
    · intro x
      specialize h x
      exact Exists.choose_spec h.exists
    use f
    ext ⟨x,y⟩
    constructor
    · intro hxy
      apply mem_graphOn.mpr
      constructor
      · apply mem_univ
      · simp
        specialize h x
        rcases h with ⟨y', h_exists, h_unique⟩
        simp at h_unique
        apply h_unique at hxy
        rw [hxy]
        apply h_unique
        exact hf x
    · intro hxy
      apply mem_graphOn.mp at hxy
      simp at hxy
      rw [← hxy]
      exact hf x

Conclusion ""

NewTheorem Set.graphOn mem_graphOn Set.mem_univ Exists.choose Exists.choose_spec
NewTactic cases constructor specialize ext rfl apply simp «have» «let»
