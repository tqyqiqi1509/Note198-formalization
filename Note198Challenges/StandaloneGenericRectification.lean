import OAI.Algebra.Finitistic.Rectification.RectificationLemma

namespace Note198
noncomputable section
open CategoryTheory HomologicalComplex OAI OAI.LittleFinitistic
open ExternalTensor.Section4 QuadraticEncoding
universe u

/-- Lemma 4.2 for arbitrary bounded finitely generated projective right
complexes and arbitrary assigned relation homotopies. `Verified` refers to
the actual three-column induced total; its fields give boundedness, finite
terms, right projectivity, the original vertex insertion homotopy
equivalences and both arrow-compatibility homotopies. No selected diagram
or conclusion about the total is supplied as an input. -/
theorem standalone_generic_rectification
    {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
    (D₀ D₁ D₂ : RightComplex (B P))
    (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
    (H : ∀ r, Homotopy
      (relationMap (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g r) 0)
    (b₀ : ∃ lo hi : ℤ, ∀ n, n < lo ∨ hi < n → CategoryTheory.Limits.IsZero (D₀.X n))
    (b₁ : ∃ lo hi : ℤ, ∀ n, n < lo ∨ hi < n → CategoryTheory.Limits.IsZero (D₁.X n))
    (b₂ : ∃ lo hi : ℤ, ∀ n, n < lo ∨ hi < n → CategoryTheory.Limits.IsZero (D₂.X n))
    (p₀ : ∀ n, Module.Projective (B P)ᵐᵒᵖ (D₀.X n))
    (p₁ : ∀ n, Module.Projective (B P)ᵐᵒᵖ (D₁.X n))
    (p₂ : ∀ n, Module.Projective (B P)ᵐᵒᵖ (D₂.X n))
    (f₀ : ∀ n, Module.Finite (B P)ᵐᵒᵖ (D₀.X n))
    (f₁ : ∀ n, Module.Finite (B P)ᵐᵒᵖ (D₁.X n))
    (f₂ : ∀ n, Module.Finite (B P)ᵐᵒᵖ (D₂.X n)) :
    ∃ lo hi : ℤ, RectificationLemma.Verified P D₀ D₁ D₂ f g H lo hi := by
  sorry

end
end Note198

