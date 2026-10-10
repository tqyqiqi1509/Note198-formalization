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
  obtain ⟨lo₀,hi₀,h₀⟩ := b₀
  obtain ⟨lo₁,hi₁,h₁⟩ := b₁
  obtain ⟨lo₂,hi₂,h₂⟩ := b₂
  let lo := min lo₀ (min lo₁ lo₂)
  let hi := max hi₀ (max hi₁ hi₂)
  refine ⟨lo,hi,RectificationLemma.rectification P D₀ D₁ D₂ f g H lo hi
    ?_ ?_ ?_ p₀ p₁ p₂ f₀ f₁ f₂⟩
  · intro n hn
    apply h₀ n
    dsimp [lo,hi] at hn
    omega
  · intro n hn
    apply h₁ n
    dsimp [lo,hi] at hn
    omega
  · intro n hn
    apply h₂ n
    dsimp [lo,hi] at hn
    omega

end
end Note198

