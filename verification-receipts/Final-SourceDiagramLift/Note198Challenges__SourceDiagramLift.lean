import OAI.Algebra.Finitistic.Localization.DiagramLifting
import OAI.Algebra.Finitistic.Localization.SourceShiftLinear

namespace Note198
noncomputable section
open CategoryTheory OAI.LittleFinitistic
universe u
variable {k : Type u} [Field k] {d t : ℕ}

/-- Simultaneous lifting of the entire finite quadratic diagram in the
manuscript's actual bounded homotopy category and thick Verdier quotient. -/
theorem source_quadratic_diagram_lift (P : QuadraticEncoding.Relations k d t)
    (na nb nr : ℕ) (Y₀ Y₁ Y₂ : SourceVerdier.Q P)
    (a : Fin na → (Y₀ ⟶ Y₁)) (b : Fin nb → (Y₁ ⟶ Y₂))
    (r : Fin nr → Fin na → Fin nb → k)
    (hr : ∀ ρ, ∑ i, ∑ j, r ρ i j • (a i ≫ b j) = 0) :
    ∃ (X₀ X₁ X₂ : SourceVerdier.K P)
      (e₀ : (SourceVerdier.q P).obj X₀ ≅ Y₀)
      (e₁ : (SourceVerdier.q P).obj X₁ ≅ Y₁)
      (e₂ : (SourceVerdier.q P).obj X₂ ≅ Y₂)
      (f : Fin na → (X₀ ⟶ X₁)) (g : Fin nb → (X₁ ⟶ X₂)),
      (∀ i, (SourceVerdier.q P).map (f i) ≫ e₁.hom = e₀.hom ≫ a i) ∧
      (∀ j, (SourceVerdier.q P).map (g j) ≫ e₂.hom = e₁.hom ≫ b j) ∧
      (∀ ρ, ∑ i, ∑ j, r ρ i j • (f i ≫ g j) = 0) := by
  sorry

end
end Note198
