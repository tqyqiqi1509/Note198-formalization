import Note198.EndomorphismSelection
import OAI.Algebra.Finitistic.Localization.SourceQuotientAction
import OAI.Algebra.Finitistic.Localization.ConcreteFixedDiagram

namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open OAI.LittleFinitistic
open SelectionEncoding RelationBasisCoefficients RelationBasisAction FormalSummandAction
attribute [local instance] Karoubi.karoubi_hasFiniteBiproducts
  hasBinaryBiproducts_of_finite_biproducts
universe u

/-- Lemma 3.4 in the actual bounded projective homotopy category and its
actual localization. All objects, arrows and identifications are chosen
before an evaluation module. The action is the constructed quotient action,
not an assumed representation with the required conclusions. -/
theorem selecting_fixed_diagram_endomorphism
    {k R : Type u} [Field k] [Ring R] [Algebra k R]
    (E : Encoding k R) (S : EndomorphismSelection.Data k R) :
    ∃ (V₀ : SourceVerdier.Q E.relations) (ρ₀ : R →ₐ[k] End V₀)
      (i : (toKaroubi (SourceVerdier.Q E.relations)).obj V₀ ≅
        summand (SourceQuotientAction.theta E) S.e S.idempotent ⊞
          OddDouble.formalShift
            (summand (SourceQuotientAction.theta E) S.e S.idempotent) 3)
      (D₀ D₁ D₂ : SourceVerdier.K E.relations)
      (φ₀ : (SourceVerdier.q E.relations).obj D₀ ≅ V₀)
      (φ₁ : (SourceVerdier.q E.relations).obj D₁ ≅ V₀)
      (φ₂ : (SourceVerdier.q E.relations).obj D₂ ≅ V₀)
      (f : Fin (E.generators + 1) → (D₀ ⟶ D₁))
      (g : Fin (E.generators + 1) → (D₁ ⟶ D₂)),
      (∀ r : R, (toKaroubi (SourceVerdier.Q E.relations)).map (ρ₀ r) ≫ i.hom =
        i.hom ≫ oddDoubleAction (SourceQuotientAction.theta E)
          S.e S.idempotent (fun r => (S.central r).eq) S.α r) ∧
      (∀ a, (SourceVerdier.q E.relations).map (f a) ≫ φ₁.hom =
        φ₀.hom ≫ ρ₀ (arrow (generator E) a)) ∧
      (∀ b, (SourceVerdier.q E.relations).map (g b) ≫ φ₂.hom =
        φ₁.hom ≫ ρ₀ (arrow (generator E) b)) ∧
      (∀ r : RelationIndex E.relations,
        ∑ a, ∑ b, basisCoefficient E.relations r a b • (f a ≫ g b) = 0) := by
  exact ConcreteFixedDiagram.fixed_diagram E (SourceQuotientAction.theta E)
    S.e S.idempotent (fun r => (S.central r).eq) S.α

end
end Note198
