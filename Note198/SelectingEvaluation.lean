import Note198.SelectingRectification
import OAI.Algebra.Finitistic.Localization.SourceOddDoubleEvaluation
import OAI.Algebra.Finitistic.Localization.DiagramEvaluationSquares

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.Note198DiagramEvaluation
open QuadraticEncoding SourceImageEvaluation
open Note198.SelectingRectification
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {E : SelectionEncoding.Encoding k R} {S : Note198.EndomorphismSelection.Data k R}
variable {Y : Type u} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]

abbrev F := SourceImageEvaluation.evaluation (Y := Y) E
abbrev G := completed (Y := Y) E
abbrev target := imageDerived (k := k) (Y := Y) S.e ⊞ (imageDerived (k := k) (Y := Y) S.e)⟦(3 : ℤ)⟧
def targetAction (r : R) : (target (S := S) (Y := Y)) ⟶ (target (S := S) (Y := Y)) :=
  biprod.map (imageCorner (k := k) (Y := Y) S.e (S.α r)) ((imageCorner (k := k) (Y := Y) S.e (S.α r))⟦(3 : ℤ)⟧')

/-- Evaluation of the one fixed actual V0 is precisely eY direct-sum eY[3]. -/
def V0Iso : ((F (E := E) (Y := Y))).obj (fixedData E S).V₀ ≅ (target (S := S) (Y := Y)) :=
  (factors (Y := Y) E).symm.app (fixedData E S).V₀ ≪≫
    (((G (E := E) (Y := Y))).mapIso (fixedData E S).iso ≪≫ oddDoubleImageIso (Y := Y) E S.e S.idempotent)

/-- The V0 identification intertwines every selected algebra element on both summands. -/
theorem V0_action (r : R) :
    ((F (E := E) (Y := Y))).map ((fixedData E S).ρ₀ r) ≫ ((V0Iso (E := E) (S := S) (Y := Y))).hom =
      ((V0Iso (E := E) (S := S) (Y := Y))).hom ≫ (targetAction (S := S) (Y := Y)) r := by
  have hf := (factors (Y := Y) E).inv.naturality ((fixedData E S).ρ₀ r)
  have hi := congrArg (fun f => ((G (E := E) (Y := Y))).map f) ((fixedData E S).equivariant r)
  simp only [Functor.map_comp] at hi
  have ho := oddDouble_selecting_square (Y := Y) E S.e S.idempotent (fun r => (S.central r).eq) S.α r
  exact DiagramEvaluationSquares.compose _ _ _
    ((factors (Y := Y) E).symm.app (fixedData E S).V₀)
    ((factors (Y := Y) E).symm.app (fixedData E S).V₀)
    (((G (E := E) (Y := Y))).mapIso (fixedData E S).iso ≪≫ oddDoubleImageIso (Y := Y) E S.e S.idempotent)
    (((G (E := E) (Y := Y))).mapIso (fixedData E S).iso ≪≫ oddDoubleImageIso (Y := Y) E S.e S.idempotent)
    hf (DiagramEvaluationSquares.compose _ _ _
      (((G (E := E) (Y := Y))).mapIso (fixedData E S).iso) (((G (E := E) (Y := Y))).mapIso (fixedData E S).iso)
      (oddDoubleImageIso (Y := Y) E S.e S.idempotent) (oddDoubleImageIso (Y := Y) E S.e S.idempotent)
      hi ho)

abbrev sourceEvaluation := SourceEvaluation.finite
  (SourceActionEvaluation.representation (Y := Y) E) ⋙ (FiniteProjectiveHomotopy.derivedEmbedding k).toEssImage

def sourceFactors : SourceVerdier.q E.relations ⋙ (F (E := E) (Y := Y)) ≅ (sourceEvaluation (E := E) (Y := Y)) :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
    (SourceEvaluation.finiteFactors (SourceActionEvaluation.representation (Y := Y) E))
    (FiniteProjectiveHomotopy.derivedEmbedding k).toEssImage

def D0Iso : ((sourceEvaluation (E := E) (Y := Y))).obj (fixedData E S).D₀ ≅ (target (S := S) (Y := Y)) :=
  ((sourceFactors (E := E) (Y := Y))).symm.app (fixedData E S).D₀ ≪≫ (((F (E := E) (Y := Y))).mapIso (fixedData E S).φ₀ ≪≫ (V0Iso (E := E) (S := S) (Y := Y)))
def D1Iso : ((sourceEvaluation (E := E) (Y := Y))).obj (fixedData E S).D₁ ≅ (target (S := S) (Y := Y)) :=
  ((sourceFactors (E := E) (Y := Y))).symm.app (fixedData E S).D₁ ≪≫ (((F (E := E) (Y := Y))).mapIso (fixedData E S).φ₁ ≪≫ (V0Iso (E := E) (S := S) (Y := Y)))
def D2Iso : ((sourceEvaluation (E := E) (Y := Y))).obj (fixedData E S).D₂ ≅ (target (S := S) (Y := Y)) :=
  ((sourceFactors (E := E) (Y := Y))).symm.app (fixedData E S).D₂ ≪≫ (((F (E := E) (Y := Y))).mapIso (fixedData E S).φ₂ ≪≫ (V0Iso (E := E) (S := S) (Y := Y)))

/-- Every first-family arrow of the same fixed K diagram has its selected action. -/
theorem D_arrow01 (a : Fin (E.generators+1)) :
    ((sourceEvaluation (E := E) (Y := Y))).map ((fixedData E S).f a) ≫ ((D1Iso (E := E) (S := S) (Y := Y))).hom =
      ((D0Iso (E := E) (S := S) (Y := Y))).hom ≫ (targetAction (S := S) (Y := Y))
        (RelationBasisAction.arrow (SelectionEncoding.generator E) a) := by
  have hn := ((sourceFactors (E := E) (Y := Y))).inv.naturality ((fixedData E S).f a)
  have hp := congrArg (fun f => ((F (E := E) (Y := Y))).map f) ((fixedData E S).arrow01 a)
  simp only [Functor.map_comp] at hp
  exact DiagramEvaluationSquares.compose _ _ _
    (((sourceFactors (E := E) (Y := Y))).symm.app (fixedData E S).D₀) (((sourceFactors (E := E) (Y := Y))).symm.app (fixedData E S).D₁)
    (((F (E := E) (Y := Y))).mapIso (fixedData E S).φ₀ ≪≫ (V0Iso (E := E) (S := S) (Y := Y)))
    (((F (E := E) (Y := Y))).mapIso (fixedData E S).φ₁ ≪≫ (V0Iso (E := E) (S := S) (Y := Y))) hn
    (DiagramEvaluationSquares.compose _ _ _
      (((F (E := E) (Y := Y))).mapIso (fixedData E S).φ₀) (((F (E := E) (Y := Y))).mapIso (fixedData E S).φ₁)
      ((V0Iso (E := E) (S := S) (Y := Y))) ((V0Iso (E := E) (S := S) (Y := Y))) hp ((V0_action (E := E) (S := S)) _))

theorem D_arrow12 (a : Fin (E.generators+1)) :
    ((sourceEvaluation (E := E) (Y := Y))).map ((fixedData E S).g a) ≫ ((D2Iso (E := E) (S := S) (Y := Y))).hom =
      ((D1Iso (E := E) (S := S) (Y := Y))).hom ≫ (targetAction (S := S) (Y := Y))
        (RelationBasisAction.arrow (SelectionEncoding.generator E) a) := by
  have hn := ((sourceFactors (E := E) (Y := Y))).inv.naturality ((fixedData E S).g a)
  have hp := congrArg (fun f => ((F (E := E) (Y := Y))).map f) ((fixedData E S).arrow12 a)
  simp only [Functor.map_comp] at hp
  exact DiagramEvaluationSquares.compose _ _ _
    (((sourceFactors (E := E) (Y := Y))).symm.app (fixedData E S).D₁) (((sourceFactors (E := E) (Y := Y))).symm.app (fixedData E S).D₂)
    (((F (E := E) (Y := Y))).mapIso (fixedData E S).φ₁ ≪≫ (V0Iso (E := E) (S := S) (Y := Y)))
    (((F (E := E) (Y := Y))).mapIso (fixedData E S).φ₂ ≪≫ (V0Iso (E := E) (S := S) (Y := Y))) hn
    (DiagramEvaluationSquares.compose _ _ _
      (((F (E := E) (Y := Y))).mapIso (fixedData E S).φ₁) (((F (E := E) (Y := Y))).mapIso (fixedData E S).φ₂)
      ((V0Iso (E := E) (S := S) (Y := Y))) ((V0Iso (E := E) (S := S) (Y := Y))) hp ((V0_action (E := E) (S := S)) _))

include E in
theorem targetAction_one : (targetAction (S := S) (Y := Y)) (1 : R) = 𝟙 _ := by
  apply (cancel_epi ((V0Iso (E := E) (S := S) (Y := Y))).hom).mp
  rw [← (V0_action (E := E) (S := S)),map_one]
  change ((F (E := E) (Y := Y))).map (𝟙 (fixedData E S).V₀) ≫ _ = _
  rw [CategoryTheory.Functor.map_id,Category.id_comp,Category.comp_id]

theorem distinguished_arrow01 :
    ((sourceEvaluation (E := E) (Y := Y))).map ((fixedData E S).f 0) ≫ ((D1Iso (E := E) (S := S) (Y := Y))).hom = ((D0Iso (E := E) (S := S) (Y := Y))).hom := by
  have h := (D_arrow01 (E := E) (S := S) (Y := Y)) 0
  simpa only [RelationBasisAction.arrow,Fin.cases_zero,(targetAction_one (E := E) (S := S)),Category.comp_id] using h

theorem distinguished_arrow12 :
    ((sourceEvaluation (E := E) (Y := Y))).map ((fixedData E S).g 0) ≫ ((D2Iso (E := E) (S := S) (Y := Y))).hom = ((D1Iso (E := E) (S := S) (Y := Y))).hom := by
  have h := (D_arrow12 (E := E) (S := S) (Y := Y)) 0
  simpa only [RelationBasisAction.arrow,Fin.cases_zero,(targetAction_one (E := E) (S := S)),Category.comp_id] using h

/-- The same globally chosen K diagram evaluates correctly for every finite module. -/
theorem fixed_diagram_evaluates :
    ∃ (i0 : ((sourceEvaluation (E := E) (Y := Y))).obj (fixedData E S).D₀ ≅ (target (S := S) (Y := Y)))
      (i1 : ((sourceEvaluation (E := E) (Y := Y))).obj (fixedData E S).D₁ ≅ (target (S := S) (Y := Y)))
      (i2 : ((sourceEvaluation (E := E) (Y := Y))).obj (fixedData E S).D₂ ≅ (target (S := S) (Y := Y))),
      (∀ a, ((sourceEvaluation (E := E) (Y := Y))).map ((fixedData E S).f a) ≫ i1.hom =
        i0.hom ≫ (targetAction (S := S) (Y := Y)) (RelationBasisAction.arrow (SelectionEncoding.generator E) a)) ∧
      (∀ b, ((sourceEvaluation (E := E) (Y := Y))).map ((fixedData E S).g b) ≫ i2.hom =
        i1.hom ≫ (targetAction (S := S) (Y := Y)) (RelationBasisAction.arrow (SelectionEncoding.generator E) b)) :=
  ⟨(D0Iso (E := E) (S := S)),(D1Iso (E := E) (S := S)),(D2Iso (E := E) (S := S)),(D_arrow01 (E := E) (S := S)),(D_arrow12 (E := E) (S := S))⟩

omit [FiniteDimensional k Y] in
/-- Exact vector formula for the selected action, including the S.α restriction. -/
theorem targetAction_on_image (r : R) (y : imageSpace (k := k) (Y := Y) S.e) :
    ((imageCornerEnd (action (k := k) (Y := Y) S.e).hom (action (k := k) (Y := Y) (S.α r)).hom) y).val =
      (action (k := k) (Y := Y) (S.α r)).hom y.val :=
  imageCorner_restriction S.e (S.α r) S.idempotent ((fun r => (S.central r).eq) (S.α r)) y
end LittleFinitistic.Note198DiagramEvaluation

end

end OAI
