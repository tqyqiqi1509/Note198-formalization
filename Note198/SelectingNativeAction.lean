import Note198.SelectingNativeEvaluation

namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace SelectingNativeEvaluation
open OAI.LittleFinitistic
open QuadraticEncoding SourceImageEvaluation FiniteProjectiveHomotopy SelectingRectification
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {E : SelectionEncoding.Encoding k R} {S : EndomorphismSelection.Data k R}
variable {Y : Type u} [AddCommGroup Y] [Module k Y]
  [Module R Y] [IsScalarTower k R Y]

abbrev imageEnd (r : R) := imageCornerEnd
  (action (k := k) (Y := Y) S.e).hom (action (k := k) (Y := Y) (S.α r)).hom
abbrev moduleIso := (SelectingImageComparison.equiv S (Y := Y)).toModuleIso

def HAction (r : R) : End (H (S := S) (Y := Y)) :=
  (moduleIso (S := S) (Y := Y)).inv ≫ imageEnd (S := S) (Y := Y) r ≫ (moduleIso (S := S) (Y := Y)).hom

/-- The conjugated map is the primary selectionStep module action, on every vector. -/
theorem HAction_apply (r : R) (x : H (S := S) (Y := Y)) :
    (HAction (S := S) (Y := Y) r).hom x = SelectingImageComparison.moduleAction S (Y := Y) r x := by
  have h := SelectingImageComparison.equiv_action S (Y := Y) r
    ((SelectingImageComparison.equiv S (Y := Y)).symm x)
  dsimp only [HAction,moduleIso,LinearEquiv.toModuleIso] at *
  simp only [LinearEquiv.apply_symm_apply] at h
  exact h

lemma module_square (r : R) :
    imageEnd (S := S) (Y := Y) r ≫ (moduleIso (S := S) (Y := Y)).hom =
      (moduleIso (S := S) (Y := Y)).hom ≫ HAction (S := S) (Y := Y) r := by
  simp only [HAction,Iso.hom_inv_id_assoc]

variable [FiniteDimensional k Y]

def HKAction (r : R) : End (HK (S := S) (Y := Y)) :=
  (inclusion k).preimage ((vectorStalk (k := k)).map (HAction (S := S) (Y := Y) r))
def HDerivedAction (r : R) : End (HDerived (S := S) (Y := Y)) :=
  (derivedEmbedding k).toEssImage.map (HKAction (S := S) (Y := Y) r)

lemma imageIsoK_hom : (inclusion k).map (imageIsoK (S := S) (Y := Y)).hom =
    (vectorStalk (k := k)).map (moduleIso (S := S) (Y := Y)).hom := by
  simp only [imageIsoK,Functor.preimageIso,Functor.mapIso_hom]
  erw [Functor.map_preimage]

lemma image_square (r : R) :
    imageCorner (k := k) (Y := Y) S.e (S.α r) ≫ (imageIso (S := S) (Y := Y)).hom =
      (imageIso (S := S) (Y := Y)).hom ≫ HDerivedAction (S := S) (Y := Y) r := by
  apply (derivedTargetInclusion (k := k)).map_injective
  rw [Functor.map_comp,Functor.map_comp]
  dsimp only [imageCorner]
  erw [Functor.map_preimage]
  change DerivedCategory.Qh.map ((vectorStalk (k := k)).map (imageEnd (S := S) (Y := Y) r)) ≫
    DerivedCategory.Qh.map ((inclusion k).map (imageIsoK (S := S) (Y := Y)).hom) =
    DerivedCategory.Qh.map ((inclusion k).map (imageIsoK (S := S) (Y := Y)).hom) ≫
    DerivedCategory.Qh.map ((inclusion k).map (HKAction (S := S) (Y := Y) r))
  rw [(imageIsoK_hom (S := S))]
  dsimp only [HKAction]
  erw [Functor.map_preimage]
  erw [← Functor.map_comp,← Functor.map_comp,← Functor.map_comp,← Functor.map_comp,(module_square (S := S))]
  rfl

abbrev targetAction (r : R) : End (target (S := S) (Y := Y)) :=
  biprod.map (HDerivedAction (S := S) (Y := Y) r) ((HDerivedAction (S := S) (Y := Y) r)⟦(3 : ℤ)⟧')

lemma target_square (r : R) :
    Note198DiagramEvaluation.targetAction (S := S) (Y := Y) r ≫ (targetIso (S := S) (Y := Y)).hom =
      (targetIso (S := S) (Y := Y)).hom ≫ targetAction (S := S) (Y := Y) r := by
  have h := image_square (S := S) (Y := Y) r
  have hs := congrArg (shiftFunctor (FiniteVectorDerived.{u,u} (k := k)) (3 : ℤ)).map h
  simp only [Functor.map_comp] at hs
  dsimp only [Note198DiagramEvaluation.targetAction,targetIso,targetAction,biprod.mapIso]
  apply biprod.hom_ext
  · simp only [Category.assoc,biprod.map_fst,biprod.map_fst_assoc,h]
  · simp only [Category.assoc,biprod.map_snd,biprod.map_snd_assoc,Functor.mapIso_hom,hs]

/-- The fixed V0 evaluates equivariantly to the primary (H (S := S))(Y) plus (H (S := S))(Y)[3]. -/
theorem V0_action (r : R) :
    (Note198DiagramEvaluation.F (E := E) (Y := Y)).map ((fixedData E S).ρ₀ r) ≫ (V0Iso (E := E) (S := S) (Y := Y)).hom =
      (V0Iso (E := E) (S := S) (Y := Y)).hom ≫ targetAction (S := S) (Y := Y) r :=
  DiagramEvaluationSquares.compose _ _ _ (Note198DiagramEvaluation.V0Iso (E := E) (S := S))
    (Note198DiagramEvaluation.V0Iso (E := E) (S := S)) (targetIso (S := S)) (targetIso (S := S))
    ((Note198DiagramEvaluation.V0_action (E := E) (S := S)) r) ((target_square (S := S)) r)

theorem D_arrow01 (a : Fin (E.generators+1)) :
    (Note198DiagramEvaluation.sourceEvaluation (E := E) (Y := Y)).map ((fixedData E S).f a) ≫ (D1Iso (E := E) (S := S) (Y := Y)).hom =
      (D0Iso (E := E) (S := S) (Y := Y)).hom ≫ targetAction (S := S) (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator E) a) :=
  DiagramEvaluationSquares.compose _ _ _ (Note198DiagramEvaluation.D0Iso (E := E) (S := S))
    (Note198DiagramEvaluation.D1Iso (E := E) (S := S)) (targetIso (S := S)) (targetIso (S := S))
    ((Note198DiagramEvaluation.D_arrow01 (E := E) (S := S)) a) ((target_square (S := S)) _)

theorem D_arrow12 (a : Fin (E.generators+1)) :
    (Note198DiagramEvaluation.sourceEvaluation (E := E) (Y := Y)).map ((fixedData E S).g a) ≫ (D2Iso (E := E) (S := S) (Y := Y)).hom =
      (D1Iso (E := E) (S := S) (Y := Y)).hom ≫ targetAction (S := S) (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator E) a) :=
  DiagramEvaluationSquares.compose _ _ _ (Note198DiagramEvaluation.D1Iso (E := E) (S := S))
    (Note198DiagramEvaluation.D2Iso (E := E) (S := S)) (targetIso (S := S)) (targetIso (S := S))
    ((Note198DiagramEvaluation.D_arrow12 (E := E) (S := S)) a) ((target_square (S := S)) _)
end SelectingNativeEvaluation

end

end Note198
