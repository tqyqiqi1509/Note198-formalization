import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Note198.GenericOddDiagramEvaluation
import Note198.GenericTwoDegrees
import Note198.SelectingImageComparison
import OAI.Algebra.Finitistic.Localization.EvaluationVertexDiagram
import OAI.Algebra.Finitistic.Localization.TensorCohomologyDiagram
import OAI.Algebra.Finitistic.Localization.UnderlyingRepresentatives
import OAI.Algebra.Finitistic.Rectification.FullTensorProperties
import OAI.Algebra.Finitistic.Rectification.VertexCategoricalAssembly

/-! Parametric §7.3 tensor realization. The actual source data are chosen before Y. -/

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.Note198GenericOddTensorComparison
open QuadraticEncoding FiniteProjectiveHomotopy
universe u v
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

abbrev tensor (D : SourceVerdier.K P) :=
  ((BalancedTensor.tensorFunctor k (B P) X.Evaluation).mapHomologicalComplex (.up ℤ)).obj
    (UnderlyingRepresentatives.complex P D)

/-- The chosen representative's actual tensor is the source evaluation object. -/
def homotopyIso (D : SourceVerdier.K P) :
    (HomotopyCategory.quotient _ _).obj (tensor X D) ≅ (SourceEvaluation.evaluation X).obj D :=
  Iso.refl _

variable [FiniteDimensional k Y]
def finiteIso (D : SourceVerdier.K P) :
    (HomotopyCategory.quotient _ _).obj (tensor X D) ≅
      (inclusion k).obj ((SourceEvaluation.finite X).obj D) := Iso.refl _

abbrev tensorMap {D E : SourceVerdier.K P}
    (f : ConcreteChainRepresentatives.representative P D ⟶
      ConcreteChainRepresentatives.representative P E) :=
  ((BalancedTensor.tensorFunctor k (B P) X.Evaluation).mapHomologicalComplex (.up ℤ)).map
    (((UnderlyingRepresentatives.forget P).mapHomologicalComplex (.up ℤ)).map f)

theorem map_comparison {D E : SourceVerdier.K P}
    (f : ConcreteChainRepresentatives.representative P D ⟶
      ConcreteChainRepresentatives.representative P E)
    (a : D ⟶ E)
    (ha : (HomotopyCategory.quotient _ _).map f = a.hom) :
    (HomotopyCategory.quotient _ _).map (tensorMap X f) ≫ (finiteIso X E).hom =
      (finiteIso X D).hom ≫ (inclusion k).map ((SourceEvaluation.finite X).map a) := by
  dsimp only [finiteIso,Iso.refl_hom]
  erw [Category.comp_id,Category.id_comp]
  change _ = ((BalancedTensor.tensorFunctor k (B P) X.Evaluation).mapHomotopyCategory (.up ℤ)).map
    (((UnderlyingRepresentatives.forget P).mapHomotopyCategory (.up ℤ)).map a.hom)
  erw [← ha,Functor.mapHomotopyCategory_map,Functor.mapHomotopyCategory_map]
end LittleFinitistic.Note198GenericOddTensorComparison

end

end OAI



namespace Note198.GenericOddNativeEvaluation
noncomputable section
open CategoryTheory CategoryTheory.Limits
open OAI.LittleFinitistic OAI.LittleFinitistic.SourceImageEvaluation
open OAI.LittleFinitistic.FiniteProjectiveHomotopy
open OAI.LittleFinitistic.QuadraticEncoding
attribute [local instance] HasDerivedCategory.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {E : SelectionEncoding.Encoding k R} {S : EndomorphismSelection.Data k R}
variable {s : ℤ} {hs : 3 ≤ s} {hodd : Odd s}
variable {Y : Type u} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]

abbrev H := EndomorphismSelection.vectorObject (k := k) (EndomorphismSelection.H S (ModuleCat.of R Y))
instance : FiniteDimensional k (H (S := S) (Y := Y)) :=
  Module.Finite.of_surjective (SelectingImageComparison.equiv S (Y := Y)).toLinearMap
    (SelectingImageComparison.equiv S (Y := Y)).surjective

def HK : K.{u,u} k := ⟨(vectorStalk (k := k)).obj (H (S := S) (Y := Y)), single_property _ 0⟩
def HDerived : FiniteVectorDerived.{u,u} (k := k) :=
  (derivedEmbedding k).toEssImage.obj (HK (S := S) (Y := Y))
def imageIsoK : imageK (k := k) (Y := Y) S.e ≅ HK (S := S) (Y := Y) :=
  (inclusion k).preimageIso ((vectorStalk (k := k)).mapIso
    (SelectingImageComparison.equiv S (Y := Y)).toModuleIso)
def imageIso : imageDerived (k := k) (Y := Y) S.e ≅ HDerived (S := S) (Y := Y) :=
  (derivedEmbedding k).toEssImage.mapIso (imageIsoK (S := S) (Y := Y))

abbrev target := HDerived (S := S) (Y := Y) ⊞ (HDerived (S := S) (Y := Y))⟦s⟧
def targetIso : Note198GenericOddDiagramEvaluation.target (S := S) (s := s) (Y := Y) ≅
    target (S := S) (s := s) (Y := Y) :=
  biprod.mapIso (imageIso (S := S) (Y := Y))
    ((shiftFunctor (FiniteVectorDerived.{u,u} (k := k)) s).mapIso
      (imageIso (S := S) (Y := Y)))

def V0Iso : (Note198GenericOddDiagramEvaluation.F (E := E) (Y := Y)).obj
    (GenericOddRectification.fixedData E S s hs hodd).V₀ ≅ target (S := S) (s := s) (Y := Y) :=
  Note198GenericOddDiagramEvaluation.V0Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd) ≪≫ targetIso
def D0Iso : (Note198GenericOddDiagramEvaluation.sourceEvaluation (E := E) (Y := Y)).obj
    (GenericOddRectification.fixedData E S s hs hodd).D₀ ≅ target (S := S) (s := s) (Y := Y) :=
  Note198GenericOddDiagramEvaluation.D0Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd) ≪≫ targetIso
def D1Iso : (Note198GenericOddDiagramEvaluation.sourceEvaluation (E := E) (Y := Y)).obj
    (GenericOddRectification.fixedData E S s hs hodd).D₁ ≅ target (S := S) (s := s) (Y := Y) :=
  Note198GenericOddDiagramEvaluation.D1Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd) ≪≫ targetIso
def D2Iso : (Note198GenericOddDiagramEvaluation.sourceEvaluation (E := E) (Y := Y)).obj
    (GenericOddRectification.fixedData E S s hs hodd).D₂ ≅ target (S := S) (s := s) (Y := Y) :=
  Note198GenericOddDiagramEvaluation.D2Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd) ≪≫ targetIso

/-- All three vertices of the fixed source diagram evaluate to the actual
selected module H(Y), in degrees zero and minus s. -/
theorem fixed_vertices :
    Nonempty ((Note198GenericOddDiagramEvaluation.sourceEvaluation (E := E) (Y := Y)).obj
      (GenericOddRectification.fixedData E S s hs hodd).D₀ ≅ target (S := S) (s := s) (Y := Y)) ∧
    Nonempty ((Note198GenericOddDiagramEvaluation.sourceEvaluation (E := E) (Y := Y)).obj
      (GenericOddRectification.fixedData E S s hs hodd).D₁ ≅ target (S := S) (s := s) (Y := Y)) ∧
    Nonempty ((Note198GenericOddDiagramEvaluation.sourceEvaluation (E := E) (Y := Y)).obj
      (GenericOddRectification.fixedData E S s hs hodd).D₂ ≅ target (S := S) (s := s) (Y := Y)) :=
  ⟨⟨Note198GenericOddDiagramEvaluation.D0Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd) ≪≫ targetIso⟩,
    ⟨Note198GenericOddDiagramEvaluation.D1Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd) ≪≫ targetIso⟩,
    ⟨Note198GenericOddDiagramEvaluation.D2Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd) ≪≫ targetIso⟩⟩

end
end Note198.GenericOddNativeEvaluation



namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace GenericOddNativeEvaluation
open OAI.LittleFinitistic
open QuadraticEncoding SourceImageEvaluation FiniteProjectiveHomotopy GenericOddRectification
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {E : SelectionEncoding.Encoding k R} {S : EndomorphismSelection.Data k R}
variable {s : ℤ} {hs : 3 ≤ s} {hodd : Odd s}
variable {Y : Type u} [AddCommGroup Y] [Module k Y]
  [Module R Y] [IsScalarTower k R Y]

abbrev imageEnd (r : R) := imageCornerEnd
  (action (k := k) (Y := Y) S.e).hom (action (k := k) (Y := Y) (S.α r)).hom
abbrev moduleIso := ((SelectingImageComparison.equiv S (Y := Y))).toModuleIso

def HAction (r : R) : End ((H (S := S) (Y := Y))) :=
  ((moduleIso (S := S) (Y := Y))).inv ≫ (imageEnd (S := S) (Y := Y)) r ≫ ((moduleIso (S := S) (Y := Y))).hom

/-- The conjugated map is the primary selectionStep module action, on every vector. -/
theorem HAction_apply (r : R) (x : (H (S := S) (Y := Y))) :
    ((HAction (S := S) (Y := Y)) r).hom x = (SelectingImageComparison.moduleAction S (Y := Y)) r x := by
  have h := SelectingImageComparison.equiv_action S (Y := Y) r
    (((SelectingImageComparison.equiv S (Y := Y))).symm x)
  dsimp only [HAction,moduleIso,LinearEquiv.toModuleIso] at *
  simp only [LinearEquiv.apply_symm_apply] at h
  exact h

lemma module_square (r : R) :
    (imageEnd (S := S) (Y := Y)) r ≫ ((moduleIso (S := S) (Y := Y))).hom =
      ((moduleIso (S := S) (Y := Y))).hom ≫ (HAction (S := S) (Y := Y)) r := by
  simp only [HAction,Iso.hom_inv_id_assoc]

variable [FiniteDimensional k Y]

def HKAction (r : R) : End ((HK (S := S) (Y := Y))) :=
  (inclusion k).preimage ((vectorStalk (k := k)).map ((HAction (S := S) (Y := Y)) r))
def HDerivedAction (r : R) : End ((HDerived (S := S) (Y := Y))) :=
  (derivedEmbedding k).toEssImage.map ((HKAction (S := S) (Y := Y)) r)

lemma imageIsoK_hom : (inclusion k).map ((imageIsoK (S := S) (Y := Y))).hom =
    (vectorStalk (k := k)).map ((moduleIso (S := S) (Y := Y))).hom := by
  simp only [imageIsoK,Functor.preimageIso,Functor.mapIso_hom]
  erw [Functor.map_preimage]

lemma image_square (r : R) :
    imageCorner (k := k) (Y := Y) S.e (S.α r) ≫ ((imageIso (S := S) (Y := Y))).hom =
      ((imageIso (S := S) (Y := Y))).hom ≫ (HDerivedAction (S := S) (Y := Y)) r := by
  apply (derivedTargetInclusion (k := k)).map_injective
  rw [Functor.map_comp,Functor.map_comp]
  dsimp only [imageCorner]
  erw [Functor.map_preimage]
  change DerivedCategory.Qh.map ((vectorStalk (k := k)).map ((imageEnd (S := S) (Y := Y)) r)) ≫
    DerivedCategory.Qh.map ((inclusion k).map ((imageIsoK (S := S) (Y := Y))).hom) =
    DerivedCategory.Qh.map ((inclusion k).map ((imageIsoK (S := S) (Y := Y))).hom) ≫
    DerivedCategory.Qh.map ((inclusion k).map ((HKAction (S := S) (Y := Y)) r))
  rw [(imageIsoK_hom (S := S))]
  dsimp only [HKAction]
  erw [Functor.map_preimage]
  erw [← Functor.map_comp,← Functor.map_comp,← Functor.map_comp,← Functor.map_comp,(module_square (S := S))]
  rfl

abbrev targetAction (r : R) : End ((target (S := S) (s := s) (Y := Y))) :=
  biprod.map ((HDerivedAction (S := S) (Y := Y)) r) (((HDerivedAction (S := S) (Y := Y)) r)⟦s⟧')

lemma target_square (r : R) :
    (Note198GenericOddDiagramEvaluation.targetAction (S := S) (s := s) (Y := Y)) r ≫ ((targetIso (S := S) (s := s) (Y := Y))).hom =
      ((targetIso (S := S) (s := s) (Y := Y))).hom ≫ (targetAction (S := S) (s := s) (Y := Y)) r := by
  have h := (image_square (S := S) (Y := Y)) r
  have hs := congrArg (shiftFunctor (FiniteVectorDerived.{u,u} (k := k)) s).map h
  simp only [Functor.map_comp] at hs
  dsimp only [Note198GenericOddDiagramEvaluation.targetAction,targetIso,targetAction,biprod.mapIso]
  apply biprod.hom_ext
  · simp only [Category.assoc,biprod.map_fst,biprod.map_fst_assoc,h]
  · simp only [Category.assoc,biprod.map_snd,biprod.map_snd_assoc,Functor.mapIso_hom,hs]

/-- The fixed V0 evaluates equivariantly to the primary (H (S := S))(Y) plus (H (S := S))(Y)[3]. -/
theorem V0_action (r : R) :
    ((Note198GenericOddDiagramEvaluation.F (E := E) (Y := Y))).map ((fixedData E S s hs hodd).ρ₀ r) ≫ ((V0Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd) (Y := Y))).hom =
      ((V0Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd) (Y := Y))).hom ≫ (targetAction (S := S) (s := s) (Y := Y)) r :=
  DiagramEvaluationSquares.compose _ _ _ (Note198GenericOddDiagramEvaluation.V0Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd))
    (Note198GenericOddDiagramEvaluation.V0Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) (targetIso (S := S) (s := s)) (targetIso (S := S) (s := s))
    ((Note198GenericOddDiagramEvaluation.V0_action (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) r) ((target_square (S := S) (s := s)) r)

theorem D_arrow01 (a : Fin (E.generators+1)) :
    ((Note198GenericOddDiagramEvaluation.sourceEvaluation (E := E) (Y := Y))).map ((fixedData E S s hs hodd).f a) ≫ ((D1Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd) (Y := Y))).hom =
      ((D0Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd) (Y := Y))).hom ≫ (targetAction (S := S) (s := s) (Y := Y))
        (RelationBasisAction.arrow (SelectionEncoding.generator E) a) :=
  DiagramEvaluationSquares.compose _ _ _ (Note198GenericOddDiagramEvaluation.D0Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd))
    (Note198GenericOddDiagramEvaluation.D1Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) (targetIso (S := S) (s := s)) (targetIso (S := S) (s := s))
    ((Note198GenericOddDiagramEvaluation.D_arrow01 (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) a) ((target_square (S := S) (s := s)) _)

theorem D_arrow12 (a : Fin (E.generators+1)) :
    ((Note198GenericOddDiagramEvaluation.sourceEvaluation (E := E) (Y := Y))).map ((fixedData E S s hs hodd).g a) ≫ ((D2Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd) (Y := Y))).hom =
      ((D1Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd) (Y := Y))).hom ≫ (targetAction (S := S) (s := s) (Y := Y))
        (RelationBasisAction.arrow (SelectionEncoding.generator E) a) :=
  DiagramEvaluationSquares.compose _ _ _ (Note198GenericOddDiagramEvaluation.D1Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd))
    (Note198GenericOddDiagramEvaluation.D2Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) (targetIso (S := S) (s := s)) (targetIso (S := S) (s := s))
    ((Note198GenericOddDiagramEvaluation.D_arrow12 (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) a) ((target_square (S := S) (s := s)) _)
end GenericOddNativeEvaluation

end

end Note198



namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace GenericOddTargetHomology
open OAI.LittleFinitistic
open QuadraticEncoding GenericOddNativeEvaluation FiniteProjectiveHomotopy
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {S : EndomorphismSelection.Data k R}
variable {s : ℤ} {hs : 3 ≤ s} {hodd : Odd s}
variable {Y : Type u} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]
abbrev C := ModuleCat.{u} k
abbrev I := derivedTargetInclusion.{u,u} (k := k)
abbrev cohomology (n : ℤ) := (I (k := k)) ⋙ DerivedCategory.homologyFunctor (C (k := k)) n
instance (n : ℤ) : ((cohomology (k := k)) n).Additive := by dsimp [cohomology]; infer_instance
instance (n : ℤ) : PreservesBinaryBiproducts ((cohomology (k := k)) n) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

def stalkIso : (I (k := k)).obj ((HDerived (S := S) (Y := Y))) ≅
    (DerivedCategory.singleFunctor (C (k := k)) 0).obj ((H (S := S) (Y := Y))) := Iso.refl _
def shiftedIso : (I (k := k)).obj (((HDerived (S := S) (Y := Y)))⟦s⟧) ≅
    (DerivedCategory.singleFunctor (C (k := k)) ((-s))).obj ((H (S := S) (Y := Y))) :=
  ((I (k := k)).commShiftIso s).app _ ≪≫
    (shiftFunctor _ s).mapIso ((stalkIso (S := S) (Y := Y))) ≪≫
      ((DerivedCategory.singleFunctors (C (k := k))).shiftIso s ((-s)) 0 (by omega)).app _

def stalkHomologyIso : ((cohomology (k := k)) 0).obj ((HDerived (S := S) (Y := Y))) ≅ (H (S := S) (Y := Y)) :=
  (DerivedCategory.homologyFunctor (C (k := k)) 0).mapIso (stalkIso (S := S)) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (C (k := k)) 0).app _
def shiftedHomologyIso : ((cohomology (k := k)) ((-s))).obj (((HDerived (S := S) (Y := Y)))⟦s⟧) ≅ (H (S := S) (Y := Y)) :=
  (DerivedCategory.homologyFunctor (C (k := k)) ((-s))).mapIso (shiftedIso (S := S) (s := s)) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (C (k := k)) ((-s))).app _

theorem single_zero (M : (C (k := k))) (i n : ℤ) (hn : n ≠ i) :
    IsZero ((DerivedCategory.homologyFunctor (C (k := k)) n).obj
      ((DerivedCategory.singleFunctor (C (k := k)) i).obj M)) := by
  rcases lt_or_gt_of_ne hn with h | h
  · exact DerivedCategory.isZero_of_isGE _ i n h
  · exact DerivedCategory.isZero_of_isLE _ i n h
theorem stalk_zero (n : ℤ) (hn : n ≠ 0) :
    IsZero (((cohomology (k := k)) n).obj ((HDerived (S := S) (Y := Y)))) :=
  ((DerivedCategory.homologyFunctor (C (k := k)) n).mapIso ((stalkIso (S := S) (Y := Y)))).isZero_iff.mpr
    ((single_zero (k := k)) _ _ _ hn)
theorem shifted_zero (n : ℤ) (hn : n ≠ (-s)) :
    IsZero (((cohomology (k := k)) n).obj (((HDerived (S := S) (Y := Y)))⟦s⟧)) :=
  ((DerivedCategory.homologyFunctor (C (k := k)) n).mapIso ((shiftedIso (S := S) (s := s) (Y := Y)))).isZero_iff.mpr
    ((single_zero (k := k)) _ _ _ hn)

def targetH0 : ((cohomology (k := k)) 0).obj ((target (S := S) (s := s) (Y := Y))) ≅ (H (S := S) (Y := Y)) :=
  ((cohomology (k := k)) 0).mapBiprod _ _ ≪≫
    (isoBiprodZero ((shifted_zero (S := S) (s := s) (Y := Y)) 0 (by omega))).symm ≪≫ (stalkHomologyIso (S := S))

def targetHms : ((cohomology (k := k)) ((-s))).obj ((target (S := S) (s := s) (Y := Y))) ≅ (H (S := S) (Y := Y)) :=
  ((cohomology (k := k)) ((-s))).mapBiprod _ _ ≪≫
    (isoZeroBiprod ((stalk_zero (S := S) (Y := Y)) ((-s)) (by omega))).symm ≪≫ (shiftedHomologyIso (S := S) (s := s))

theorem target_zero (n : ℤ) (h0 : n ≠ 0) (hm : n ≠ (-s)) :
    IsZero (((cohomology (k := k)) n).obj ((target (S := S) (s := s) (Y := Y)))) :=
  (((cohomology (k := k)) n).mapBiprod _ _).isZero_iff.mpr
    ((biprod_isZero_iff _ _).mpr ⟨(stalk_zero (S := S)) n h0,(shifted_zero (S := S) (s := s)) n hm⟩)

theorem stalkHomologyIso_hom : ((stalkHomologyIso (S := S) (Y := Y))).hom =
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (C (k := k)) 0).app ((H (S := S) (Y := Y)))).hom := by
  change (DerivedCategory.homologyFunctor (C (k := k)) 0).map
    (𝟙 ((DerivedCategory.singleFunctor (C (k := k)) 0).obj ((H (S := S) (Y := Y))))) ≫ _ = _
  rw [CategoryTheory.Functor.map_id,Category.id_comp]

theorem stalk_action (r : R) :
    ((cohomology (k := k)) 0).map ((HDerivedAction (S := S) (Y := Y)) r) ≫ ((stalkHomologyIso (S := S) (Y := Y))).hom =
      ((stalkHomologyIso (S := S) (Y := Y))).hom ≫ (HAction (S := S) (Y := Y)) r := by
  rw [(stalkHomologyIso_hom (S := S))]
  change (DerivedCategory.homologyFunctor (C (k := k)) 0).map
    (DerivedCategory.Qh.map ((inclusion k).map (HKAction (Y := Y) r))) ≫ _ = _
  dsimp only [HKAction]
  erw [Functor.map_preimage]
  change (DerivedCategory.homologyFunctor (C (k := k)) 0).map
    ((DerivedCategory.singleFunctor (C (k := k)) 0).map ((HAction (S := S) (Y := Y)) r)) ≫ _ = _
  exact (DerivedCategory.singleFunctorCompHomologyFunctorIso (C (k := k)) 0).hom.naturality
    ((HAction (S := S) (Y := Y)) r)

theorem shifted_action (r : R) :
    ((cohomology (k := k)) ((-s))).map (((HDerivedAction (S := S) (Y := Y)) r)⟦s⟧') ≫
      ((shiftedHomologyIso (S := S) (s := s) (Y := Y))).hom =
        ((shiftedHomologyIso (S := S) (s := s) (Y := Y))).hom ≫ (HAction (S := S) (Y := Y)) r := by
  have hst : (I (k := k)).map ((HDerivedAction (S := S) (Y := Y)) r) =
      (DerivedCategory.singleFunctor (C (k := k)) 0).map ((HAction (S := S) (Y := Y)) r) := by
    change DerivedCategory.Qh.map ((inclusion k).map (HKAction (Y := Y) r)) = _
    dsimp only [HKAction]
    erw [Functor.map_preimage]
    rfl
  have hshift : (I (k := k)).map (((HDerivedAction (S := S) (Y := Y)) r)⟦s⟧') ≫ ((shiftedIso (S := S) (s := s) (Y := Y))).hom =
      ((shiftedIso (S := S) (s := s) (Y := Y))).hom ≫
        (DerivedCategory.singleFunctor (C (k := k)) ((-s))).map ((HAction (S := S) (Y := Y)) r) := by
    have h1 := ((I (k := k)).commShiftIso s).hom.naturality ((HDerivedAction (S := S) (Y := Y)) r)
    have h2 := ((DerivedCategory.singleFunctors (C (k := k))).shiftIso s ((-s)) 0 (by omega)).hom.naturality
      ((HAction (S := S) (Y := Y)) r)
    dsimp only [Functor.comp_map] at h1 h2
    rw [hst] at h1
    have hh := (congrArg (fun f => f ≫
      (((DerivedCategory.singleFunctors (C (k := k))).shiftIso s ((-s)) 0 (by omega)).app
        ((H (S := S) (Y := Y)))).hom) h1).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun g => ((I (k := k)).commShiftIso s).hom.app ((HDerived (S := S) (Y := Y))) ≫ g) h2))
    dsimp only [shiftedIso, stalkIso, Iso.trans_hom, Functor.mapIso_hom, Iso.refl_hom]
    erw [CategoryTheory.Functor.mapIso_hom, Iso.refl_hom,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact (Category.assoc _ _ _).symm.trans (hh.trans (Category.assoc _ _ _).symm)

  have h := congrArg (DerivedCategory.homologyFunctor (C (k := k)) ((-s))).map hshift
  simp only [Functor.map_comp] at h
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso (C (k := k)) ((-s))).hom.naturality
    ((HAction (S := S) (Y := Y)) r)
  dsimp only [Functor.comp_map,Functor.id_map] at hn
  dsimp only [shiftedHomologyIso,Iso.trans_hom,Functor.mapIso_hom,cohomology,Functor.comp_map]
  rw [← Category.assoc,h,Category.assoc]
  exact (congrArg (fun g => (DerivedCategory.homologyFunctor (C (k := k)) ((-s))).map
    ((shiftedIso (S := S) (s := s) (Y := Y))).hom ≫ g) hn).trans (Category.assoc _ _ _).symm

theorem targetH0_hom : ((targetH0 (S := S) (s := s) (hs := hs) (Y := Y))).hom =
    ((cohomology (k := k)) 0).map biprod.fst ≫ ((stalkHomologyIso (S := S) (Y := Y))).hom := by
  simp [targetH0,isoBiprodZero]
  erw [biprod.lift_fst_assoc]
theorem targetHms_hom : ((targetHms (S := S) (s := s) (hs := hs) (Y := Y))).hom =
    ((cohomology (k := k)) ((-s))).map biprod.snd ≫ ((shiftedHomologyIso (S := S) (s := s) (Y := Y))).hom := by
  simp [targetHms,isoZeroBiprod]
  erw [biprod.lift_snd_assoc]

theorem targetH0_action (r : R) :
    ((cohomology (k := k)) 0).map ((targetAction (S := S) (s := s) (Y := Y)) r) ≫ ((targetH0 (S := S) (s := s) (hs := hs) (Y := Y))).hom =
      ((targetH0 (S := S) (s := s) (hs := hs) (Y := Y))).hom ≫ (HAction (S := S) (Y := Y)) r := by
  rw [(targetH0_hom (S := S) (s := s) (hs := hs)),← Category.assoc,← Functor.map_comp]
  simp only [targetAction,biprod.map_fst,Functor.map_comp,Category.assoc,(stalk_action (S := S))]
theorem targetHms_action (r : R) :
    ((cohomology (k := k)) ((-s))).map ((targetAction (S := S) (s := s) (Y := Y)) r) ≫ ((targetHms (S := S) (s := s) (hs := hs) (Y := Y))).hom =
      ((targetHms (S := S) (s := s) (hs := hs) (Y := Y))).hom ≫ (HAction (S := S) (Y := Y)) r := by
  rw [(targetHms_hom (S := S) (s := s) (hs := hs)),← Category.assoc,← Functor.map_comp]
  simp only [targetAction,biprod.map_snd,Functor.map_comp,Category.assoc,(shifted_action (S := S) (s := s))]
end GenericOddTargetHomology

end

end Note198



namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace GenericOddChainHomology
open OAI.LittleFinitistic
open QuadraticEncoding GenericOddRectification GenericOddNativeEvaluation Note198GenericOddTensorComparison
open GenericOddTargetHomology
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {E : SelectionEncoding.Encoding k R} {S : EndomorphismSelection.Data k R}
variable {s : ℤ} {hs : 3 ≤ s} {hodd : Odd s}
variable {Y : Type u} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]
abbrev representation := SourceActionEvaluation.representation (Y := Y) E
abbrev complex (D : SourceVerdier.K E.relations) := tensor ((representation (E := E) (Y := Y))) D
abbrev source := (Note198GenericOddDiagramEvaluation.sourceEvaluation (E := E) (Y := Y))

def derivedIso (D : SourceVerdier.K E.relations) :
    DerivedCategory.Q.obj ((complex (E := E) (Y := Y)) D) ≅ (I (k := k)).obj (((source (E := E) (Y := Y))).obj D) :=
  (DerivedCategory.quotientCompQhIso (C (k := k))).symm.app _ ≪≫
    DerivedCategory.Qh.mapIso (finiteIso ((representation (E := E) (Y := Y))) D)

def comparison (D : SourceVerdier.K E.relations) (n : ℤ) :
    ((complex (E := E) (Y := Y)) D).homology n ≅ ((cohomology (k := k)) n).obj (((source (E := E) (Y := Y))).obj D) :=
  (DerivedCategory.homologyFunctorFactors (C (k := k)) n).symm.app _ ≪≫
    (DerivedCategory.homologyFunctor (C (k := k)) n).mapIso ((derivedIso (E := E) (Y := Y)) D)

theorem derived_map {D D' : SourceVerdier.K E.relations}
    (f : ConcreteChainRepresentatives.representative E.relations D ⟶
      ConcreteChainRepresentatives.representative E.relations D') (a : D ⟶ D')
    (ha : (HomotopyCategory.quotient _ _).map f = a.hom) :
    DerivedCategory.Q.map (tensorMap ((representation (E := E) (Y := Y))) f) ≫
      ((derivedIso (E := E) (Y := Y)) D').hom =
        ((derivedIso (E := E) (Y := Y)) D).hom ≫ (I (k := k)).map (((source (E := E) (Y := Y))).map a) := by
  have h := congrArg DerivedCategory.Qh.map (map_comparison ((representation (E := E) (Y := Y))) f a ha)
  simp only [Functor.map_comp] at h
  have hn := (DerivedCategory.quotientCompQhIso (C (k := k))).inv.naturality
    (tensorMap ((representation (E := E) (Y := Y))) f)
  exact DiagramEvaluationSquares.compose _ _ _
    ((DerivedCategory.quotientCompQhIso (C (k := k))).symm.app ((complex (E := E) (Y := Y)) D))
    ((DerivedCategory.quotientCompQhIso (C (k := k))).symm.app ((complex (E := E) (Y := Y)) D'))
    (DerivedCategory.Qh.mapIso (finiteIso ((representation (E := E) (Y := Y))) D))
    (DerivedCategory.Qh.mapIso (finiteIso ((representation (E := E) (Y := Y))) D')) hn h

theorem comparison_map {D D' : SourceVerdier.K E.relations}
    (f : ConcreteChainRepresentatives.representative E.relations D ⟶
      ConcreteChainRepresentatives.representative E.relations D') (a : D ⟶ D')
    (ha : (HomotopyCategory.quotient _ _).map f = a.hom) (n : ℤ) :
    HomologicalComplex.homologyMap (tensorMap ((representation (E := E) (Y := Y))) f) n ≫
      ((comparison (E := E) (Y := Y)) D' n).hom =
        ((comparison (E := E) (Y := Y)) D n).hom ≫ ((cohomology (k := k)) n).map (((source (E := E) (Y := Y))).map a) := by
  have h := congrArg (DerivedCategory.homologyFunctor (C (k := k)) n).map ((derived_map (E := E) (Y := Y)) f a ha)
  simp only [Functor.map_comp] at h
  have hn := (DerivedCategory.homologyFunctorFactors (C (k := k)) n).inv.naturality
    (tensorMap ((representation (E := E) (Y := Y))) f)
  exact DiagramEvaluationSquares.compose _ _ _
    ((DerivedCategory.homologyFunctorFactors (C (k := k)) n).symm.app ((complex (E := E) (Y := Y)) D))
    ((DerivedCategory.homologyFunctorFactors (C (k := k)) n).symm.app ((complex (E := E) (Y := Y)) D'))
    ((DerivedCategory.homologyFunctor (C (k := k)) n).mapIso ((derivedIso (E := E) (Y := Y)) D))
    ((DerivedCategory.homologyFunctor (C (k := k)) n).mapIso ((derivedIso (E := E) (Y := Y)) D')) hn h

def modelIso (n : ℤ) (hn : n = 0 ∨ n = (-s)) :
    ((cohomology (k := k)) n).obj ((target (S := S) (s := s) (Y := Y))) ≅ (H (S := S) (Y := Y)) := by
  by_cases h : n = 0
  · subst n; exact (targetH0 (S := S) (s := s) (hs := hs))
  · have hm : n = (-s) := hn.resolve_left h
    subst n; exact (targetHms (S := S) (s := s) (hs := hs))

theorem model_action (n : ℤ) (hn : n = 0 ∨ n = (-s)) (r : R) :
    ((cohomology (k := k)) n).map ((targetAction (S := S) (s := s) (Y := Y)) r) ≫ ((modelIso (S := S) (s := s) (hs := hs) (Y := Y)) n hn).hom =
      ((modelIso (S := S) (s := s) (hs := hs) (Y := Y)) n hn).hom ≫ (HAction (S := S) (Y := Y)) r := by
  rcases hn with rfl | rfl
  · exact (targetH0_action (S := S) (s := s) (hs := hs) (Y := Y)) r
  · simpa [modelIso, show (-s : ℤ) ≠ 0 by omega] using
      (targetHms_action (S := S) (s := s) (hs := hs) (Y := Y)) r

/-- Actual homology of a selected chain tensor, with its chosen (target (S := S) (s := s)) identification. -/
def homologyIso (D : SourceVerdier.K E.relations)
    (e : ((source (E := E) (Y := Y))).obj D ≅ (target (S := S) (s := s) (Y := Y)))
    (n : ℤ) (hn : n = 0 ∨ n = (-s)) : ((complex (E := E) (Y := Y)) D).homology n ≅ (H (S := S) (Y := Y)) :=
  (comparison (E := E)) D n ≪≫ ((cohomology (k := k)) n).mapIso e ≪≫ (modelIso (S := S) (s := s) (hs := hs)) n hn

theorem homology_zero (D : SourceVerdier.K E.relations)
    (e : ((source (E := E) (Y := Y))).obj D ≅ (target (S := S) (s := s) (Y := Y)))
    (n : ℤ) (h0 : n ≠ 0) (hm : n ≠ (-s)) : IsZero (((complex (E := E) (Y := Y)) D).homology n) :=
  ((comparison (E := E)) D n ≪≫ ((cohomology (k := k)) n).mapIso e).isZero_iff.mpr ((target_zero (S := S) (s := s)) n h0 hm)

theorem homology_arrow {D D' : SourceVerdier.K E.relations}
    (f : ConcreteChainRepresentatives.representative E.relations D ⟶
      ConcreteChainRepresentatives.representative E.relations D') (a : D ⟶ D')
    (ha : (HomotopyCategory.quotient _ _).map f = a.hom)
    (eD : ((source (E := E) (Y := Y))).obj D ≅ (target (S := S) (s := s) (Y := Y)))
    (eE : ((source (E := E) (Y := Y))).obj D' ≅ (target (S := S) (s := s) (Y := Y))) (r : R)
    (hSquare : ((source (E := E) (Y := Y))).map a ≫ eE.hom = eD.hom ≫ (targetAction (S := S) (s := s) (Y := Y)) r)
    (n : ℤ) (hn : n = 0 ∨ n = (-s)) :
    HomologicalComplex.homologyMap (tensorMap ((representation (E := E) (Y := Y))) f) n ≫
      ((homologyIso (E := E) (S := S) (s := s) (hs := hs)) D' eE n hn).hom =
        ((homologyIso (E := E) (S := S) (s := s) (hs := hs)) D eD n hn).hom ≫ (HAction (S := S) (Y := Y)) r := by
  have h := congrArg ((cohomology (k := k)) n).map hSquare
  simp only [Functor.map_comp] at h
  exact DiagramEvaluationSquares.compose _ _ _
    ((comparison (E := E)) D n) ((comparison (E := E)) D' n)
    (((cohomology (k := k)) n).mapIso eD ≪≫ (modelIso (S := S) (s := s) (hs := hs)) n hn)
    (((cohomology (k := k)) n).mapIso eE ≪≫ (modelIso (S := S) (s := s) (hs := hs)) n hn)
    ((comparison_map (E := E)) f a ha n)
    (DiagramEvaluationSquares.compose _ _ _ (((cohomology (k := k)) n).mapIso eD)
      (((cohomology (k := k)) n).mapIso eE) ((modelIso (S := S) (s := s) (hs := hs)) n hn) ((modelIso (S := S) (s := s) (hs := hs)) n hn) h ((model_action (S := S) (s := s) (hs := hs)) n hn r))

/-- All three actual tensors have the primary (H (S := S))(Y) as homology in both selected degrees. -/
def D0Iso (n : ℤ) (hn : n = 0 ∨ n = (-s)) :
    ((complex (E := E) (Y := Y)) (fixedData E S s hs hodd).D₀).homology n ≅ (H (S := S) (Y := Y)) :=
  (homologyIso (E := E) (S := S) (s := s) (hs := hs)) _ (GenericOddNativeEvaluation.D0Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) n hn
def D1Iso (n : ℤ) (hn : n = 0 ∨ n = (-s)) :
    ((complex (E := E) (Y := Y)) (fixedData E S s hs hodd).D₁).homology n ≅ (H (S := S) (Y := Y)) :=
  (homologyIso (E := E) (S := S) (s := s) (hs := hs)) _ (GenericOddNativeEvaluation.D1Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) n hn
def D2Iso (n : ℤ) (hn : n = 0 ∨ n = (-s)) :
    ((complex (E := E) (Y := Y)) (fixedData E S s hs hodd).D₂).homology n ≅ (H (S := S) (Y := Y)) :=
  (homologyIso (E := E) (S := S) (s := s) (hs := hs)) _ (GenericOddNativeEvaluation.D2Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) n hn

theorem D0_zero (n : ℤ) (h0 : n ≠ 0) (hm : n ≠ (-s)) :
    IsZero (((complex (E := E) (Y := Y)) (fixedData E S s hs hodd).D₀).homology n) :=
  (homology_zero (E := E) (S := S) (s := s)) _ (GenericOddNativeEvaluation.D0Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) n h0 hm
theorem D1_zero (n : ℤ) (h0 : n ≠ 0) (hm : n ≠ (-s)) :
    IsZero (((complex (E := E) (Y := Y)) (fixedData E S s hs hodd).D₁).homology n) :=
  (homology_zero (E := E) (S := S) (s := s)) _ (GenericOddNativeEvaluation.D1Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) n h0 hm
theorem D2_zero (n : ℤ) (h0 : n ≠ 0) (hm : n ≠ (-s)) :
    IsZero (((complex (E := E) (Y := Y)) (fixedData E S s hs hodd).D₂).homology n) :=
  (homology_zero (E := E) (S := S) (s := s)) _ (GenericOddNativeEvaluation.D2Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) n h0 hm

/-- This applies to any chain representative of the same fixed first arrow. -/
theorem arrow01 (a : Fin (E.generators+1))
    (f : (ConcreteChainRepresentatives.representative E.relations (fixedData E S s hs hodd).D₀) ⟶ (ConcreteChainRepresentatives.representative E.relations (fixedData E S s hs hodd).D₁))
    (hf : (HomotopyCategory.quotient _ _).map f = ((fixedData E S s hs hodd).f a).hom)
    (n : ℤ) (hn : n = 0 ∨ n = (-s)) :
    HomologicalComplex.homologyMap (tensorMap ((representation (E := E) (Y := Y))) f) n ≫ ((D1Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) n hn).hom =
      ((D0Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) n hn).hom ≫ (HAction (S := S) (Y := Y))
        (RelationBasisAction.arrow (SelectionEncoding.generator E) a) :=
  (homology_arrow (E := E) (S := S) (s := s) (hs := hs)) f ((fixedData E S s hs hodd).f a) hf (GenericOddNativeEvaluation.D0Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) (GenericOddNativeEvaluation.D1Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) _
    ((GenericOddNativeEvaluation.D_arrow01 (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) a) n hn

theorem arrow12 (a : Fin (E.generators+1))
    (g : (ConcreteChainRepresentatives.representative E.relations (fixedData E S s hs hodd).D₁) ⟶ (ConcreteChainRepresentatives.representative E.relations (fixedData E S s hs hodd).D₂))
    (hg : (HomotopyCategory.quotient _ _).map g = ((fixedData E S s hs hodd).g a).hom)
    (n : ℤ) (hn : n = 0 ∨ n = (-s)) :
    HomologicalComplex.homologyMap (tensorMap ((representation (E := E) (Y := Y))) g) n ≫ ((D2Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) n hn).hom =
      ((D1Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) n hn).hom ≫ (HAction (S := S) (Y := Y))
        (RelationBasisAction.arrow (SelectionEncoding.generator E) a) :=
  (homology_arrow (E := E) (S := S) (s := s) (hs := hs)) g ((fixedData E S s hs hodd).g a) hg (GenericOddNativeEvaluation.D1Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) (GenericOddNativeEvaluation.D2Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) _
    ((GenericOddNativeEvaluation.D_arrow12 (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) a) n hn

theorem fixed_arrow01 (a : Fin (E.generators+1)) (n : ℤ) (hn : n = 0 ∨ n = (-s)) :
    HomologicalComplex.homologyMap
      (tensorMap ((representation (E := E) (Y := Y))) ((GenericOddRectification.fixedChain E S s hs hodd).f a)) n ≫ ((D1Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) n hn).hom =
      ((D0Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) n hn).hom ≫ (HAction (S := S) (Y := Y))
        (RelationBasisAction.arrow (SelectionEncoding.generator E) a) :=
  (arrow01 (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) a _ ((GenericOddRectification.fixedChain E S s hs hodd).f_quotient a) n hn
theorem fixed_arrow12 (a : Fin (E.generators+1)) (n : ℤ) (hn : n = 0 ∨ n = (-s)) :
    HomologicalComplex.homologyMap
      (tensorMap ((representation (E := E) (Y := Y))) ((GenericOddRectification.fixedChain E S s hs hodd).g a)) n ≫ ((D2Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) n hn).hom =
      ((D1Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) n hn).hom ≫ (HAction (S := S) (Y := Y))
        (RelationBasisAction.arrow (SelectionEncoding.generator E) a) :=
  (arrow12 (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) a _ ((GenericOddRectification.fixedChain E S s hs hodd).g_quotient a) n hn
end GenericOddChainHomology

end

end Note198



namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace GenericOddTensor
open OAI.LittleFinitistic
open GenericOddRectification QuadraticEncoding
universe u
variable {k R₀ : Type u} [Field k] [Ring R₀] [Algebra k R₀]
variable {enc : SelectionEncoding.Encoding k R₀} {S : EndomorphismSelection.Data k R₀}
variable {s : ℤ} {hs : 3 ≤ s} {hodd : Odd s}
variable (N : Type u) [AddCommGroup N] [Module k N] [Module (B enc.relations) N]

/-- Evaluate the one fixed selecting (GenericOddRectification.bimodule enc S s hs hodd), retaining its full left action. -/
abbrev complex := FullTensorRectification.tensor enc.relations (GenericOddRectification.D₀ enc S s hs hodd) (GenericOddRectification.D₁ enc S s hs hodd) (GenericOddRectification.D₂ enc S s hs hodd) (GenericOddRectification.f enc S s hs hodd) (GenericOddRectification.g enc S s hs hodd) (GenericOddRectification.relations enc S s hs hodd) N
abbrev source (v : Fin 3) := FullTensorRectification.source enc.relations (GenericOddRectification.D₀ enc S s hs hodd) (GenericOddRectification.D₁ enc S s hs hodd) (GenericOddRectification.D₂ enc S s hs hodd) N v
abbrev comparison (v : Fin 3) (n : ℤ) :=
  TensorCohomologyDiagram.comparison enc.relations (GenericOddRectification.D₀ enc S s hs hodd) (GenericOddRectification.D₁ enc S s hs hodd) (GenericOddRectification.D₂ enc S s hs hodd) (GenericOddRectification.f enc S s hs hodd) (GenericOddRectification.g enc S s hs hodd) (GenericOddRectification.relations enc S s hs hodd) N v n

/-- Every cohomology (comparison (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) is invertible for the fixed selected representatives. -/
instance comparison_isIso (v : Fin 3) (n : ℤ) : IsIso ((comparison (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N v n) := by
  obtain ⟨l₀,h₀,b₀⟩ := UnderlyingRepresentatives.bounded enc.relations (fixedData enc S s hs hodd).D₀
  obtain ⟨l₁,h₁,b₁⟩ := UnderlyingRepresentatives.bounded enc.relations (fixedData enc S s hs hodd).D₁
  obtain ⟨l₂,h₂,b₂⟩ := UnderlyingRepresentatives.bounded enc.relations (fixedData enc S s hs hodd).D₂
  let lo := min l₀ (min l₁ l₂)
  let hi := max h₀ (max h₁ h₂)
  refine TensorCohomologyDiagram.comparison_isIso enc.relations (GenericOddRectification.D₀ enc S s hs hodd) (GenericOddRectification.D₁ enc S s hs hodd) (GenericOddRectification.D₂ enc S s hs hodd) (GenericOddRectification.f enc S s hs hodd) (GenericOddRectification.g enc S s hs hodd) (GenericOddRectification.relations enc S s hs hodd) N v n lo hi
    (fun n hn => b₀ n ?_) (fun n hn => b₁ n ?_) (fun n hn => b₂ n ?_)
    (UnderlyingRepresentatives.projective enc.relations (fixedData enc S s hs hodd).D₀)
    (UnderlyingRepresentatives.projective enc.relations (fixedData enc S s hs hodd).D₁)
    (UnderlyingRepresentatives.projective enc.relations (fixedData enc S s hs hodd).D₂)
  all_goals dsimp [lo,hi] at hn; omega

def comparisonIso (v : Fin 3) (n : ℤ) := asIso ((comparison (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N v n)

/-- The actual tensor (complex (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) has (bounded (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) support. -/
theorem bounded : ∃ lo hi : ℤ, ∀ n, n < lo ∨ hi < n → IsZero (((complex (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N).X n) := by
  obtain ⟨lo,hi,h⟩ := (GenericOddRectification.verified enc S s hs hodd)
  exact ⟨lo-2,hi,FullTensorProperties.bounded k (B enc.relations) N (GenericOddRectification.bimodule enc S s hs hodd) (lo-2) hi h.bounded⟩

/-- Every actual evaluated term is (finite (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd))-dimensional. -/
theorem finite [FiniteDimensional k N] (n : ℤ) :
    FiniteDimensional k ((ModuleCat.restrictScalars (algebraMap k (B enc.relations))).obj (((complex (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N).X n)) := by
  obtain ⟨lo,hi,h⟩ := (GenericOddRectification.verified enc S s hs hodd)
  letI : FiniteDimensional k ((OAI.ExternalTensor.Section4.forgetK k (B enc.relations)).obj ((GenericOddRectification.bimodule enc S s hs hodd).X n)) := h.finite n
  exact FullTensorProperties.finite k (B enc.relations) N ((GenericOddRectification.bimodule enc S s hs hodd).X n)
end GenericOddTensor

end

end Note198



namespace Note198
noncomputable section
open CategoryTheory HomologicalComplex
namespace GenericOddCohomologyAssembly
open OAI.LittleFinitistic
open GenericOddRectification QuadraticEncoding
section General
variable {C : Type*} [Category C]
variable {X0 X1 M0 M1 N0 N1 : C}
lemma transfer_square (f : X0 ⟶ X1) (m : M0 ⟶ M1) (n : N0 ⟶ N1)
    (c0 : X0 ≅ M0) (c1 : X1 ≅ M1) (e0 : X0 ≅ N0) (e1 : X1 ≅ N1)
    (hc : f ≫ c1.hom = c0.hom ≫ m) (he : f ≫ e1.hom = e0.hom ≫ n) :
    m ≫ (c1.symm ≪≫ e1).hom = (c0.symm ≪≫ e0).hom ≫ n := by
  apply (cancel_epi c0.hom).1
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  calc
    c0.hom ≫ m ≫ c1.inv ≫ e1.hom = (c0.hom ≫ m) ≫ c1.inv ≫ e1.hom := by simp only [Category.assoc]
    _ = (f ≫ c1.hom) ≫ c1.inv ≫ e1.hom := by rw [← hc]
    _ = f ≫ e1.hom := by simp
    _ = e0.hom ≫ n := he
    _ = c0.hom ≫ (c0.inv ≫ e0.hom) ≫ n := by simp
end General

universe u
variable {k R₀ : Type u} [Field k] [Ring R₀] [Algebra k R₀]
variable {enc : SelectionEncoding.Encoding k R₀} {S : EndomorphismSelection.Data k R₀}
variable {s : ℤ} {hs : 3 ≤ s} {hodd : Odd s}
variable (N : Type u) [AddCommGroup N] [Module k N] [Module (B enc.relations) N]
variable (n : ℤ) (R : ModuleCat (B enc.relations))
variable (E : ∀ v : Fin 3, ((GenericOddTensor.source (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N v).homology n ≅
  (LeftVertexHomology.vertex k (B enc.relations) (ThreeVertexAlgebra.vertex (composition enc.relations) v)).obj R)

/-- Convert an identified evaluated-representative cohomology diagram into the
full cohomology B-module of the one fixed selecting tensor. Only the reference
diagram identification is an input; the tensor vertex comparisons are proved. -/
def iso
    (h01 : ∀ a,
      homologyMap (((BalancedTensor.tensorFunctor k (B enc.relations) N).mapHomologicalComplex (.up ℤ)).map ((GenericOddRectification.f enc S s hs hodd) a)) n ≫
        (E 1).hom = (E 0).hom ≫
        (LeftVertexHomology.arrow k (B enc.relations) (ThreeVertexAlgebra.vertex (composition enc.relations) 0)
          (ThreeVertexAlgebra.vertex (composition enc.relations) 1) (arrow01 enc.relations a)
          (CanonicalArrowCompatibility.arrow01_target enc.relations a)).app R)
    (h12 : ∀ b,
      homologyMap (((BalancedTensor.tensorFunctor k (B enc.relations) N).mapHomologicalComplex (.up ℤ)).map ((GenericOddRectification.g enc S s hs hodd) b)) n ≫
        (E 2).hom = (E 1).hom ≫
        (LeftVertexHomology.arrow k (B enc.relations) (ThreeVertexAlgebra.vertex (composition enc.relations) 1)
          (ThreeVertexAlgebra.vertex (composition enc.relations) 2) (arrow12 enc.relations b)
          (CanonicalArrowCompatibility.arrow12_target enc.relations b)).app R) :
    ((GenericOddTensor.complex (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N).homology n ≅ R :=
  VertexCategoricalAssembly.iso enc.relations _ R
    (fun v => ((GenericOddTensor.comparisonIso (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N v n).symm ≪≫ E v)
    (fun a => transfer_square _ _ _ ((GenericOddTensor.comparisonIso (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N 0 n)
      ((GenericOddTensor.comparisonIso (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N 1 n) (E 0) (E 1)
      (TensorCohomologyDiagram.arrow01_square enc.relations (GenericOddRectification.D₀ enc S s hs hodd) (GenericOddRectification.D₁ enc S s hs hodd) (GenericOddRectification.D₂ enc S s hs hodd) (GenericOddRectification.f enc S s hs hodd) (GenericOddRectification.g enc S s hs hodd) (GenericOddRectification.relations enc S s hs hodd) N a n) (h01 a))
    (fun b => transfer_square _ _ _ ((GenericOddTensor.comparisonIso (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N 1 n)
      ((GenericOddTensor.comparisonIso (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N 2 n) (E 1) (E 2)
      (TensorCohomologyDiagram.arrow12_square enc.relations (GenericOddRectification.D₀ enc S s hs hodd) (GenericOddRectification.D₁ enc S s hs hodd) (GenericOddRectification.D₂ enc S s hs hodd) (GenericOddRectification.f enc S s hs hodd) (GenericOddRectification.g enc S s hs hodd) (GenericOddRectification.relations enc S s hs hodd) N b n) (h12 b))
end GenericOddCohomologyAssembly

end

end Note198



namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace GenericOddCohomologyVanishing
open OAI.LittleFinitistic
open QuadraticEncoding
section General
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- The three actual vertex functors jointly detect a zero module. -/
theorem module_isZero (M : ModuleCat.{u} (B P))
    (h : ∀ i : Fin 3, IsZero
      ((LeftVertexHomology.vertex k (B P) (ThreeVertexAlgebra.vertex (composition P) i)).obj M)) :
    IsZero M := by
  let M' := (ModuleCat.restrictScalars (algebraMap k (B P))).obj M
  have (i : Fin 3) : Subsingleton
      (VertexDecomposition.Space (EncodingModuleAssembly.system P) M' i) := by
    let := ModuleCat.subsingleton_of_isZero (h i)
    exact (LeftVertexHomology.spaceEquiv k (B P) (ThreeVertexAlgebra.vertex (composition P) i) M).symm.injective.subsingleton
  have : Subsingleton M' := (VertexDecomposition.equiv (EncodingModuleAssembly.system P) M').injective.subsingleton
  have : Subsingleton M := inferInstanceAs (Subsingleton M')
  exact ModuleCat.isZero_of_subsingleton M
end General

open GenericOddRectification
variable {k R₀ : Type u} [Field k] [Ring R₀] [Algebra k R₀]
variable {enc : SelectionEncoding.Encoding k R₀} {S : EndomorphismSelection.Data k R₀}
variable {s : ℤ} {hs : 3 ≤ s} {hodd : Odd s}
variable (N : Type u) [AddCommGroup N] [Module k N] [Module (B enc.relations) N]

/-- Vanishing on all three evaluated representatives gives actual cohomology
vanishing of the fixed selecting tensor as a B-module. -/
theorem cohomology_isZero (n : ℤ)
    (h : ∀ v : Fin 3, IsZero (((GenericOddTensor.source (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N v).homology n)) :
    IsZero (((GenericOddTensor.complex (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N).homology n) := by
  apply module_isZero enc.relations
  intro v
  exact ((GenericOddTensor.comparisonIso (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N v n).isZero_iff.mp (h v)
end GenericOddCohomologyVanishing

end

end Note198



namespace Note198
noncomputable section
open CategoryTheory HomologicalComplex
namespace GenericOddReferenceCohomology
open OAI.LittleFinitistic
open GenericOddRectification QuadraticEncoding

lemma transfer_to_vertices {C : Type*} [Category C]
    {A₀ A₁ B₀ B₁ Y₀ Y₁ : C} (f : A₀ ⟶ A₁) (g : B₀ ⟶ B₁) (h : Y₀ ⟶ Y₁)
    (e₀ : A₀ ≅ Y₀) (e₁ : A₁ ≅ Y₁) (v₀ : B₀ ≅ Y₀) (v₁ : B₁ ≅ Y₁)
    (hf : f ≫ e₁.hom = e₀.hom ≫ h) (hg : g ≫ v₁.hom = v₀.hom ≫ h) :
    f ≫ (e₁ ≪≫ v₁.symm).hom = (e₀ ≪≫ v₀.symm).hom ≫ g := by
  apply (cancel_mono v₁.hom).1
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [hg, Iso.inv_hom_id_assoc]
  exact hf

universe u
variable {k R₀ : Type u} [Field k] [Ring R₀] [Algebra k R₀]
variable {enc : SelectionEncoding.Encoding k R₀} {S : EndomorphismSelection.Data k R₀}
variable {s : ℤ} {hs : 3 ≤ s} {hodd : Odd s}
variable (N : Type u) [AddCommGroup N] [Module k N] [Module (B enc.relations) N]
variable {Y : Type u} [AddCommGroup Y] [Module k Y] (X : Representation enc.relations Y)
variable (n : ℤ) (E : ∀ v : Fin 3,
  ((GenericOddTensor.source (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N v).homology n ≅ ModuleCat.of k Y)

/-- Identify the full tensor cohomology with the actual evaluation module from
three coordinate models and their generator actions. -/
def iso
    (h01 : ∀ a,
      homologyMap (((BalancedTensor.tensorFunctor k (B enc.relations) N).mapHomologicalComplex (.up ℤ)).map ((GenericOddRectification.f enc S s hs hodd) a)) n ≫
        (E 1).hom = (E 0).hom ≫ EvaluationVertexDiagram.action X a)
    (h12 : ∀ b,
      homologyMap (((BalancedTensor.tensorFunctor k (B enc.relations) N).mapHomologicalComplex (.up ℤ)).map ((GenericOddRectification.g enc S s hs hodd) b)) n ≫
        (E 2).hom = (E 1).hom ≫ EvaluationVertexDiagram.action X b) :
    ((GenericOddTensor.complex (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N).homology n ≅ EvaluationVertexDiagram.module X := by
  apply (GenericOddCohomologyAssembly.iso (enc := enc) (S := S)) N n (EvaluationVertexDiagram.module X)
    (fun v => E v ≪≫ (EvaluationVertexDiagram.vertexIso X v).symm)
  · intro a
    exact transfer_to_vertices _ _ _ (E 0) (E 1)
      (EvaluationVertexDiagram.vertexIso X 0) (EvaluationVertexDiagram.vertexIso X 1)
      (h01 a) (EvaluationVertexDiagram.arrow01_square X a (CanonicalArrowCompatibility.arrow01_target enc.relations a))
  · intro b
    exact transfer_to_vertices _ _ _ (E 1) (E 2)
      (EvaluationVertexDiagram.vertexIso X 1) (EvaluationVertexDiagram.vertexIso X 2)
      (h12 b) (EvaluationVertexDiagram.arrow12_square X b (CanonicalArrowCompatibility.arrow12_target enc.relations b))
end GenericOddReferenceCohomology

end

end Note198



namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace GenericOddTensorSplitting
open OAI.LittleFinitistic
open QuadraticEncoding
universe u
variable {k R₀ : Type u} [Field k] [Ring R₀] [Algebra k R₀]
variable {enc : SelectionEncoding.Encoding k R₀} {S : EndomorphismSelection.Data k R₀}
variable {s : ℤ} {hs : 3 ≤ s} {hodd : Odd s}
variable (N : Type u) [AddCommGroup N] [Module k N] [Module (B enc.relations) N]

/-- The actual derived (object (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) represented by the full B-valued fixed tensor complex. -/
abbrev object : DerivedCategory (ModuleCat (B enc.relations)) := DerivedCategory.Q.obj ((GenericOddTensor.complex (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N)

def homologyIso (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat (B enc.relations)) n).obj ((object (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N) ≅
      ((GenericOddTensor.complex (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N).homology n :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat (B enc.relations)) n).app ((GenericOddTensor.complex (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N)

/-- Support of the evaluated representative diagram implies actual derived
cohomological support of the full tensor (object (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)). -/
theorem twoDegrees
    (h : ∀ n : ℤ, n ≠ 0 → n ≠ (-s) → ∀ v : Fin 3,
      IsZero (((GenericOddTensor.source (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N v).homology n)) :
    GenericTwoDegrees.TwoDegrees enc.relations s.toNat ((object (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N) := by
  intro n hn0 hn3
  have hsCast : (s.toNat : ℤ) = s := Int.toNat_of_nonneg (by omega)
  rw [hsCast] at hn3
  exact ((homologyIso (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N n).isZero_iff.mpr
    ((GenericOddCohomologyVanishing.cohomology_isZero (enc := enc) (S := S)) N n (h n hn0 hn3))

/-- Apply the proved B-linear truncation splitting to the actual fixed tensor,
using full module cohomology models and source-diagram support. -/
def split (R : ModuleCat (B enc.relations))
    (h0 : ((GenericOddTensor.complex (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N).homology 0 ≅ R)
    (h3 : ((GenericOddTensor.complex (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N).homology ((-s)) ≅ R)
    (hz : ∀ n : ℤ, n ≠ 0 → n ≠ (-s) → ∀ v : Fin 3,
      IsZero (((GenericOddTensor.source (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N v).homology n)) :
    (object (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N ≅ (DerivedCategory.singleFunctor (ModuleCat (B enc.relations)) 0).obj R ⊞
      ((DerivedCategory.singleFunctor (ModuleCat (B enc.relations)) 0).obj R)⟦s⟧ :=
by
  have hsNat : 3 ≤ s.toNat := by omega
  have hsCast : (s.toNat : ℤ) = s := Int.toNat_of_nonneg (by omega)
  have h := GenericTwoDegrees.splitIsoWithModels enc.relations s.toNat hsNat
    ((object (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N)
    ((twoDegrees (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N hz) R R
    ((homologyIso (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N 0 ≪≫ h0)
    (by simpa only [hsCast] using
      ((homologyIso (enc := enc) (S := S) (s := s) (hs := hs) (hodd := hodd)) N (-s) ≪≫ h3))
  simpa only [hsCast] using h
end GenericOddTensorSplitting

end

end Note198



namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace GenericOddRealization
open OAI.LittleFinitistic
open QuadraticEncoding GenericOddNativeEvaluation
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {E : SelectionEncoding.Encoding k R} {S : EndomorphismSelection.Data k R}
variable {s : ℤ} {hs : 3 ≤ s} {hodd : Odd s}
variable {Y : Type u} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]

local instance selectedModule : Module R ((H (S := S) (Y := Y))) :=
  inferInstanceAs (Module R (EndomorphismSelection.H S (ModuleCat.of R Y)))
local instance selectedTower : IsScalarTower k R ((H (S := S) (Y := Y))) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

abbrev input := ((GenericOddChainHomology.representation (E := E) (Y := Y))).Evaluation
abbrev selectedRepresentation := SourceActionEvaluation.representation (Y := (H (S := S) (Y := Y))) E
abbrev reference := EvaluationVertexDiagram.module ((selectedRepresentation (E := E) (S := S) (Y := Y)))

omit [FiniteDimensional k Y] in
theorem selected_action (a : Fin (E.generators+1)) :
    EvaluationVertexDiagram.action (Y := (H (S := S) (Y := Y))) ((selectedRepresentation (E := E) (S := S) (Y := Y))) a =
      (HAction (S := S) (Y := Y)) (RelationBasisAction.arrow (SelectionEncoding.generator E) a) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [(HAction_apply (S := S))]
  refine Fin.cases ?_ (fun j => ?_) a
  · change x = (1 : R) • x
    rw [one_smul]
  · rfl

def coordinates (n : ℤ) (hn : n = 0 ∨ n = (-s)) :
    ∀ v : Fin 3, ((GenericOddTensor.source (enc := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) ((input (E := E) (Y := Y))) v).homology n ≅ (H (S := S) (Y := Y)) :=
  Fin.cases ((GenericOddChainHomology.D0Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) n hn)
    (Fin.cases ((GenericOddChainHomology.D1Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) n hn)
      (fun _ => (GenericOddChainHomology.D2Iso (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) n hn))

theorem coordinates01 (a : Fin (E.generators+1)) (n : ℤ) (hn : n = 0 ∨ n = (-s)) :
    homologyMap (((BalancedTensor.tensorFunctor k (B E.relations) ((input (E := E) (Y := Y)))).mapHomologicalComplex (.up ℤ)).map
      ((GenericOddRectification.f E S s hs hodd) a)) n ≫ ((coordinates (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd) (Y := Y)) n hn 1).hom =
      ((coordinates (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd) (Y := Y)) n hn 0).hom ≫ EvaluationVertexDiagram.action (Y := (H (S := S) (Y := Y))) ((selectedRepresentation (E := E) (S := S) (Y := Y))) a := by
  erw [(selected_action (E := E) (S := S) (Y := Y))]
  exact (GenericOddChainHomology.fixed_arrow01 (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) a n hn

theorem coordinates12 (a : Fin (E.generators+1)) (n : ℤ) (hn : n = 0 ∨ n = (-s)) :
    homologyMap (((BalancedTensor.tensorFunctor k (B E.relations) ((input (E := E) (Y := Y)))).mapHomologicalComplex (.up ℤ)).map
      ((GenericOddRectification.g E S s hs hodd) a)) n ≫ ((coordinates (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd) (Y := Y)) n hn 2).hom =
      ((coordinates (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd) (Y := Y)) n hn 1).hom ≫ EvaluationVertexDiagram.action (Y := (H (S := S) (Y := Y))) ((selectedRepresentation (E := E) (S := S) (Y := Y))) a := by
  erw [(selected_action (E := E) (S := S) (Y := Y))]
  exact (GenericOddChainHomology.fixed_arrow12 (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) a n hn

/-- The entire (cohomology (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) B-module is the manuscript's M((H (S := S))(Y)), in both degrees. -/
def cohomology (n : ℤ) (hn : n = 0 ∨ n = (-s)) :
    ((GenericOddTensor.complex (enc := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) ((input (E := E) (Y := Y)))).homology n ≅ (reference (E := E) (S := S) (Y := Y)) :=
  (GenericOddReferenceCohomology.iso (enc := E) (S := S)) _ ((selectedRepresentation (E := E) (S := S) (Y := Y))) n ((coordinates (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd) (Y := Y)) n hn)
    (fun a => (coordinates01 (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) a n hn) (fun a => (coordinates12 (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) a n hn)

theorem source_zero (n : ℤ) (hn0 : n ≠ 0) (hn3 : n ≠ (-s)) (v : Fin 3) :
    IsZero (((GenericOddTensor.source (enc := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) ((input (E := E) (Y := Y))) v).homology n) := by
  fin_cases v
  · exact (GenericOddChainHomology.D0_zero (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) n hn0 hn3
  · exact (GenericOddChainHomology.D1_zero (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) n hn0 hn3
  · exact (GenericOddChainHomology.D2_zero (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) n hn0 hn3

/-- The one fixed selecting bimodule realizes (H (S := S)) on every finite-dimensional Y.
This is an isomorphism in the full B-module derived category. -/
def realization :
    (GenericOddTensorSplitting.object (enc := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) ((input (E := E) (Y := Y))) ≅
      (DerivedCategory.singleFunctor (ModuleCat (B E.relations)) 0).obj ((reference (E := E) (S := S) (Y := Y))) ⊞
        ((DerivedCategory.singleFunctor (ModuleCat (B E.relations)) 0).obj ((reference (E := E) (S := S) (Y := Y))))⟦s⟧ :=
  (GenericOddTensorSplitting.split (enc := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) _ _ ((cohomology (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) 0 (Or.inl rfl))
    ((cohomology (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd)) ((-s)) (Or.inr rfl)) (source_zero (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd))
theorem realizes_selection : Nonempty (
    GenericOddTensorSplitting.object (enc := E) (S := S) (s := s) (hs := hs) (hodd := hodd) (input (E := E) (Y := Y)) ≅
      (DerivedCategory.singleFunctor (ModuleCat (B E.relations)) 0).obj
        (reference (E := E) (S := S) (Y := Y)) ⊞
      ((DerivedCategory.singleFunctor (ModuleCat (B E.relations)) 0).obj
        (reference (E := E) (S := S) (Y := Y)))⟦s⟧) :=
  ⟨realization (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd) (Y := Y)⟩

end GenericOddRealization

end

end Note198

namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
attribute [local instance] HasDerivedCategory.standard
universe u

/-- For each odd shift, choose the actual bounded finite enveloping-projective
complex before every finite evaluation module. Its actual balanced tensor realizes
M(H(Y)) in degrees zero and minus s, as a full B-module derived isomorphism. -/
theorem fixed_selecting_complex_all_odd
    {k R : Type u} [Field k] [Ring R] [Algebra k R]
    (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
    (s : ℤ) (hs : 3 ≤ s) (hodd : Odd s) :
    ∃ P : ExternalTensor.Section4.BiComplex k (QuadraticEncoding.B E.relations),
      (∃ lo hi : ℤ, ∀ n, n < lo ∨ hi < n → IsZero (P.X n)) ∧
      (∀ n, Projective (P.X n)) ∧
      (∀ n, FiniteDimensional k ((ExternalTensor.Section4.forgetK k
        (QuadraticEncoding.B E.relations)).obj (P.X n))) ∧
      ∀ (Y : Type u) [AddCommGroup Y] [Module k Y] [Module R Y]
        [IsScalarTower k R Y] [FiniteDimensional k Y],
        Nonempty (DerivedCategory.Q.obj
          (((BimoduleBalancedTensor.functor k (QuadraticEncoding.B E.relations)
            (GenericOddRealization.input (E := E) (Y := Y))).mapHomologicalComplex (.up ℤ)).obj P) ≅
          (DerivedCategory.singleFunctor (ModuleCat (QuadraticEncoding.B E.relations)) 0).obj
            (GenericOddRealization.reference (E := E) (S := S) (Y := Y)) ⊞
          ((DerivedCategory.singleFunctor (ModuleCat (QuadraticEncoding.B E.relations)) 0).obj
            (GenericOddRealization.reference (E := E) (S := S) (Y := Y)))⟦s⟧) := by
  obtain ⟨lo, hi, hv⟩ := GenericOddRectification.verified E S s hs hodd
  refine ⟨GenericOddRectification.bimodule E S s hs hodd,
    ⟨lo - 2, hi, hv.bounded⟩,
    GenericOddRectification.bimodule_enveloping_projective E S s hs hodd,
    hv.finite, ?_⟩
  intro Y _ _ _ _ _
  exact GenericOddRealization.realizes_selection
    (E := E) (S := S) (s := s) (hs := hs) (hodd := hodd) (Y := Y)

end
end Note198
