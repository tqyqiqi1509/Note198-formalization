import Note198.SelectingReferenceCohomology
import Note198.SelectingTensorSplitting
import Note198.SelectingChainHomology
import Note198.SelectingBimoduleProperties

namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace SelectingRealization
open OAI.LittleFinitistic
open QuadraticEncoding SelectingNativeEvaluation
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {E : SelectionEncoding.Encoding k R} {S : EndomorphismSelection.Data k R}
variable {Y : Type u} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]

local instance selectedModule : Module R (H (S := S) (Y := Y)) :=
  inferInstanceAs (Module R (EndomorphismSelection.H S (ModuleCat.of R Y)))
local instance selectedTower : IsScalarTower k R (H (S := S) (Y := Y)) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

abbrev input := (SelectingChainHomology.representation (E := E) (Y := Y)).Evaluation
abbrev selectedRepresentation := SourceActionEvaluation.representation (Y := H (S := S) (Y := Y)) E
abbrev reference := EvaluationVertexDiagram.module (selectedRepresentation (E := E) (S := S) (Y := Y))

omit [FiniteDimensional k Y] in
theorem selected_action (a : Fin (E.generators+1)) :
    EvaluationVertexDiagram.action (Y := H (S := S) (Y := Y)) (selectedRepresentation (E := E) (S := S) (Y := Y)) a =
      HAction (S := S) (Y := Y) (RelationBasisAction.arrow (SelectionEncoding.generator E) a) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [(HAction_apply (S := S))]
  refine Fin.cases ?_ (fun j => ?_) a
  · change x = (1 : R) • x
    rw [one_smul]
  · rfl

def coordinates (n : ℤ) (hn : n = 0 ∨ n = -3) :
    ∀ v : Fin 3, ((SelectingTensor.source (enc := E) (S := S)) (input (E := E) (Y := Y)) v).homology n ≅ H (S := S) (Y := Y) :=
  Fin.cases ((SelectingChainHomology.D0Iso (E := E) (S := S)) n hn)
    (Fin.cases ((SelectingChainHomology.D1Iso (E := E) (S := S)) n hn)
      (fun _ => (SelectingChainHomology.D2Iso (E := E) (S := S)) n hn))

theorem coordinates01 (a : Fin (E.generators+1)) (n : ℤ) (hn : n = 0 ∨ n = -3) :
    homologyMap (((BalancedTensor.tensorFunctor k (B E.relations) (input (E := E) (Y := Y))).mapHomologicalComplex (.up ℤ)).map
      ((SelectingRectification.f E S) a)) n ≫ (coordinates (E := E) (S := S) (Y := Y) n hn 1).hom =
      (coordinates (E := E) (S := S) (Y := Y) n hn 0).hom ≫ EvaluationVertexDiagram.action (Y := H (S := S) (Y := Y)) (selectedRepresentation (E := E) (S := S) (Y := Y)) a := by
  erw [selected_action (E := E) (S := S) (Y := Y)]
  exact (SelectingChainHomology.fixed_arrow01 (E := E) (S := S)) a n hn

theorem coordinates12 (a : Fin (E.generators+1)) (n : ℤ) (hn : n = 0 ∨ n = -3) :
    homologyMap (((BalancedTensor.tensorFunctor k (B E.relations) (input (E := E) (Y := Y))).mapHomologicalComplex (.up ℤ)).map
      ((SelectingRectification.g E S) a)) n ≫ (coordinates (E := E) (S := S) (Y := Y) n hn 2).hom =
      (coordinates (E := E) (S := S) (Y := Y) n hn 1).hom ≫ EvaluationVertexDiagram.action (Y := H (S := S) (Y := Y)) (selectedRepresentation (E := E) (S := S) (Y := Y)) a := by
  erw [selected_action (E := E) (S := S) (Y := Y)]
  exact (SelectingChainHomology.fixed_arrow12 (E := E) (S := S)) a n hn

/-- The entire (cohomology (E := E) (S := S)) B-module is the manuscript's M((H (S := S))(Y)), in both degrees. -/
def cohomology (n : ℤ) (hn : n = 0 ∨ n = -3) :
    ((SelectingTensor.complex (enc := E) (S := S)) (input (E := E) (Y := Y))).homology n ≅ reference (E := E) (S := S) (Y := Y) :=
  (SelectingReferenceCohomology.iso (enc := E) (S := S)) _ (selectedRepresentation (E := E) (S := S) (Y := Y)) n (coordinates (E := E) (S := S) (Y := Y) n hn)
    (fun a => (coordinates01 (E := E) (S := S)) a n hn) (fun a => (coordinates12 (E := E) (S := S)) a n hn)

theorem source_zero (n : ℤ) (hn0 : n ≠ 0) (hn3 : n ≠ -3) (v : Fin 3) :
    IsZero (((SelectingTensor.source (enc := E) (S := S)) (input (E := E) (Y := Y)) v).homology n) := by
  fin_cases v
  · exact (SelectingChainHomology.D0_zero (E := E) (S := S)) n hn0 hn3
  · exact (SelectingChainHomology.D1_zero (E := E) (S := S)) n hn0 hn3
  · exact (SelectingChainHomology.D2_zero (E := E) (S := S)) n hn0 hn3

/-- The one fixed selecting bimodule realizes (H (S := S)) on every finite-dimensional Y.
This is an isomorphism in the full B-module derived category. -/
def realization :
    (SelectingTensorSplitting.object (enc := E) (S := S)) (input (E := E) (Y := Y)) ≅
      (DerivedCategory.singleFunctor (ModuleCat (B E.relations)) 0).obj (reference (E := E) (S := S) (Y := Y)) ⊞
        ((DerivedCategory.singleFunctor (ModuleCat (B E.relations)) 0).obj (reference (E := E) (S := S) (Y := Y)))⟦(3 : ℤ)⟧ :=
  (SelectingTensorSplitting.split (enc := E) (S := S)) _ _ ((cohomology (E := E) (S := S)) 0 (Or.inl rfl))
    ((cohomology (E := E) (S := S)) (-3) (Or.inr rfl)) (source_zero (E := E) (S := S))
theorem realizes_selection : Nonempty (
    SelectingTensorSplitting.object (enc := E) (S := S) (input (E := E) (Y := Y)) ≅
      (DerivedCategory.singleFunctor (ModuleCat (B E.relations)) 0).obj
        (reference (E := E) (S := S) (Y := Y)) ⊞
      ((DerivedCategory.singleFunctor (ModuleCat (B E.relations)) 0).obj
        (reference (E := E) (S := S) (Y := Y)))⟦(3 : ℤ)⟧) :=
  ⟨realization (E := E) (S := S) (Y := Y)⟩

end SelectingRealization

end

end Note198
