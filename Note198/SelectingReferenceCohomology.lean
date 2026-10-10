import Note198.SelectingCohomologyAssembly
import OAI.Algebra.Finitistic.Localization.EvaluationVertexDiagram

namespace Note198
noncomputable section
open CategoryTheory HomologicalComplex
namespace SelectingReferenceCohomology
open OAI.LittleFinitistic
open SelectingRectification QuadraticEncoding

private lemma transfer_to_vertices {C : Type*} [Category C]
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
variable (N : Type u) [AddCommGroup N] [Module k N] [Module (B enc.relations) N]
variable {Y : Type u} [AddCommGroup Y] [Module k Y] (X : Representation enc.relations Y)
variable (n : ℤ) (E : ∀ v : Fin 3,
  ((SelectingTensor.source (enc := enc) (S := S)) N v).homology n ≅ ModuleCat.of k Y)

/-- Identify the full tensor cohomology with the actual evaluation module from
three coordinate models and their generator actions. -/
def iso
    (h01 : ∀ a,
      homologyMap (((BalancedTensor.tensorFunctor k (B enc.relations) N).mapHomologicalComplex (.up ℤ)).map ((SelectingRectification.f enc S) a)) n ≫
        (E 1).hom = (E 0).hom ≫ EvaluationVertexDiagram.action X a)
    (h12 : ∀ b,
      homologyMap (((BalancedTensor.tensorFunctor k (B enc.relations) N).mapHomologicalComplex (.up ℤ)).map ((SelectingRectification.g enc S) b)) n ≫
        (E 2).hom = (E 1).hom ≫ EvaluationVertexDiagram.action X b) :
    ((SelectingTensor.complex (enc := enc) (S := S)) N).homology n ≅ EvaluationVertexDiagram.module X := by
  apply (SelectingCohomologyAssembly.iso (enc := enc) (S := S)) N n (EvaluationVertexDiagram.module X)
    (fun v => E v ≪≫ (EvaluationVertexDiagram.vertexIso X v).symm)
  · intro a
    exact transfer_to_vertices _ _ _ (E 0) (E 1)
      (EvaluationVertexDiagram.vertexIso X 0) (EvaluationVertexDiagram.vertexIso X 1)
      (h01 a) (EvaluationVertexDiagram.arrow01_square X a (CanonicalArrowCompatibility.arrow01_target enc.relations a))
  · intro b
    exact transfer_to_vertices _ _ _ (E 1) (E 2)
      (EvaluationVertexDiagram.vertexIso X 1) (EvaluationVertexDiagram.vertexIso X 2)
      (h12 b) (EvaluationVertexDiagram.arrow12_square X b (CanonicalArrowCompatibility.arrow12_target enc.relations b))
end SelectingReferenceCohomology

end

end Note198
