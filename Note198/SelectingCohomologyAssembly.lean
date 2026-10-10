import Note198.SelectingTensor
import OAI.Algebra.Finitistic.Rectification.VertexCategoricalAssembly

namespace Note198
noncomputable section
open CategoryTheory HomologicalComplex
namespace SelectingCohomologyAssembly
open OAI.LittleFinitistic
open SelectingRectification QuadraticEncoding
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
variable (N : Type u) [AddCommGroup N] [Module k N] [Module (B enc.relations) N]
variable (n : ℤ) (R : ModuleCat (B enc.relations))
variable (E : ∀ v : Fin 3, ((SelectingTensor.source (enc := enc) (S := S)) N v).homology n ≅
  (LeftVertexHomology.vertex k (B enc.relations) (ThreeVertexAlgebra.vertex (composition enc.relations) v)).obj R)

/-- Convert an identified evaluated-representative cohomology diagram into the
full cohomology B-module of the one fixed selecting tensor. Only the reference
diagram identification is an input; the tensor vertex comparisons are proved. -/
def iso
    (h01 : ∀ a,
      homologyMap (((BalancedTensor.tensorFunctor k (B enc.relations) N).mapHomologicalComplex (.up ℤ)).map ((SelectingRectification.f enc S) a)) n ≫
        (E 1).hom = (E 0).hom ≫
        (LeftVertexHomology.arrow k (B enc.relations) (ThreeVertexAlgebra.vertex (composition enc.relations) 0)
          (ThreeVertexAlgebra.vertex (composition enc.relations) 1) (arrow01 enc.relations a)
          (CanonicalArrowCompatibility.arrow01_target enc.relations a)).app R)
    (h12 : ∀ b,
      homologyMap (((BalancedTensor.tensorFunctor k (B enc.relations) N).mapHomologicalComplex (.up ℤ)).map ((SelectingRectification.g enc S) b)) n ≫
        (E 2).hom = (E 1).hom ≫
        (LeftVertexHomology.arrow k (B enc.relations) (ThreeVertexAlgebra.vertex (composition enc.relations) 1)
          (ThreeVertexAlgebra.vertex (composition enc.relations) 2) (arrow12 enc.relations b)
          (CanonicalArrowCompatibility.arrow12_target enc.relations b)).app R) :
    ((SelectingTensor.complex (enc := enc) (S := S)) N).homology n ≅ R :=
  VertexCategoricalAssembly.iso enc.relations _ R
    (fun v => ((SelectingTensor.comparisonIso (enc := enc) (S := S)) N v n).symm ≪≫ E v)
    (fun a => transfer_square _ _ _ ((SelectingTensor.comparisonIso (enc := enc) (S := S)) N 0 n)
      ((SelectingTensor.comparisonIso (enc := enc) (S := S)) N 1 n) (E 0) (E 1)
      (TensorCohomologyDiagram.arrow01_square enc.relations (SelectingRectification.D₀ enc S) (SelectingRectification.D₁ enc S) (SelectingRectification.D₂ enc S) (SelectingRectification.f enc S) (SelectingRectification.g enc S) (SelectingRectification.relations enc S) N a n) (h01 a))
    (fun b => transfer_square _ _ _ ((SelectingTensor.comparisonIso (enc := enc) (S := S)) N 1 n)
      ((SelectingTensor.comparisonIso (enc := enc) (S := S)) N 2 n) (E 1) (E 2)
      (TensorCohomologyDiagram.arrow12_square enc.relations (SelectingRectification.D₀ enc S) (SelectingRectification.D₁ enc S) (SelectingRectification.D₂ enc S) (SelectingRectification.f enc S) (SelectingRectification.g enc S) (SelectingRectification.relations enc S) N b n) (h12 b))
end SelectingCohomologyAssembly

end

end Note198
