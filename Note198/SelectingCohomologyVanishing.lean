import Note198.SelectingCohomologyAssembly

namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace SelectingCohomologyVanishing
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

open SelectingRectification
variable {k R₀ : Type u} [Field k] [Ring R₀] [Algebra k R₀]
variable {enc : SelectionEncoding.Encoding k R₀} {S : EndomorphismSelection.Data k R₀}
variable (N : Type u) [AddCommGroup N] [Module k N] [Module (B enc.relations) N]

/-- Vanishing on all three evaluated representatives gives actual cohomology
vanishing of the fixed selecting tensor as a B-module. -/
theorem cohomology_isZero (n : ℤ)
    (h : ∀ v : Fin 3, IsZero (((SelectingTensor.source (enc := enc) (S := S)) N v).homology n)) :
    IsZero (((SelectingTensor.complex (enc := enc) (S := S)) N).homology n) := by
  apply module_isZero enc.relations
  intro v
  exact ((SelectingTensor.comparisonIso (enc := enc) (S := S)) N v n).isZero_iff.mp (h v)
end SelectingCohomologyVanishing

end

end Note198
