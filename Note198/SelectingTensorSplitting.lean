import Note198.SelectingCohomologyVanishing
import OAI.Algebra.Finitistic.Localization.TwoDegreeFormalityNaturality

namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace SelectingTensorSplitting
open OAI.LittleFinitistic
open QuadraticEncoding
universe u
variable {k R₀ : Type u} [Field k] [Ring R₀] [Algebra k R₀]
variable {enc : SelectionEncoding.Encoding k R₀} {S : EndomorphismSelection.Data k R₀}
variable (N : Type u) [AddCommGroup N] [Module k N] [Module (B enc.relations) N]

/-- The actual derived (object (enc := enc) (S := S)) represented by the full B-valued fixed tensor complex. -/
abbrev object : DerivedCategory (ModuleCat (B enc.relations)) := DerivedCategory.Q.obj ((SelectingTensor.complex (enc := enc) (S := S)) N)

def homologyIso (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat (B enc.relations)) n).obj ((object (enc := enc) (S := S)) N) ≅
      ((SelectingTensor.complex (enc := enc) (S := S)) N).homology n :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat (B enc.relations)) n).app ((SelectingTensor.complex (enc := enc) (S := S)) N)

/-- Support of the evaluated representative diagram implies actual derived
cohomological support of the full tensor (object (enc := enc) (S := S)). -/
theorem twoDegrees
    (h : ∀ n : ℤ, n ≠ 0 → n ≠ -3 → ∀ v : Fin 3,
      IsZero (((SelectingTensor.source (enc := enc) (S := S)) N v).homology n)) :
    DerivedTruncation.TwoDegrees ((object (enc := enc) (S := S)) N) := by
  intro n hn0 hn3
  exact ((homologyIso (enc := enc) (S := S)) N n).isZero_iff.mpr
    ((SelectingCohomologyVanishing.cohomology_isZero (enc := enc) (S := S)) N n (h n hn0 hn3))

/-- Apply the proved B-linear truncation splitting to the actual fixed tensor,
using full module cohomology models and source-diagram support. -/
def split (R : ModuleCat (B enc.relations))
    (h0 : ((SelectingTensor.complex (enc := enc) (S := S)) N).homology 0 ≅ R)
    (h3 : ((SelectingTensor.complex (enc := enc) (S := S)) N).homology (-3) ≅ R)
    (hz : ∀ n : ℤ, n ≠ 0 → n ≠ -3 → ∀ v : Fin 3,
      IsZero (((SelectingTensor.source (enc := enc) (S := S)) N v).homology n)) :
    (object (enc := enc) (S := S)) N ≅ (DerivedCategory.singleFunctor (ModuleCat (B enc.relations)) 0).obj R ⊞
      ((DerivedCategory.singleFunctor (ModuleCat (B enc.relations)) 0).obj R)⟦(3 : ℤ)⟧ :=
  TwoDegreeFormality.splitIsoWithModels enc.relations ((object (enc := enc) (S := S)) N) ((twoDegrees (enc := enc) (S := S)) N hz) R R
    ((homologyIso (enc := enc) (S := S)) N 0 ≪≫ h0) ((homologyIso (enc := enc) (S := S)) N (-3) ≪≫ h3)
end SelectingTensorSplitting

end

end Note198
