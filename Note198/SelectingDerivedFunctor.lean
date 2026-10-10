import Note198.SelectingRealization
import OAI.Algebra.Finitistic.Localization.NativeSingleEvaluation

set_option maxHeartbeats 0

namespace Note198.SelectingDerivedFunctor
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)

def lower : ℤ := Classical.choose (SelectingRectification.verified E S)
def upper : ℤ := Classical.choose (Classical.choose_spec (SelectingRectification.verified E S))
theorem window_verified : RectificationLemma.Verified E.relations
    (SelectingRectification.D₀ E S) (SelectingRectification.D₁ E S)
    (SelectingRectification.D₂ E S) (SelectingRectification.f E S)
    (SelectingRectification.g E S) (SelectingRectification.relations E S)
    (lower E S) (upper E S) :=
  Classical.choose_spec (Classical.choose_spec (SelectingRectification.verified E S))

/-- The native derived tensor functor of the single fixed selecting complex,
constructed from its actual bounded right-projective model. -/
def model : BimoduleTotal.BoundedProjective k (QuadraticEncoding.B E.relations)
    (SelectingRectification.bimodule E S) :=
  BimoduleTotal.nativeProjectiveModel (SelectingRectification.bimodule E S)
    (lower E S - 2) (upper E S) (window_verified E S).bounded
    (window_verified E S).projective

abbrev Phi := (model E S).derived

variable {Y : Type u} [AddCommGroup Y] [Module k Y] [Module R Y]
  [IsScalarTower k R Y] [FiniteDimensional k Y]

/-- The genuine derived tensor evaluation, including the full B-module
structure, rather than only the underlying vector-space cohomology. -/
theorem native_realization : Nonempty (
    (Phi E S).obj ((DerivedCategory.singleFunctor
      (ModuleCat (QuadraticEncoding.B E.relations)) 0).obj
        (ModuleCat.of (QuadraticEncoding.B E.relations) (SelectingRealization.input (E := E) (Y := Y)))) ≅
    (DerivedCategory.singleFunctor (ModuleCat (QuadraticEncoding.B E.relations)) 0).obj
      (SelectingRealization.reference (E := E) (S := S) (Y := Y)) ⊞
    ((DerivedCategory.singleFunctor (ModuleCat (QuadraticEncoding.B E.relations)) 0).obj
      (SelectingRealization.reference (E := E) (S := S) (Y := Y)))⟦(3 : ℤ)⟧) :=
  ⟨(model E S).nativeSingleEvaluation (SelectingRealization.input (E := E) (Y := Y)) ≪≫
    SelectingRealization.realization (E := E) (S := S) (Y := Y)⟩

end
end Note198.SelectingDerivedFunctor
