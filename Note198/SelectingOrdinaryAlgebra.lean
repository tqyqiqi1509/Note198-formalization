import Note198.SelectingDerivedFunctor
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBlockBimodule
import OAI.Algebra.Finitistic.Ordinary.OrdinaryRightProjective
import Mathlib.Algebra.TrivSqZeroExt.Basic

set_option maxHeartbeats 0

namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace SelectingOrdinaryAlgebra
open OAI OAI.LittleFinitistic QuadraticEncoding
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
open OrdinarySimulation

/-- A fixed support interval containing degree zero, chosen before any test module. -/
def a : ℤ := min (SelectingDerivedFunctor.lower E S-2) 0
def b : ℤ := max (SelectingDerivedFunctor.upper E S) 0
def length : ℕ := ((b E S)-(a E S)).toNat

theorem a_le_zero : (a E S) ≤ 0 := min_le_right _ _
theorem b_nonneg : 0 ≤ (b E S) := le_max_right _ _
theorem endpoints : (a E S) + ((length E S) : ℤ) = (b E S) := by
  have ha := a_le_zero E S
  have hb := b_nonneg E S
  dsimp [length]
  omega

theorem support (n : ℤ) (hn : n < (a E S) ∨ (b E S) < n) :
    IsZero ((SelectingRectification.bimodule E S).X n) := by
  apply (SelectingDerivedFunctor.window_verified E S).bounded n
  dsimp [a,b] at hn
  omega

instance term_finite (n : ℤ) :
    FiniteDimensional k ((underlyingComplex (k := k) (SelectingRectification.bimodule E S)).X n) :=
  (SelectingDerivedFunctor.window_verified E S).finite n
instance term_projective (n : ℤ) :
    Module.Projective (B E.relations)ᵐᵒᵖ ((underlyingRightComplex (SelectingRectification.bimodule E S)).X n) := by
  let : Projective ((underlyingRightComplex (SelectingRectification.bimodule E S)).X n) :=
    (SelectingDerivedFunctor.window_verified E S).projective n
  exact ModuleCat.projective_of_module_projective _

/-- The actual finite-dimensional ordinary algebra and off-diagonal bimodule. -/
abbrev D := AlgebraD k (length E S) (B E.relations)
abbrev O := BimoduleO (SelectingRectification.bimodule E S) (a E S) (length E S)
abbrev X := BimoduleX (SelectingRectification.bimodule E S) (a E S) (length E S)
instance base_finite : FiniteDimensional k (B E.relations) := QuadraticEncoding.finiteDimensional E.relations
instance D_finite : FiniteDimensional k (D E S) := inferInstance
instance O_finite : FiniteDimensional k (O E S) := inferInstance
instance X_finite : FiniteDimensional k (X E S) := ordinary_finite _ _ _
instance O_right_projective : Module.Projective (B E.relations)ᵐᵒᵖ (O E S) :=
  ordinaryO_right_projective _ _ _

/-- The manuscript's one fixed square-zero algebra. No projective-dimension
conclusion is asserted here. -/
abbrev A := TrivSqZeroExt (D E S) (X E S)
abbrev augmentation : (A E S) →ₐ[k] (D E S) := TrivSqZeroExt.fstHom k (D E S) (X E S)

instance A_finite : FiniteDimensional k (A E S) :=
  inferInstanceAs (FiniteDimensional k ((D E S) × (X E S)))
end SelectingOrdinaryAlgebra

end

end Note198
