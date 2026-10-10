import Note198.SelectingOrdinarySimulation
import OAI.Algebra.Finitistic.Ordinary.OrdinarySourceDerivedComparison

namespace Note198.SelectingOrdinaryBimoduleComparison
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
attribute [local instance] HasDerivedCategory.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
open SelectingOrdinaryAlgebra

/-- The actual T-resolution tensor O comparison keeps both exterior B
actions: it lies in the native derived category of genuine B-bimodules. -/
theorem compression : Nonempty (
    (OrdinarySimulation.TensorResolution.resolutionModel k
      (QuadraticEncoding.B E.relations) (length E S)).tensorOrdinary
      (QuadraticEncoding.B E.relations) (O E S) ≅
    DerivedCategory.Q.obj ((SelectingRectification.bimodule E S)⟦b E S⟧)) :=
  ⟨OrdinarySimulation.resolvedBimoduleComparison
    (SelectingRectification.bimodule E S) (a E S) (length E S) (b E S)
    (endpoints E S) (support E S)⟩

end
end Note198.SelectingOrdinaryBimoduleComparison
