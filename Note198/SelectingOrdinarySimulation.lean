import Note198.SelectingOrdinaryAlgebra
import OAI.Algebra.Finitistic.Ordinary.OrdinaryDerivedIterates

set_option maxHeartbeats 0

namespace Note198.SelectingOrdinarySimulation
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
open SelectingOrdinaryAlgebra

abbrev ordinary := OrdinarySimulation.XResolution.derivedTensor
  (SelectingRectification.bimodule E S) (a E S) (length E S)

abbrev first := BlockModule.derivedFirst (QuadraticEncoding.B E.relations)
  ((QuadraticEncoding.B E.relations) ⊗[k] OrdinarySimulation.ChainAlgebra k (length E S))

abbrev shifted := OrdinarySimulation.shiftedDerivedTensor
  (SelectingRectification.bimodule E S) (b E S) (length E S)

/-- Section 5's actual square of the ordinary derived tensor, for every
derived B-module, with the fixed support interval discharged. -/
theorem square (Y : DerivedCategory (ModuleCat.{u} (QuadraticEncoding.B E.relations))) :
    Nonempty ((ordinary E S).obj ((ordinary E S).obj ((first E S).obj Y)) ≅
      (first E S).obj ((shifted E S).obj Y)) :=
  ⟨OrdinarySimulation.XResolution.derivedSquareObject
    (SelectingRectification.bimodule E S) (a E S) (length E S) (b E S)
    (endpoints E S) (support E S) Y⟩

/-- Every even ordinary iterate is the inflated shifted selecting iterate;
this is an actual derived isomorphism, not only a cohomology identity. -/
theorem even_iteration (j : ℕ)
    (Y : DerivedCategory (ModuleCat.{u} (QuadraticEncoding.B E.relations))) :
    Nonempty (((ordinary E S).obj^[2*j]) ((first E S).obj Y) ≅
      (first E S).obj (((shifted E S).obj^[j]) Y)) :=
  ⟨OrdinarySimulation.XResolution.derivedEvenIterate
    (SelectingRectification.bimodule E S) (a E S) (length E S) (b E S)
    (endpoints E S) (support E S) j Y⟩

end
end Note198.SelectingOrdinarySimulation
