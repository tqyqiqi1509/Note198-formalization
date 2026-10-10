import Note198.OrdinaryProductDimensionExact
import Note198.SelectingOrdinaryBimoduleComparison

namespace Note198.RemainingOrdinarySimulation
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u v
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]

/-- Proposition 5.1 for the actual fixed ordinary algebra and bimodule:
both global bounds, the full derived square, and the bimodule compression. -/
theorem ordinary_simulation
    (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R) :
    ((⨆ M : ModuleCat.{max u v} (SelectingOrdinaryAlgebra.D E S),
        projectiveDimension M) ≤ (SelectingOrdinaryAlgebra.length E S + 2 : ℕ)) ∧
    ((⨆ M : ModuleCat.{max u v} (SelectingOrdinaryAlgebra.D E S)ᵐᵒᵖ,
        projectiveDimension M) ≤ (SelectingOrdinaryAlgebra.length E S + 2 : ℕ)) ∧
    (∀ Y : DerivedCategory (ModuleCat.{u} (QuadraticEncoding.B E.relations)),
      Nonempty ((SelectingOrdinarySimulation.ordinary E S).obj
        ((SelectingOrdinarySimulation.ordinary E S).obj
          ((SelectingOrdinarySimulation.first E S).obj Y)) ≅
        (SelectingOrdinarySimulation.first E S).obj
          ((SelectingOrdinarySimulation.shifted E S).obj Y))) ∧
    Nonempty ((OrdinarySimulation.TensorResolution.resolutionModel k
      (QuadraticEncoding.B E.relations) (SelectingOrdinaryAlgebra.length E S)).tensorOrdinary
        (QuadraticEncoding.B E.relations) (SelectingOrdinaryAlgebra.O E S) ≅
      DerivedCategory.Q.obj
        ((SelectingRectification.bimodule E S)⟦SelectingOrdinaryAlgebra.b E S⟧)) := by
  sorry

end
end Note198.RemainingOrdinarySimulation