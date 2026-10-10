import Note198.ActualDimensionFormulas

namespace Note198.RemainingDimensions
noncomputable section
open OAI.LittleFinitistic QuadraticEncoding OrdinarySimulation
open scoped TensorProduct
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)

/-- The actual displayed dimension formulas. The relation cardinality is
that of a basis of the relation span, rather than the raw presentation list. -/
theorem actual_dimensions {ι : Type*} [Fintype ι]
    (r : Module.Basis ι k (relationSpace E.relations)) :
    Module.finrank k (B E.relations) =
      3+2*(E.generators+1)+(E.generators+1)^2-Fintype.card ι ∧
    Module.finrank k k=1 ∧
    Module.finrank k (ChainAlgebra k (SelectingOrdinaryAlgebra.length E S)) =
      2*SelectingOrdinaryAlgebra.length E S+1 ∧
    Module.finrank k (SelectingOrdinaryAlgebra.A E S) =
      (2*SelectingOrdinaryAlgebra.length E S+3)*Module.finrank k (B E.relations)+
      ∑ n ∈ Finset.Icc (SelectingOrdinaryAlgebra.a E S) (SelectingOrdinaryAlgebra.b E S),
        Module.finrank k ((underlyingComplex (k:=k) (SelectingRectification.bimodule E S)).X n) := by
  sorry

end
end Note198.RemainingDimensions
