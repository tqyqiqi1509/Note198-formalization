import Note198.SelectingOrdinaryAlgebra
import Note198.RadicalConstructed
import Note198.ConstructedResidue
import Note198.ConstructedCorners
import Note198.TensorGlobalDimensionHeight

namespace Note198
noncomputable section
open CategoryTheory OAI.LittleFinitistic QuadraticEncoding OrdinarySimulation
open scoped TensorProduct
universe u v
namespace SelectingAlgebraProperties
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)

abbrev Eblock := B E.relations ⊗[k] ChainAlgebra k (SelectingOrdinaryAlgebra.length E S)
abbrev VertexIndex := Sum (Fin 3) (Fin ((SelectingOrdinaryAlgebra.length E S + 1) * 3))

/-- The manuscript's actual displayed vertices in its one fixed algebra. -/
def vertex (i : VertexIndex E S) : SelectingOrdinaryAlgebra.A E S :=
  constructed_vertex
    (O := SelectingOrdinaryAlgebra.O E S) (T := TerminalTensor (B E.relations))
    (composition E.relations) (SelectingOrdinaryAlgebra.length E S) i

theorem finite : FiniteDimensional k (SelectingOrdinaryAlgebra.A E S) := inferInstance

theorem radical_pow_seven_zero : Ring.jacobson (SelectingOrdinaryAlgebra.A E S)^7 = ⊥ :=
  constructed_radical_pow_seven_zero
    (O := SelectingOrdinaryAlgebra.O E S) (T := TerminalTensor (B E.relations))
    (composition E.relations) (SelectingOrdinaryAlgebra.length E S)

/-- An actual k-algebra isomorphism for A/J_A. Together with finite
dimensionality, this is the explicit split-basic assertion. -/
def residueEquiv : NoncommutativeQuotient (Ring.jacobson (SelectingOrdinaryAlgebra.A E S))
    ≃ₐ[k] (Fin (3 * SelectingOrdinaryAlgebra.length E S + 6) → k) :=
  constructed_residue_equiv
    (O := SelectingOrdinaryAlgebra.O E S) (T := TerminalTensor (B E.relations))
    (composition E.relations) (SelectingOrdinaryAlgebra.length E S)

theorem residue_isomorphism : Nonempty
    (NoncommutativeQuotient (Ring.jacobson (SelectingOrdinaryAlgebra.A E S))
      ≃ₐ[k] (Fin (3 * SelectingOrdinaryAlgebra.length E S + 6) → k)) :=
  ⟨residueEquiv E S⟩

theorem complete_orthogonal_idempotents : CompleteOrthogonalIdempotents (vertex E S) :=
  constructed_complete_orthogonal_idempotents
    (O := SelectingOrdinaryAlgebra.O E S) (T := TerminalTensor (B E.relations))
    (composition E.relations) (SelectingOrdinaryAlgebra.length E S)

theorem primitive (i : VertexIndex E S) : IsPrimitiveIdempotent (vertex E S i) :=
  constructed_vertex_primitive
    (O := SelectingOrdinaryAlgebra.O E S) (T := TerminalTensor (B E.relations))
    (composition E.relations) (SelectingOrdinaryAlgebra.length E S) i

/-- The genuine corner ring, whose identity is the chosen vertex, is k. -/
theorem corner_is_field (i : VertexIndex E S) :
    ∃ he : IsIdempotentElem (vertex E S i), Nonempty (he.Corner ≃+* k) :=
  constructed_vertex_corner_is_field
    (O := SelectingOrdinaryAlgebra.O E S) (T := TerminalTensor (B E.relations))
    (composition E.relations) (SelectingOrdinaryAlgebra.length E S) i

/-- The precise tensor-block global-dimension bound, on both sides and
for arbitrary modules, is l+2. -/
theorem tensor_block_globalDimension_le :
    (⨆ N : ModuleCat.{max u v} (Eblock E S), projectiveDimension N) ≤
      (SelectingOrdinaryAlgebra.length E S + 2 : ℕ) ∧
    (⨆ N : ModuleCat.{max u v} (Eblock E S)ᵐᵒᵖ, projectiveDimension N) ≤
      (SelectingOrdinaryAlgebra.length E S + 2 : ℕ) :=
  ⟨tensor_chain_globalDimension_le (ThreeVertexAlgebra.directedSystem (composition E.relations))
      (SelectingOrdinaryAlgebra.length E S),
    tensor_chain_opposite_globalDimension_le (ThreeVertexAlgebra.directedSystem (composition E.relations))
      (SelectingOrdinaryAlgebra.length E S)⟩

end SelectingAlgebraProperties
end
end Note198
