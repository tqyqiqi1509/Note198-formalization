import Note198.SelectingAlgebraProperties
import Note198.SelectingModuleProperties
import Note198.SourceInflationHom

namespace Note198.RemainingAlgebraModules
noncomputable section
open OAI.LittleFinitistic QuadraticEncoding
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)

/-- The canonical full Hom correspondence preserves addition and the
actual field action, not only the underlying Hom sets. -/
def source_hom_linearEquiv (Y Z : ModuleCat.{u} R) :
    (Y →ₗ[R] Z) ≃ₗ[k]
      (SelectingModuleProperties.M E S Y →ₗ[SelectingOrdinaryAlgebra.A E S]
        SelectingModuleProperties.M E S Z) where
  toEquiv := source_selecting_hom_equiv
    (S := SelectingAlgebraProperties.Eblock E S)
    (X := SelectingOrdinaryAlgebra.X E S) (Y := Y) (Z := Z) E
  map_add' f g := by ext x <;> rfl
  map_smul' c f := by ext x <;> rfl

/-- Proposition 7.1 for the single actual A, with arbitrary source modules
in its full Hom assertion. Nonzero modules have Loewy length three even
without the manuscript's finite dimensionality restriction. -/
theorem constructed_algebra_and_modules :
    FiniteDimensional k (SelectingOrdinaryAlgebra.A E S) ∧
    Nonempty (NoncommutativeQuotient (Ring.jacobson (SelectingOrdinaryAlgebra.A E S))
      ≃ₐ[k] (Fin (3*SelectingOrdinaryAlgebra.length E S+6) → k)) ∧
    Ring.jacobson (SelectingOrdinaryAlgebra.A E S)^7 = ⊥ ∧
    CompleteOrthogonalIdempotents (SelectingAlgebraProperties.vertex E S) ∧
    (∀ i, IsPrimitiveIdempotent (SelectingAlgebraProperties.vertex E S i)) ∧
    (∀ i, ∃ he : IsIdempotentElem (SelectingAlgebraProperties.vertex E S i),
      Nonempty (he.Corner ≃+* k)) ∧
    (∀ i (a : SelectingOrdinaryAlgebra.A E S), ∃ c : k,
      SelectingAlgebraProperties.vertex E S i*a*SelectingAlgebraProperties.vertex E S i =
        c • SelectingAlgebraProperties.vertex E S i) ∧
    (∀ Y : ModuleCat.{u} R, Nontrivial Y →
      (∀ a ∈ Ring.jacobson (SelectingOrdinaryAlgebra.A E S)^3,
        ∀ y : SelectingModuleProperties.M E S Y, a • y=0) ∧
      (∃ a ∈ Ring.jacobson (SelectingOrdinaryAlgebra.A E S)^2,
        ∃ y : SelectingModuleProperties.M E S Y, a • y≠0)) ∧
    (∀ Y Z : ModuleCat.{u} R, Nonempty ((Y →ₗ[R] Z) ≃ₗ[k]
      (SelectingModuleProperties.M E S Y →ₗ[SelectingOrdinaryAlgebra.A E S]
        SelectingModuleProperties.M E S Z))) := by
  sorry

end
end Note198.RemainingAlgebraModules
