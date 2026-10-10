import Note198.SelectingOrdinaryAlgebra
import Note198.SourceEndRing
import Note198.SelectionIsomorphism
import Note198.InflatedLoewy
import Note198.InflationScalars

namespace Note198
noncomputable section
open OAI.LittleFinitistic OAI.LittleFinitistic.QuadraticEncoding
open scoped TensorProduct ModuleCat.Algebra
universe u
namespace SelectingModuleProperties
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)

/-- M(Y) with the actual first-projection action of the one fixed ordinary
square-zero algebra. Its underlying vector space consists of three copies
of Y; source simplicity is a property over R. -/
abbrev M (Y : ModuleCat.{u} R) :=
  SelectingEvaluation
    (S := B E.relations ⊗[k] OrdinarySimulation.ChainAlgebra k (SelectingOrdinaryAlgebra.length E S))
    (X := SelectingOrdinaryAlgebra.X E S) (Y := Y) E

theorem finite (Y : ModuleCat.{u} R)
    [FiniteDimensional k (EndomorphismSelection.vectorObject (k := k) Y)] :
    FiniteDimensional k (M E S Y) := by
  letI : FiniteDimensional k Y := inferInstanceAs
    (FiniteDimensional k (EndomorphismSelection.vectorObject (k := k) Y))
  infer_instance

theorem dimension (Y : ModuleCat.{u} R)
    [FiniteDimensional k (EndomorphismSelection.vectorObject (k := k) Y)] :
    Module.finrank k (M E S Y) =
      3 * Module.finrank k (EndomorphismSelection.vectorObject (k := k) Y) := by
  letI : FiniteDimensional k Y := inferInstanceAs
    (FiniteDimensional k (EndomorphismSelection.vectorObject (k := k) Y))
  change Module.finrank k (Y × Y × Y) = 3 * Module.finrank k Y
  rw [Module.finrank_prod, Module.finrank_prod]
  omega

theorem loewy_exact_three (Y : ModuleCat.{u} R) [Nontrivial Y] :
    (∀ a ∈ Ring.jacobson (SelectingOrdinaryAlgebra.A E S)^3,
      ∀ y : M E S Y, a • y = 0) ∧
    (∃ a ∈ Ring.jacobson (SelectingOrdinaryAlgebra.A E S)^2,
      ∃ y : M E S Y, a • y ≠ 0) :=
  inflated_evaluation_loewy_exact_three E.relations (sourceRepresentation (Y := Y) E)

/-- The division-ring inverses preserve the original addition,
composition, and identity of End_A M(Y). No A-simplicity is assumed. -/
def endDivisionRing (Y : ModuleCat.{u} R) [IsSimpleModule R Y] :
    DivisionRing (Module.End (SelectingOrdinaryAlgebra.A E S) (M E S Y)) :=
  source_selecting_end_divisionRing E

theorem endDivisionRing_original_ring (Y : ModuleCat.{u} R) [IsSimpleModule R Y] :
    (endDivisionRing E S Y).toRing =
      inferInstanceAs (Ring (Module.End (SelectingOrdinaryAlgebra.A E S) (M E S Y))) :=
  source_selecting_end_divisionRing_original_ring E

/-- Exact extinction times under the actual H distinguish the source
simple modules and force all cross Hom sets over the fixed A to vanish. -/
theorem cross_hom_zero (Y Z : ModuleCat.{u} R) [IsSimpleModule R Y] [IsSimpleModule R Z]
    (m n : ℕ) (hmn : m ≠ n)
    (hY : (∀ j < m, Nontrivial (EndomorphismSelection.iterate S Y j)) ∧
      Subsingleton (EndomorphismSelection.iterate S Y m))
    (hZ : (∀ j < n, Nontrivial (EndomorphismSelection.iterate S Z j)) ∧
      Subsingleton (EndomorphismSelection.iterate S Z n))
    (F : M E S Y →ₗ[SelectingOrdinaryAlgebra.A E S] M E S Z) : F = 0 :=
  source_selecting_hom_zero_of_nonisomorphic E
    (EndomorphismSelection.nonisomorphic_of_extinction_times S Y Z m n hmn hY hZ) F

end SelectingModuleProperties
end
end Note198
