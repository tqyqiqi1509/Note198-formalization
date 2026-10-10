import Note198.SelectingModuleProperties
import Note198.SelectingSimpleFamily
import Note198.SelectionEndomorphismBridge
import Note198.FiniteEncoding

namespace Note198
noncomputable section
open OAI.LittleFinitistic
open scoped ModuleCat.Algebra
universe u
namespace SelectingBrickFamily

/-- Source data from Proposition 2.1, indexed by its positive extinction
time. All conclusions about the A-modules are derived below. -/
structure SourceFamily (k R : Type u) [Field k] [Ring R] [Algebra k R]
    (S : EndomorphismSelection.Data k R) where
  V : ℕ+ → ModuleCat.{u} R
  simple : ∀ m, IsSimpleModule R (V m)
  finite : ∀ m, FiniteDimensional k (EndomorphismSelection.vectorObject (k := k) (V m))
  alive : ∀ m, ∀ j < m.val, Nontrivial (EndomorphismSelection.iterate S (V m) j)
  extinct : ∀ m, Subsingleton (EndomorphismSelection.iterate S (V m) m.val)

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
variable (F : SourceFamily k R S)

abbrev module (m : ℕ+) := SelectingModuleProperties.M E S (F.V m)

theorem finite (m : ℕ+) : FiniteDimensional k (module E S F m) := by
  letI := F.finite m
  exact SelectingModuleProperties.finite E S (F.V m)

theorem dimension (m : ℕ+) : Module.finrank k (module E S F m) =
    3 * Module.finrank k (EndomorphismSelection.vectorObject (k := k) (F.V m)) := by
  letI := F.finite m
  exact SelectingModuleProperties.dimension E S (F.V m)

theorem loewy_exact_three (m : ℕ+) :
    (∀ a ∈ Ring.jacobson (SelectingOrdinaryAlgebra.A E S)^3,
      ∀ y : module E S F m, a • y = 0) ∧
    (∃ a ∈ Ring.jacobson (SelectingOrdinaryAlgebra.A E S)^2,
      ∃ y : module E S F m, a • y ≠ 0) := by
  letI : Nontrivial (F.V m) := by
    have h := F.alive m 0 m.pos
    change Nontrivial (F.V m) at h
    exact h
  exact SelectingModuleProperties.loewy_exact_three E S (F.V m)

def endDivisionRing (m : ℕ+) :
    DivisionRing (Module.End (SelectingOrdinaryAlgebra.A E S) (module E S F m)) := by
  letI := F.simple m
  exact SelectingModuleProperties.endDivisionRing E S (F.V m)

theorem endDivisionRing_original_ring (m : ℕ+) :
    (endDivisionRing E S F m).toRing =
      inferInstanceAs (Ring (Module.End (SelectingOrdinaryAlgebra.A E S) (module E S F m))) := by
  letI := F.simple m
  exact SelectingModuleProperties.endDivisionRing_original_ring E S (F.V m)

theorem cross_hom_zero (m n : ℕ+) (hmn : m ≠ n)
    (f : module E S F m →ₗ[SelectingOrdinaryAlgebra.A E S] module E S F n) : f = 0 := by
  letI := F.simple m
  letI := F.simple n
  apply SelectingModuleProperties.cross_hom_zero E S (F.V m) (F.V n) m.val n.val
  · intro h
    exact hmn (Subtype.ext h)
  · exact ⟨F.alive m,F.extinct m⟩
  · exact ⟨F.alive n,F.extinct n⟩

/-- The source family and encoding are actually constructed for every
field. Together with the preceding theorems this supplies one fixed A
and its complete orthogonal brick family from Section 7.1. -/
theorem exists_source_family (k : Type u) [Field k] :
    ∃ (R : Type u) (ringR : Ring R),
      letI : Ring R := ringR
      ∃ (algebraR : Algebra k R),
        letI : Algebra k R := algebraR
        ∃ (S : Selection.Data k R) (E : SelectionEncoding.Encoding k R),
          Nonempty (SourceFamily k R S.toEndomorphism) := by
  classical
  obtain ⟨R,hr,ha,S,hpres,hfamily⟩ := selecting_simple_family k
  letI := hr
  letI := ha
  obtain ⟨E⟩ := encoding_of_finite_presentation k R hpres
  let V : ℕ+ → ModuleCat.{u} R := fun m => Classical.choose (hfamily m.val m.pos)
  have hv (m : ℕ+) := Classical.choose_spec (hfamily m.val m.pos)
  refine ⟨R,hr,ha,S,E,⟨{
    V := V
    simple := fun m => (hv m).1
    finite := fun m => (hv m).2.2.1
    alive := ?_
    extinct := ?_ }⟩⟩
  · intro m j hj
    rw [selection_iterate_endomorphism]
    exact (hv m).2.2.2.1 j hj
  · intro m
    rw [selection_iterate_endomorphism]
    exact (hv m).2.2.2.2

end SelectingBrickFamily
end
end Note198
