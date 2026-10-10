import Note198.ExplicitSimpleModules
import Note198.SelectingBrickFamily
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! The concrete complex brick family, with its actual scalar endomorphism algebra. -/
namespace Note198.ComplexBrickFamily
noncomputable section
open CategoryTheory OAI.LittleFinitistic
open scoped ModuleCat.Algebra

abbrev R := GroupAlgebraSelection.Ring ℂ 2

def selection : Selection.Data ℂ R := GroupAlgebraSelection.dataTwo ℂ (by norm_num)

/-- One actual encoding, chosen once before the positive integer parameter. -/
def encoding : SelectionEncoding.Encoding ℂ R :=
  Classical.choice (encoding_of_finite_presentation ℂ R
    (selecting_algebra_finitely_presented ℂ 2))

/-- The full explicit coordinate module, without passing to a simple quotient. -/
def source (m : ℕ+) : ModuleCat R := by
  letI : NeZero m.val := ⟨Nat.ne_of_gt m.pos⟩
  exact ModuleCat.of R (ExplicitSimpleModules.ExplicitModule m.val)

/-- All members use the same group algebra, selecting operator, and finite encoding. -/
def family : SelectingBrickFamily.SourceFamily ℂ R selection.toEndomorphism where
  V := source
  simple m := by
    letI : NeZero m.val := ⟨Nat.ne_of_gt m.pos⟩
    exact ExplicitSimpleModules.explicitModule_simple m.val
  finite m := by
    letI : NeZero m.val := ⟨Nat.ne_of_gt m.pos⟩
    exact ExplicitSimpleModules.explicitVector_finiteDimensional m.val
  alive m j hj := by
    letI : NeZero m.val := ⟨Nat.ne_of_gt m.pos⟩
    rw [selection_iterate_endomorphism]
    exact (ExplicitSimpleModules.explicitModule_extinction m.val).1 j hj
  extinct m := by
    letI : NeZero m.val := ⟨Nat.ne_of_gt m.pos⟩
    rw [selection_iterate_endomorphism]
    exact (ExplicitSimpleModules.explicitModule_extinction m.val).2

abbrev A := SelectingOrdinaryAlgebra.A encoding selection.toEndomorphism
abbrev M (m : ℕ+) := SelectingBrickFamily.module encoding selection.toEndomorphism family m

/-- The source vector spaces have exactly the manuscript's exponential dimensions. -/
theorem source_dimension (m : ℕ+) :
    Module.finrank ℂ (EndomorphismSelection.vectorObject (k := ℂ) (source m)) =
      2 ^ (3 * m.val) := by
  letI : NeZero m.val := ⟨Nat.ne_of_gt m.pos⟩
  exact ExplicitSimpleModules.explicitVector_dimension m.val

/-- These are the actual A-modules, each with three copies of the full coordinate space. -/
theorem module_dimension (m : ℕ+) : Module.finrank ℂ (M m) = 3 * 2 ^ (3 * m.val) := by
  rw [SelectingBrickFamily.dimension encoding selection.toEndomorphism family m]
  exact congrArg (fun d : ℕ => 3*d) (source_dimension m)

instance module_finite (m : ℕ+) : FiniteDimensional ℂ (M m) :=
  SelectingBrickFamily.finite encoding selection.toEndomorphism family m

section Endomorphisms
variable {A₀ M₀ : Type*} [Ring A₀] [Algebra ℂ A₀]
  [AddCommGroup M₀] [Module A₀ M₀] [Module ℂ M₀]
  [IsScalarTower ℂ A₀ M₀] [SMulCommClass A₀ ℂ M₀]

/-- Restriction preserves the actual addition, composition and scalar algebra map. -/
def endomorphismRestriction : Module.End A₀ M₀ →ₐ[ℂ] Module.End ℂ M₀ where
  toFun := LinearMap.restrictScalars ℂ
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' c := by
    ext x
    rfl

/-- Finiteness of the vector space makes the actual endomorphism subalgebra integral. -/
theorem endomorphisms_integral [FiniteDimensional ℂ M₀] :
    Algebra.IsIntegral ℂ (Module.End A₀ M₀) :=
  Algebra.IsIntegral.of_injective (endomorphismRestriction (A₀ := A₀) (M₀ := M₀))
    (LinearMap.restrictScalars_injective ℂ)
end Endomorphisms

/-- Over the algebraically closed field ℂ, the actual brick endomorphism algebra is ℂ.
The proof uses integrality of the finite-dimensional operator algebra in addition to Schur. -/
def scalar_end_equiv (m : ℕ+) : ℂ ≃ₐ[ℂ] Module.End A (M m) := by
  let d := SelectingBrickFamily.endDivisionRing encoding selection.toEndomorphism family m
  have hd : @IsDomain (Module.End A (M m)) d.toRing.toSemiring :=
    @DivisionRing.isDomain (Module.End A (M m)) d
  have hr : d.toRing = inferInstanceAs (Ring (Module.End A (M m))) :=
    SelectingBrickFamily.endDivisionRing_original_ring encoding selection.toEndomorphism family m
  rw [hr] at hd
  letI : IsDomain (Module.End A (M m)) := hd
  letI : Algebra.IsIntegral ℂ (Module.End A (M m)) := endomorphisms_integral
  exact AlgEquiv.ofBijective (Algebra.ofId ℂ (Module.End A (M m)))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- The complex branch supplies actual pairwise orthogonal bricks over one fixed A. -/
theorem complex_bricks (m : ℕ+) :
    Module.finrank ℂ (M m) = 3 * 2 ^ (3 * m.val) ∧
    Nonempty (ℂ ≃ₐ[ℂ] Module.End A (M m)) ∧
    (∀ n : ℕ+, m ≠ n → ∀ f : M m →ₗ[A] M n, f = 0) := by
  refine ⟨module_dimension m, ⟨scalar_end_equiv m⟩, ?_⟩
  intro n hmn f
  exact SelectingBrickFamily.cross_hom_zero encoding selection.toEndomorphism family m n hmn f

end
end Note198.ComplexBrickFamily
