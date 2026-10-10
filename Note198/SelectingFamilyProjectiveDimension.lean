import Note198.SelectingFamilyMaximum
import Note198.SelectingFamilyInflatedModule

namespace Note198.SelectingFamilyProjectiveDimension
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
open ComplexProjectiveDimension SelectingOrdinaryAlgebra
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
variable (F : SelectingBrickFamily.SourceFamily k R S)

/-- Exact projective dimension of the actual inflated family module,
computed from the full finite bar and its proved even/odd dimensions. -/
theorem inflated_dimension (m : ℕ+) :
    projectiveDimension (SelectingFamilyInflatedModule.module E S F m) =
      (SelectingFamilyMaximum.maximum E S F m : ℕ) := by
  let N := SelectingFamilyFiniteBar.firstModule E S F m
  letI : Module k N := DerivedBar.BimoduleTensor.scalarModule k (D E S) N
  letI : IsScalarTower k (D E S) N :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := D E S) (M := N) (fun _ _ => rfl)
  letI : Module (A E S) N := DerivedBar.ParityBridge.inflatedModule (D E S) (X E S) N
  letI : IsScalarTower k (A E S) N := IsScalarTower.of_algebraMap_smul
    (R := k) (A := A E S) (M := N)
    (fun a v => IsScalarTower.algebraMap_smul (D E S) a v)
  letI : FiniteDimensional k N := SelectingFamilyInflatedModule.module_finite E S F m
  letI : Nontrivial N := SelectingFamilyInflatedModule.module_nontrivial E S F m
  have hN : ¬ IsZero (ModuleCat.of (A E S) N) := by
    rw [ModuleCat.isZero_iff_subsingleton]
    exact not_subsingleton N
  let g := length E S+2
  have hg (M : ModuleCat.{u} (D E S)) : HasProjectiveDimensionLE M g :=
    (projectiveDimension_le_iff M g).mp (SelectingOrdinaryDimension.module_dimension_le E S M)
  let e := Classical.choice (SelectingFiniteBar.finite_bar_model E S N (2*m.val)
    (SelectingFamilyFiniteBar.ordinary_extinction E S F m))
  exact ComplexFiniteBarDimension.module_pd_eq_finite_max g hg
    (TrivSqZeroExt.fstHom k (D E S) (X E S))
    (fun d => ⟨TrivSqZeroExt.inl d,rfl⟩)
    (fun a ha b hb => PDSquareZero.kernel_square_zero (X E S) a b ha hb)
    N hN (2*m.val)
    (fun r => SelectingFiniteBar.count E S N r.val) (fun _ => 0)
    (fun r => SelectingFamilyCountBounded.count_bounded E S F m r.val)
    (e ≪≫ biproduct.mapIso (fun r : Fin (2*m.val) =>
      (shiftZero ℤ (SelectingFiniteBar.count E S N r.val)).symm))
    (SelectingFamilyMaximum.maximum E S F m)
    (by simpa using SelectingFamilyMaximum.count_maximum E S F m)

/-- The same value holds for the manuscript's original three-copy A-module,
using the actual identity linear equivalence of its two action descriptions. -/
theorem brick_dimension (m : ℕ+) :
    projectiveDimension (ModuleCat.of (A E S) (SelectingBrickFamily.module E S F m)) =
      (SelectingFamilyMaximum.maximum E S F m : ℕ) := by
  rw [← SelectingFamilyInflatedModule.brick_dimension_eq E S F m]
  exact inflated_dimension E S F m

theorem brick_bounds (m : ℕ+) :
    ((SelectingFamilyMaximum.coefficient E S+5)*(m.val-1)+1 : ℕ) ≤
      projectiveDimension (ModuleCat.of (A E S) (SelectingBrickFamily.module E S F m)) ∧
    projectiveDimension (ModuleCat.of (A E S) (SelectingBrickFamily.module E S F m)) ≤
      ((SelectingFamilyMaximum.coefficient E S+5)*(m.val-1)+length E S+3 : ℕ) := by
  rw [brick_dimension E S F m]
  have h := SelectingFamilyMaximum.maximum_bounds E S F m
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2

theorem brick_finite_pd (m : ℕ+) :
    projectiveDimension (ModuleCat.of (A E S) (SelectingBrickFamily.module E S F m)) < ⊤ := by
  rw [brick_dimension E S F m]
  exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _)

end
end Note198.SelectingFamilyProjectiveDimension
