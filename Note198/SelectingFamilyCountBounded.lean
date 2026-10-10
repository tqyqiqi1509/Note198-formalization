import Note198.SelectingFamilyCountDimensions
import Note198.ComplexFiniteBarDimension

namespace Note198.SelectingFamilyCountBounded
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
open SelectingIteration ComplexStupidTruncation
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)

theorem bounded_of_iso {A : Type u} [Ring A] {Z T : DerivedCategory (ModuleCat.{u} A)}
    (hZ : InBoundedFiniteDerived Z) (e : Z ≅ T) : InBoundedFiniteDerived T := by
  obtain ⟨P,lo,hi,hP,hb,⟨eP⟩⟩ := hZ
  exact ⟨P,lo,hi,hP,hb,⟨eP ≪≫ e⟩⟩

theorem even_bounded (Y : Family (k := k) (R := R)) (j : ℕ) :
    InBoundedFiniteDerived (((SelectingOrdinarySimulation.ordinary E S).obj^[2*j])
      (SelectingOrdinaryIteration.evaluated E S Y)) := by
  let g := SelectingOrdinaryAlgebra.length E S+2
  have hg (N : ModuleCat.{u} (SelectingOrdinaryAlgebra.D E S)) : HasProjectiveDimensionLE N g :=
    (projectiveDimension_le_iff N g).mp (SelectingOrdinaryDimension.module_dimension_le E S N)
  exact bounded_of_iso (ComplexBinomialModuleDimension.binomial_bounded_finite g hg
    (SelectingFamilyEvenSigned.finiteFirst E S (((selected S)^[j]) Y)) j
    (SelectingOrdinaryAlgebra.b E S))
    (Classical.choice (SelectingOrdinaryEvenSplit.even_shifted_modules E S j Y)).symm

theorem odd_bounded (Y : Family (k := k) (R := R)) (j : ℕ) :
    InBoundedFiniteDerived (((SelectingOrdinarySimulation.ordinary E S).obj^[2*j+1])
      (SelectingOrdinaryIteration.evaluated E S Y)) := by
  let g := SelectingOrdinaryAlgebra.length E S+2
  have hg (N : ModuleCat.{u} (SelectingOrdinaryAlgebra.D E S)) : HasProjectiveDimensionLE N g :=
    (projectiveDimension_le_iff N g).mp (SelectingOrdinaryDimension.module_dimension_le E S N)
  exact bounded_of_iso (ComplexBinomialModuleDimension.binomial_bounded_finite g hg
    (SelectingFamilyOddSigned.finiteQ E S (((selected S)^[j]) Y)) j
    (SelectingOrdinaryAlgebra.b E S))
    (Classical.choice (SelectingOrdinaryOddSplit.odd_shifted_modules E S j Y)).symm

theorem iterate_bounded (Y : Family (k := k) (R := R)) (r : ℕ) :
    InBoundedFiniteDerived (((SelectingOrdinarySimulation.ordinary E S).obj^[r])
      (SelectingOrdinaryIteration.evaluated E S Y)) := by
  rcases Nat.mod_two_eq_zero_or_one r with h | h
  · have hr : r = 2*(r/2) := by omega
    rw [hr]
    exact even_bounded E S Y (r/2)
  · have hr : r = 2*(r/2)+1 := by omega
    rw [hr]
    exact odd_bounded E S Y (r/2)

variable (F : SelectingBrickFamily.SourceFamily k R S)

/-- Every actual shifted original-X bar count belongs to Db of finite
modules. This supplies the literal essential-image condition required by
the finite-bar dimension theorem, rather than a dimension-list certificate. -/
theorem count_bounded (m : ℕ+) (r : ℕ) :
    InBoundedFiniteDerived (SelectingFiniteBar.count E S
      (SelectingFamilyFiniteBar.firstModule E S F m) r) := by
  let e := mapObjectIteration (SelectingOrdinarySimulation.ordinary E S)
    (SelectingOrdinaryEvenSplit.evaluatedStalkIso E S (SelectingFamilyFiniteBar.source F m)) r ≪≫
    Classical.choice (SelectingOrdinaryBarComparison.ordinary_stalk_bar E S
      (SelectingFamilyFiniteBar.firstModule E S F m) r)
  exact ComplexFiniteBarDimension.boundedFinite_shift _
    (bounded_of_iso (iterate_bounded E S (SelectingFamilyFiniteBar.source F m) r) e) (r:ℤ)
end
end Note198.SelectingFamilyCountBounded
