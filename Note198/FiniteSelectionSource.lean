import Note198.PrimeFiniteQuotient
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! An actual nonzero vector for the all-field selector source.
The coefficient used to prove nonvanishing is at z_last, not at identity:
in characteristic two with p=3 the identity coefficient can vanish. -/
namespace Note198.FiniteSelectionSource
noncomputable section
open MonoidAlgebra
open scoped BigOperators
universe u v w

section WeightedProjector
variable {k : Type u} [Field k] {H : Type v} {F : Type w}
  [Group H] [Group F] [Fintype H]

def weightedProjector (ψ : H →* F) (weight : H → k) : MonoidAlgebra k F :=
  ∑ h : H, single (ψ h) (weight h)

theorem weightedProjector_coefficient (ψ : H →* F) (weight : H → k)
    (hinj : Function.Injective ψ) (a : H) :
    (weightedProjector ψ weight).coeff (ψ a) = weight a := by
  classical
  simp [weightedProjector, coeff_sum, coeff_single, Finsupp.single_apply, hinj.eq_iff]

theorem weightedProjector_nonzero (ψ : H →* F) (weight : H → k)
    (hinj : Function.Injective ψ) (a : H) (ha : weight a ≠ 0) :
    weightedProjector ψ weight ≠ 0 := by
  intro hz
  have h := weightedProjector_coefficient ψ weight hinj a
  rw [hz] at h
  exact ha h.symm

/-- Translation-invariant coefficients give a fixed vector of a subgroup element. -/
theorem weightedProjector_fixed (ψ : H →* F) (weight : H → k) (a : H)
    (hweight : ∀ h, weight (a * h) = weight h) :
    single (ψ a) (1 : k) * weightedProjector ψ weight = weightedProjector ψ weight := by
  classical
  unfold weightedProjector
  rw [Finset.mul_sum]
  rw [← Equiv.sum_comp (Equiv.mulLeft a) (fun h : H => single (ψ h) (weight h))]
  apply Finset.sum_congr rfl
  intro h _
  simp [map_mul, single_mul_single, hweight]
theorem weightedProjector_translate (ψ : H →* F) (weight : H → k) (a : H) :
    single (ψ a) (1 : k) * weightedProjector ψ weight =
      weightedProjector ψ (fun h => weight (a⁻¹ * h)) := by
  classical
  unfold weightedProjector
  rw [Finset.mul_sum]
  rw [← Equiv.sum_comp (Equiv.mulLeft a)
    (fun h : H => single (ψ h) (weight (a⁻¹ * h)))]
  apply Finset.sum_congr rfl
  intro h _
  simp [map_mul, single_mul_single]

theorem weightedProjector_sum {J : Type*} [Fintype J]
    (ψ : H →* F) (weight : J → H → k) :
    weightedProjector ψ (fun h => ∑ j, weight j h) =
      ∑ j, weightedProjector ψ (weight j) := by
  classical
  unfold weightedProjector
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  ext g
  simp only [coeff_single, coeff_sum, Finset.sum_apply, Finsupp.single_apply]
  by_cases he : ψ h = g <;> simp [he]

end WeightedProjector

variable (k : Type u) [Field k] (p m : ℕ) [Fact p.Prime] [NeZero m]
abbrev CoefficientGroup := Multiplicative (Fin m → ZMod p)
abbrev F := PrimeGroup.FiniteQuotientGroup p m

noncomputable instance : Fintype (CoefficientGroup p m) := Fintype.ofFinite _

def lastIndex : Fin m := ⟨m - 1, by have hm := Nat.pos_of_ne_zero (NeZero.ne m); omega⟩

def sourceWeight (c : CoefficientGroup p m) : k :=
  (if c.toAdd (lastIndex m) = 0 then 1 else 0) - (p : k)⁻¹

def sourceWitness : CoefficientGroup p m :=
  Multiplicative.ofAdd (Pi.single (lastIndex m) 1)

def sourceVector : MonoidAlgebra k (F p m) :=
  weightedProjector (PrimeGroup.quotientCentralEmbedding p m) (sourceWeight k p m)

theorem sourceWeight_witness :
    sourceWeight k p m (sourceWitness p m) = -(p : k)⁻¹ := by
  simp [sourceWeight, sourceWitness, Pi.single_apply]

theorem sourceVector_coefficient :
    (sourceVector k p m).coeff (PrimeGroup.quotientCentralEmbedding p m (sourceWitness p m)) =
      -(p : k)⁻¹ := by
  rw [sourceVector, weightedProjector_coefficient _ _
    (PrimeGroup.quotientCentralEmbedding_injective p m), sourceWeight_witness]

theorem sourceVector_nonzero (hp : (p : k) ≠ 0) : sourceVector k p m ≠ 0 := by
  apply weightedProjector_nonzero (PrimeGroup.quotientCentralEmbedding p m)
    (sourceWeight k p m) (PrimeGroup.quotientCentralEmbedding_injective p m)
    (sourceWitness p m)
  rw [sourceWeight_witness]
  exact neg_ne_zero.mpr (inv_ne_zero hp)

/-- Every earlier central coordinate fixes the actual nonzero source vector. -/
theorem sourceVector_fixed_earlier (i : Fin m) (hi : i ≠ lastIndex m) (a : ZMod p) :
    single (PrimeGroup.quotientCentralEmbedding p m
      (Multiplicative.ofAdd (Pi.single i a))) (1 : k) * sourceVector k p m =
      sourceVector k p m := by
  apply weightedProjector_fixed
  intro c
  simp [sourceWeight, Pi.single_apply, hi]

/-- Summing the last-coordinate translates of the weight gives zero. -/
theorem sourceWeight_last_sum (hp : (p : k) ≠ 0) (c : Fin m → ZMod p) :
    (∑ a : ZMod p, sourceWeight k p m
      (Multiplicative.ofAdd (c - Pi.single (lastIndex m) a))) = 0 := by
  classical
  have hzero (a : ZMod p) : c (lastIndex m) - a = 0 ↔ a = c (lastIndex m) :=
    sub_eq_zero.trans eq_comm
  simp [sourceWeight, Pi.single_apply, hzero, Finset.sum_sub_distrib,
    nsmul_eq_mul, hp]

/-- The last-coordinate averaging operator kills the actual source vector. -/
theorem sourceVector_last_sum (hp : (p : k) ≠ 0) :
    (∑ a : ZMod p, single (PrimeGroup.quotientCentralEmbedding p m
      (Multiplicative.ofAdd (Pi.single (lastIndex m) a))) (1 : k) *
      sourceVector k p m) = 0 := by
  classical
  unfold sourceVector
  simp only [weightedProjector_translate]
  rw [← weightedProjector_sum]
  have hz : (fun c : CoefficientGroup p m =>
      ∑ a : ZMod p, sourceWeight k p m
        ((Multiplicative.ofAdd (Pi.single (lastIndex m) a))⁻¹ * c)) = (fun _ => 0) := by
    funext c
    change (∑ a : ZMod p, sourceWeight k p m
      (Multiplicative.ofAdd (-Pi.single (lastIndex m) a + c.toAdd))) = 0
    simpa only [sub_eq_add_neg, add_comm] using sourceWeight_last_sum k p m hp c.toAdd
  rw [hz]
  simp [weightedProjector]

/-- The normalized average over a single central cyclic factor. -/
def selector (i : Fin m) : MonoidAlgebra k (F p m) :=
  (p : k)⁻¹ • ∑ a : ZMod p, single (PrimeGroup.quotientCentralEmbedding p m
    (Multiplicative.ofAdd (Pi.single i a))) 1

theorem selector_central (i : Fin m) (b : MonoidAlgebra k (F p m)) :
    Commute (selector k p m i) b := by
  classical
  show selector k p m i * b = b * selector k p m i
  unfold selector
  rw [smul_mul_assoc, mul_smul_comm]
  congr 1
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact (MonoidAlgebra.single_commute
    (PrimeGroup.quotientCentralEmbedding_central p m
      (Multiplicative.ofAdd (Pi.single i a))) Commute.one_left b).eq

theorem selector_source_earlier (hp : (p : k) ≠ 0) (i : Fin m)
    (hi : i ≠ lastIndex m) : selector k p m i * sourceVector k p m = sourceVector k p m := by
  classical
  unfold selector
  rw [smul_mul_assoc, Finset.sum_mul]
  simp only [sourceVector_fixed_earlier k p m i hi, Finset.sum_const,
    Finset.card_univ, ZMod.card]
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hp, one_smul]

theorem selector_source_last (hp : (p : k) ≠ 0) :
    selector k p m (lastIndex m) * sourceVector k p m = 0 := by
  classical
  unfold selector
  rw [smul_mul_assoc, Finset.sum_mul, sourceVector_last_sum k p m hp, smul_zero]

/-- A concrete finite left ideal defined by the required selector actions. -/
def sourceIdeal : Submodule (MonoidAlgebra k (F p m)) (MonoidAlgebra k (F p m)) where
  carrier := {x | (∀ i : Fin m, i ≠ lastIndex m → selector k p m i * x = x) ∧
    selector k p m (lastIndex m) * x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact ⟨fun i hi => by rw [mul_add, hx.1 i hi, hy.1 i hi],
      by rw [mul_add, hx.2, hy.2, add_zero]⟩
  smul_mem' := by
    intro b x hx
    change (∀ i : Fin m, i ≠ lastIndex m → selector k p m i * (b * x) = b * x) ∧
      selector k p m (lastIndex m) * (b * x) = 0
    constructor
    · intro i hi
      rw [← mul_assoc, (selector_central k p m i b).eq, mul_assoc, hx.1 i hi]
    · rw [← mul_assoc, (selector_central k p m (lastIndex m) b).eq,
        mul_assoc, hx.2, mul_zero]

theorem sourceVector_mem_sourceIdeal (hp : (p : k) ≠ 0) :
    sourceVector k p m ∈ sourceIdeal k p m :=
  ⟨fun i hi => selector_source_earlier k p m hp i hi, selector_source_last k p m hp⟩

theorem sourceIdeal_nontrivial (hp : (p : k) ≠ 0) : Nontrivial (sourceIdeal k p m) := by
  refine ⟨⟨⟨sourceVector k p m, sourceVector_mem_sourceIdeal k p m hp⟩, 0, ?_⟩⟩
  intro h
  exact sourceVector_nonzero k p m hp (congrArg Subtype.val h)

theorem sourceIdeal_finiteDimensional : FiniteDimensional k (sourceIdeal k p m) := by
  have : FiniteDimensional k (MonoidAlgebra k (F p m)) :=
    Module.Finite.equiv (MonoidAlgebra.coeffLinearEquiv k :
      MonoidAlgebra k (F p m) ≃ₗ[k] (F p m →₀ k)).symm
  exact FiniteDimensional.of_injective ((sourceIdeal k p m).restrictScalars k).subtype
    Subtype.val_injective

end
end Note198.FiniteSelectionSource
