import Note198.FiniteSelectionSource
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Note198.SelectionProductNormalization
noncomputable section
open MonoidAlgebra
open scoped BigOperators
universe u
variable (k : Type u) [Field k] (p m : ℕ) [Fact p.Prime] [NeZero m]
abbrev H := FiniteSelectionSource.CoefficientGroup p m
abbrev BaseRing := MonoidAlgebra k (H p m)

def coordinateWeight (i : Fin m) (a : ZMod p) : k :=
  if i = FiniteSelectionSource.lastIndex m then
    (if a = 0 then 1 else 0) - (p : k)⁻¹ else (p : k)⁻¹

def coordinateFactor (i : Fin m) : BaseRing k p m :=
  ∑ a : ZMod p, single (Multiplicative.ofAdd (Pi.single i a)) (coordinateWeight k p m i a)

def centralTransport : BaseRing k p m →ₐ[k]
    MonoidAlgebra k (FiniteSelectionSource.F p m) :=
  MonoidAlgebra.mapDomainAlgHom k k (PrimeGroup.quotientCentralEmbedding p m)

/-- The ordered product of the first m-1 averaging factors and the final
complementary factor. It is computed in the commutative central-subgroup
algebra, then embedded into the finite quotient algebra. -/
def normalizedProduct : MonoidAlgebra k (FiniteSelectionSource.F p m) :=
  centralTransport k p m (∏ i : Fin m, coordinateFactor k p m i)

theorem coordinateWeight_product (c : Fin m → ZMod p) :
    (∏ i : Fin m, coordinateWeight k p m i (c i)) =
      ((p : k)⁻¹ ^ (m - 1)) * FiniteSelectionSource.sourceWeight k p m (Multiplicative.ofAdd c) := by
  classical
  rw [← Finset.prod_erase_mul Finset.univ
    (fun i => coordinateWeight k p m i (c i))
    (Finset.mem_univ (FiniteSelectionSource.lastIndex m))]
  have he : (∏ i ∈ Finset.univ.erase (FiniteSelectionSource.lastIndex m),
      coordinateWeight k p m i (c i)) = (p : k)⁻¹ ^ (m - 1) := by
    calc
      _ = ∏ _i ∈ Finset.univ.erase (FiniteSelectionSource.lastIndex m), (p : k)⁻¹ := by
        apply Finset.prod_congr rfl
        intro i hi
        simp only [coordinateWeight, if_neg (Finset.ne_of_mem_erase hi)]
      _ = _ := by simp
  rw [he]
  simp [coordinateWeight, FiniteSelectionSource.sourceWeight]

theorem basisCoordinate_product (c : Fin m → ZMod p) :
    (∏ i : Fin m, (Multiplicative.ofAdd (Pi.single i (c i)) : H p m)) =
      Multiplicative.ofAdd c := by
  apply Multiplicative.toAdd.injective
  change (∑ i : Fin m, Pi.single i (c i)) = c
  ext j
  simp [Pi.single_apply]

/-- Expanding the canonical central-coordinate product gives its exact coefficients. -/
theorem coordinateFactor_product :
    (∏ i : Fin m, coordinateFactor k p m i) =
      ∑ c : Fin m → ZMod p, single (Multiplicative.ofAdd c)
        (((p : k)⁻¹ ^ (m - 1)) *
          FiniteSelectionSource.sourceWeight k p m (Multiplicative.ofAdd c)) := by
  classical
  unfold coordinateFactor
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [MonoidAlgebra.prod_single, basisCoordinate_product, coordinateWeight_product]

/-- Exact normalization of the product used in the manuscript's source construction. -/
theorem normalizedProduct_eq_sourceVector :
    normalizedProduct k p m = ((p : k)⁻¹ ^ (m - 1)) • FiniteSelectionSource.sourceVector k p m := by
  classical
  unfold normalizedProduct
  rw [coordinateFactor_product, map_sum]
  have hs : (∑ c : Fin m → ZMod p,
      centralTransport k p m (single (Multiplicative.ofAdd c)
        (((p : k)⁻¹ ^ (m - 1)) *
          FiniteSelectionSource.sourceWeight k p m (Multiplicative.ofAdd c)))) =
      ((p : k)⁻¹ ^ (m - 1)) •
        ∑ c : Fin m → ZMod p, single
          (PrimeGroup.quotientCentralEmbedding p m (Multiplicative.ofAdd c))
          (FiniteSelectionSource.sourceWeight k p m (Multiplicative.ofAdd c)) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro c _
    simp [centralTransport, smul_single, smul_eq_mul]
  rw [hs]
  congr 1
  let e : (Fin m → ZMod p) ≃ H p m :=
    ⟨Multiplicative.ofAdd, Multiplicative.toAdd, fun _ => rfl, fun _ => rfl⟩
  exact Equiv.sum_comp e (fun c => single
    (PrimeGroup.quotientCentralEmbedding p m c) (FiniteSelectionSource.sourceWeight k p m c))

/-- Every factor before the last is the manuscript's normalized averaging operator. -/
theorem coordinateFactor_earlier (i : Fin m) (hi : i ≠ FiniteSelectionSource.lastIndex m) :
    centralTransport k p m (coordinateFactor k p m i) =
      FiniteSelectionSource.selector k p m i := by
  classical
  unfold coordinateFactor FiniteSelectionSource.selector
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp [centralTransport, coordinateWeight, hi, smul_single]

/-- The last factor is exactly one minus the final averaging operator. -/
theorem coordinateFactor_last :
    centralTransport k p m (coordinateFactor k p m (FiniteSelectionSource.lastIndex m)) =
      1 - FiniteSelectionSource.selector k p m (FiniteSelectionSource.lastIndex m) := by
  classical
  unfold coordinateFactor FiniteSelectionSource.selector
  rw [map_sum, Finset.smul_sum]
  have hterm (a : ZMod p) : centralTransport k p m
      (single (Multiplicative.ofAdd (Pi.single (FiniteSelectionSource.lastIndex m) a))
        (coordinateWeight k p m (FiniteSelectionSource.lastIndex m) a)) =
      (if a = 0 then 1 else 0) - (p : k)⁻¹ •
        single (PrimeGroup.quotientCentralEmbedding p m
          (Multiplicative.ofAdd (Pi.single (FiniteSelectionSource.lastIndex m) a))) 1 := by
    have hmap (c : k) : centralTransport k p m
        (single (Multiplicative.ofAdd (Pi.single (FiniteSelectionSource.lastIndex m) a)) c) =
        single (PrimeGroup.quotientCentralEmbedding p m
          (Multiplicative.ofAdd (Pi.single (FiniteSelectionSource.lastIndex m) a))) c := by
      simp [centralTransport]
    rw [hmap]
    by_cases ha : a = 0
    · subst a
      simp [coordinateWeight, MonoidAlgebra.one_def, single_sub, smul_single]
    · simp [coordinateWeight, ha, single_sub, smul_single]
  simp only [hterm, Finset.sum_sub_distrib]
  simp

end
end Note198.SelectionProductNormalization


