import Note198.SelectionProductNormalization

namespace Note198.SelectionProductNormalization
noncomputable section
open MonoidAlgebra
open scoped BigOperators
universe u
variable (k : Type u) [Field k] (p m : ℕ) [Fact p.Prime] [NeZero m]

/-- The manuscript's p_m: the central-coordinate product before the last
coordinate, multiplied by one minus the last averaging idempotent. -/
def paperProduct : MonoidAlgebra k (FiniteSelectionSource.F p m) :=
  centralTransport k p m
    (∏ i ∈ Finset.univ.erase (FiniteSelectionSource.lastIndex m), coordinateFactor k p m i) *
      (1 - FiniteSelectionSource.selector k p m (FiniteSelectionSource.lastIndex m))

theorem normalizedProduct_eq_paperProduct :
    normalizedProduct k p m = paperProduct k p m := by
  classical
  unfold normalizedProduct paperProduct
  rw [← Finset.prod_erase_mul Finset.univ
    (coordinateFactor k p m) (Finset.mem_univ (FiniteSelectionSource.lastIndex m)),
    map_mul, coordinateFactor_last]

theorem paperProduct_eq_sourceVector :
    paperProduct k p m = ((p : k)⁻¹ ^ (m-1)) • FiniteSelectionSource.sourceVector k p m := by
  rw [← normalizedProduct_eq_paperProduct, normalizedProduct_eq_sourceVector]

/-- The exact scalar relation, with p nonzero in k and m positive. -/
theorem sourceVector_eq_paperProduct (hp : (p : k) ≠ 0) :
    FiniteSelectionSource.sourceVector k p m =
      (p : k) ^ (m-1) • paperProduct k p m := by
  rw [paperProduct_eq_sourceVector, smul_smul, ← mul_pow, mul_inv_cancel₀ hp, one_pow, one_smul]

theorem paperProduct_mem_sourceIdeal (hp : (p : k) ≠ 0) :
    paperProduct k p m ∈ FiniteSelectionSource.sourceIdeal k p m := by
  rw [paperProduct_eq_sourceVector]
  constructor
  · intro i hi
    rw [mul_smul_comm, FiniteSelectionSource.selector_source_earlier k p m hp i hi]
  · change FiniteSelectionSource.selector k p m (FiniteSelectionSource.lastIndex m) *
      (((p : k)⁻¹ ^ (m-1)) • FiniteSelectionSource.sourceVector k p m) = 0
    rw [mul_smul_comm, FiniteSelectionSource.selector_source_last k p m hp, smul_zero]

theorem coordinateFactor_central (i : Fin m)
    (b : MonoidAlgebra k (FiniteSelectionSource.F p m)) :
    Commute (centralTransport k p m (coordinateFactor k p m i)) b := by
  classical
  by_cases hi : i = FiniteSelectionSource.lastIndex m
  · subst i
    rw [coordinateFactor_last]
    exact (Commute.one_left b).sub_left (FiniteSelectionSource.selector_central k p m _ b)
  · rw [coordinateFactor_earlier k p m i hi]
    exact FiniteSelectionSource.selector_central k p m i b

theorem paperProduct_central (b : MonoidAlgebra k (FiniteSelectionSource.F p m)) :
    Commute (paperProduct k p m) b := by
  classical
  rw [← normalizedProduct_eq_paperProduct]
  unfold normalizedProduct
  have h (s : Finset (Fin m)) :
      Commute (centralTransport k p m (∏ i ∈ s, coordinateFactor k p m i)) b := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, map_mul]
      exact (coordinateFactor_central k p m i b).mul_left ih
  exact h Finset.univ

theorem paperProduct_mul_sourceIdeal
    (x : MonoidAlgebra k (FiniteSelectionSource.F p m))
    (hx : x ∈ FiniteSelectionSource.sourceIdeal k p m) : paperProduct k p m * x = x := by
  classical
  have hc (i : Fin m) : centralTransport k p m (coordinateFactor k p m i) * x = x := by
    by_cases hi : i = FiniteSelectionSource.lastIndex m
    · subst i
      rw [coordinateFactor_last, sub_mul, one_mul, hx.2, sub_zero]
    · rw [coordinateFactor_earlier k p m i hi]
      exact hx.1 i hi
  have h (s : Finset (Fin m)) :
      centralTransport k p m (∏ i ∈ s, coordinateFactor k p m i) * x = x := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, map_mul, mul_assoc, ih, hc]
  rw [← normalizedProduct_eq_paperProduct]
  exact h Finset.univ

/-- Equality of the actual Lean source ideal and the manuscript's left principal ideal. -/
theorem sourceIdeal_eq_paperProduct_span (hp : (p : k) ≠ 0) :
    FiniteSelectionSource.sourceIdeal k p m =
      Submodule.span (MonoidAlgebra k (FiniteSelectionSource.F p m)) {paperProduct k p m} := by
  apply le_antisymm
  · intro x hx
    apply Submodule.mem_span_singleton.mpr
    refine ⟨x, ?_⟩
    change x * paperProduct k p m = x
    rw [← (paperProduct_central k p m x).eq]
    exact paperProduct_mul_sourceIdeal k p m x hx
  · apply Submodule.span_le.mpr
    intro x hx
    have he : x = paperProduct k p m := Set.mem_singleton_iff.mp hx
    rw [he]
    exact paperProduct_mem_sourceIdeal k p m hp

end
end Note198.SelectionProductNormalization
