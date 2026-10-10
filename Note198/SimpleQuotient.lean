import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace Note198
universe u

/-- The simple quotient step in Proposition 2.1. The source module must
already be constructed and proved nonzero and finite-dimensional. -/
theorem exists_finite_simple_quotient
    (k R M : Type u) [Field k] [Ring R] [Algebra k R]
    [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
    [Nontrivial M] [FiniteDimensional k M] :
    ∃ N : Submodule R M,
      IsSimpleModule R (M ⧸ N) ∧ FiniteDimensional k (M ⧸ N) := by
  letI : IsNoetherian R M := isNoetherian_of_tower k inferInstance
  obtain ⟨N, hN⟩ := IsCoatomic.exists_coatom (α := Submodule R M)
  exact ⟨N, isSimpleModule_iff_isCoatom.mpr hN, inferInstance⟩

/-- An identity action descends through the actual quotient map. -/
theorem quotient_identity_action
    {R M : Type u} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) (r : R) (h : ∀ x : M, r • x = x) :
    ∀ x : M ⧸ N, r • x = x := by
  intro x
  obtain ⟨y, rfl⟩ := N.mkQ_surjective x
  rw [← N.mkQ.map_smul, h]

/-- A zero action descends through the actual quotient map. -/
theorem quotient_zero_action
    {R M : Type u} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) (r : R) (h : ∀ x : M, r • x = 0) :
    ∀ x : M ⧸ N, r • x = 0 := by
  intro x
  obtain ⟨y, rfl⟩ := N.mkQ_surjective x
  rw [← N.mkQ.map_smul, h, map_zero]

end Note198
