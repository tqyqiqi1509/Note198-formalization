import Note198.InflationHom
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace Note198
noncomputable section
universe u v w z
variable {k : Type u} [Field k] {A : Type v} {B : Type w} [Ring A] [Ring B]

instance (priority := 100) ringInflationScalarModule (f : A →+* B)
    {M : Type z} [AddCommGroup M] [Module B M] [Module k M] :
    Module k (RingInflation f M) := inferInstanceAs (Module k M)

/-- Inflation preserves the actual underlying vector space by identity. -/
def ringInflationLinearEquiv (f : A →+* B) {M : Type z}
    [AddCommGroup M] [Module B M] [Module k M] :
    RingInflation f M ≃ₗ[k] M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance ringInflationFiniteDimensional (f : A →+* B) {M : Type z}
    [AddCommGroup M] [Module B M] [Module k M] [FiniteDimensional k M] :
    FiniteDimensional k (RingInflation f M) :=
  inferInstanceAs (FiniteDimensional k M)

instance ringInflationScalarTowerCodomain (f : A →+* B) {M : Type z}
    [Algebra k B] [AddCommGroup M] [Module B M] [Module k M]
    [IsScalarTower k B M] : IsScalarTower k B (RingInflation f M) :=
  inferInstanceAs (IsScalarTower k B M)

/-- The domain scalar tower follows from the actual map's compatibility
with scalar multiplication; this condition is proved for the concrete
selecting projection below. -/
def ringInflationScalarTowerDomain (f : A →+* B) {M : Type z}
    [Algebra k A] [Algebra k B] [AddCommGroup M] [Module B M] [Module k M]
    [IsScalarTower k B M] (hf : ∀ c : k, ∀ a : A, f (c • a) = c • f a) :
    IsScalarTower k A (RingInflation f M) where
  smul_assoc c a x := by
    change f (c • a) • x = c • (f a • x)
    rw [hf]
    exact smul_assoc c (f a) x

theorem ringInflationLinearEquiv_bijective (f : A →+* B) {M : Type z}
    [AddCommGroup M] [Module B M] [Module k M] :
    Function.Bijective (ringInflationLinearEquiv (k := k) (M := M) f) :=
  (ringInflationLinearEquiv f).bijective

section Selecting
variable {L R X : Type u} [Ring L] [Ring R] [Algebra k L] [Algebra k R]
  [AddCommGroup X] [Module k X] [Module (L × R) X] [Module (L × R)ᵐᵒᵖ X]
  [IsScalarTower k (L × R) X] [IsScalarTower k (L × R)ᵐᵒᵖ X]
  [SMulCommClass (L × R) (L × R)ᵐᵒᵖ X]

theorem selecting_first_projection_smul (c : k) (a : TrivSqZeroExt (L × R) X) :
    selecting_first_projection (k := k) (L := L) (R := R) (X := X) (c • a) =
      c • selecting_first_projection (k := k) (L := L) (R := R) (X := X) a := rfl

instance selectingInflationScalarTower {M : Type z}
    [AddCommGroup M] [Module L M] [Module k M] [IsScalarTower k L M] :
    IsScalarTower k (TrivSqZeroExt (L × R) X)
      (RingInflation (selecting_first_projection (k := k) (L := L) (R := R) (X := X)) M) :=
  ringInflationScalarTowerDomain _ selecting_first_projection_smul

theorem selecting_inflation_scalar_tower {M : Type z}
    [AddCommGroup M] [Module L M] [Module k M] [IsScalarTower k L M] :
    IsScalarTower k (TrivSqZeroExt (L × R) X)
      (RingInflation (selecting_first_projection (k := k) (L := L) (R := R) (X := X)) M) :=
  inferInstance

theorem selecting_inflation_finiteDimensional {M : Type z}
    [AddCommGroup M] [Module L M] [Module k M] [FiniteDimensional k M] :
    FiniteDimensional k
      (RingInflation (selecting_first_projection (k := k) (L := L) (R := R) (X := X)) M) :=
  inferInstance

end Selecting
end
end Note198
