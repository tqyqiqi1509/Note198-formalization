import Mathlib.Algebra.TrivSqZeroExt.Basic

namespace Note198
noncomputable section
universe u v w z
variable {A : Type u} {B : Type v} [Ring A] [Ring B]

/-- A separate type synonym records inflation along a concrete ring map. -/
def RingInflation (f : A →+* B) (M : Type w) := M

instance (f : A →+* B) {M : Type w} [AddCommGroup M] :
    AddCommGroup (RingInflation f M) := inferInstanceAs (AddCommGroup M)

instance (f : A →+* B) {M : Type w} [AddCommGroup M] [Module B M] :
    Module B (RingInflation f M) := inferInstanceAs (Module B M)

instance (f : A →+* B) {M : Type w} [AddCommGroup M] [Module B M] :
    Module A (RingInflation f M) := Module.compHom _ f

variable (f : A →+* B) {M : Type w} {N : Type z}
  [AddCommGroup M] [AddCommGroup N] [Module B M] [Module B N]

/-- Restriction along a surjective ring homomorphism is fully faithful on
the actual module Hom sets: its inverse uses a preimage of each scalar. -/
def inflation_hom_equiv (hf : Function.Surjective f) :
    (M →ₗ[B] N) ≃ (RingInflation f M →ₗ[A] RingInflation f N) where
  toFun F :=
    { toFun := F
      map_add' := F.map_add
      map_smul' := fun a x => F.map_smul (f a) x }
  invFun F :=
    { toFun := F
      map_add' := F.map_add
      map_smul' := by
        intro b x
        obtain ⟨a,rfl⟩ := hf b
        exact F.map_smul a x }
  left_inv F := by ext x; rfl
  right_inv F := by ext x; rfl

section ActualSelectingAlgebra
open scoped TensorProduct
variable {k L R X : Type u} [Field k] [Ring L] [Ring R]
  [Algebra k L] [Algebra k R] [AddCommGroup X] [Module k X]
  [Module (L × R) X] [Module (L × R)ᵐᵒᵖ X]
  [IsScalarTower k (L × R) X] [IsScalarTower k (L × R)ᵐᵒᵖ X]
  [SMulCommClass (L × R) (L × R)ᵐᵒᵖ X]

/-- The manuscript's augmentation followed by its first product projection. -/
def selecting_first_projection : TrivSqZeroExt (L × R) X →+* L :=
  (RingHom.fst L R).comp (TrivSqZeroExt.fstHom k (L × R) X).toRingHom

theorem selecting_first_projection_surjective :
    Function.Surjective (selecting_first_projection (k := k) (L := L) (R := R) (X := X)) := by
  intro l
  exact ⟨TrivSqZeroExt.inl (l,0),rfl⟩

/-- Actual A-inflation preserves all L-module maps, for the very square-zero
selecting algebra rather than an assumed Hom certificate. -/
def selecting_inflation_hom_equiv {M : Type w} {N : Type z}
    [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N] :
    (M →ₗ[L] N) ≃
      (RingInflation (selecting_first_projection (k := k) (L := L) (R := R) (X := X)) M →ₗ[
        TrivSqZeroExt (L × R) X]
      RingInflation (selecting_first_projection (k := k) (L := L) (R := R) (X := X)) N) :=
  inflation_hom_equiv _ selecting_first_projection_surjective

end ActualSelectingAlgebra
end
end Note198
