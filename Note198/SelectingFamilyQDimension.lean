import Note198.SelectingFamilyFiniteBar
import Note198.SelectingOrdinaryNonzero
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBalancedCongruence

namespace Note198.SelectingFamilyQDimension
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
open SelectingIteration SelectingOrdinaryOddSplit
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)

local instance (Y : Family (k := k) (R := R)) : Module k Y.val :=
  Module.compHom Y.val (algebraMap k R)
local instance (Y : Family (k := k) (R := R)) : IsScalarTower k R Y.val :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance (Y : Family (k := k) (R := R)) : FiniteDimensional k Y.val := Y.property

def inputEquiv (Y : Family (k := k) (R := R)) :
    BalancedTensor.ScalarLeftModule k (QuadraticEncoding.B E.relations) (input E Y) ≃ₗ[QuadraticEncoding.B E.relations]
      SelectingRealization.input (E := E) (Y := Y.val) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem input_finite (Y : Family (k := k) (R := R)) :
    FiniteDimensional k (BalancedTensor.ScalarLeftModule k (QuadraticEncoding.B E.relations) (input E Y)) := by
  let f : SelectingRealization.input (E := E) (Y := Y.val) →ₗ[k]
      BalancedTensor.ScalarLeftModule k (QuadraticEncoding.B E.relations) (input E Y) :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun c x =>
        (IsScalarTower.algebraMap_smul (QuadraticEncoding.B E.relations) c x).symm }
  exact Module.Finite.of_surjective f (fun x => ⟨x,rfl⟩)

theorem Q_finite (Y : Family (k := k) (R := R)) :
    FiniteDimensional k (BalancedTensor.ScalarLeftModule k (SelectingOrdinaryQ.Eblock E S)
      (Qmodule E S Y)) := by
  letI := input_finite E Y
  exact SelectingOrdinaryQ.finite E S (input E Y)

theorem Q_nontrivial (Y : Family (k := k) (R := R))
    [Nontrivial Y.val] [Nontrivial (SelectingOrdinaryAlgebra.O E S)] :
    Nontrivial (Qmodule E S Y) := by
  let rep := SelectingChainHomology.representation (E := E) (Y := Y.val)
  letI := projective_evaluation_tensor_nontrivial E.relations rep (SelectingOrdinaryAlgebra.O E S)
  let e := BalancedTensor.congr (k := k)
    (LinearEquiv.refl (QuadraticEncoding.B E.relations)ᵐᵒᵖ (SelectingOrdinaryAlgebra.O E S))
    (inputEquiv E Y)
  obtain ⟨x,y,hxy⟩ := exists_pair_ne (BalancedTensor.Tensor k (QuadraticEncoding.B E.relations)
    (SelectingOrdinaryAlgebra.O E S) rep.Evaluation)
  exact ⟨⟨e.symm x,e.symm y,fun h => hxy (e.symm.injective h)⟩⟩

theorem finite_numeric_dimension {A : Type u} [Ring A] (M : ModuleCat.{u} A)
    [Nontrivial M] (g : ℕ) (hbound : projectiveDimension M ≤ g) :
    ∃ n : ℕ, n ≤ g ∧ projectiveDimension M = n := by
  generalize hp : projectiveDimension M = d at hbound
  induction d with
  | bot =>
    have hz := (projectiveDimension_eq_bot_iff M).mp hp
    have hsub := ModuleCat.isZero_iff_subsingleton.mp hz
    exact False.elim (not_subsingleton M hsub)
  | coe d =>
    induction d with
    | top =>
      change ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((g : ℕ∞) : WithBot ℕ∞) at hbound
      have hx : (⊤ : ℕ∞) ≤ (g : ℕ∞) := WithBot.coe_le_coe.mp hbound
      have hb : (g : ℕ∞) = ⊤ := le_antisymm le_top hx
      have hn : (g : ℕ∞) ≠ ⊤ := by simp
      exact False.elim (hn hb)
    | coe n =>
      exact ⟨n, by exact_mod_cast hbound, rfl⟩

variable (F : SelectingBrickFamily.SourceFamily k R S)

include F in
theorem O_nontrivial : Nontrivial (SelectingOrdinaryAlgebra.O E S) := by
  let m : ℕ+ := ⟨2,by omega⟩
  letI : Module k (F.V m) := Module.compHom (F.V m) (algebraMap k R)
  letI : IsScalarTower k R (F.V m) :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := R) (M := F.V m) (fun _ _ => rfl)
  letI : FiniteDimensional k (F.V m) := by
    change FiniteDimensional k (EndomorphismSelection.vectorObject (k := k) (F.V m))
    exact F.finite m
  letI : Nontrivial (SelectingNativeEvaluation.H (S := S) (Y := F.V m)) := by
    change Nontrivial (EndomorphismSelection.iterate S (F.V m) 1)
    exact F.alive m 1 (by dsimp [m]; omega)
  exact SelectingOrdinaryNonzero.ordinary_O_nontrivial E S (Y := F.V m)

/-- The actual odd coefficient dimensions δ_j exist and satisfy the
manuscript's uniform interval 0≤δ_j≤l+2, for every surviving source iterate.
The nonzero tensor input and right projectivity are proved from the same F/O. -/
theorem odd_dimension_exists (m : ℕ+) (j : ℕ) (hj : j < m.val) :
    ∃ n : ℕ, n ≤ SelectingOrdinaryAlgebra.length E S+2 ∧
      projectiveDimension (inflatedQmodule E S
        (((selected S)^[j]) (SelectingFamilyFiniteBar.source F m))) = n := by
  let Y := ((selected S)^[j]) (SelectingFamilyFiniteBar.source F m)
  have hY : Nontrivial Y.val := by
    dsimp [Y]
    rw [SelectingIteration.iterate_val]
    exact F.alive m j hj
  letI := hY
  letI := O_nontrivial E S F
  letI : Nontrivial (inflatedQmodule E S Y) := by
    change Nontrivial (Qmodule E S Y)
    exact Q_nontrivial E S Y
  exact finite_numeric_dimension (inflatedQmodule E S Y)
    (SelectingOrdinaryAlgebra.length E S+2) (Q_dimension_le E S Y)
end
end Note198.SelectingFamilyQDimension
