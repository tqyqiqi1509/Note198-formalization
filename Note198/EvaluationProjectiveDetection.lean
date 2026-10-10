import OAI.Algebra.Finitistic.Ordinary.OrdinaryFreeTensor
import OAI.Algebra.Finitistic.Tensor.BalancedTensorMaps

namespace Note198
noncomputable section
open OAI.LittleFinitistic
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (I N : Type u) [AddCommGroup N] [Module k N] [Module A N]
  [IsScalarTower k A N]

/-- Coordinate evaluation keeps the right coefficient's `unop` and its
left action on the evaluation module in their actual order. -/
theorem free_tensor_evaluation_coordinate (w : I →₀ Aᵐᵒᵖ) (n : N) (j : I) :
    (BalancedTensor.Free.evaluation (k := k) I N
      (BalancedTensor.mk k A (I →₀ Aᵐᵒᵖ) N w n)) j = (w j).unop • n := by
  change (BalancedTensor.Free.evaluateBilinear (k := k) I N w n) j = _
  induction w using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero, LinearMap.zero_apply, Finsupp.zero_apply,
      MulOpposite.unop_zero, zero_smul]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, Finsupp.add_apply,
      MulOpposite.unop_add, add_smul, hx, hy]
  | single i c =>
    rw [BalancedTensor.Free.evaluateBilinear_single]
    classical
    by_cases h : i = j
    · subst j
      simp
    · simp [h]

variable {M : Type u} [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
  [IsScalarTower k Aᵐᵒᵖ M]

/-- If an actual retract has zero balanced tensor, each coefficient of
its free-module projector annihilates the left module. This is the tensor
to matrix bridge; no annihilator or projector coefficient is assumed. -/
theorem retract_tensor_zero_projector_coefficient
    (i : M →ₗ[Aᵐᵒᵖ] (I →₀ Aᵐᵒᵖ))
    (p : (I →₀ Aᵐᵒᵖ) →ₗ[Aᵐᵒᵖ] M)
    [Subsingleton (BalancedTensor.Tensor k A M N)] (a b : I) (n : N) :
    ((i.comp p) (Finsupp.single a 1) b).unop • n = 0 := by
  have hz : BalancedTensor.mk k A M N (p (Finsupp.single a 1)) n = 0 :=
    Subsingleton.elim _ _
  have hm := congrArg (BalancedTensor.mapLeft (k := k) N i) hz
  rw [BalancedTensor.mapLeft_mk, map_zero] at hm
  have he := congrArg (fun z =>
    (BalancedTensor.Free.evaluation (k := k) I N z) b) hm
  simpa only [free_tensor_evaluation_coordinate, map_zero, Finsupp.zero_apply,
    LinearMap.comp_apply] using he

end
end Note198
