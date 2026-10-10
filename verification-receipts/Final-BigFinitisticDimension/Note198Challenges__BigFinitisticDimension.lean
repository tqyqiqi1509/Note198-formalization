import OAI.Algebra.Finitistic.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Finiteness.Basic

namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
variable (A : Type u) [Ring A]

/-- The big finitistic dimension ranges over all modules in the fixed
universe, retaining only those of finite projective dimension. -/
def bigFinitisticDimension : WithBot ℕ∞ :=
  ⨆ (M : ModuleCat.{u} A) (_ : projectiveDimension M < ⊤), projectiveDimension M

theorem le_bigFinitisticDimension (M : ModuleCat.{u} A)
    (h : projectiveDimension M < ⊤) :
    projectiveDimension M ≤ bigFinitisticDimension A := by
  sorry

theorem little_le_big :
    OAI.LittleFinitistic.littleFinitisticDimension A ≤ bigFinitisticDimension A := by
  sorry

theorem big_eq_top_of_little_eq_top
    (h : OAI.LittleFinitistic.littleFinitisticDimension A = ⊤) :
    bigFinitisticDimension A = ⊤ := by
  sorry

/-- The regular nonzero projective module gives the lower endpoint zero.
The premise applies to all modules, including infinitely generated ones. -/
theorem both_eq_zero_of_finite_pd_projective [Nontrivial A]
    (h : ∀ M : ModuleCat.{u} A, projectiveDimension M < ⊤ → Projective M) :
    OAI.LittleFinitistic.littleFinitisticDimension A = 0 ∧
      bigFinitisticDimension A = 0 := by
  sorry

end
end Note198
