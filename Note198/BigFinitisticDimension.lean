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
  exact le_iSup_of_le M (le_iSup_of_le h le_rfl)

theorem little_le_big :
    OAI.LittleFinitistic.littleFinitisticDimension A ≤ bigFinitisticDimension A := by
  unfold OAI.LittleFinitistic.littleFinitisticDimension
  refine iSup_le fun M => iSup_le fun _ => iSup_le fun h => ?_
  exact le_bigFinitisticDimension A M h

theorem big_eq_top_of_little_eq_top
    (h : OAI.LittleFinitistic.littleFinitisticDimension A = ⊤) :
    bigFinitisticDimension A = ⊤ := by
  exact top_le_iff.mp (h ▸ little_le_big A)

/-- The regular nonzero projective module gives the lower endpoint zero.
The premise applies to all modules, including infinitely generated ones. -/
theorem both_eq_zero_of_finite_pd_projective [Nontrivial A]
    (h : ∀ M : ModuleCat.{u} A, projectiveDimension M < ⊤ → Projective M) :
    OAI.LittleFinitistic.littleFinitisticDimension A = 0 ∧
      bigFinitisticDimension A = 0 := by
  letI : Module.Projective A (ModuleCat.of A A) :=
    inferInstanceAs (Module.Projective A A)
  letI : Module.Finite A (ModuleCat.of A A) :=
    inferInstanceAs (Module.Finite A A)
  have hupper : bigFinitisticDimension A ≤ 0 := by
    refine iSup_le fun M => iSup_le fun hM => ?_
    letI := h M hM
    exact Projective.projectiveDimension_le_zero M
  have hregular : projectiveDimension (ModuleCat.of A A) = 0 := by
    apply (projectiveDimension_eq_zero_iff (ModuleCat.of A A)).mpr
    refine ⟨inferInstance, ?_⟩
    intro hz
    letI : Subsingleton A := ModuleCat.subsingleton_of_isZero hz
    exact (zero_ne_one : (0 : A) ≠ 1) (Subsingleton.elim 0 1)
  have hfinite : projectiveDimension (ModuleCat.of A A) < ⊤ := by
    rw [hregular]
    exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top 0)
  have hlower : 0 ≤ OAI.LittleFinitistic.littleFinitisticDimension A := by
    rw [← hregular]
    exact OAI.LittleFinitistic.le_littleFinitisticDimension A _ hfinite
  have hbig : bigFinitisticDimension A = 0 :=
    le_antisymm hupper (hlower.trans (little_le_big A))
  exact ⟨le_antisymm ((little_le_big A).trans hupper) hlower, hbig⟩

end
end Note198
