import Note198.GenericExactDimension
import OAI.Algebra.Finitistic.Bar.CountRetracts

namespace Note198.GenericPDDetection
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
open Note198.ComplexProjectiveDimension Note198.ComplexStupidTruncation
attribute [local instance] HasDerivedCategory.standard
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable [FiniteDimensional k D] [FiniteDimensional k X]
local instance instModuleCarrier_note198 (N : ModuleCat.{u} D) : Module k N :=
  DerivedBar.BimoduleTensor.scalarModule k D N
local instance instIsScalarTowerCarrier_note198 (N : ModuleCat.{u} D) : IsScalarTower k D N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance instModuleTrivSqZeroExtCarrier_note198 (N : ModuleCat.{u} D) : Module (TrivSqZeroExt D X) N :=
  DerivedBar.ParityBridge.inflatedModule D X N
local instance instIsScalarTowerTrivSqZeroExtCarrier_note198 (N : ModuleCat.{u} D) : IsScalarTower k (TrivSqZeroExt D X) N :=
  IsScalarTower.of_algebraMap_smul (fun a v => IsScalarTower.algebraMap_smul D a v)

/-- Every nonzero actual derived iterate gives the general lower bound,
even when A-module projective dimension is infinite. The actual count
summand is retained as a retract of the native base change. -/
theorem lower_bound_of_survival (N : ModuleCat.{u} D) [FiniteDimensional k N]
    (r : ℕ) (h : ¬ IsZero (GenericFiniteBar.iterate k D X N r)) :
    (r:ℕ) ≤ projectiveDimension (ModuleCat.of (TrivSqZeroExt D X) N) := by
  sorry

variable (g : ℕ) (hg : ∀ M : ModuleCat.{u} D, HasProjectiveDimensionLE M g)

include g hg in
/-- Actual tensor extinction gives finite pd over the actual square-zero
extension, for every finite module N. X is not assumed projective. -/
theorem finite_pd_of_extinction (N : ModuleCat.{u} D) [FiniteDimensional k N]
    (t : ℕ) (ht : IsZero (GenericFiniteBar.iterate k D X N t)) :
    projectiveDimension (ModuleCat.of (TrivSqZeroExt D X) N) < ⊤ := by
  sorry

/-- The entire general Corollary 6.2, with literal finite global
dimension and no chosen g/hg or derived-resolution certificate. The
manuscript's two-sided finite global dimension implies the left-sided
hypothesis here. The lower bound allows infinite A-module pd. -/
theorem detection_of_finite_global_dimension
    (hD : (⨆ M : ModuleCat.{u} D, projectiveDimension M) < ⊤)
    (N : ModuleCat.{u} D) [FiniteDimensional k N] :
    (∀ t : ℕ, IsZero (GenericFiniteBar.iterate k D X N t) →
      projectiveDimension (ModuleCat.of (TrivSqZeroExt D X) N) < ⊤) ∧
    (∀ r : ℕ, ¬ IsZero (GenericFiniteBar.iterate k D X N r) →
      (r:ℕ) ≤ projectiveDimension (ModuleCat.of (TrivSqZeroExt D X) N)) := by
  sorry

end
end Note198.GenericPDDetection

