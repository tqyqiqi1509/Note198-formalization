import Note198.GenericFiniteBar
import Note198.FiniteGlobalDimensionNormalization

namespace Note198.GenericExactDimension
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
variable (g : ℕ) (hg : ∀ M : ModuleCat.{u} D, HasProjectiveDimensionLE M g)

include g hg in
/-- Original Proposition 6.3: actual module projective dimension, embedded in
signed extended integers, equals the maximum of shifted actual derived
iterate dimensions. It includes the zero module and the empty surviving
prefix, and imposes no projectivity assumption on X. -/
theorem exact_projective_dimension (N : ModuleCat.{u} D) [FiniteDimensional k N]
    (t : ℕ) (ht : IsZero (GenericFiniteBar.iterate k D X N t)) :
    ComplexResidueBaseChange.signedModuleProjectiveDimension
      (ModuleCat.of (TrivSqZeroExt D X) N) =
      ⨆ r : Fin t,
        signedProjectiveDimension (GenericFiniteBar.iterate k D X N r) +
          ((((r.val:ℤ):WithTop ℤ):WithBot (WithTop ℤ))) := by
  sorry

/-- Proposition 6.3 with literal finite global dimension instead of a
chosen numerical bound. The left global dimension suffices, so the
manuscript's two-sided finite-global-dimension assumption specializes
directly. Zero inputs and empty surviving prefixes are retained. -/
theorem exact_projective_dimension_of_finite_global_dimension
    (hD : (⨆ M : ModuleCat.{u} D, projectiveDimension M) < ⊤)
    (N : ModuleCat.{u} D) [FiniteDimensional k N]
    (t : ℕ) (ht : IsZero (GenericFiniteBar.iterate k D X N t)) :
    ComplexResidueBaseChange.signedModuleProjectiveDimension
      (ModuleCat.of (TrivSqZeroExt D X) N) =
      ⨆ r : Fin t,
        signedProjectiveDimension (GenericFiniteBar.iterate k D X N r) +
          ((((r.val:ℤ):WithTop ℤ):WithBot (WithTop ℤ))) := by
  sorry

end
end Note198.GenericExactDimension


