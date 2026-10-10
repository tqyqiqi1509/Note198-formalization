import Note198.FiniteTailCoproduct
import Note198.NativeBaseChangeDetection
import Note198.ComplexFiniteBarDimension
import OAI.Algebra.Finitistic.Iteration.IntegerIterateExtinction
import OAI.Algebra.Finitistic.Iteration.FiniteIntegerIterate

namespace Note198.GenericFiniteBar
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
open Note198.ComplexProjectiveDimension Note198.ComplexStupidTruncation
attribute [local instance] HasDerivedCategory.standard
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance (N : ModuleCat.{u} D) : Module k N :=
  DerivedBar.BimoduleTensor.scalarModule k D N
local instance (N : ModuleCat.{u} D) : IsScalarTower k D N :=
  IsScalarTower.of_algebraMap_smul (R := k) (A := D) (M := N)
    (fun _ _ => rfl)
local instance (N : ModuleCat.{u} D) : Module (TrivSqZeroExt D X) N :=
  DerivedBar.ParityBridge.inflatedModule D X N
local instance (N : ModuleCat.{u} D) : IsScalarTower k (TrivSqZeroExt D X) N :=
  IsScalarTower.of_algebraMap_smul (R := k) (A := TrivSqZeroExt D X) (M := N)
    (fun a v => IsScalarTower.algebraMap_smul D a v)

abbrev iterate (N : ModuleCat.{u} D) (r : ℕ) :=
  DerivedBar.IterateSupport.object k D X N r
abbrev count (N : ModuleCat.{u} D) (r : ℕ) := (iterate k D X N r)⟦(r:ℤ)⟧

/-- Arbitrary finite-dimensional square-zero extensions, with their actual
bar-derived powers. No projectivity assumption on X is imposed. -/
theorem finite_bar (N : ModuleCat.{u} D) (t : ℕ)
    (ht : IsZero (iterate k D X N t)) :
    Nonempty (DerivedCategory.Q.obj
      (ComplexResidueBaseChange.bar (TrivSqZeroExt.fstHom k D X) N) ≅
      (⨁ fun r : Fin t => count k D X N r)) := by
  letI : HasColimit (Discrete.functor (count k D X N)) := by
    change HasColimit (DerivedBar.ParityBridge.shiftedIterateDiagram k D X N)
    infer_instance
  let e := (NativeBaseChangeDetection.barComparison
    (TrivSqZeroExt.fstHom k D X) N).symm ≪≫
    DerivedBar.ParityBridge.derivedTensorBarSplitting k D X N
  exact ⟨e ≪≫ (FiniteTailCoproduct.iso (count k D X N) t
    (fun r hr => (shiftFunctor _ (r:ℤ)).map_isZero
      (DerivedBar.IterateSupport.zero_of_le k D X N t r hr ht))).symm⟩

variable [FiniteDimensional k D] [FiniteDimensional k X]
variable (g : ℕ) (hg : ∀ M : ModuleCat.{u} D, HasProjectiveDimensionLE M g)

include g hg in
/-- Finite cohomology and its bounded window are proved on every actual
derived iterate; a bounded finite projective representative is then built. -/
theorem iterate_boundedFinite (N : ModuleCat.{u} D) [FiniteDimensional k N] (r : ℕ) :
    InBoundedFiniteDerived (iterate k D X N r) := by
  have hlow := DerivedBar.IterateSupport.isGE_bound k D X g hg N r
  haveI := hlow
  exact ComplexCohomologyModels.finite_dimensional_cohomology_in_bounded_finite_derived
    (k:=k) g hg (iterate k D X N r) (-((r*(g+2):ℕ):ℤ)) 0
    (fun n => DerivedBar.IterateSupport.cohomology_finite k D X N r n)
    (fun n hn => hn.elim
      (fun h => DerivedCategory.isZero_of_isGE _ _ n h)
      (fun h => DerivedCategory.isZero_of_isLE _ 0 n h))

include g hg in
/-- The exact finite maximum is proved for the actual signed dimension of
base change, including bottom values of zero iterates. -/
theorem signed_base_max (N : ModuleCat.{u} D) [FiniteDimensional k N] (t : ℕ)
    (ht : IsZero (iterate k D X N t)) :
    signedProjectiveDimension (DerivedCategory.Q.obj
      (ComplexResidueBaseChange.bar (TrivSqZeroExt.fstHom k D X) N)) =
      ⨆ r : Fin t, signedProjectiveDimension (iterate k D X N r) +
        ((((r.val:ℤ):WithTop ℤ):WithBot (WithTop ℤ))) := by
  letI : FiniteDimensional k (TrivSqZeroExt D X) :=
    inferInstanceAs (FiniteDimensional k (D × X))
  exact ComplexFiniteBarDimension.signed_base_finite_max g hg
    (TrivSqZeroExt.fstHom k D X) N t (fun r => iterate k D X N r)
    (fun r => (r.val:ℤ)) (fun r => iterate_boundedFinite k D X g hg N r)
    (Classical.choice (finite_bar k D X N t ht))

end
end Note198.GenericFiniteBar
