import Note198.MainPacket
import Note198.BarSplitting
import Note198.GenericPDDetection

/-! # Principal results for collaborators

Each declaration below displays its full conclusion and invokes its original
proof. Theorem 1.1, with all fifteen main-property fields expanded, is in
`Note198.CollaboratorMain`. The names here retain the manuscript numbering.
-/
namespace Note198.Collaborator
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
attribute [local instance] HasDerivedCategory.standard
universe u

/-- The complex-field family: dimensions, scalar endomorphisms, and cross-Hom vanishing. -/
theorem theorem_1_1_complex (m : ℕ+) :
    SelectingMain.MainProperties ComplexBrickFamily.encoding
      ComplexBrickFamily.selection.toEndomorphism ComplexBrickFamily.family ∧
    Module.finrank ℂ (ComplexBrickFamily.M m) = 3*2^(3*m.val) ∧
    Nonempty (ℂ ≃ₐ[ℂ] Module.End ComplexBrickFamily.A (ComplexBrickFamily.M m)) ∧
    (∀ n : ℕ+, m ≠ n → ∀ f : ComplexBrickFamily.M m →ₗ[ComplexBrickFamily.A]
      ComplexBrickFamily.M n, f=0) :=
  ⟨SelectingMain.main_properties _ _ _,ComplexBrickFamily.complex_bricks m⟩

/-- For each odd integer s >= 3, one bounded projective bimodule complex
works for every finite-dimensional input Y. -/
theorem proposition_7_3
    {k R : Type u} [Field k] [Ring R] [Algebra k R]
    (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
    (s : ℤ) (hs : 3 ≤ s) (hodd : Odd s) :
    ∃ P : ExternalTensor.Section4.BiComplex k (QuadraticEncoding.B E.relations),
      (∃ lo hi : ℤ, ∀ n, n < lo ∨ hi < n → IsZero (P.X n)) ∧
      (∀ n, Projective (P.X n)) ∧
      (∀ n, FiniteDimensional k ((ExternalTensor.Section4.forgetK k
        (QuadraticEncoding.B E.relations)).obj (P.X n))) ∧
      ∀ (Y : Type u) [AddCommGroup Y] [Module k Y] [Module R Y]
        [IsScalarTower k R Y] [FiniteDimensional k Y],
        Nonempty (DerivedCategory.Q.obj
          (((BimoduleBalancedTensor.functor k (QuadraticEncoding.B E.relations)
            (GenericOddRealization.input (E := E) (Y := Y))).mapHomologicalComplex (.up ℤ)).obj P) ≅
          (DerivedCategory.singleFunctor (ModuleCat (QuadraticEncoding.B E.relations)) 0).obj
            (GenericOddRealization.reference (E := E) (S := S) (Y := Y)) ⊞
          ((DerivedCategory.singleFunctor (ModuleCat (QuadraticEncoding.B E.relations)) 0).obj
            (GenericOddRealization.reference (E := E) (S := S) (Y := Y)))⟦s⟧) :=
  fixed_selecting_complex_all_odd E S s hs hodd

/-- Exact projective dimension of the constructed family; both summand
types and every finite index are displayed. -/
theorem exact_module_projective_dimension
    {k R : Type u} [Field k] [Ring R] [Algebra k R]
    (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
    (F : SelectingBrickFamily.SourceFamily k R S) (m : ℕ+) :
    projectiveDimension (ModuleCat.of (SelectingOrdinaryAlgebra.A E S)
      (SelectingBrickFamily.module E S F m)) =
      ⨆ i : Sum (Fin m.val) (Fin m.val), match i with
        | .inl j => (((SelectingFamilyMaximum.coefficient E S+5)*j.val : ℕ) : WithBot ℕ∞) +
            projectiveDimension (SelectingOrdinaryOddSplit.input E
              (((SelectingIteration.selected S)^[j.val]) (SelectingFamilyFiniteBar.source F m)))
        | .inr j => (((SelectingFamilyMaximum.coefficient E S+5)*j.val+1 : ℕ) : WithBot ℕ∞) +
            projectiveDimension (SelectingOrdinaryOddSplit.Qmodule E S
              (((SelectingIteration.selected S)^[j.val]) (SelectingFamilyFiniteBar.source F m))) :=
  SelectingFamilyExactFormula.brick_exact_formula E S F m

/-- The same general-field construction supplies the main properties and
all seven asymmetry clauses. The main-property fields are expanded in
`CollaboratorMain`. -/
theorem main_and_corollary_8_1 (k : Type u) [Field k] :
    ∃ (R : Type u) (rR : Ring R), letI : Ring R := rR
      ∃ aR : Algebra k R, letI : Algebra k R := aR
        ∃ (S : Selection.Data k R) (E : SelectionEncoding.Encoding k R)
          (F : SelectingBrickFamily.SourceFamily k R S.toEndomorphism),
          SelectingMain.MainProperties E S.toEndomorphism F ∧
          FiniteDimensional k (SelectingAsymmetry.Lambda E S.toEndomorphism) ∧
          littleFinitisticDimension (SelectingAsymmetry.Lambda E S.toEndomorphism)=⊤ ∧
          bigFinitisticDimension (SelectingAsymmetry.Lambda E S.toEndomorphism)=⊤ ∧
          littleFinitisticDimension (SelectingAsymmetry.Lambda E S.toEndomorphism)ᵐᵒᵖ=0 ∧
          bigFinitisticDimension (SelectingAsymmetry.Lambda E S.toEndomorphism)ᵐᵒᵖ=0 ∧
          ¬ InjectivesGenerate (SelectingAsymmetry.Lambda E S.toEndomorphism) ∧
          InjectivesGenerate (SelectingAsymmetry.Lambda E S.toEndomorphism)ᵐᵒᵖ :=
  SelectingMain.every_field_with_asymmetry k

/-- General-field version of Corollary 8.1 for the fixed construction.
The manuscript specializes to the complex field; the opposite-algebra
conventions and all seven conclusions are displayed here. -/
theorem corollary_8_1
    {k R : Type u} [Field k] [Ring R] [Algebra k R]
    (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
    (F : SelectingBrickFamily.SourceFamily k R S) :
    FiniteDimensional k (SelectingAsymmetry.Lambda E S) ∧
    littleFinitisticDimension (SelectingAsymmetry.Lambda E S)=⊤ ∧
    bigFinitisticDimension (SelectingAsymmetry.Lambda E S)=⊤ ∧
    littleFinitisticDimension (SelectingAsymmetry.Lambda E S)ᵐᵒᵖ=0 ∧
    bigFinitisticDimension (SelectingAsymmetry.Lambda E S)ᵐᵒᵖ=0 ∧
    ¬ InjectivesGenerate (SelectingAsymmetry.Lambda E S) ∧
    InjectivesGenerate (SelectingAsymmetry.Lambda E S)ᵐᵒᵖ :=
  SelectingMain.asymmetry E S F

end
end Note198.Collaborator

namespace Note198.Collaborator.Bar
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.DerivedBar TrivSqZeroExt
open OAI.DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
attribute [local instance] OAI.DerivedBar.derivedTensorBarSplittingHasDerivedCategory

/-- Proposition 6.1: base change for the square-zero extension is the
coproduct of all shifted tensor iterates. The original diagram records its
nonnegative index and cohomological shift conventions. -/
theorem proposition_6_1 (N : ModuleCat.{u} D) :
    Nonempty ((derivedBaseChange D (fstHom k D X)).obj
      (@ModuleCat.of (TrivSqZeroExt D X) inferInstance N inferInstance
        (inflatedModule D X N)) ≅
      colimit (ParityBridge.shiftedIterateDiagram k D X N)) :=
  Note198.square_zero_derived_bar_splitting k D X N

end
end Note198.Collaborator.Bar

namespace Note198.Collaborator.Detection
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
open Note198.ComplexProjectiveDimension Note198.ComplexStupidTruncation
attribute [local instance] HasDerivedCategory.standard
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable [FiniteDimensional k D] [FiniteDimensional k X]
local instance (N : ModuleCat.{u} D) : Module k N :=
  DerivedBar.BimoduleTensor.scalarModule k D N
local instance (N : ModuleCat.{u} D) : IsScalarTower k D N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance (N : ModuleCat.{u} D) : Module (TrivSqZeroExt D X) N :=
  DerivedBar.ParityBridge.inflatedModule D X N
local instance (N : ModuleCat.{u} D) : IsScalarTower k (TrivSqZeroExt D X) N :=
  IsScalarTower.of_algebraMap_smul (fun a v => IsScalarTower.algebraMap_smul D a v)

/-- Corollary 6.2: extinction implies finite projective dimension, and
survival at index r gives the lower bound r. The supremum in hD is over
all left D-modules. -/
theorem corollary_6_2
    (hD : (⨆ M : ModuleCat.{u} D, projectiveDimension M) < ⊤)
    (N : ModuleCat.{u} D) [FiniteDimensional k N] :
    (∀ t : ℕ, IsZero (GenericFiniteBar.iterate k D X N t) →
      projectiveDimension (ModuleCat.of (TrivSqZeroExt D X) N) < ⊤) ∧
    (∀ r : ℕ, ¬ IsZero (GenericFiniteBar.iterate k D X N r) →
      (r:ℕ) ≤ projectiveDimension (ModuleCat.of (TrivSqZeroExt D X) N)) :=
  Note198.GenericPDDetection.detection_of_finite_global_dimension k D X hD N

end
end Note198.Collaborator.Detection

namespace Note198.Collaborator.Dimension
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
open Note198.ComplexProjectiveDimension Note198.ComplexStupidTruncation
attribute [local instance] HasDerivedCategory.standard
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable [FiniteDimensional k D] [FiniteDimensional k X]
local instance (N : ModuleCat.{u} D) : Module k N :=
  DerivedBar.BimoduleTensor.scalarModule k D N
local instance (N : ModuleCat.{u} D) : IsScalarTower k D N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance (N : ModuleCat.{u} D) : Module (TrivSqZeroExt D X) N :=
  DerivedBar.ParityBridge.inflatedModule D X N
local instance (N : ModuleCat.{u} D) : IsScalarTower k (TrivSqZeroExt D X) N :=
  IsScalarTower.of_algebraMap_smul (fun a v => IsScalarTower.algebraMap_smul D a v)

/-- Proposition 6.3: signed projective dimension is the supremum of the
shifted iterate dimensions for r < t. The value type includes both infinities;
the zero module and the empty index set t = 0 retain the value bottom. -/
theorem proposition_6_3
    (hD : (⨆ M : ModuleCat.{u} D, projectiveDimension M) < ⊤)
    (N : ModuleCat.{u} D) [FiniteDimensional k N]
    (t : ℕ) (ht : IsZero (GenericFiniteBar.iterate k D X N t)) :
    ComplexResidueBaseChange.signedModuleProjectiveDimension
      (ModuleCat.of (TrivSqZeroExt D X) N) =
      ⨆ r : Fin t,
        signedProjectiveDimension (GenericFiniteBar.iterate k D X N r) +
          ((((r.val:ℤ):WithTop ℤ):WithBot (WithTop ℤ))) :=
  Note198.GenericExactDimension.exact_projective_dimension_of_finite_global_dimension
    k D X hD N t ht

end
end Note198.Collaborator.Dimension

