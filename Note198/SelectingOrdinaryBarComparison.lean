import Note198.SelectingOrdinarySimulation
import OAI.Algebra.Finitistic.Bimodule.BimoduleBarTensorComparison
import OAI.Algebra.Finitistic.Bar.BarBimoduleCongruence
import OAI.Algebra.Finitistic.Bimodule.BimoduleResolutionBarAPI
import OAI.Algebra.Finitistic.Bimodule.BimoduleShiftedPresentation
import OAI.Algebra.Finitistic.Iteration.FunctorObjectIteration
import OAI.Algebra.Finitistic.Iteration.IntegerIterateSupport

namespace Note198.SelectingOrdinaryBarComparison
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor OAI OAI.LittleFinitistic
attribute [local instance] HasDerivedCategory.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
open SelectingOrdinaryAlgebra

abbrev complex := OrdinarySimulation.XResolution.complex
  (SelectingRectification.bimodule E S) (a E S) (length E S)
abbrev target := OrdinarySimulation.XResolution.ordinaryXObject
  (SelectingRectification.bimodule E S) (a E S) (length E S)
abbrev augmentation := OrdinarySimulation.XResolution.augmentationToX
  (SelectingRectification.bimodule E S) (a E S) (length E S)

theorem augmentation_quasiIso : QuasiIso (augmentation E S) :=
  OrdinarySimulation.XResolution.augmentationToX_quasiIso
    (SelectingRectification.bimodule E S) (a E S) (length E S)

theorem right_projective (n : ℤ) : Module.Projective (D E S)ᵐᵒᵖ
    (BimoduleCoefficients k (D E S) (D E S) ((complex E S).X n)) :=
  OrdinarySimulation.XResolution.right_projective
    (SelectingRectification.bimodule E S) (a E S) (length E S) n

theorem bounded (n : ℤ) (hn : n < -(length E S : ℤ) ∨ 0 < n) :
    IsZero ((complex E S).X n) :=
  OrdinarySimulation.XResolution.vanishes
    (SelectingRectification.bimodule E S) (a E S) (length E S) n hn

def resolution := BimoduleTotal.ofNonpositiveResolution
  (complex E S) (target E S) (length E S)
  (augmentation E S) (augmentation_quasiIso E S)
  (fun n => right_projective E S n) (bounded E S)

abbrev native := (resolution E S).data.derived
abbrev comparisonX := BimoduleBarComparison.Actions k (D E S) (target E S)

def rightEquiv : comparisonX E S ≃ₗ[(D E S)ᵐᵒᵖ] X E S :=
  RetainedBimodule.rightEquiv k (D E S) (D E S) (X E S)

theorem left_action (d : D E S) (x : comparisonX E S) :
    rightEquiv E S (d • x) = d • rightEquiv E S x :=
  RetainedBimodule.rightEquiv_left k (D E S) (D E S) (X E S) d x

def leftEquiv : comparisonX E S ≃ₗ[D E S] X E S where
  toFun := rightEquiv E S
  invFun := (rightEquiv E S).symm
  left_inv := (rightEquiv E S).left_inv
  right_inv := (rightEquiv E S).right_inv
  map_add' := (rightEquiv E S).map_add
  map_smul' := left_action E S

theorem right_action (d : (D E S)ᵐᵒᵖ) (x : comparisonX E S) :
    leftEquiv E S (d • x) = d • leftEquiv E S x :=
  (rightEquiv E S).map_smul d x

def ordinaryNativeIso : SelectingOrdinarySimulation.ordinary E S ≅ native E S := by
  letI : ∀ n, Module.Projective (D E S)ᵐᵒᵖ
      (ComplexTensor.rightTerm k (D E S) (BimoduleTotal.right k (D E S) (complex E S)) n) :=
    fun n => right_projective E S n
  exact BimoduleTotalPresentation.boundedNonpositiveDerivedIso k (D E S) (complex E S)
    (resolution E S).data (length E S) rfl rfl

/-- The actual augmentation and both exterior actions identify the finite
right-projective model with bar-derived tensor by the original X. -/
def powerIso (N : ModuleCat.{u} (D E S)) (r : ℕ) :
    ((native E S).obj^[r])
      (DerivedCategory.Q.obj (BimoduleTotal.singleInput (D E S) N)) ≅
      DerivedBar.IterateSupport.object k (D E S) (X E S) N r :=
  BimoduleTotal.nonpositiveResolutionPowerIso
    (complex E S) (target E S) (length E S)
    (augmentation E S) (augmentation_quasiIso E S)
    (fun n => right_projective E S n) (bounded E S) N r ≪≫
  (DerivedBar.integerDerivedIterateIndexedIso (D E S) k (comparisonX E S) N r).symm ≪≫
  (DerivedBar.chainToIntegerDerived (D E S)).mapIso
    ((DerivedBar.BimoduleTensor.derivedIterateCongr k (D E S)
      (leftEquiv E S) (right_action E S) r).app
      ((DerivedBar.chainQ (D E S)).obj
        ((ChainComplex.single₀ (ModuleCat (D E S))).obj N)))

/-- All powers of the actual ordinary derived functor agree with the
original-X bar powers on every actual stalk module. -/
theorem ordinary_stalk_bar (N : ModuleCat.{u} (D E S)) (r : ℕ) :
    Nonempty ((((SelectingOrdinarySimulation.ordinary E S).obj^[r])
      ((DerivedCategory.singleFunctor (ModuleCat (D E S)) 0).obj N)) ≅
      DerivedBar.IterateSupport.object k (D E S) (X E S) N r) := by
  exact ⟨functorObjectIteration (ordinaryNativeIso E S) r _ ≪≫
    mapObjectIteration (native E S)
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat (D E S)) 0).app N) r ≪≫
    powerIso E S N r⟩

end
end Note198.SelectingOrdinaryBarComparison
