import Note198.SelectingOrdinaryBarComparison
import Note198.FiniteTailCoproduct
import Note198.BarSplitting
import Note198.NativeBaseChangeDetection
import Note198.ComplexResidueBaseChange
import OAI.Algebra.Finitistic.Iteration.IntegerIterateExtinction

namespace Note198.SelectingFiniteBar
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
attribute [local instance] HasDerivedCategory.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
open SelectingOrdinaryAlgebra
local instance (N : ModuleCat.{u} (D E S)) : Module k N :=
  DerivedBar.BimoduleTensor.scalarModule k (D E S) N
local instance (N : ModuleCat.{u} (D E S)) : IsScalarTower k (D E S) N :=
  IsScalarTower.of_algebraMap_smul (R := k) (A := D E S) (M := N)
    (fun _ _ => rfl)
local instance (N : ModuleCat.{u} (D E S)) : Module (A E S) N :=
  DerivedBar.ParityBridge.inflatedModule (D E S) (X E S) N
local instance (N : ModuleCat.{u} (D E S)) : IsScalarTower k (A E S) N :=
  IsScalarTower.of_algebraMap_smul (R := k) (A := A E S) (M := N)
    (fun a v => IsScalarTower.algebraMap_smul (D E S) a v)

abbrev count (N : ModuleCat.{u} (D E S)) (r : ℕ) :=
  (DerivedBar.IterateSupport.object k (D E S) (X E S) N r)⟦(r:ℤ)⟧

/-- Actual tensor extinction, checked using the finite right-projective
ordinary model, kills the original bar counts from that index onwards. -/
theorem tail_zero (N : ModuleCat.{u} (D E S)) (t r : ℕ) (htr : t ≤ r)
    (h : IsZero (((SelectingOrdinarySimulation.ordinary E S).obj^[t])
      ((DerivedCategory.singleFunctor (ModuleCat (D E S)) 0).obj N))) :
    IsZero (count E S N r) := by
  have ht := (Classical.choice
    (SelectingOrdinaryBarComparison.ordinary_stalk_bar E S N t)).isZero_iff.mp h
  exact (shiftFunctor _ (r:ℤ)).map_isZero
    (DerivedBar.IterateSupport.zero_of_le k (D E S) (X E S) N t r htr ht)

/-- The genuine base change over the actual square-zero algebra is a finite
direct sum of the original shifted bar iterates when extinction occurs.
The extinction condition is the actual ordinary tensor functor, rather
than an assumed bar comparison or a list of numerical dimensions. -/
theorem finite_bar_splitting (N : ModuleCat.{u} (D E S)) (t : ℕ)
    (h : IsZero (((SelectingOrdinarySimulation.ordinary E S).obj^[t])
      ((DerivedCategory.singleFunctor (ModuleCat (D E S)) 0).obj N))) :
    Nonempty ((DerivedBar.derivedBaseChange (D E S)
      (TrivSqZeroExt.fstHom k (D E S) (X E S))).obj
      (@ModuleCat.of (A E S) inferInstance N inferInstance
        (DerivedBar.ParityBridge.inflatedModule (D E S) (X E S) N)) ≅
      (⨁ fun i : Fin t => count E S N i)) := by
  letI : HasColimit (Discrete.functor (count E S N)) := by
    change HasColimit (DerivedBar.ParityBridge.shiftedIterateDiagram k (D E S) (X E S) N)
    infer_instance
  let e := DerivedBar.ParityBridge.derivedTensorBarSplitting
    k (D E S) (X E S) N
  exact ⟨e ≪≫ (FiniteTailCoproduct.iso (count E S N) t
    (fun r hr => tail_zero E S N t r hr h)).symm⟩

/-- The same finite decomposition on the concrete integer bar model used
by the signed projective-dimension theorem. -/
theorem finite_bar_model (N : ModuleCat.{u} (D E S)) (t : ℕ)
    (h : IsZero (((SelectingOrdinarySimulation.ordinary E S).obj^[t])
      ((DerivedCategory.singleFunctor (ModuleCat (D E S)) 0).obj N))) :
    Nonempty (DerivedCategory.Q.obj
      (ComplexResidueBaseChange.bar
        (TrivSqZeroExt.fstHom k (D E S) (X E S)) N) ≅
      (⨁ fun i : Fin t => count E S N i)) := by
  exact ⟨(NativeBaseChangeDetection.barComparison
    (TrivSqZeroExt.fstHom k (D E S) (X E S)) N).symm ≪≫
    Classical.choice (finite_bar_splitting E S N t h)⟩

end
end Note198.SelectingFiniteBar
