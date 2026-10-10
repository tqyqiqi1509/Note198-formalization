import Note198.SelectingIteration
import Note198.SelectingOrdinaryAlgebra
import OAI.Algebra.Finitistic.Ordinary.OrdinaryShiftDerivedTensor
import OAI.Algebra.Finitistic.Bimodule.BimoduleShiftedPresentation

set_option maxHeartbeats 0

namespace Note198.SelectingShiftedRealization
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
attribute [local instance] HasDerivedCategory.standard HasExt.standard
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
open SelectingOrdinaryAlgebra SelectingIteration

abbrev shifted := (SelectingRectification.bimodule E S)⟦b E S⟧

def model : BimoduleTotal.BoundedProjective k (QuadraticEncoding.B E.relations)
    (shifted E S) where
  lower := -(length E S : ℤ)
  upper := 0
  bounded := OrdinarySimulation.shifted_support _ (b E S) (length E S)
    (a E S) (endpoints E S) (support E S)
  projective n := SelectingOrdinaryAlgebra.term_projective E S (n + b E S)

abbrev G := (model E S).derived

local instance (Y : Family (k := k) (R := R)) : Module k Y.val :=
  Module.compHom Y.val (algebraMap k R)
local instance (Y : Family (k := k) (R := R)) : IsScalarTower k R Y.val :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance (Y : Family (k := k) (R := R)) : FiniteDimensional k Y.val := Y.property

def comparison (Y : Family (k := k) (R := R)) :
    (G E S).obj (evaluation E Y) ≅
      (SelectingTensorSplitting.object (enc := E) (S := S)
        (SelectingRealization.input (E := E) (Y := Y.val)))⟦b E S⟧ :=
  (model E S).nativeSingleEvaluation (SelectingRealization.input (E := E) (Y := Y.val)) ≪≫
    DerivedCategory.Q.mapIso
      ((((BimoduleBalancedTensor.functor k (QuadraticEncoding.B E.relations)
        (SelectingRealization.input (E := E) (Y := Y.val))).mapHomologicalComplex
          (.up ℤ)).commShiftIso (b E S)).app (SelectingRectification.bimodule E S)) ≪≫
    (DerivedCategory.Q.commShiftIso (b E S)).app _

def realizationNested (Y : Family (k := k) (R := R)) :
    (G E S).obj (evaluation E Y) ≅
      (evaluation E (selected S Y))⟦b E S⟧ ⊞
      ((evaluation E (selected S Y))⟦(3 : ℤ)⟧)⟦b E S⟧ :=
  comparison E S Y ≪≫ (shiftFunctor _ (b E S)).mapIso
    (SelectingRealization.realization (E := E) (S := S) (Y := Y.val)) ≪≫
    (shiftFunctor _ (b E S)).mapBiprod _ _

def realization (Y : Family (k := k) (R := R)) :
    (G E S).obj (evaluation E Y) ≅
      (evaluation E (selected S Y))⟦b E S⟧ ⊞
      (evaluation E (selected S Y))⟦b E S + 3⟧ :=
  realizationNested E S Y ≪≫ biprod.mapIso (Iso.refl _)
    ((shiftAdd _ (3 : ℤ) (b E S)).symm ≪≫
      eqToIso (by rw [add_comm (3 : ℤ) (b E S)]))

/-- Both presentations compute the same actual shifted derived tensor. -/
theorem native_shifted_comparison : Nonempty (
    OrdinarySimulation.shiftedDerivedTensor (SelectingRectification.bimodule E S)
      (b E S) (length E S) ≅ G E S) :=
  ⟨BimoduleTotalPresentation.shiftedDerivedIso (SelectingRectification.bimodule E S)
    (b E S) (length E S) (model E S) rfl rfl⟩

theorem shifted_binomial_iteration (j : ℕ) (Y : Family (k := k) (R := R)) :
    Nonempty (((G E S).obj^[j]) (evaluation E Y) ≅
      ExternalTensor.Binomial.binomialObject (b E S) 3 j
        (evaluation E (((selected S)^[j]) Y))) :=
  ⟨ExternalTensor.Binomial.binomialIteration (G E S) (evaluation E) (selected S)
    (b E S) 3 (realization E S) j Y⟩

end
end Note198.SelectingShiftedRealization
