import Note198.SelectingDerivedFunctor
import OAI.Algebra.Finitistic.Iteration.BinomialIteration

set_option maxHeartbeats 0

namespace Note198.SelectingIteration
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)

/-- All finite-dimensional R-modules, retaining their actual R-actions. -/
def Family := {Y : ModuleCat.{u} R //
  FiniteDimensional k (EndomorphismSelection.vectorObject (k := k) Y)}

local instance (Y : Family (k := k) (R := R)) : Module k Y.val :=
  Module.compHom Y.val (algebraMap k R)
local instance (Y : Family (k := k) (R := R)) : IsScalarTower k R Y.val :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance (Y : Family (k := k) (R := R)) : FiniteDimensional k Y.val :=
  Y.property

def selected (Y : Family (k := k) (R := R)) : Family (k := k) (R := R) := by
  letI : FiniteDimensional k (EndomorphismSelection.vectorObject (k := k) Y.val) :=
    Y.property
  exact ⟨EndomorphismSelection.H S Y.val,
    EndomorphismSelection.H_finiteDimensional S Y.val⟩

def evaluation (Y : Family (k := k) (R := R)) :
    DerivedCategory (ModuleCat.{u} (QuadraticEncoding.B E.relations)) :=
  (DerivedCategory.singleFunctor (ModuleCat (QuadraticEncoding.B E.relations)) 0).obj
    (ModuleCat.of (QuadraticEncoding.B E.relations) (SelectingRealization.input (E := E) (Y := Y.val)))

theorem module_zero (Y : Family (k := k) (R := R)) :
    IsZero (ModuleCat.of (QuadraticEncoding.B E.relations) (SelectingRealization.input (E := E) (Y := Y.val))) ↔ Subsingleton Y.val := by
  let rep := SourceActionEvaluation.representation (Y := Y.val) E
  constructor
  · intro h
    letI := ModuleCat.subsingleton_of_isZero h
    have inj : Function.Injective (rep.inclusion 0) := by
      intro x y hxy
      have he := congrArg (rep.projection 0) hxy
      simpa only [QuadraticEncoding.Representation.projection_inclusion] using he
    exact inj.subsingleton
  · intro h
    letI := h
    letI : Subsingleton rep.Evaluation :=
      inferInstanceAs (Subsingleton (Y.val × Y.val × Y.val))
    exact ModuleCat.isZero_of_subsingleton _

theorem evaluation_zero (Y : Family (k := k) (R := R)) :
    IsZero (evaluation E Y) ↔ Subsingleton Y.val := by
  rw [← module_zero E Y]
  constructor
  · intro h
    exact ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat (QuadraticEncoding.B E.relations)) 0).app
      (ModuleCat.of (QuadraticEncoding.B E.relations) (SelectingRealization.input (E := E) (Y := Y.val)))).isZero_iff.mp
        ((DerivedCategory.homologyFunctor
          (ModuleCat (QuadraticEncoding.B E.relations)) 0).map_isZero h)
  · exact (DerivedCategory.singleFunctor
      (ModuleCat (QuadraticEncoding.B E.relations)) 0).map_isZero

theorem iterate_val (j : ℕ) (Y : Family (k := k) (R := R)) :
    (((selected S)^[j]) Y).val = EndomorphismSelection.iterate S Y.val j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    change EndomorphismSelection.H S (((selected S)^[j]) Y).val =
      EndomorphismSelection.H S (EndomorphismSelection.iterate S Y.val j)
    exact congrArg (EndomorphismSelection.H S) ih

/-- The splitting is objectwise; no naturality in the evaluation module is assumed. -/
def split (Y : Family (k := k) (R := R)) :
    (SelectingDerivedFunctor.Phi E S).obj (evaluation E Y) ≅
      evaluation E (selected S Y) ⊞
      (evaluation E (selected S Y))⟦(3 : ℤ)⟧ :=
  Classical.choice (SelectingDerivedFunctor.native_realization E S (Y := Y.val))

/-- Corollary 4.3, with the actual fixed derived tensor functor and the full
binomial multiplicity, for every finite evaluation module and every iterate. -/
theorem binomial_iteration (j : ℕ) (Y : Family (k := k) (R := R)) :
    Nonempty (((SelectingDerivedFunctor.Phi E S).obj^[j]) (evaluation E Y) ≅
      ⨁ fun q : Fin (j+1) => ⨁ fun _ : Fin (Nat.choose j q.val) =>
        (evaluation E (((selected S)^[j]) Y))⟦(3 : ℤ)*(q.val : ℤ)⟧) :=
  ⟨ExternalTensor.Binomial.section4Iteration
    (SelectingDerivedFunctor.Phi E S) (evaluation E) (selected S) (split E S) j Y⟩

end
end Note198.SelectingIteration
