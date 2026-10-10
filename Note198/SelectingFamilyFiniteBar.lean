import Note198.SelectingOrdinaryEvenSplit
import Note198.SelectingFiniteBar
import Note198.SelectingBrickFamily

namespace Note198.SelectingFamilyFiniteBar
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
variable (F : SelectingBrickFamily.SourceFamily k R S)
open SelectingOrdinaryAlgebra

variable {S} in
def source (m : ℕ+) : SelectingIteration.Family (k := k) (R := R) := ⟨F.V m,F.finite m⟩
abbrev firstModule (m : ℕ+) := SelectingOrdinaryEvenSplit.firstModule E S (source F m)

/-- The actual first-inflated source module has tensor extinction at 2m;
the hypothesis is the constructed source family's exact extinction time. -/
theorem ordinary_extinction (m : ℕ+) :
    IsZero (((SelectingOrdinarySimulation.ordinary E S).obj^[2*m.val])
      ((DerivedCategory.singleFunctor (ModuleCat (D E S)) 0).obj (firstModule E S F m))) := by
  have he : IsZero (((SelectingOrdinarySimulation.ordinary E S).obj^[2*m.val])
      (SelectingOrdinaryIteration.evaluated E S (source F m))) := by
    apply (SelectingOrdinaryIteration.even_isZero_iff E S m.val (source F m)).mpr
    rw [SelectingIteration.iterate_val]
    exact F.extinct m
  exact (mapObjectIteration (SelectingOrdinarySimulation.ordinary E S)
    (SelectingOrdinaryEvenSplit.evaluatedStalkIso E S (source F m)) (2*m.val)).isZero_iff.mp he

/-- The finite bar decomposition applies to the actual family modules,
without an extinction or bar-isomorphism certificate supplied by a caller. -/
theorem finite_bar (m : ℕ+) :
    Nonempty ((DerivedBar.derivedBaseChange (D E S)
      (TrivSqZeroExt.fstHom k (D E S) (X E S))).obj
      (@ModuleCat.of (A E S) inferInstance (firstModule E S F m) inferInstance
        (DerivedBar.ParityBridge.inflatedModule (D E S) (X E S) (firstModule E S F m))) ≅
      (⨁ fun i : Fin (2*m.val) => SelectingFiniteBar.count E S (firstModule E S F m) i)) :=
  SelectingFiniteBar.finite_bar_splitting E S (firstModule E S F m) (2*m.val)
    (ordinary_extinction E S F m)
end
end Note198.SelectingFamilyFiniteBar
