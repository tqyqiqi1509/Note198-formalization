import Note198.SelectingOrdinarySimulation
import Note198.SelectingShiftedRealization
import OAI.Algebra.Finitistic.Iteration.FunctorObjectIteration
import OAI.Algebra.Finitistic.Iteration.BinomialVanishing
import OAI.Algebra.Finitistic.Ordinary.OrdinaryFirstDerivedRetraction

namespace Note198.SelectingOrdinaryIteration
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
open SelectingIteration SelectingOrdinarySimulation

/-- Inflation into the first block of the actual product algebra D. -/
abbrev evaluated (Y : Family (k := k) (R := R)) :=
  (first E S).obj (evaluation E Y)

/-- The ordinary even iterate is identified with the full binomial object,
with its original multiplicities, followed by actual first-block inflation. -/
theorem even_binomial (j : ℕ) (Y : Family (k := k) (R := R)) :
    Nonempty (((ordinary E S).obj^[2*j]) (evaluated E S Y) ≅
      (first E S).obj (ExternalTensor.Binomial.binomialObject
        (SelectingOrdinaryAlgebra.b E S) 3 j
        (evaluation E (((selected S)^[j]) Y)))) := by
  let e := Classical.choice (SelectingShiftedRealization.native_shifted_comparison E S)
  exact ⟨Classical.choice (even_iteration E S j (evaluation E Y)) ≪≫
    (first E S).mapIso (functorObjectIteration e j (evaluation E Y)) ≪≫
    (first E S).mapIso
      (Classical.choice (SelectingShiftedRealization.shifted_binomial_iteration E S j Y))⟩

/-- Actual ordinary tensor extinction is equivalent to extinction of the
selected source module; first-block inflation reflects zero objects. -/
theorem even_isZero_iff (j : ℕ) (Y : Family (k := k) (R := R)) :
    IsZero (((ordinary E S).obj^[2*j]) (evaluated E S Y)) ↔
      Subsingleton ((((selected S)^[j]) Y).val) := by
  exact (Classical.choice (even_binomial E S j Y)).isZero_iff.trans
    ((BlockModule.derivedFirst_isZero_iff _ _ _).trans
      ((ExternalTensor.Binomial.binomialObject_isZero_iff
        (SelectingOrdinaryAlgebra.b E S) 3 j _).trans
        (evaluation_zero E (((selected S)^[j]) Y))))

end
end Note198.SelectingOrdinaryIteration
