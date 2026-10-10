import Note198.SelectingFamilyProjectiveDimension

namespace Note198.SelectingFamilyExactFormula
noncomputable section
open CategoryTheory OAI OAI.LittleFinitistic
open SelectingFamilyCountDimensions
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
variable (F : SelectingBrickFamily.SourceFamily k R S)

/-- The chosen finite integer is exactly the projective dimension of
M(H^jY_m) over B, rather than a dimension certificate supplied externally. -/
theorem epsilon_actual (m : ℕ+) (j : Fin m.val) :
    projectiveDimension (SelectingOrdinaryOddSplit.input E
      (((SelectingIteration.selected S)^[j.val]) (SelectingFamilyFiniteBar.source F m))) =
      (epsilon E S F m j : ℕ) := by
  rw [← SelectingOrdinaryEvenSplit.first_module_dimension E S]
  exact (Classical.choose_spec
    (SelectingFamilyEvenSigned.even_signed_dimension_exists E S F m j.val j.isLt)).2.1

/-- The odd coefficient is exactly pd_E Q(H^jY_m), with the actual tensor
module Q and its full E-action. -/
theorem delta_actual (m : ℕ+) (j : Fin m.val) :
    projectiveDimension (SelectingOrdinaryOddSplit.Qmodule E S
      (((SelectingIteration.selected S)^[j.val]) (SelectingFamilyFiniteBar.source F m))) =
      (delta E S F m j : ℕ) := by
  rw [← SelectingOrdinaryOddSplit.inflated_Q_dimension_eq E S]
  exact (Classical.choose_spec
    (SelectingFamilyOddSigned.odd_signed_dimension_exists E S F m j.val j.isLt)).2.1

/-- The manuscript's exact two-contribution maximum. Sum(Fin m)(Fin m)
indexes its even and odd alternatives, so both original module dimensions
and the extra odd shift by one appear explicitly. -/
theorem brick_exact_formula (m : ℕ+) :
    projectiveDimension (ModuleCat.of (SelectingOrdinaryAlgebra.A E S)
      (SelectingBrickFamily.module E S F m)) =
      ⨆ i : Sum (Fin m.val) (Fin m.val), match i with
        | .inl j => (((SelectingFamilyMaximum.coefficient E S+5)*j.val : ℕ) : WithBot ℕ∞) +
            projectiveDimension (SelectingOrdinaryOddSplit.input E
              (((SelectingIteration.selected S)^[j.val]) (SelectingFamilyFiniteBar.source F m)))
        | .inr j => (((SelectingFamilyMaximum.coefficient E S+5)*j.val+1 : ℕ) : WithBot ℕ∞) +
            projectiveDimension (SelectingOrdinaryOddSplit.Qmodule E S
              (((SelectingIteration.selected S)^[j.val]) (SelectingFamilyFiniteBar.source F m))) := by
  rw [SelectingFamilyProjectiveDimension.brick_dimension E S F m]
  change (FiniteMaximum.maximum (SelectingFamilyMaximum.coefficient E S) m.val
    (epsilon E S F m) (delta E S F m) : WithBot ℕ∞) = _
  rw [← FiniteMaximum.natural_maximum _ _ _ _ m.pos]
  congr 1
  funext i
  rcases i with j | j
  · dsimp only [FiniteMaximum.value]
    rw [epsilon_actual E S F m j]
    simp
  · dsimp only [FiniteMaximum.value]
    rw [delta_actual E S F m j]
    simp

end
end Note198.SelectingFamilyExactFormula
