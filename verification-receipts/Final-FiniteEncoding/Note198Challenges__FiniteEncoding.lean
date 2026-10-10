import Note198.FiniteAlgebraPresentation
import OAI.Algebra.Finitistic.Selection.SelectionEncoding

namespace Note198
noncomputable section
open OAI.LittleFinitistic
universe u

/-- Finite associative presentations give finite quadratic coefficient data
for the same algebra, through an actual algebra equivalence. -/
theorem encoding_of_finite_presentation (k R : Type u)
    [Field k] [Ring R] [Algebra k R]
    (h : GroupAlgebraPresentation.HasFinitePresentation k R) :
    Nonempty (SelectionEncoding.Encoding k R) := by
  sorry

theorem encoding_algebra_finiteDimensional {k R : Type u}
    [Field k] [Ring R] [Algebra k R] (E : SelectionEncoding.Encoding k R) :
    FiniteDimensional k (QuadraticEncoding.B E.relations) := by
  sorry

open CategoryTheory in
theorem encoding_algebra_globalDimension_le_two {k R : Type u}
    [Field k] [Ring R] [Algebra k R] (E : SelectionEncoding.Encoding k R) :
    (⨆ M : ModuleCat.{u} (QuadraticEncoding.B E.relations), projectiveDimension M) ≤
      (2 : ℕ) ∧
    (⨆ M : ModuleCat.{u} (QuadraticEncoding.B E.relations)ᵐᵒᵖ, projectiveDimension M) ≤
      (2 : ℕ) := by
  sorry

end
end Note198
