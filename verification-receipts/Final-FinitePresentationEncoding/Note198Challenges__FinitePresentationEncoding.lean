import OAI.Algebra.Finitistic.Selection.SelectionEncoding

namespace Note198
noncomputable section
open OAI.LittleFinitistic
universe u v

/-- Every finitely presented associative unital algebra has the exact finite
encoding used in the realization theorem. It records finite coefficient
relations and an exact quadratic-presentation equivalence. -/
theorem exists_encoding_of_finite_presentation
    (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
    (hR : GroupAlgebraPresentation.HasFinitePresentation k R) :
    Nonempty (SelectionEncoding.Encoding k R) := by
  sorry

end
end Note198