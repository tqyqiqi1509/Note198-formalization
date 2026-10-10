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
  obtain ⟨ι, κ, hι, hκ, relations, hdegree, ⟨equiv⟩⟩ :=
    QuadraticPresentation.finite_presentation_to_quadratic k hR
  letI := hι
  letI := hκ
  obtain ⟨d, t, P, ⟨reindex⟩⟩ :=
    PresentationReindex.finite_quadratic_encoding relations hdegree
  exact ⟨⟨d, t, P, reindex.trans equiv⟩⟩

end
end Note198