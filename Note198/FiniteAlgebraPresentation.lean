import Note198.PrimeFinitePresentation
import Note198.GroupAlgebraSelection
import OAI.Algebra.Finitistic.Encoding.PresentationReindex

namespace Note198
noncomputable section
open OAI.LittleFinitistic
universe u

/-- The actual selecting algebra is finitely presented as an associative
unital algebra; no commutativity of this algebra is assumed. -/
theorem selecting_algebra_finitely_presented (k : Type u) [Field k] (p : ℕ) :
    GroupAlgebraPresentation.HasFinitePresentation k (GroupAlgebraSelection.Ring k p) := by
  letI := PrimeGroup.FinitePresentation.auxiliaryGroup_isFinitelyPresented p
  exact GroupAlgebraPresentation.groupAlgebra_hasFinitePresentation k
    (PrimeGroup.Presentation.AuxiliaryGroup p)

/-- The finite prefix conversion in Section 3 preserves the actual
group algebra through an algebra equivalence. -/
theorem selecting_algebra_quadratic_presentation (k : Type u) [Field k] (p : ℕ) :
    QuadraticPresentation.HasFiniteQuadraticPresentation k (GroupAlgebraSelection.Ring k p) :=
  QuadraticPresentation.finite_presentation_to_quadratic k
    (selecting_algebra_finitely_presented k p)

/-- Concrete finite coefficient data for the three-vertex encoding,
over every field and for the same selecting algebra. -/
theorem selecting_algebra_coefficient_encoding (k : Type u) [Field k] (p : ℕ) :
    ∃ (d t : ℕ) (P : QuadraticEncoding.Relations k d t),
      Nonempty (QuadraticPresentation.Original k (Fin d)
        (QuotientAction.polynomial P) ≃ₐ[k] GroupAlgebraSelection.Ring k p) := by
  obtain ⟨ι, κ, hι, hκ, relations, hdegree, ⟨equiv⟩⟩ :=
    selecting_algebra_quadratic_presentation k p
  letI := hι
  letI := hκ
  obtain ⟨d, t, P, ⟨reindex⟩⟩ :=
    PresentationReindex.finite_quadratic_encoding relations hdegree
  exact ⟨d, t, P, ⟨reindex.trans equiv⟩⟩

end
end Note198
