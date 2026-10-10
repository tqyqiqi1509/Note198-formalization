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
  obtain ⟨ι, κ, hι, hκ, relations, hdegree, ⟨equiv⟩⟩ :=
    QuadraticPresentation.finite_presentation_to_quadratic k h
  letI := hι
  letI := hκ
  obtain ⟨d, t, P, ⟨reindex⟩⟩ :=
    PresentationReindex.finite_quadratic_encoding relations hdegree
  exact ⟨⟨d, t, P, reindex.trans equiv⟩⟩

theorem encoding_algebra_finiteDimensional {k R : Type u}
    [Field k] [Ring R] [Algebra k R] (E : SelectionEncoding.Encoding k R) :
    FiniteDimensional k (QuadraticEncoding.B E.relations) :=
  QuadraticEncoding.finiteDimensional E.relations

open CategoryTheory in
theorem encoding_algebra_globalDimension_le_two {k R : Type u}
    [Field k] [Ring R] [Algebra k R] (E : SelectionEncoding.Encoding k R) :
    (⨆ M : ModuleCat.{u} (QuadraticEncoding.B E.relations), projectiveDimension M) ≤
      (2 : ℕ) ∧
    (⨆ M : ModuleCat.{u} (QuadraticEncoding.B E.relations)ᵐᵒᵖ, projectiveDimension M) ≤
      (2 : ℕ) :=
  QuadraticEncoding.globalDimension_le_two E.relations

end
end Note198
