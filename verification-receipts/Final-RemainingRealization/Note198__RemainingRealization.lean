import Note198.FinitePresentationEncoding
import Note198.SelectingDerivedFunctor
import Note198.SelectingBimoduleProperties

namespace Note198.RemainingRealization
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]

/-- Theorem 4.1: one genuine bimodule complex and its derived tensor
model are fixed before every finite-dimensional input module. -/
theorem fixed_selecting_bimodule_realization
    (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R) :
    ∃ (P : ExternalTensor.Section4.BiComplex k (QuadraticEncoding.B E.relations))
      (M : BimoduleTotal.BoundedProjective k (QuadraticEncoding.B E.relations) P),
      (∃ lo hi : ℤ, ∀ n, n < lo ∨ hi < n → IsZero (P.X n)) ∧
      (∀ n, Projective (P.X n)) ∧
      (∀ n, FiniteDimensional k
        ((ExternalTensor.Section4.forgetK k (QuadraticEncoding.B E.relations)).obj (P.X n))) ∧
      ∀ (Y : Type u) [AddCommGroup Y] [Module k Y] [Module R Y]
        [IsScalarTower k R Y] [FiniteDimensional k Y],
        Nonempty (M.derived.obj ((DerivedCategory.singleFunctor
          (ModuleCat (QuadraticEncoding.B E.relations)) 0).obj
            (ModuleCat.of (QuadraticEncoding.B E.relations)
              (SelectingRealization.input (E := E) (Y := Y)))) ≅
          (DerivedCategory.singleFunctor (ModuleCat (QuadraticEncoding.B E.relations)) 0).obj
            (SelectingRealization.reference (E := E) (S := S) (Y := Y)) ⊞
          ((DerivedCategory.singleFunctor (ModuleCat (QuadraticEncoding.B E.relations)) 0).obj
            (SelectingRealization.reference (E := E) (S := S) (Y := Y)))⟦(3 : ℤ)⟧) := by
  obtain ⟨lo, hi, h⟩ := SelectingRectification.verified E S
  refine ⟨SelectingRectification.bimodule E S, SelectingDerivedFunctor.model E S,
    ⟨lo - 2, hi, h.bounded⟩, SelectingRectification.bimodule_enveloping_projective E S,
    h.finite, ?_⟩
  intro Y _ _ _ _ _
  exact SelectingDerivedFunctor.native_realization E S (Y := Y)

end
end Note198.RemainingRealization