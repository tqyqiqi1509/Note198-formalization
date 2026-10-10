import Note198.FiniteSelectionRestriction
import Note198.FiniteAlgebraPresentation

namespace Note198
noncomputable section
open OAI.LittleFinitistic
universe u

/-- Proposition 2.1 over every field, with a constructed selecting algebra
and constructed finite-dimensional simple modules. The same R and S are used
for all positive extinction times m. -/
theorem selecting_simple_family (k : Type u) [Field k] :
    ∃ (R : Type u) (ringR : Ring R),
      letI : Ring R := ringR
      ∃ (algebraR : Algebra k R),
        letI : Algebra k R := algebraR
        ∃ S : Selection.Data k R,
          GroupAlgebraPresentation.HasFinitePresentation k R ∧
          ∀ m : ℕ, 0 < m → ∃ M : ModuleCat.{u} R,
            IsSimpleModule R M ∧ Nontrivial M ∧
            FiniteDimensional k (Selection.vectorObject (k := k) M) ∧
            (∀ j < m, Nontrivial (Selection.iterate S M j)) ∧
            Subsingleton (Selection.iterate S M m) := by
  sorry

end
end Note198
