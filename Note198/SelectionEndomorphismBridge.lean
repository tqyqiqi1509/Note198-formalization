import Note198.Selection
import Note198.EndomorphismSelection

namespace Note198
noncomputable section
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]

/-- The automorphism used in Proposition 2.1 is an allowed input of the
more general endomorphism construction of Section 4. -/
def Selection.Data.toEndomorphism (S : Selection.Data k R) :
    EndomorphismSelection.Data k R where
  e := S.e
  idempotent := S.idempotent
  central := S.central
  α := S.α.toAlgHom

theorem selection_H_endomorphism (S : Selection.Data k R) (M : ModuleCat.{u} R) :
    EndomorphismSelection.H S.toEndomorphism M = Selection.H S M := rfl

theorem selection_iterate_endomorphism (S : Selection.Data k R)
    (M : ModuleCat.{u} R) (j : ℕ) :
    EndomorphismSelection.iterate S.toEndomorphism M j = Selection.iterate S M j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change EndomorphismSelection.H S.toEndomorphism
      (EndomorphismSelection.iterate S.toEndomorphism M j) =
      Selection.H S (Selection.iterate S M j)
    rw [ih, selection_H_endomorphism]

end
end Note198
