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
  rcases GroupAlgebraSelection.two_or_three_invertible k with hp | hp
  · refine ⟨GroupAlgebraSelection.Ring k 2, inferInstance, inferInstance,
      GroupAlgebraSelection.dataTwo k hp, selecting_algebra_finitely_presented k 2, ?_⟩
    intro m hm
    letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
    obtain ⟨N, hs, hf, hj, hz⟩ := FiniteSelectionRestriction.exists_simple_two k m hp
    let M := ModuleCat.of (GroupAlgebraSelection.Ring k 2)
      (FiniteSelectionRestriction.restrictedSource k 2 m ⧸ N)
    letI : IsSimpleModule (GroupAlgebraSelection.Ring k 2)
        (FiniteSelectionRestriction.restrictedSource k 2 m ⧸ N) := hs
    exact ⟨M, hs, IsSimpleModule.nontrivial (GroupAlgebraSelection.Ring k 2)
      (FiniteSelectionRestriction.restrictedSource k 2 m ⧸ N), hf, hj, hz⟩
  · refine ⟨GroupAlgebraSelection.Ring k 3, inferInstance, inferInstance,
      GroupAlgebraSelection.dataThree k hp, selecting_algebra_finitely_presented k 3, ?_⟩
    intro m hm
    letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
    obtain ⟨N, hs, hf, hj, hz⟩ := FiniteSelectionRestriction.exists_simple_three k m hp
    let M := ModuleCat.of (GroupAlgebraSelection.Ring k 3)
      (FiniteSelectionRestriction.restrictedSource k 3 m ⧸ N)
    letI : IsSimpleModule (GroupAlgebraSelection.Ring k 3)
        (FiniteSelectionRestriction.restrictedSource k 3 m ⧸ N) := hs
    exact ⟨M, hs, IsSimpleModule.nontrivial (GroupAlgebraSelection.Ring k 3)
      (FiniteSelectionRestriction.restrictedSource k 3 m ⧸ N), hf, hj, hz⟩

end
end Note198
