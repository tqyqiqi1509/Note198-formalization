import Note198.PrimePresentationBridge

/-! The complete Lemma 2.3, including all generator actions of the same
constructed automorphism. The accepted off-diagonal presentation equivalence
identifies this actual presented group with the manuscript group. -/
namespace Note198.RemainingCentralShift
open scoped commutatorElement
open PrimeGroup PrimeGroup.Presentation

/-- The whole original central-shift statement. The same automorphism works
for every central element and every generator. The off-diagonal equivalence
is included explicitly; no centrality or automorphism certificate is input. -/
theorem complete_central_shift (p : ℕ) :
    Nonempty (PresentationBridge.OffGroup p ≃* AuxiliaryGroup p) ∧
    ∃ α : AuxiliaryGroup p ≃* AuxiliaryGroup p,
      (∀ N : ℤ,
        (∀ (i : Fin 3) (a b : ℤ), a+b=N →
          z p N = ⁅(data p).U i a, (data p).V i b⁆) ∧
        (∀ g : AuxiliaryGroup p, Commute (z p N) g) ∧
        z p N ^ p = 1 ∧ α (z p N) = z p (N+1)) ∧
      (∀ i : Fin 3, α ((data p).T i) = (data p).T i) ∧
      (∀ (i : Fin 3) (a : ℤ), α ((data p).V i a) = (data p).V i a) ∧
      (∀ (i j : Fin 3) (a : ℤ), α ((data p).W i j a) = (data p).W i j a) ∧
      (∀ (i : Fin 3) (a : ℤ), α ((data p).U i a) = (data p).U i (a+1)) := by
  refine ⟨⟨PresentationBridge.offDiagonalEquiv p⟩, shiftAut p 1, ?_⟩
  refine ⟨fun N => lemma_2_3 p N, ?_, ?_, ?_, ?_⟩
  · intro i
    change shiftHom p 1 ((data p).T i) = (data p).T i
    exact shiftHom_T p 1 i
  · intro i a
    change shiftHom p 1 ((data p).V i a) = (data p).V i a
    exact shiftHom_V p 1 i a
  · intro i j a
    change shiftHom p 1 ((data p).W i j a) = (data p).W i j a
    exact shiftHom_W p 1 i j a
  · intro i a
    change shiftHom p 1 ((data p).U i a) = (data p).U i (a+1)
    exact shiftHom_U p 1 i a

end Note198.RemainingCentralShift
