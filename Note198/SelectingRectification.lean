import Note198.SelectingRectificationData

set_option maxHeartbeats 500000

namespace Note198.SelectingRectification
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CategoryTheory.Idempotents
open OAI OAI.LittleFinitistic
open SelectionEncoding RelationBasisCoefficients RelationBasisAction FormalSummandAction
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : Encoding k R) (S : EndomorphismSelection.Data k R)

/-- All original vertex inverses and arrow homotopies, boundedness,
finiteness and right projectivity of the actual selecting complex.
Enveloping-algebra projectivity is provided by a separate stronger bridge. -/
theorem verified : ∃ lo hi : ℤ,
    RectificationLemma.Verified E.relations (D₀ E S) (D₁ E S) (D₂ E S)
      (f E S) (g E S) (relations E S) lo hi := by
  obtain ⟨l₀, h₀, b₀⟩ := UnderlyingRepresentatives.bounded E.relations (fixedData E S).D₀
  obtain ⟨l₁, h₁, b₁⟩ := UnderlyingRepresentatives.bounded E.relations (fixedData E S).D₁
  obtain ⟨l₂, h₂, b₂⟩ := UnderlyingRepresentatives.bounded E.relations (fixedData E S).D₂
  let lo := min l₀ (min l₁ l₂)
  let hi := max h₀ (max h₁ h₂)
  refine ⟨lo, hi, RectificationLemma.rectification E.relations
    (D₀ E S) (D₁ E S) (D₂ E S) (f E S) (g E S) (relations E S) lo hi
    (fun n hn => b₀ n ?_) (fun n hn => b₁ n ?_) (fun n hn => b₂ n ?_)
    (UnderlyingRepresentatives.projective E.relations (fixedData E S).D₀)
    (UnderlyingRepresentatives.projective E.relations (fixedData E S).D₁)
    (UnderlyingRepresentatives.projective E.relations (fixedData E S).D₂)
    (UnderlyingRepresentatives.finite E.relations (fixedData E S).D₀)
    (UnderlyingRepresentatives.finite E.relations (fixedData E S).D₁)
    (UnderlyingRepresentatives.finite E.relations (fixedData E S).D₂)⟩
  all_goals dsimp [lo, hi] at hn; omega

end
end Note198.SelectingRectification
