import Note198.SelectingRectification
import OAI.Algebra.Finitistic.Localization.TensorCohomologyDiagram
import OAI.Algebra.Finitistic.Rectification.FullTensorProperties

namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SelectingTensor
open OAI OAI.LittleFinitistic
open SelectingRectification QuadraticEncoding
universe u
variable {k R₀ : Type u} [Field k] [Ring R₀] [Algebra k R₀]
variable {enc : SelectionEncoding.Encoding k R₀} {S : EndomorphismSelection.Data k R₀}
variable (N : Type u) [AddCommGroup N] [Module k N] [Module (B enc.relations) N]

/-- Evaluate the one fixed selecting (SelectingRectification.bimodule enc S), retaining its full left action. -/
abbrev complex := FullTensorRectification.tensor enc.relations (SelectingRectification.D₀ enc S) (SelectingRectification.D₁ enc S) (SelectingRectification.D₂ enc S) (SelectingRectification.f enc S) (SelectingRectification.g enc S) (SelectingRectification.relations enc S) N
abbrev source (v : Fin 3) := FullTensorRectification.source enc.relations (SelectingRectification.D₀ enc S) (SelectingRectification.D₁ enc S) (SelectingRectification.D₂ enc S) N v
abbrev comparison (v : Fin 3) (n : ℤ) :=
  TensorCohomologyDiagram.comparison enc.relations (SelectingRectification.D₀ enc S) (SelectingRectification.D₁ enc S) (SelectingRectification.D₂ enc S) (SelectingRectification.f enc S) (SelectingRectification.g enc S) (SelectingRectification.relations enc S) N v n

/-- Every cohomology (comparison (enc := enc) (S := S)) is invertible for the fixed selected representatives. -/
instance comparison_isIso (v : Fin 3) (n : ℤ) : IsIso ((comparison (enc := enc) (S := S)) N v n) := by
  obtain ⟨l₀,h₀,b₀⟩ := UnderlyingRepresentatives.bounded enc.relations (fixedData enc S).D₀
  obtain ⟨l₁,h₁,b₁⟩ := UnderlyingRepresentatives.bounded enc.relations (fixedData enc S).D₁
  obtain ⟨l₂,h₂,b₂⟩ := UnderlyingRepresentatives.bounded enc.relations (fixedData enc S).D₂
  let lo := min l₀ (min l₁ l₂)
  let hi := max h₀ (max h₁ h₂)
  refine TensorCohomologyDiagram.comparison_isIso enc.relations (SelectingRectification.D₀ enc S) (SelectingRectification.D₁ enc S) (SelectingRectification.D₂ enc S) (SelectingRectification.f enc S) (SelectingRectification.g enc S) (SelectingRectification.relations enc S) N v n lo hi
    (fun n hn => b₀ n ?_) (fun n hn => b₁ n ?_) (fun n hn => b₂ n ?_)
    (UnderlyingRepresentatives.projective enc.relations (fixedData enc S).D₀)
    (UnderlyingRepresentatives.projective enc.relations (fixedData enc S).D₁)
    (UnderlyingRepresentatives.projective enc.relations (fixedData enc S).D₂)
  all_goals dsimp [lo,hi] at hn; omega

def comparisonIso (v : Fin 3) (n : ℤ) := asIso ((comparison (enc := enc) (S := S)) N v n)

/-- The actual tensor (complex (enc := enc) (S := S)) has (bounded (enc := enc) (S := S)) support. -/
theorem bounded : ∃ lo hi : ℤ, ∀ n, n < lo ∨ hi < n → IsZero (((complex (enc := enc) (S := S)) N).X n) := by
  obtain ⟨lo,hi,h⟩ := (SelectingRectification.verified enc S)
  exact ⟨lo-2,hi,FullTensorProperties.bounded k (B enc.relations) N (SelectingRectification.bimodule enc S) (lo-2) hi h.bounded⟩

/-- Every actual evaluated term is (finite (enc := enc) (S := S))-dimensional. -/
theorem finite [FiniteDimensional k N] (n : ℤ) :
    FiniteDimensional k ((ModuleCat.restrictScalars (algebraMap k (B enc.relations))).obj (((complex (enc := enc) (S := S)) N).X n)) := by
  obtain ⟨lo,hi,h⟩ := (SelectingRectification.verified enc S)
  letI : FiniteDimensional k ((ExternalTensor.Section4.forgetK k (B enc.relations)).obj ((SelectingRectification.bimodule enc S).X n)) := h.finite n
  exact FullTensorProperties.finite k (B enc.relations) N ((SelectingRectification.bimodule enc S).X n)
end SelectingTensor

end

end Note198
