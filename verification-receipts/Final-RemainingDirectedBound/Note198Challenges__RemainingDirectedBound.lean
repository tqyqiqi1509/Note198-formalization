import OAI.Algebra.Finitistic.Encoding.DirectedBound

namespace Note198.RemainingDirectedBound
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe u v

/-- Lemma 3.1 for every vertex count. When the count is zero, all left
and right modules are zero, so the empty boundary does not use a
truncated natural-number subtraction to mask the projective dimension. -/
theorem complete_directed_bound {k A : Type u} [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] {n : ℕ} (e : Fin n → A)
    (idem : ∀ i, e i * e i = e i)
    (orthogonal : ∀ i j, i ≠ j → e i * e j = 0)
    (complete : ∑ i, e i = 1)
    (diagonal : ∀ i a, ∃ c : k, e i * a * e i = c • e i)
    (directed : ∀ i j, j < i → ∀ a, e j * a * e i = 0) :
    ((⨆ N : ModuleCat.{max u v} A, projectiveDimension N) ≤ (n - 1 : ℕ) ∧
      (⨆ N : ModuleCat.{max u v} Aᵐᵒᵖ, projectiveDimension N) ≤ (n - 1 : ℕ)) ∧
    (n = 0 → ∀ N : ModuleCat.{max u v} A, projectiveDimension N = ⊥) ∧
    (n = 0 → ∀ N : ModuleCat.{max u v} Aᵐᵒᵖ, projectiveDimension N = ⊥) := by
  sorry

end
end Note198.RemainingDirectedBound
