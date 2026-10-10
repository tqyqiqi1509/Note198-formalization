import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Category.ModuleCat.Abelian

namespace Note198
noncomputable section
open CategoryTheory
universe u v
variable (D : Type u) [Ring D]

/-- Finite global dimension, expressed as the actual supremum of all module
projective dimensions in the declared module universe, is equivalent to
one natural bound on every actual module. Zero rings/categories are covered
by choosing bound zero when this supremum is bottom. -/
theorem finite_global_dimension_iff_uniform_bound :
    (⨆ M : ModuleCat.{max u v} D, projectiveDimension M) < ⊤ ↔
      ∃ g : ℕ, ∀ M : ModuleCat.{max u v} D, HasProjectiveDimensionLE M g := by
  constructor
  · intro hfin
    generalize hvalue : (⨆ M : ModuleCat.{max u v} D, projectiveDimension M) = value at hfin
    induction value using WithBot.recBotCoe with
    | bot =>
      refine ⟨0,fun M => (projectiveDimension_le_iff M 0).mp ?_⟩
      exact (le_iSup (fun M : ModuleCat.{max u v} D => projectiveDimension M) M).trans
        (by rw [hvalue]; exact bot_le)
    | coe value =>
      induction value using WithTop.recTopCoe with
      | top => exact (lt_irrefl _ hfin).elim
      | coe n =>
        refine ⟨n,fun M => (projectiveDimension_le_iff M n).mp ?_⟩
        exact (le_iSup (fun M : ModuleCat.{max u v} D => projectiveDimension M) M).trans
          (by
            rw [hvalue]
            change ((n : ℕ∞) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞)
            exact le_of_eq (WithBot.coe_natCast n))
  · rintro ⟨g,hg⟩
    have hle : (⨆ M : ModuleCat.{max u v} D, projectiveDimension M) ≤ (g : ℕ) :=
      iSup_le (fun M => (projectiveDimension_le_iff M g).mpr (hg M))
    exact lt_of_le_of_lt hle (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top g))

end
end Note198
