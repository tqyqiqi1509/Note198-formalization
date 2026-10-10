import OAI.Algebra.Finitistic.Encoding.DirectedBound
import OAI.Algebra.Finitistic.Localization.OddDouble
import OAI.Algebra.Finitistic.Localization.DiagramLifting
import OAI.Algebra.Finitistic.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Individually stated results from Note198.
This module does not assert that the remaining manuscript is formalized.
Lean's composition `f ≫ g` applies f first, matching the paper's product gf.
-/

namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open scoped BigOperators

universe u v

/-- Lemma 3.1. Global dimension here is the supremum over all modules,
not only finite-dimensional modules. The corner hypothesis is expanded.
The positive number of vertices makes n - 1 agree with the paper's bound. -/
theorem directed_bound {k A : Type u} [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] {n : ℕ} (_hn : 0 < n) (e : Fin n → A)
    (idem : ∀ i, e i * e i = e i)
    (orthogonal : ∀ i j, i ≠ j → e i * e j = 0)
    (complete : ∑ i, e i = 1)
    (diagonal : ∀ i a, ∃ c : k, e i * a * e i = c • e i)
    (directed : ∀ i j, j < i → ∀ a, e j * a * e i = 0) :
    (⨆ N : ModuleCat.{max u v} A, projectiveDimension N) ≤ (n - 1 : ℕ) ∧
    (⨆ N : ModuleCat.{max u v} Aᵐᵒᵖ, projectiveDimension N) ≤ (n - 1 : ℕ) := by
  sorry

section OddDouble
variable {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ]
    [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [hpre : Pretriangulated C]
attribute [local instance] Karoubi.karoubi_hasFiniteBiproducts
  hasBinaryBiproducts_of_finite_biproducts

include hpre

/-- Lemma 3.2. A Karoubi object stores both the original object and its
idempotent, so no idempotent splitting is assumed in C. -/
theorem odd_double (U : Karoubi C) :
    (∃ S : C, Nonempty ((toKaroubi C).obj S ≅
      U ⊞ OAI.LittleFinitistic.OddDouble.formalShift U 1)) ∧
    (∃ Z : C, Nonempty ((toKaroubi C).obj Z ≅
      U ⊞ OAI.LittleFinitistic.OddDouble.formalShift U 3)) := by
  sorry

end OddDouble

section DiagramLift
variable {C D : Type*} [Category C] [Category D]
    {k : Type*} [CommRing k] [Preadditive C] [Preadditive D]
    [Linear k C] [Linear k D]
    (L : C ⥤ D) (W : MorphismProperty C) [hloc : L.IsLocalization W]
    [hfractions : W.HasRightCalculusOfFractions] [hadd : L.Additive] [hlinear : L.Linear k]

include W hloc hfractions hadd hlinear

/-- Lemma 3.3 in the more general setting of a linear right-fraction
localization. In the paper C = K and D = Q; proving that that specific
localization satisfies these instances is a separate connection step.
The relation coefficient r ρ i j is the paper's ρ_{ba} with a = i, b = j. -/
theorem quadratic_diagram_lift (na nb nr : ℕ) (Y₀ Y₁ Y₂ : D)
    (a : Fin na → (Y₀ ⟶ Y₁)) (b : Fin nb → (Y₁ ⟶ Y₂))
    (r : Fin nr → Fin na → Fin nb → k)
    (hr : ∀ ρ, ∑ i, ∑ j, r ρ i j • (a i ≫ b j) = 0) :
    ∃ (X₀ X₁ X₂ : C) (e₀ : L.obj X₀ ≅ Y₀) (e₁ : L.obj X₁ ≅ Y₁)
      (e₂ : L.obj X₂ ≅ Y₂) (f : Fin na → (X₀ ⟶ X₁))
      (g : Fin nb → (X₁ ⟶ X₂)),
      (∀ i, L.map (f i) ≫ e₁.hom = e₀.hom ≫ a i) ∧
      (∀ j, L.map (g j) ≫ e₂.hom = e₁.hom ≫ b j) ∧
      (∀ ρ, ∑ i, ∑ j, r ρ i j • (f i ≫ g j) = 0) := by
  sorry

end DiagramLift

/-- The final implication of Theorem 1.1, conditional on the actual finite
modules and the paper's lower bound. This does not construct those modules. -/
theorem infinite_little_dimension_of_note_bounds
    (A : Type u) [Ring A] (b : ℕ)
    (h : ∀ m : ℕ, 0 < m → ∃ M : ModuleCat.{u} A,
      Module.Finite A M ∧ projectiveDimension M < ⊤ ∧
      (((b + 5) * (m - 1) + 1 : ℕ) : WithBot ℕ∞) ≤ projectiveDimension M) :
    OAI.LittleFinitistic.littleFinitisticDimension A = ⊤ := by
  sorry

end
end Note198
