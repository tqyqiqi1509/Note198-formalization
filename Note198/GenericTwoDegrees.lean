import OAI.Algebra.Finitistic.Localization.TwoDegreeSplitting

namespace Note198.GenericTwoDegrees
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open OAI.LittleFinitistic OAI.LittleFinitistic.QuadraticEncoding DerivedCategory
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u v
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
abbrev C := ModuleCat.{max u v} (B P)
abbrev D := DerivedCategory (C.{u,v} P)
abbrev H (n : ℤ) (X : D.{u,v} P) := (homologyFunctor (C P) n).obj X
abbrev stalk (M : C.{u,v} P) := (singleFunctor (C P) 0).obj M

/-- Cohomology is confined to degrees zero and minus the specified positive shift. -/
def TwoDegrees (s : ℕ) (X : D.{u,v} P) : Prop :=
  ∀ n : ℤ, n ≠ 0 → n ≠ -(s : ℤ) → IsZero (H P n X)

variable (s : ℕ) (hs : 3 ≤ s) (X : D.{u,v} P) (hX : TwoDegrees P s X)
include hs hX

lemma isLE_zero : X.IsLE 0 := by
  rw [DerivedCategory.isLE_iff]
  intro n hn
  exact hX n (by omega) (by omega)

lemma isGE_negative : X.IsGE (-(s : ℤ)) := by
  rw [DerivedCategory.isGE_iff]
  intro n hn
  exact hX n (by omega) (by omega)

lemma lower_isGE : (DerivedTruncation.lower X).IsGE (-(s : ℤ)) := by
  haveI := isGE_negative P s hs X hX
  infer_instance

lemma lower_isLE : (DerivedTruncation.lower X).IsLE (-(s : ℤ)) := by
  rw [DerivedCategory.isLE_iff]
  intro n hn
  by_cases hn₀ : n < 0
  · exact (DerivedTruncation.lowerHomologyIso X n hn₀).isZero_iff.mpr
      (hX n (by omega) (by omega))
  · exact DerivedCategory.isZero_of_isLE (DerivedTruncation.lower X) (-1) n (by omega)

lemma upper_isLE : (DerivedTruncation.upper X).IsLE 0 := by
  haveI := isLE_zero P s hs X hX
  infer_instance

def upperIso : DerivedTruncation.upper X ≅ stalk P (H P 0 X) := by
  haveI := upper_isLE P s hs X hX
  exact DerivedTruncation.canonicalIso 0 (DerivedTruncation.upper X) ≪≫
    (singleFunctor (C P) 0).mapIso (DerivedTruncation.upperHomologyIso X 0 (by omega)).symm

def lowerIso : DerivedTruncation.lower X ≅ (stalk P (H P (-(s : ℤ)) X))⟦(s : ℤ)⟧ := by
  haveI := lower_isLE P s hs X hX
  haveI := lower_isGE P s hs X hX
  exact DerivedTruncation.canonicalIso (-(s : ℤ)) (DerivedTruncation.lower X) ≪≫
    (singleFunctor (C P) (-(s : ℤ))).mapIso
      (DerivedTruncation.lowerHomologyIso X (-(s : ℤ)) (by omega)) ≪≫
    ((singleFunctors (C P)).shiftIso (s : ℤ) (-(s : ℤ)) 0 (by omega)).symm.app
      (H P (-(s : ℤ)) X)

def lowerShiftIso : (DerivedTruncation.lower X)⟦(1 : ℤ)⟧ ≅
    (stalk P (H P (-(s : ℤ)) X))⟦((s + 1 : ℕ) : ℤ)⟧ := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (shiftFunctor (D P) (1 : ℤ)).mapIso (lowerIso P s hs X hX) ≪≫
      (shiftFunctorAdd (D P) (s : ℤ) (1 : ℤ)).symm.app (stalk P (H P (-(s : ℤ)) X))

/-- The actual connecting morphism has degree s+1, so it vanishes for s at least three. -/
theorem connecting_eq_zero : (DerivedTruncation.triangle X).mor₃ = 0 := by
  have hz := TwoDegreeFormality.shifted_hom_eq_zero P (H P 0 X) (H P (-(s : ℤ)) X)
    (s + 1) (by omega)
    ((upperIso P s hs X hX).inv ≫ (DerivedTruncation.triangle X).mor₃ ≫
      (lowerShiftIso P s hs X hX).hom)
  apply (cancel_epi (upperIso P s hs X hX).inv).mp
  apply (cancel_mono (lowerShiftIso P s hs X hX).hom).mp
  erw [Category.assoc, comp_zero, zero_comp]
  exact hz

/-- The splitting retains the actual inclusion and projection of truncation. -/
structure TruncationSplit where
  iso : X ≅ DerivedTruncation.lower X ⊞ DerivedTruncation.upper X
  inclusion : DerivedTruncation.inclusion X ≫ iso.hom = biprod.inl
  projection : DerivedTruncation.projection X = iso.hom ≫ biprod.snd

def truncationSplit : TruncationSplit P X := Classical.choice (by
  obtain ⟨e, hi, hp⟩ := exists_iso_binaryBiproduct_of_distTriang
    (DerivedTruncation.triangle X) (DerivedTruncation.distinguished X)
    (connecting_eq_zero P s hs X hX)
  exact ⟨⟨e, hi, hp⟩⟩)

/-- Actual B-linear formality with arbitrary shift s, on actual cohomology modules. -/
def splitIso : X ≅ stalk P (H P 0 X) ⊞ (stalk P (H P (-(s : ℤ)) X))⟦(s : ℤ)⟧ :=
  (truncationSplit P s hs X hX).iso ≪≫
    biprod.mapIso (lowerIso P s hs X hX) (upperIso P s hs X hX) ≪≫ biprod.braiding _ _

/-- Substitute B-linear identifications of both actual cohomology modules. -/
def splitIsoWithModels (M N : C.{u,v} P)
    (e0 : H P 0 X ≅ M) (em : H P (-(s : ℤ)) X ≅ N) :
    X ≅ stalk P M ⊞ (stalk P N)⟦(s : ℤ)⟧ :=
  splitIso P s hs X hX ≪≫ biprod.mapIso ((singleFunctor (C P) 0).mapIso e0)
    ((shiftFunctor (D P) (s : ℤ)).mapIso ((singleFunctor (C P) 0).mapIso em))

/-- The constructed splitting is an actual derived B-module isomorphism. -/
theorem formality_with_models (M N : C.{u,v} P)
    (e0 : H P 0 X ≅ M) (em : H P (-(s : ℤ)) X ≅ N) :
    Nonempty (X ≅ stalk P M ⊞ (stalk P N)⟦(s : ℤ)⟧) := by
  exact ⟨splitIsoWithModels P s hs X hX M N e0 em⟩

end
end Note198.GenericTwoDegrees