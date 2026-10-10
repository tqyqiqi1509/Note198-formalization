import Note198.BimoduleDerivedTriangleObjects
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.Retract

namespace Note198.TriangleObjectInverseImage
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
universe v v' u u'
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
variable [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
variable [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
variable (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
variable (hF : ∀ (T : Triangle C), T ∈ distTriang C →
  BimoduleDerivedTriangleObjects.RotatedObjects F T)
variable (P : ObjectProperty D)

include hF in
/-- Rotated triangle objects suffice for inverse images of triangulated
 properties; compatibility of their arrows is unnecessary here. -/
theorem inverse_triangulated [P.IsTriangulated] [P.IsClosedUnderIsomorphisms] :
    (P.inverseImage F).IsTriangulated := by
  letI : (P.inverseImage F).IsTriangulatedClosed₃ :=
    ObjectProperty.IsTriangulatedClosed₃.mk' (by
      intro T hT h₁ h₂
      obtain ⟨U,hU,⟨e₁⟩,⟨e₂⟩,⟨e₃⟩⟩ := hF T hT
      have hu₁ : P U.obj₁ := P.prop_of_iso e₁ h₂
      have hu₃ : P U.obj₃ := P.prop_of_iso e₃ (P.le_shift (1 : ℤ) _ h₁)
      exact P.prop_of_iso e₂.symm (P.ext_of_isTriangulatedClosed₂ U hU hu₁ hu₃))
  letI : (P.inverseImage F).IsTriangulatedClosed₂ :=
    ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃
  exact
    { toContainsZero := inferInstance
      toIsStableUnderShift := inferInstance
      toIsTriangulatedClosed₂ := inferInstance }

/-- Retracts are preserved by every functor. -/
theorem inverse_retracts [P.IsStableUnderRetracts] :
    (P.inverseImage F).IsStableUnderRetracts :=
  { of_retract := fun r h => P.prop_of_retract (r.map F) h }

theorem zero_retracts : ObjectProperty.IsStableUnderRetracts (IsZero (C := C) : ObjectProperty C) := by
  refine ⟨?_⟩
  intro X Y r hY
  rw [IsZero.iff_id_eq_zero, ← r.retract, hY.eq_of_tgt r.i 0, zero_comp]

theorem zero_triangulated : ObjectProperty.IsTriangulated (IsZero (C := C) : ObjectProperty C) := by
  letI : ObjectProperty.IsStableUnderRetracts (IsZero (C := C) : ObjectProperty C) := zero_retracts
  letI : ObjectProperty.IsStableUnderShift (IsZero (C := C) : ObjectProperty C) ℤ :=
    { isStableUnderShiftBy := fun n =>
        { le_shift := fun X hX => (shiftFunctor C n).map_isZero hX } }
  letI : ObjectProperty.IsTriangulatedClosed₂ (IsZero (C := C) : ObjectProperty C) :=
    ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ =>
      T.isZero₂_of_isZero₁₃ hT h₁ h₃)
  exact
    { toContainsZero := inferInstance
      toIsStableUnderShift := inferInstance
      toIsTriangulatedClosed₂ := inferInstance }
end
end Note198.TriangleObjectInverseImage
