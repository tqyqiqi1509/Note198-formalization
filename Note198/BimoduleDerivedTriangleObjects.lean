import Note198.BimoduleTotalConeSequence
import OAI.Algebra.Finitistic.Bimodule.BimoduleDerivedShift

namespace Note198.BimoduleDerivedTriangleObjects
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated OAI.LittleFinitistic
open OAI.ExternalTensor.Section4 BimoduleTotal
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
variable [∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) (p i))]

/-- This assertion records only the objects of a distinguished triangle;
 it imposes no compatibility condition on its three morphisms. -/
def RotatedObjects {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    [HasZeroObject D] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) (T : Triangle C) : Prop :=
  ∃ U : Triangle D, U ∈ distTriang D ∧
    Nonempty (F.obj T.obj₂ ≅ U.obj₁) ∧
    Nonempty (F.obj T.obj₃ ≅ U.obj₂) ∧
    Nonempty ((F.obj T.obj₁)⟦(1 : ℤ)⟧ ≅ U.obj₃)

/-- The native derived tensor functor sends the three objects of every
 distinguished triangle to those of a rotated distinguished triangle. -/
theorem rotated_objects (T : Triangle (DerivedCategory (ModuleCat.{u} B)))
    (hT : T ∈ distTriang _) : RotatedObjects (derived k B P p hp) T := by
  obtain ⟨K,L,f,⟨e⟩⟩ := (DerivedCategory.mem_distTriang_iff T).mp hT
  let h := BimoduleTotalConeSequence.total_cone_sequence_shortExact f k P p hp
  let U := DerivedCategory.triangleOfSES h
  refine ⟨U,DerivedCategory.triangleOfSES_distinguished h,?_,?_,?_⟩
  · exact ⟨(derived k B P p hp).mapIso (Triangle.π₂.mapIso e) ≪≫
      (derivedComparison k B P p hp).app L⟩
  · exact ⟨(derived k B P p hp).mapIso (Triangle.π₃.mapIso e) ≪≫
      (derivedComparison k B P p hp).app (CochainComplex.mappingCone f)⟩
  · exact ⟨(shiftFunctor _ (1 : ℤ)).mapIso
        ((derived k B P p hp).mapIso (Triangle.π₁.mapIso e) ≪≫
          (derivedComparison k B P p hp).app K) ≪≫
      ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app
        ((functor k B P p hp).obj K)).symm ≪≫
      DerivedCategory.Q.mapIso (((functor k B P p hp).commShiftIso (1 : ℤ)).app K).symm⟩
end
end Note198.BimoduleDerivedTriangleObjects
