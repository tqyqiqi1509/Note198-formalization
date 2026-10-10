import Note198.TriangleObjectInverseImage
import Note198.SelectingKernelChain

namespace Note198.SelectingThickKernelChain
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated OAI OAI.LittleFinitistic
open ExternalTensor.Section4
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u v w

section General
variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C]
variable [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable (F : C ⥤ C) [F.Additive] [F.CommShift ℤ]
variable (hF : ∀ (T : Triangle C), T ∈ distTriang C →
  BimoduleDerivedTriangleObjects.RotatedObjects F T)

include hF in
theorem iterated_kernel_thick (j : ℕ) :
    ObjectProperty.IsTriangulated (fun Z => IsZero ((F.obj^[j]) Z) : ObjectProperty C) ∧
    ObjectProperty.IsStableUnderRetracts (fun Z => IsZero ((F.obj^[j]) Z) : ObjectProperty C) := by
  induction j with
  | zero =>
    exact ⟨TriangleObjectInverseImage.zero_triangulated,
      TriangleObjectInverseImage.zero_retracts⟩
  | succ j ih =>
    let P : ObjectProperty C := fun Z => IsZero ((F.obj^[j]) Z)
    letI : P.IsTriangulated := ih.1
    letI : P.IsStableUnderRetracts := ih.2
    have heq : (fun Z => IsZero ((F.obj^[j+1]) Z) : ObjectProperty C) =
        P.inverseImage F := by
      funext Z
      rw [Function.iterate_succ_apply]
      rfl
    rw [heq]
    exact ⟨TriangleObjectInverseImage.inverse_triangulated F hF P,
      TriangleObjectInverseImage.inverse_retracts F P⟩
end General

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)

/-- The assertion is discharged for the actual fixed native tensor functor,
 using its constructed bounded right-projective bimodule. -/
theorem phi_rotated_objects
    (T : Triangle (DerivedCategory (ModuleCat.{u} (QuadraticEncoding.B E.relations))))
    (hT : T ∈ distTriang _) :
    BimoduleDerivedTriangleObjects.RotatedObjects (SelectingDerivedFunctor.Phi E S) T := by
  let d := SelectingDerivedFunctor.model E S
  letI : ∀ i, Module.Projective (QuadraticEncoding.B E.relations)ᵐᵒᵖ
      (ComplexTensor.rightTerm k (QuadraticEncoding.B E.relations)
        (BimoduleTotal.right k _ (SelectingRectification.bimodule E S)) (d.degrees i)) :=
    fun i => d.projective (d.degrees i)
  exact BimoduleDerivedTriangleObjects.rotated_objects k _ _ d.degrees
    (BimoduleTotal.intervalDegrees_strictMono d.lower d.upper) T hT

/-- Every actual iterated kernel is closed under shifts, triangles and retracts. -/
theorem actual_kernel_thick (j : ℕ) :
    ObjectProperty.IsTriangulated (fun Z => IsZero (((SelectingDerivedFunctor.Phi E S).obj^[j]) Z) :
      ObjectProperty (DerivedCategory (ModuleCat.{u} (QuadraticEncoding.B E.relations)))) ∧
    ObjectProperty.IsStableUnderRetracts (fun Z => IsZero (((SelectingDerivedFunctor.Phi E S).obj^[j]) Z) :
      ObjectProperty (DerivedCategory (ModuleCat.{u} (QuadraticEncoding.B E.relations)))) :=
  iterated_kernel_thick (SelectingDerivedFunctor.Phi E S) (phi_rotated_objects E S) j

/-- The fixed selecting functor has a strictly increasing chain of actual
 thick kernels, witnessed by the constructed source family. -/
theorem strictly_increasing_thick_kernels
    (F : SelectingBrickFamily.SourceFamily k R S) (j : ℕ) :
    ObjectProperty.IsTriangulated (fun Z => IsZero (((SelectingDerivedFunctor.Phi E S).obj^[j]) Z) :
      ObjectProperty (DerivedCategory (ModuleCat.{u} (QuadraticEncoding.B E.relations)))) ∧
    ObjectProperty.IsStableUnderRetracts (fun Z => IsZero (((SelectingDerivedFunctor.Phi E S).obj^[j]) Z) :
      ObjectProperty (DerivedCategory (ModuleCat.{u} (QuadraticEncoding.B E.relations)))) ∧
    {Z | IsZero (((SelectingDerivedFunctor.Phi E S).obj^[j]) Z)} ⊂
      {Z | IsZero (((SelectingDerivedFunctor.Phi E S).obj^[j+1]) Z)} :=
  ⟨(actual_kernel_thick E S j).1,(actual_kernel_thick E S j).2,
    SelectingKernelChain.strict_kernel_chain E S F j⟩
end
end Note198.SelectingThickKernelChain
