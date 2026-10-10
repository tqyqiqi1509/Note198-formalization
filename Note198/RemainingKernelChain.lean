import Note198.SelectingMain
import Note198.SelectingBoundedThickKernelChain
import OAI.Algebra.FinitisticAsymmetry.Rickard.NonGeneration

namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
attribute [local instance] HasDerivedCategory.standard
universe u

/-- The same field-level construction supplies the entire strict thick kernel
chain in its bounded finite-dimensional derived category. -/
theorem remaining_field_kernel_chain (k : Type u) [Field k] :
    ∃ (R : Type u) (rR : Ring R), letI : Ring R := rR
      ∃ aR : Algebra k R, letI : Algebra k R := aR
        ∃ (S : Selection.Data k R) (E : SelectionEncoding.Encoding k R)
          (F : SelectingBrickFamily.SourceFamily k R S.toEndomorphism),
          SelectingMain.MainProperties E S.toEndomorphism F ∧
          ¬ InjectivesGenerate (SelectingOrdinaryAlgebra.A E S.toEndomorphism) ∧
          ∀ j : ℕ,
            ObjectProperty.IsTriangulated
              (fun Z => IsZero (((SelectingBoundedThickKernelChain.phi E
              S.toEndomorphism).obj^[j]) Z) :
              ObjectProperty (SelectingBoundedThickKernelChain.Db E)) ∧
            ObjectProperty.IsStableUnderRetracts
              (fun Z => IsZero (((SelectingBoundedThickKernelChain.phi E
              S.toEndomorphism).obj^[j]) Z) :
              ObjectProperty (SelectingBoundedThickKernelChain.Db E)) ∧
            {Z : SelectingBoundedThickKernelChain.Db E |
              IsZero (((SelectingBoundedThickKernelChain.phi E S.toEndomorphism).obj^[j]) Z)} ⊂
            {Z : SelectingBoundedThickKernelChain.Db E |
              IsZero (((SelectingBoundedThickKernelChain.phi E S.toEndomorphism).obj^[j+1]) Z)} := by
  obtain ⟨R,rR,aR,S,E,F,h⟩ := SelectingMain.every_field k
  letI := rR
  letI := aR
  letI : FiniteDimensional k (SelectingOrdinaryAlgebra.A E S.toEndomorphism) :=
    h.algebra_finite
  refine ⟨R,rR,aR,S,E,F,h,?_,?_⟩
  · exact OAI.LittleFinitistic.Rickard.not_injectivesGenerate_of_little_eq_top
      k h.finitistic_infinite
  · intro j
    exact ⟨(SelectingBoundedThickKernelChain.literal_restricted_kernel_thick E
      S.toEndomorphism j).1,
      (SelectingBoundedThickKernelChain.literal_restricted_kernel_thick E
        S.toEndomorphism j).2,
      SelectingBoundedThickKernelChain.literal_restricted_strict_chain E
        S.toEndomorphism F j⟩

end
end Note198
