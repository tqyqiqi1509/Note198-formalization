import Note198.BimoduleDerivedExact
import Note198.SelectingBoundedThickKernelChain

namespace Note198.SelectingExactFunctor
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
open ExternalTensor.Section4
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)

/-- Exactness of the actually constructed native selecting derived tensor
functor; no exactness witness is a hypothesis. -/
theorem phi_isTriangulated : (SelectingDerivedFunctor.Phi E S).IsTriangulated := by
  let d := SelectingDerivedFunctor.model E S
  letI : ∀ i, Module.Projective (QuadraticEncoding.B E.relations)ᵐᵒᵖ
      (ComplexTensor.rightTerm k (QuadraticEncoding.B E.relations)
        (BimoduleTotal.right k _ (SelectingRectification.bimodule E S)) (d.degrees i)) :=
    fun i => d.projective (d.degrees i)
  exact BimoduleDerivedExact.derived_isTriangulated k _ _ d.degrees
    (BimoduleTotal.intervalDegrees_strictMono d.lower d.upper)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Genuine exactness of the same functor restricted to the original Db scope. -/
theorem restricted_phi_isTriangulated :
    (SelectingBoundedThickKernelChain.phi E S).IsTriangulated := by
  letI : (SelectingDerivedFunctor.Phi E S).IsTriangulated := phi_isTriangulated E S
  let Db := SelectingBoundedThickKernelChain.boundedProperty E
  let h := fun Z : Db.FullSubcategory =>
    SelectingBoundedScope.phi_preserves_bounded_finite E S Z.obj Z.property
  letI : (SelectingDerivedFunctor.Phi E S).CommShift ℤ := inferInstance
  letI : Db.ι.CommShift ℤ := inferInstance
  letI : (Db.ι ⋙ SelectingDerivedFunctor.Phi E S).CommShift ℤ := inferInstance
  letI : (Db.lift (Db.ι ⋙ SelectingDerivedFunctor.Phi E S) h).CommShift ℤ :=
    ObjectProperty.commShiftLift Db (Db.ι ⋙ SelectingDerivedFunctor.Phi E S) h
  exact (Functor.isTriangulated_iff_comp_right
    (Db.liftCompιIso (Db.ι ⋙ SelectingDerivedFunctor.Phi E S) h)).mpr inferInstance
end
end Note198.SelectingExactFunctor
