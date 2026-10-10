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
  sorry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Genuine exactness of the same functor restricted to the original Db scope. -/
theorem restricted_phi_isTriangulated :
    (SelectingBoundedThickKernelChain.phi E S).IsTriangulated := by
  sorry

end
end Note198.SelectingExactFunctor
