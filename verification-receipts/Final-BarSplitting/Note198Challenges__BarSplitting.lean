import OAI.Algebra.Finitistic.Bar.DerivedTensorBarSplitting

namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.DerivedBar TrivSqZeroExt OAI.DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
attribute [local instance] OAI.DerivedBar.derivedTensorBarSplittingHasDerivedCategory

/-- For the actual square-zero extension A=D⋉X and inflated N, derived
base change is the categorical coproduct of the shifted derived tensor
iterates. X is not assumed right-projective. The coproduct lives in the
integer derived category and includes every nonnegative iterate. -/
theorem square_zero_derived_bar_splitting (N : ModuleCat.{u} D) :
    Nonempty ((derivedBaseChange D (fstHom k D X)).obj
      (@ModuleCat.of (TrivSqZeroExt D X) inferInstance N inferInstance
        (inflatedModule D X N)) ≅
      colimit (ParityBridge.shiftedIterateDiagram k D X N)) := by
  sorry

end
end Note198
