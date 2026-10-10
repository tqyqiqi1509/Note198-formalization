import Note198.SelectingMain
import Note198.SelectingFamilyExactFormula
import Note198.ComplexBrickFamily
import Note198.GenericOddRealization

/-! Final-statement checks for the main construction. This packet does not
claim to be the whole twenty-result manuscript: the general bar statements,
rectification, and thick kernel assertion have their own checks. -/
namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
attribute [local instance] HasDerivedCategory.standard
universe u

theorem packet_general_main_and_asymmetry (k : Type u) [Field k] :
    ∃ (R : Type u) (rR : Ring R), letI : Ring R := rR
      ∃ aR : Algebra k R, letI : Algebra k R := aR
        ∃ (S : Selection.Data k R) (E : SelectionEncoding.Encoding k R)
          (F : SelectingBrickFamily.SourceFamily k R S.toEndomorphism),
          SelectingMain.MainProperties E S.toEndomorphism F ∧
          FiniteDimensional k (SelectingAsymmetry.Lambda E S.toEndomorphism) ∧
          littleFinitisticDimension (SelectingAsymmetry.Lambda E S.toEndomorphism)=⊤ ∧
          bigFinitisticDimension (SelectingAsymmetry.Lambda E S.toEndomorphism)=⊤ ∧
          littleFinitisticDimension (SelectingAsymmetry.Lambda E S.toEndomorphism)ᵐᵒᵖ=0 ∧
          bigFinitisticDimension (SelectingAsymmetry.Lambda E S.toEndomorphism)ᵐᵒᵖ=0 ∧
          ¬ InjectivesGenerate (SelectingAsymmetry.Lambda E S.toEndomorphism) ∧
          InjectivesGenerate (SelectingAsymmetry.Lambda E S.toEndomorphism)ᵐᵒᵖ := by
  sorry

theorem packet_complex_bricks (m : ℕ+) :
    SelectingMain.MainProperties ComplexBrickFamily.encoding
      ComplexBrickFamily.selection.toEndomorphism ComplexBrickFamily.family ∧
    Module.finrank ℂ (ComplexBrickFamily.M m) = 3*2^(3*m.val) ∧
    Nonempty (ℂ ≃ₐ[ℂ] Module.End ComplexBrickFamily.A (ComplexBrickFamily.M m)) ∧
    (∀ n : ℕ+, m ≠ n → ∀ f : ComplexBrickFamily.M m →ₗ[ComplexBrickFamily.A]
      ComplexBrickFamily.M n, f=0) := by
  sorry

theorem packet_all_odd_shifts
    {k R : Type u} [Field k] [Ring R] [Algebra k R]
    (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
    (s : ℤ) (hs : 3 ≤ s) (hodd : Odd s) :
    ∃ P : ExternalTensor.Section4.BiComplex k (QuadraticEncoding.B E.relations),
      (∃ lo hi : ℤ, ∀ n, n < lo ∨ hi < n → IsZero (P.X n)) ∧
      (∀ n, Projective (P.X n)) ∧
      (∀ n, FiniteDimensional k ((ExternalTensor.Section4.forgetK k
        (QuadraticEncoding.B E.relations)).obj (P.X n))) ∧
      ∀ (Y : Type u) [AddCommGroup Y] [Module k Y] [Module R Y]
        [IsScalarTower k R Y] [FiniteDimensional k Y],
        Nonempty (DerivedCategory.Q.obj
          (((BimoduleBalancedTensor.functor k (QuadraticEncoding.B E.relations)
            (GenericOddRealization.input (E := E) (Y := Y))).mapHomologicalComplex (.up ℤ)).obj P) ≅
          (DerivedCategory.singleFunctor (ModuleCat (QuadraticEncoding.B E.relations)) 0).obj
            (GenericOddRealization.reference (E := E) (S := S) (Y := Y)) ⊞
          ((DerivedCategory.singleFunctor (ModuleCat (QuadraticEncoding.B E.relations)) 0).obj
            (GenericOddRealization.reference (E := E) (S := S) (Y := Y)))⟦s⟧) := by
  sorry

theorem packet_actual_module_formula
    {k R : Type u} [Field k] [Ring R] [Algebra k R]
    (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
    (F : SelectingBrickFamily.SourceFamily k R S) (m : ℕ+) :
    projectiveDimension (ModuleCat.of (SelectingOrdinaryAlgebra.A E S)
      (SelectingBrickFamily.module E S F m)) =
      ⨆ i : Sum (Fin m.val) (Fin m.val), match i with
        | .inl j => (((SelectingFamilyMaximum.coefficient E S+5)*j.val : ℕ) : WithBot ℕ∞) +
            projectiveDimension (SelectingOrdinaryOddSplit.input E
              (((SelectingIteration.selected S)^[j.val]) (SelectingFamilyFiniteBar.source F m)))
        | .inr j => (((SelectingFamilyMaximum.coefficient E S+5)*j.val+1 : ℕ) : WithBot ℕ∞) +
            projectiveDimension (SelectingOrdinaryOddSplit.Qmodule E S
              (((SelectingIteration.selected S)^[j.val]) (SelectingFamilyFiniteBar.source F m))) := by
  sorry

end
end Note198
