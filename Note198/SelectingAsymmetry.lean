import Note198.SelectingAlgebraProperties
import OAI.Algebra.FinitisticAsymmetry.Asymmetry
import OAI.Algebra.FinitisticAsymmetry.Augmentation.SplitBasic

namespace Note198
noncomputable section
open OAI.LittleFinitistic
universe u
namespace SelectingAsymmetry
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)

instance actual_A_nontrivial : Nontrivial (SelectingOrdinaryAlgebra.A E S) :=
  ⟨⟨SelectingAlgebraProperties.vertex E S (Sum.inl 0),0,
    (SelectingAlgebraProperties.primitive E S (Sum.inl 0)).1⟩⟩

/-- Lift the finite vertex index to the algebra's universe, preserving
all vertices. This is needed by the upstream unbounded derived-category
statement over arbitrary fields, whose coproduct sizes live in Type u. -/
abbrev Vertices := ULift.{u} (Fin (3 * SelectingOrdinaryAlgebra.length E S + 6))

def residueEquiv : NoncommutativeQuotient (Ring.jacobson (SelectingOrdinaryAlgebra.A E S))
    ≃ₐ[k] (Vertices E S → k) :=
  (SelectingAlgebraProperties.residueEquiv E S).trans
    (field_product_reindex (Equiv.ulift.symm :
      Fin (3 * SelectingOrdinaryAlgebra.length E S + 6) ≃ Vertices E S))

def augmentation : SelectingOrdinaryAlgebra.A E S →ₐ[k] (Vertices E S → k) :=
  (residueEquiv E S).toAlgHom.comp
    ((ideal_ring_con (Ring.jacobson (SelectingOrdinaryAlgebra.A E S))).mkₐ k)

theorem augmentation_surjective : Function.Surjective (augmentation E S) :=
  (residueEquiv E S).surjective.comp
    ((ideal_ring_con (Ring.jacobson (SelectingOrdinaryAlgebra.A E S))).mkₐ_surjective (α := k))

theorem augmentation_kernel : RingHom.ker (augmentation E S).toRingHom =
    Ring.jacobson (SelectingOrdinaryAlgebra.A E S) := by
  ext a
  change (residueEquiv E S)
    ((ideal_ring_con (Ring.jacobson (SelectingOrdinaryAlgebra.A E S))).mkₐ k a) = 0 ↔
      a ∈ Ring.jacobson (SelectingOrdinaryAlgebra.A E S)
  rw [← (residueEquiv E S).map_zero]
  change (residueEquiv E S)
    ((ideal_ring_con (Ring.jacobson (SelectingOrdinaryAlgebra.A E S))).mkₐ k a) =
      (residueEquiv E S)
        (0 : NoncommutativeQuotient (Ring.jacobson (SelectingOrdinaryAlgebra.A E S))) ↔
          a ∈ Ring.jacobson (SelectingOrdinaryAlgebra.A E S)
  rw [(residueEquiv E S).injective.eq_iff]
  change (a : NoncommutativeQuotient (Ring.jacobson (SelectingOrdinaryAlgebra.A E S))) =
      ((0 : SelectingOrdinaryAlgebra.A E S) :
        NoncommutativeQuotient (Ring.jacobson (SelectingOrdinaryAlgebra.A E S))) ↔ _
  rw [(ideal_ring_con (Ring.jacobson (SelectingOrdinaryAlgebra.A E S))).eq,
    ideal_ring_con_rel,sub_zero]

theorem augmentation_kernel_nilpotent :
    ∃ n : ℕ, (RingHom.ker (augmentation E S).toRingHom)^n = ⊥ := by
  refine ⟨7,?_⟩
  rw [augmentation_kernel]
  exact SelectingAlgebraProperties.radical_pow_seven_zero E S

def oppositeAugmentation : (SelectingOrdinaryAlgebra.A E S)ᵐᵒᵖ →ₐ[k] (Vertices E S → k) :=
  SplitBasic.oppositeAugmentation (augmentation E S)

theorem oppositeAugmentation_surjective : Function.Surjective (oppositeAugmentation E S) :=
  SplitBasic.opposite_surjective _ (augmentation_surjective E S)

theorem oppositeAugmentation_kernel_nilpotent :
    ∃ n : ℕ, (RingHom.ker (oppositeAugmentation E S).toRingHom)^n = ⊥ :=
  SplitBasic.opposite_ker_nilpotent _ (augmentation_kernel_nilpotent E S)

/-- The actual Section 8 algebra, using the already formalized lower
triangular construction and its opposite, with the fixed actual A. -/
abbrev Lambda := AsymmetryConstruction.Lambda (oppositeAugmentation E S)

/-- All Section 8 clauses follow for the actual fixed A as soon as its
already specified unbounded little finitistic dimension is established.
Injective generation and non-generation are actual derived-category
propositions proved upstream, rather than certificate fields or axioms. -/
theorem all_clauses
    (hA : OAI.LittleFinitistic.littleFinitisticDimension (SelectingOrdinaryAlgebra.A E S) = ⊤) :
    FiniteDimensional k (Lambda E S) ∧
      littleFinitisticDimension (Lambda E S) = ⊤ ∧ bigFinitisticDimension (Lambda E S) = ⊤ ∧
      littleFinitisticDimension (Lambda E S)ᵐᵒᵖ = 0 ∧ bigFinitisticDimension (Lambda E S)ᵐᵒᵖ = 0 ∧
      ¬ InjectivesGenerate (Lambda E S) ∧ InjectivesGenerate (Lambda E S)ᵐᵒᵖ :=
  AsymmetryConstruction.all_clauses (oppositeAugmentation E S)
    (oppositeAugmentation_surjective E S) (oppositeAugmentation_kernel_nilpotent E S) hA

end SelectingAsymmetry
end
end Note198
