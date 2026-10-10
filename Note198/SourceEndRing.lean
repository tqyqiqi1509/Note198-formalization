import Note198.SourceInflationHom
import Mathlib.RingTheory.SimpleModule.Basic

namespace Note198
noncomputable section
open OAI.LittleFinitistic OAI.LittleFinitistic.QuadraticEncoding
open OAI.LittleFinitistic.SelectionEncoding
universe u v w
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable (E : Encoding k R)
variable {S X : Type u} [Ring S] [Algebra k S] [AddCommGroup X] [Module k X]
  [Module (B E.relations × S) X] [Module (B E.relations × S)ᵐᵒᵖ X]
  [IsScalarTower k (B E.relations × S) X]
  [IsScalarTower k (B E.relations × S)ᵐᵒᵖ X]
  [SMulCommClass (B E.relations × S) (B E.relations × S)ᵐᵒᵖ X]
variable {Y : Type w} [AddCommGroup Y] [Module k Y] [Module R Y] [IsScalarTower k R Y]

abbrev SelectingEvaluation := RingInflation
  (selecting_first_projection (k := k) (L := B E.relations) (R := S) (X := X))
  (sourceRepresentation (Y := Y) E).Evaluation

/-- The actual Hom correspondence preserves addition and composition.
Thus Schur transfers from the simple source module to M(V), which itself
has Loewy length three and is not assumed simple as an A-module. -/
def source_selecting_end_ring_equiv : Module.End R Y ≃+*
    Module.End (TrivSqZeroExt (B E.relations × S) X) (SelectingEvaluation (S := S) (X := X) (Y := Y) E) where
  __ := source_selecting_hom_equiv (S := S) (X := X) (Y := Y) (Z := Y) E
  map_add' F G := by apply LinearMap.ext; intro y; rfl
  map_mul' F G := by apply LinearMap.ext; intro y; rfl

theorem source_selecting_end_nonzero_isUnit [IsSimpleModule R Y]
    (a : Module.End (TrivSqZeroExt (B E.relations × S) X)
      (SelectingEvaluation (S := S) (X := X) (Y := Y) E)) (ha : a ≠ 0) : IsUnit a := by
  classical
  let e := source_selecting_end_ring_equiv (S := S) (X := X) (Y := Y) E
  have hh : e.symm a ≠ 0 := by
    intro h
    have hz := congrArg e h
    simp only [RingEquiv.apply_symm_apply,map_zero] at hz
    exact ha hz
  have hu : IsUnit (e.symm a) := isUnit_iff_ne_zero.mpr hh
  have hv := hu.map e.toRingHom
  change IsUnit (e (e.symm a)) at hv
  rw [e.apply_symm_apply] at hv
  exact hv

/-- This division-ring structure retains the original endomorphism ring's
addition, multiplication and identity; only inverses are supplied. -/
def source_selecting_end_divisionRing [IsSimpleModule R Y] :
    DivisionRing (Module.End (TrivSqZeroExt (B E.relations × S) X)
      (SelectingEvaluation (S := S) (X := X) (Y := Y) E)) := by
  classical
  let e := source_selecting_end_ring_equiv (S := S) (X := X) (Y := Y) E
  letI : Nontrivial (Module.End (TrivSqZeroExt (B E.relations × S) X)
      (SelectingEvaluation (S := S) (X := X) (Y := Y) E)) :=
    ⟨⟨e 0,e 1,fun h => zero_ne_one (e.injective h)⟩⟩
  exact DivisionRing.ofIsUnitOrEqZero (fun a => by
    by_cases h : a = 0
    · exact Or.inr h
    · exact Or.inl (source_selecting_end_nonzero_isUnit E a h))

theorem source_selecting_end_divisionRing_original_ring [IsSimpleModule R Y] :
    (source_selecting_end_divisionRing (S := S) (X := X) (Y := Y) E).toRing =
      inferInstanceAs (Ring (Module.End (TrivSqZeroExt (B E.relations × S) X)
        (SelectingEvaluation (S := S) (X := X) (Y := Y) E))) := rfl

variable {Z : Type w} [AddCommGroup Z] [Module k Z] [Module R Z] [IsScalarTower k R Z]

/-- Nonisomorphic simple source modules give orthogonal inflated modules;
the hypothesis is source nonisomorphism, not an assumed vanishing Hom. -/
theorem source_selecting_hom_zero_of_nonisomorphic [IsSimpleModule R Y] [IsSimpleModule R Z]
    (hne : ¬ Nonempty (Y ≃ₗ[R] Z))
    (F : SelectingEvaluation (S := S) (X := X) (Y := Y) E →ₗ[
      TrivSqZeroExt (B E.relations × S) X]
      SelectingEvaluation (S := S) (X := X) (Y := Z) E) : F = 0 := by
  let e := source_selecting_hom_equiv (S := S) (X := X) (Y := Y) (Z := Z) E
  have hf : e.symm F = 0 := by
    by_contra h
    exact hne ⟨LinearEquiv.ofBijective (e.symm F) (LinearMap.bijective_of_ne_zero h)⟩
  have h := congrArg e hf
  have hz : e 0 = 0 := by apply LinearMap.ext; intro y; rfl
  simpa only [Equiv.apply_symm_apply,hz] using h

end
end Note198
