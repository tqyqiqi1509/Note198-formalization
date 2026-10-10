import Note198.SelectingFamilyProjectiveDimension
import Note198.SelectingAsymmetry
import OAI.Algebra.Finitistic.Basic

namespace Note198.SelectingMain
noncomputable section
open CategoryTheory OAI OAI.LittleFinitistic
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
variable (F : SelectingBrickFamily.SourceFamily k R S)
open SelectingOrdinaryAlgebra

include F in
/-- The actual family's finite projective dimensions are unbounded among
actual finitely generated A-modules, as required by the literal definition. -/
theorem infinite_little : littleFinitisticDimension (A E S) = ⊤ := by
  apply littleFinitisticDimension_eq_top_of_unbounded
  intro n
  let m : ℕ+ := ⟨n+1,by omega⟩
  let N := ModuleCat.of (A E S) (SelectingBrickFamily.module E S F m)
  letI : FiniteDimensional k (SelectingBrickFamily.module E S F m) :=
    SelectingBrickFamily.finite E S F m
  have hfg : Module.Finite (A E S) N :=
    Module.Finite.of_restrictScalars_finite k (A E S) (SelectingBrickFamily.module E S F m)
  refine ⟨N,hfg,SelectingFamilyProjectiveDimension.brick_finite_pd E S F m,?_⟩
  have hL := (SelectingFamilyProjectiveDimension.brick_bounds E S F m).1
  have hn : n ≤ (SelectingFamilyMaximum.coefficient E S+5)*(m.val-1)+1 := by
    have hmul := Nat.mul_le_mul_right n (show 5 ≤ SelectingFamilyMaximum.coefficient E S+5 by omega)
    dsimp [m]
    omega
  exact le_trans (by exact_mod_cast hn) hL

theorem vertex_scalar_corner (i : SelectingAlgebraProperties.VertexIndex E S) (a : A E S) :
    ∃ c : k, SelectingAlgebraProperties.vertex E S i * a * SelectingAlgebraProperties.vertex E S i =
      c • SelectingAlgebraProperties.vertex E S i :=
  constructed_vertex_scalar_corner
    (O := O E S) (T := OrdinarySimulation.TerminalTensor (QuadraticEncoding.B E.relations))
    (QuadraticEncoding.composition E.relations) (length E S) i a

/-- All general-field assertions about one actual algebra and its actual
three-copy family. The coefficient b_* is `coefficient E S`; the support
length l is `length E S`. The fields below are conclusions proved below. -/
structure MainProperties : Prop where
  algebra_finite : FiniteDimensional k (A E S)
  split_basic : Nonempty
    (NoncommutativeQuotient (Ring.jacobson (A E S)) ≃ₐ[k]
      (Fin (3*length E S+6) → k))
  radical_seven : Ring.jacobson (A E S)^7 = ⊥
  finite_modules : ∀ m, FiniteDimensional k (SelectingBrickFamily.module E S F m)
  module_dimensions : ∀ m, Module.finrank k (SelectingBrickFamily.module E S F m) =
    3*Module.finrank k (EndomorphismSelection.vectorObject (k:=k) (F.V m))
  loewy_three : ∀ m,
    (∀ a ∈ Ring.jacobson (A E S)^3, ∀ x : SelectingBrickFamily.module E S F m, a • x=0) ∧
    (∃ a ∈ Ring.jacobson (A E S)^2, ∃ x : SelectingBrickFamily.module E S F m, a • x≠0)
  end_division : ∀ m, ∃ d : DivisionRing
    (Module.End (A E S) (SelectingBrickFamily.module E S F m)), d.toRing =
      inferInstanceAs (Ring (Module.End (A E S) (SelectingBrickFamily.module E S F m)))
  hom_zero : ∀ m n, m≠n → ∀ f : SelectingBrickFamily.module E S F m →ₗ[A E S]
    SelectingBrickFamily.module E S F n, f=0
  exact_pd : ∀ m, projectiveDimension
    (ModuleCat.of (A E S) (SelectingBrickFamily.module E S F m)) =
      (SelectingFamilyMaximum.maximum E S F m : ℕ)
  linear_bounds : ∀ m,
    ((SelectingFamilyMaximum.coefficient E S+5)*(m.val-1)+1 : ℕ) ≤
      projectiveDimension (ModuleCat.of (A E S) (SelectingBrickFamily.module E S F m)) ∧
    projectiveDimension (ModuleCat.of (A E S) (SelectingBrickFamily.module E S F m)) ≤
      ((SelectingFamilyMaximum.coefficient E S+5)*(m.val-1)+length E S+3 : ℕ)
  complete_vertices : CompleteOrthogonalIdempotents (SelectingAlgebraProperties.vertex E S)
  primitive_vertices : ∀ i, IsPrimitiveIdempotent (SelectingAlgebraProperties.vertex E S i)
  field_corners : ∀ i, ∃ he : IsIdempotentElem (SelectingAlgebraProperties.vertex E S i),
    Nonempty (he.Corner ≃+* k)
  scalar_corners : ∀ i (a : A E S), ∃ c : k,
    SelectingAlgebraProperties.vertex E S i * a * SelectingAlgebraProperties.vertex E S i =
      c • SelectingAlgebraProperties.vertex E S i
  finitistic_infinite : littleFinitisticDimension (A E S) = ⊤

theorem main_properties : MainProperties E S F := {
  algebra_finite := SelectingAlgebraProperties.finite E S
  split_basic := SelectingAlgebraProperties.residue_isomorphism E S
  radical_seven := SelectingAlgebraProperties.radical_pow_seven_zero E S
  finite_modules := SelectingBrickFamily.finite E S F
  module_dimensions := SelectingBrickFamily.dimension E S F
  loewy_three := SelectingBrickFamily.loewy_exact_three E S F
  end_division := fun m => ⟨SelectingBrickFamily.endDivisionRing E S F m,
    SelectingBrickFamily.endDivisionRing_original_ring E S F m⟩
  hom_zero := SelectingBrickFamily.cross_hom_zero E S F
  exact_pd := SelectingFamilyProjectiveDimension.brick_dimension E S F
  linear_bounds := SelectingFamilyProjectiveDimension.brick_bounds E S F
  complete_vertices := SelectingAlgebraProperties.complete_orthogonal_idempotents E S
  primitive_vertices := SelectingAlgebraProperties.primitive E S
  field_corners := SelectingAlgebraProperties.corner_is_field E S
  scalar_corners := vertex_scalar_corner E S
  finitistic_infinite := infinite_little E S F }

include F in
/-- Section 8 for the current actually constructed A: no unboundedness
premise remains, and the derived injective-generation assertions are the
literal generic-field upstream theorems. -/
theorem asymmetry :
    FiniteDimensional k (SelectingAsymmetry.Lambda E S) ∧
    littleFinitisticDimension (SelectingAsymmetry.Lambda E S)=⊤ ∧
    bigFinitisticDimension (SelectingAsymmetry.Lambda E S)=⊤ ∧
    littleFinitisticDimension (SelectingAsymmetry.Lambda E S)ᵐᵒᵖ=0 ∧
    bigFinitisticDimension (SelectingAsymmetry.Lambda E S)ᵐᵒᵖ=0 ∧
    ¬ InjectivesGenerate (SelectingAsymmetry.Lambda E S) ∧
    InjectivesGenerate (SelectingAsymmetry.Lambda E S)ᵐᵒᵖ :=
  SelectingAsymmetry.all_clauses E S (infinite_little E S F)

/-- Theorem 1.1 over every field: the source family and its one encoding
are constructed before the fixed algebra and every member of the family. -/
theorem every_field (k : Type u) [Field k] :
    ∃ (R : Type u) (rR : Ring R), letI : Ring R := rR
      ∃ aR : Algebra k R, letI : Algebra k R := aR
        ∃ (S : Selection.Data k R) (E : SelectionEncoding.Encoding k R)
          (F : SelectingBrickFamily.SourceFamily k R S.toEndomorphism),
            MainProperties E S.toEndomorphism F := by
  obtain ⟨R,rR,aR,S,E,⟨F⟩⟩ := SelectingBrickFamily.exists_source_family k
  letI := rR
  letI := aR
  exact ⟨R,rR,aR,S,E,F,main_properties E S.toEndomorphism F⟩

/-- The same actual general-field choice supplies Section 8, together
with every assertion of the constructed Section 1/7 family. -/
theorem every_field_with_asymmetry (k : Type u) [Field k] :
    ∃ (R : Type u) (rR : Ring R), letI : Ring R := rR
      ∃ aR : Algebra k R, letI : Algebra k R := aR
        ∃ (S : Selection.Data k R) (E : SelectionEncoding.Encoding k R)
          (F : SelectingBrickFamily.SourceFamily k R S.toEndomorphism),
          MainProperties E S.toEndomorphism F ∧
          FiniteDimensional k (SelectingAsymmetry.Lambda E S.toEndomorphism) ∧
          littleFinitisticDimension (SelectingAsymmetry.Lambda E S.toEndomorphism)=⊤ ∧
          bigFinitisticDimension (SelectingAsymmetry.Lambda E S.toEndomorphism)=⊤ ∧
          littleFinitisticDimension (SelectingAsymmetry.Lambda E S.toEndomorphism)ᵐᵒᵖ=0 ∧
          bigFinitisticDimension (SelectingAsymmetry.Lambda E S.toEndomorphism)ᵐᵒᵖ=0 ∧
          ¬ InjectivesGenerate (SelectingAsymmetry.Lambda E S.toEndomorphism) ∧
          InjectivesGenerate (SelectingAsymmetry.Lambda E S.toEndomorphism)ᵐᵒᵖ := by
  obtain ⟨R,rR,aR,S,E,F,h⟩ := every_field k
  letI := rR
  letI := aR
  exact ⟨R,rR,aR,S,E,F,h,asymmetry E S.toEndomorphism F⟩
end
end Note198.SelectingMain
