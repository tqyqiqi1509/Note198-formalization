import Note198.MainPacket

/-! Complete statements of the general-field main theorem.  The equivalence
below checks that expanding the fifteen fields preserves the original interface. -/
namespace Note198.Collaborator
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
attribute [local instance] HasDerivedCategory.standard
universe u

/-- Theorem 1.1: a single algebra and its family over every field, with all
fifteen assertions displayed in the conclusion. -/
theorem theorem_1_1 (k : Type u) [Field k] :
    ∃ (R : Type u) (rR : Ring R), letI : Ring R := rR
      ∃ aR : Algebra k R, letI : Algebra k R := aR
        ∃ (S : Selection.Data k R) (E : SelectionEncoding.Encoding k R)
          (F : SelectingBrickFamily.SourceFamily k R S.toEndomorphism),
          -- 1. Finite-dimensional algebra.
          (FiniteDimensional k (SelectingOrdinaryAlgebra.A E S.toEndomorphism)) ∧
          -- 2. Split basic quotient.
          (Nonempty
            (NoncommutativeQuotient
              (Ring.jacobson (SelectingOrdinaryAlgebra.A E S.toEndomorphism)) ≃ₐ[k]
              (Fin (3*SelectingOrdinaryAlgebra.length E S.toEndomorphism+6) → k))) ∧
          -- 3. Seventh power of the radical vanishes.
          (Ring.jacobson (SelectingOrdinaryAlgebra.A E S.toEndomorphism)^7 = ⊥) ∧
          -- 4. Finite-dimensional family members.
          (∀ m : ℕ+, FiniteDimensional k (SelectingBrickFamily.module E S.toEndomorphism F m)) ∧
          -- 5. Dimensions of the three-copy modules.
          (∀ m : ℕ+, Module.finrank k (SelectingBrickFamily.module E S.toEndomorphism F m) =
            3*Module.finrank k (EndomorphismSelection.vectorObject (k:=k) (F.V m))) ∧
          -- 6. Every family member has Loewy length exactly three.
          (∀ m : ℕ+,
            (∀ a ∈ Ring.jacobson (SelectingOrdinaryAlgebra.A E S.toEndomorphism)^3,
              ∀ x : SelectingBrickFamily.module E S.toEndomorphism F m, a • x=0) ∧
            (∃ a ∈ Ring.jacobson (SelectingOrdinaryAlgebra.A E S.toEndomorphism)^2,
              ∃ x : SelectingBrickFamily.module E S.toEndomorphism F m, a • x≠0)) ∧
          -- 7. Endomorphism division rings, with the original ring structure.
          (∀ m : ℕ+, ∃ d : DivisionRing
            (Module.End (SelectingOrdinaryAlgebra.A E S.toEndomorphism)
              (SelectingBrickFamily.module E S.toEndomorphism F m)),
            d.toRing = inferInstanceAs
              (Ring (Module.End (SelectingOrdinaryAlgebra.A E S.toEndomorphism)
              (SelectingBrickFamily.module E S.toEndomorphism F m)))) ∧
          -- 8. Distinct family members have no nonzero homomorphisms.
          (∀ (m n : ℕ+), m≠n →
            ∀ f : SelectingBrickFamily.module E S.toEndomorphism F m
              →ₗ[SelectingOrdinaryAlgebra.A E S.toEndomorphism]
              SelectingBrickFamily.module E S.toEndomorphism F n,
            f=0) ∧
          -- 9. Exact projective dimensions.
          (∀ m : ℕ+, projectiveDimension
            (ModuleCat.of (SelectingOrdinaryAlgebra.A E S.toEndomorphism)
              (SelectingBrickFamily.module E S.toEndomorphism F m)) =
            (SelectingFamilyMaximum.maximum E S.toEndomorphism F m : ℕ)) ∧
          -- 10. Lower and upper projective-dimension bounds.
          (∀ m : ℕ+,
            ((SelectingFamilyMaximum.coefficient E S.toEndomorphism+5)*(m.val-1)+1 : ℕ) ≤
              projectiveDimension
              (ModuleCat.of (SelectingOrdinaryAlgebra.A E S.toEndomorphism)
              (SelectingBrickFamily.module E S.toEndomorphism F m)) ∧
            projectiveDimension
              (ModuleCat.of (SelectingOrdinaryAlgebra.A E S.toEndomorphism)
              (SelectingBrickFamily.module E S.toEndomorphism F m)) ≤
              ((SelectingFamilyMaximum.coefficient E S.toEndomorphism+5)*(m.val-1)
              +SelectingOrdinaryAlgebra.length E S.toEndomorphism+3 : ℕ)) ∧
          -- 11. Complete orthogonal vertex idempotents.
          (CompleteOrthogonalIdempotents (SelectingAlgebraProperties.vertex E S.toEndomorphism)) ∧
          -- 12. Primitive vertex idempotents.
          (∀ i, IsPrimitiveIdempotent (SelectingAlgebraProperties.vertex E S.toEndomorphism i)) ∧
          -- 13. Vertex corners are the base field.
          (∀ i, ∃ he : IsIdempotentElem (SelectingAlgebraProperties.vertex E S.toEndomorphism i),
            Nonempty (he.Corner ≃+* k)) ∧
          -- 14. Scalar action on each vertex corner.
          (∀ i (a : SelectingOrdinaryAlgebra.A E S.toEndomorphism), ∃ c : k,
            SelectingAlgebraProperties.vertex E S.toEndomorphism i * a *
              SelectingAlgebraProperties.vertex E S.toEndomorphism i =
              c • SelectingAlgebraProperties.vertex E S.toEndomorphism i) ∧
          -- 15. Infinite little finitistic dimension.
          (littleFinitisticDimension (SelectingOrdinaryAlgebra.A E S.toEndomorphism) = ⊤) := by
  obtain ⟨R, rR, aR, S, E, F, h⟩ := SelectingMain.every_field k
  letI := rR
  letI := aR
  exact ⟨R, rR, aR, S, E, F,
    h.algebra_finite,
    h.split_basic,
    h.radical_seven,
    h.finite_modules,
    h.module_dimensions,
    h.loewy_three,
    h.end_division,
    h.hom_zero,
    h.exact_pd,
    h.linear_bounds,
    h.complete_vertices,
    h.primitive_vertices,
    h.field_corners,
    h.scalar_corners,
    h.finitistic_infinite⟩

/-- Expanding the main construction preserves every field of its original statement. -/
theorem main_properties_iff_expanded
    {k R : Type u} [Field k] [Ring R] [Algebra k R]
    (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
    (F : SelectingBrickFamily.SourceFamily k R S) :
    SelectingMain.MainProperties E S F ↔
    -- 1. Finite-dimensional algebra.
    (FiniteDimensional k (SelectingOrdinaryAlgebra.A E S)) ∧
    -- 2. Split basic quotient.
    (Nonempty
      (NoncommutativeQuotient
        (Ring.jacobson (SelectingOrdinaryAlgebra.A E S)) ≃ₐ[k]
        (Fin (3*SelectingOrdinaryAlgebra.length E S+6) → k))) ∧
    -- 3. Seventh power of the radical vanishes.
    (Ring.jacobson (SelectingOrdinaryAlgebra.A E S)^7 = ⊥) ∧
    -- 4. Finite-dimensional family members.
    (∀ m : ℕ+, FiniteDimensional k (SelectingBrickFamily.module E S F m)) ∧
    -- 5. Dimensions of the three-copy modules.
    (∀ m : ℕ+, Module.finrank k (SelectingBrickFamily.module E S F m) =
      3*Module.finrank k (EndomorphismSelection.vectorObject (k:=k) (F.V m))) ∧
    -- 6. Every family member has Loewy length exactly three.
    (∀ m : ℕ+,
      (∀ a ∈ Ring.jacobson (SelectingOrdinaryAlgebra.A E S)^3,
        ∀ x : SelectingBrickFamily.module E S F m, a • x=0) ∧
      (∃ a ∈ Ring.jacobson (SelectingOrdinaryAlgebra.A E S)^2,
        ∃ x : SelectingBrickFamily.module E S F m, a • x≠0)) ∧
    -- 7. Endomorphism division rings, with the original ring structure.
    (∀ m : ℕ+, ∃ d : DivisionRing
      (Module.End (SelectingOrdinaryAlgebra.A E S)
        (SelectingBrickFamily.module E S F m)),
      d.toRing = inferInstanceAs
        (Ring (Module.End (SelectingOrdinaryAlgebra.A E S)
        (SelectingBrickFamily.module E S F m)))) ∧
    -- 8. Distinct family members have no nonzero homomorphisms.
    (∀ (m n : ℕ+), m≠n →
      ∀ f : SelectingBrickFamily.module E S F m
        →ₗ[SelectingOrdinaryAlgebra.A E S]
        SelectingBrickFamily.module E S F n,
      f=0) ∧
    -- 9. Exact projective dimensions.
    (∀ m : ℕ+, projectiveDimension
      (ModuleCat.of (SelectingOrdinaryAlgebra.A E S)
        (SelectingBrickFamily.module E S F m)) =
      (SelectingFamilyMaximum.maximum E S F m : ℕ)) ∧
    -- 10. Lower and upper projective-dimension bounds.
    (∀ m : ℕ+,
      ((SelectingFamilyMaximum.coefficient E S+5)*(m.val-1)+1 : ℕ) ≤
        projectiveDimension
        (ModuleCat.of (SelectingOrdinaryAlgebra.A E S)
        (SelectingBrickFamily.module E S F m)) ∧
      projectiveDimension
        (ModuleCat.of (SelectingOrdinaryAlgebra.A E S)
        (SelectingBrickFamily.module E S F m)) ≤
        ((SelectingFamilyMaximum.coefficient E S+5)*(m.val-1)
        +SelectingOrdinaryAlgebra.length E S+3 : ℕ)) ∧
    -- 11. Complete orthogonal vertex idempotents.
    (CompleteOrthogonalIdempotents (SelectingAlgebraProperties.vertex E S)) ∧
    -- 12. Primitive vertex idempotents.
    (∀ i, IsPrimitiveIdempotent (SelectingAlgebraProperties.vertex E S i)) ∧
    -- 13. Vertex corners are the base field.
    (∀ i, ∃ he : IsIdempotentElem (SelectingAlgebraProperties.vertex E S i),
      Nonempty (he.Corner ≃+* k)) ∧
    -- 14. Scalar action on each vertex corner.
    (∀ i (a : SelectingOrdinaryAlgebra.A E S), ∃ c : k,
      SelectingAlgebraProperties.vertex E S i * a *
        SelectingAlgebraProperties.vertex E S i =
        c • SelectingAlgebraProperties.vertex E S i) ∧
    -- 15. Infinite little finitistic dimension.
    (littleFinitisticDimension (SelectingOrdinaryAlgebra.A E S) = ⊤) := by
  constructor
  · intro h
    exact ⟨h.algebra_finite,
      h.split_basic,
      h.radical_seven,
      h.finite_modules,
      h.module_dimensions,
      h.loewy_three,
      h.end_division,
      h.hom_zero,
      h.exact_pd,
      h.linear_bounds,
      h.complete_vertices,
      h.primitive_vertices,
      h.field_corners,
      h.scalar_corners,
      h.finitistic_infinite⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
    exact {
      algebra_finite := h1
      split_basic := h2
      radical_seven := h3
      finite_modules := h4
      module_dimensions := h5
      loewy_three := h6
      end_division := h7
      hom_zero := h8
      exact_pd := h9
      linear_bounds := h10
      complete_vertices := h11
      primitive_vertices := h12
      field_corners := h13
      scalar_corners := h14
      finitistic_infinite := h15
    }
end
end Note198.Collaborator
