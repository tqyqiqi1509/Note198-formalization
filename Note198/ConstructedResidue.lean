import Note198.RadicalResidueBridge

namespace Note198
noncomputable section
open scoped TensorProduct
open OAI.LittleFinitistic OAI.LittleFinitistic.OrdinarySimulation
universe u
variable {k V W U : Type u} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U) (l : ℕ)
variable {O T : Type u} [AddCommGroup O] [AddCommGroup T] [Module k O] [Module k T]
  [Module (ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l) O]
  [Module (ThreeVertexAlgebra μ) T]
  [Module (ThreeVertexAlgebra μ)ᵐᵒᵖ O]
  [Module (ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l)ᵐᵒᵖ T]
  [SMulCommClass (ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l)
    (ThreeVertexAlgebra μ)ᵐᵒᵖ O]
  [SMulCommClass (ThreeVertexAlgebra μ)
    (ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l)ᵐᵒᵖ T]
  [IsScalarTower k (ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l) O]
  [IsScalarTower k (ThreeVertexAlgebra μ) T]
  [IsScalarTower k (ThreeVertexAlgebra μ)ᵐᵒᵖ O]
  [IsScalarTower k (ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l)ᵐᵒᵖ T]

/-- The exact residue algebra in Proposition 7.1, for the constructed
three-vertex algebra and the actual chain algebra. The equivalence is
over k and uses the actual Jacobson radical. -/
def constructed_residue_equiv :
    NoncommutativeQuotient (Ring.jacobson (TrivSqZeroExt
          (ThreeVertexAlgebra μ × (ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l))
          (OffDiagonal O T))) ≃ₐ[k] (Fin (3 * l + 6) → k) := by
  let DB := ThreeVertexAlgebra.directedSystem μ
  let hB : ∀ i, DB.e i ≠ 0 := three_vertex_nonzero μ
  let DE := TensorDirected.directedSystem DB (ChainAlgebra.directedSystem k l)
  let hE : ∀ i, DE.e i ≠ 0 := encoding_tensor_vertex_nonzero μ l
  let f := directed_augmentation DB hB
  let g := directed_augmentation DE hE
  let h := product_diagonal_augmentation f g
  have hf := directed_augmentation_surjective DB hB
  have hg := directed_augmentation_surjective DE hE
  have hh := product_diagonal_surjective f g hf hg
  have hk := product_diagonal_kernel_eq_radical f g hf hg 3 ((l + 1) * 3)
    (directed_kernel_pow_zero DB hB) (directed_kernel_pow_zero DE hE)
  let χ := h.comp (TrivSqZeroExt.fstHom k
    (ThreeVertexAlgebra μ × (ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l))
    (OffDiagonal O T))
  have hχ : Function.Surjective χ := by
    intro s
    obtain ⟨d, hd⟩ := hh s
    exact ⟨TrivSqZeroExt.inl d, hd⟩
  have hker : RingHom.ker χ.toRingHom =
      Ring.jacobson (TrivSqZeroExt
        (ThreeVertexAlgebra μ × (ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l))
        (OffDiagonal O T)) := by
    rw [square_zero_radical (k := k)]
    ext a
    change a.fst ∈ RingHom.ker h.toRingHom ↔ a.fst ∈ Ring.jacobson _
    rw [hk]
  let q := noncommutative_quotient_equiv (Ring.jacobson _) χ hker.symm hχ
  let e : Sum (Fin 3) (Fin ((l + 1) * 3)) ≃ Fin (3 * l + 6) :=
    (finSumFinEquiv : Sum (Fin 3) (Fin ((l + 1) * 3)) ≃ Fin (3 + (l + 1) * 3)).trans
      (finCongr (by omega))
  exact q.trans (field_product_reindex e)

theorem constructed_residue_isomorphism : Nonempty
    (NoncommutativeQuotient (Ring.jacobson (TrivSqZeroExt
          (ThreeVertexAlgebra μ × (ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l))
          (OffDiagonal O T))) ≃ₐ[k] (Fin (3 * l + 6) → k)) :=
  ⟨constructed_residue_equiv μ l⟩

end
end Note198
