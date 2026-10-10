import Note198.ConstructedResidue
import Note198.PrimitiveCorners
import Note198.ScalarCornerEquiv

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

def constructed_vertex (i : Sum (Fin 3) (Fin ((l + 1) * 3))) :
    TrivSqZeroExt
      (ThreeVertexAlgebra μ × (ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l))
      (OffDiagonal O T) :=
  match i with
  | .inl j => TrivSqZeroExt.inl ((ThreeVertexAlgebra.directedSystem μ).e j, 0)
  | .inr j => TrivSqZeroExt.inl (0,
      (TensorDirected.directedSystem (ThreeVertexAlgebra.directedSystem μ)
        (ChainAlgebra.directedSystem k l)).e j)

theorem constructed_vertices_orthogonal
    (i j : Sum (Fin 3) (Fin ((l + 1) * 3))) (hij : i ≠ j) :
    constructed_vertex (O := O) (T := T) μ l i * constructed_vertex μ l j = 0 := by
  let f := TrivSqZeroExt.inlHom
    (ThreeVertexAlgebra μ × (ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l)) (OffDiagonal O T)
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have h : i ≠ j := fun h => hij (congrArg Sum.inl h)
      change f ((ThreeVertexAlgebra.directedSystem μ).e i,0) *
        f ((ThreeVertexAlgebra.directedSystem μ).e j,0) = 0
      rw [← map_mul]
      have hz : ((ThreeVertexAlgebra.directedSystem μ).e i,0) *
          ((ThreeVertexAlgebra.directedSystem μ).e j,0) = (0 : ThreeVertexAlgebra μ ×
            (ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l)) :=
        Prod.ext ((ThreeVertexAlgebra.directedSystem μ).orthogonal i j h) (zero_mul 0)
      rw [hz,map_zero]
    | inr j =>
      change f ((ThreeVertexAlgebra.directedSystem μ).e i,0) *
        f (0,(TensorDirected.directedSystem (ThreeVertexAlgebra.directedSystem μ)
          (ChainAlgebra.directedSystem k l)).e j) = 0
      rw [← map_mul]
      have hz : ((ThreeVertexAlgebra.directedSystem μ).e i,0) *
          (0,(TensorDirected.directedSystem (ThreeVertexAlgebra.directedSystem μ)
            (ChainAlgebra.directedSystem k l)).e j) = (0 : ThreeVertexAlgebra μ ×
              (ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l)) :=
        Prod.ext (mul_zero _) (zero_mul _)
      rw [hz,map_zero]
  | inr i =>
    cases j with
    | inl j =>
      change f (0,(TensorDirected.directedSystem (ThreeVertexAlgebra.directedSystem μ)
        (ChainAlgebra.directedSystem k l)).e i) *
        f ((ThreeVertexAlgebra.directedSystem μ).e j,0) = 0
      rw [← map_mul]
      have hz : (0,(TensorDirected.directedSystem (ThreeVertexAlgebra.directedSystem μ)
          (ChainAlgebra.directedSystem k l)).e i) *
          ((ThreeVertexAlgebra.directedSystem μ).e j,0) = (0 : ThreeVertexAlgebra μ ×
            (ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l)) :=
        Prod.ext (zero_mul _) (mul_zero _)
      rw [hz,map_zero]
    | inr j =>
      have h : i ≠ j := fun h => hij (congrArg Sum.inr h)
      change f (0,(TensorDirected.directedSystem (ThreeVertexAlgebra.directedSystem μ)
        (ChainAlgebra.directedSystem k l)).e i) *
        f (0,(TensorDirected.directedSystem (ThreeVertexAlgebra.directedSystem μ)
          (ChainAlgebra.directedSystem k l)).e j) = 0
      rw [← map_mul]
      have hz : (0,(TensorDirected.directedSystem (ThreeVertexAlgebra.directedSystem μ)
          (ChainAlgebra.directedSystem k l)).e i) *
          (0,(TensorDirected.directedSystem (ThreeVertexAlgebra.directedSystem μ)
            (ChainAlgebra.directedSystem k l)).e j) = (0 : ThreeVertexAlgebra μ ×
              (ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l)) :=
        Prod.ext (zero_mul 0) ((TensorDirected.directedSystem
          (ThreeVertexAlgebra.directedSystem μ) (ChainAlgebra.directedSystem k l)).orthogonal i j h)
      rw [hz,map_zero]

theorem constructed_vertices_complete :
    (∑ i : Sum (Fin 3) (Fin ((l + 1) * 3)),
      constructed_vertex (O := O) (T := T) μ l i) = 1 := by
  let f := TrivSqZeroExt.inlHom
    (ThreeVertexAlgebra μ × (ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l)) (OffDiagonal O T)
  let b : Sum (Fin 3) (Fin ((l+1)*3)) →
      ThreeVertexAlgebra μ × (ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l) :=
    Sum.elim (fun i => ((ThreeVertexAlgebra.directedSystem μ).e i,0))
      (fun i => (0,(TensorDirected.directedSystem (ThreeVertexAlgebra.directedSystem μ)
        (ChainAlgebra.directedSystem k l)).e i))
  have he (i : Sum (Fin 3) (Fin ((l+1)*3))) :
      constructed_vertex (O := O) (T := T) μ l i = f (b i) := by cases i <;> rfl
  simp_rw [he]
  have hb : (∑ i,b i) = 1 := by
    apply Prod.ext
    · change (∑ i,b i).1 = (1 : ThreeVertexAlgebra μ)
      simp only [b,Fintype.sum_sum_type,Prod.fst_add,Prod.fst_sum,Sum.elim_inl,Sum.elim_inr,
        Finset.sum_const_zero,add_zero,(ThreeVertexAlgebra.directedSystem μ).complete]
    · change (∑ i,b i).2 = (1 : ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l)
      simp only [b,Fintype.sum_sum_type,Prod.snd_add,Prod.snd_sum,Sum.elim_inl,Sum.elim_inr,
        Finset.sum_const_zero,zero_add,(TensorDirected.directedSystem
          (ThreeVertexAlgebra.directedSystem μ) (ChainAlgebra.directedSystem k l)).complete]
  calc
    (∑ i,f (b i)) = f (∑ i,b i) := (map_sum f b Finset.univ).symm
    _ = 1 := by rw [hb,f.map_one]

theorem constructed_complete_orthogonal_idempotents :
    CompleteOrthogonalIdempotents (constructed_vertex (O := O) (T := T) μ l) := by
  apply CompleteOrthogonalIdempotents.iff_ortho_complete.mpr
  exact ⟨fun i j hij => constructed_vertices_orthogonal μ l i j hij,
    constructed_vertices_complete μ l⟩

/-- Every actual vertex corner of A is scalar over k. Together with the
nonzero idempotent property this identifies the corner with the field k. -/
theorem constructed_vertex_scalar_corner
    (i : Sum (Fin 3) (Fin ((l + 1) * 3)))
    (a : TrivSqZeroExt
      (ThreeVertexAlgebra μ × (ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l))
      (OffDiagonal O T)) :
    ∃ c : k, constructed_vertex μ l i * a * constructed_vertex μ l i =
      c • constructed_vertex μ l i := by
  cases i with
  | inl j =>
    exact off_diagonal_first_scalar_corner _
      ((ThreeVertexAlgebra.directedSystem μ).diagonal j) a
  | inr j =>
    exact off_diagonal_second_scalar_corner _
      ((TensorDirected.directedSystem (ThreeVertexAlgebra.directedSystem μ)
        (ChainAlgebra.directedSystem k l)).diagonal j) a

/-- All the manuscript's displayed vertex idempotents of A are primitive. -/
theorem constructed_vertex_primitive (i : Sum (Fin 3) (Fin ((l + 1) * 3))) :
    IsPrimitiveIdempotent (constructed_vertex (O := O) (T := T) μ l i) := by
  cases i with
  | inl j =>
    exact off_diagonal_first_primitive _ (three_vertex_nonzero μ j)
      ((ThreeVertexAlgebra.directedSystem μ).idem j)
      ((ThreeVertexAlgebra.directedSystem μ).diagonal j)
  | inr j =>
    exact off_diagonal_second_primitive _ (encoding_tensor_vertex_nonzero μ l j)
      ((TensorDirected.directedSystem (ThreeVertexAlgebra.directedSystem μ)
        (ChainAlgebra.directedSystem k l)).idem j)
      ((TensorDirected.directedSystem (ThreeVertexAlgebra.directedSystem μ)
        (ChainAlgebra.directedSystem k l)).diagonal j)

theorem constructed_vertex_corner_is_field
    (i : Sum (Fin 3) (Fin ((l + 1) * 3))) :
    ∃ he : IsIdempotentElem (constructed_vertex (O := O) (T := T) μ l i),
      Nonempty (he.Corner ≃+* k) := by
  have hp := constructed_vertex_primitive (O := O) (T := T) μ l i
  let he : IsIdempotentElem (constructed_vertex (O := O) (T := T) μ l i) := hp.2.1
  exact ⟨he, ⟨scalar_corner_ring_equiv _ he hp.1
    (constructed_vertex_scalar_corner μ l i)⟩⟩

end
end Note198
