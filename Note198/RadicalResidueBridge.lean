import Note198.DirectedResidue
import Note198.RadicalConstructed
import OAI.Algebra.Finitistic.Encoding.QuadraticEncoding

namespace Note198
noncomputable section
open scoped BigOperators TensorProduct
open OAI.LittleFinitistic OAI.LittleFinitistic.OrdinarySimulation
universe u v w

section Product
variable {k L R : Type u} {ι : Type v} {κ : Type w} [Field k] [Ring L] [Ring R]
  [Algebra k L] [Algebra k R] [Finite ι] [Finite κ]
variable (f : L →ₐ[k] (ι → k)) (g : R →ₐ[k] (κ → k))

def product_diagonal_augmentation : L × R →ₐ[k] (Sum ι κ → k) where
  toFun d := Sum.elim (f d.1) (g d.2)
  map_zero' := by ext i; cases i <;> simp
  map_one' := by ext i; cases i <;> simp
  map_add' a b := by ext i; cases i <;> simp
  map_mul' a b := by ext i; cases i <;> simp
  commutes' c := by ext i; cases i <;> simp

theorem product_diagonal_surjective (hf : Function.Surjective f)
    (hg : Function.Surjective g) : Function.Surjective (product_diagonal_augmentation f g) := by
  intro s
  obtain ⟨a, ha⟩ := hf (fun i => s (Sum.inl i))
  obtain ⟨b, hb⟩ := hg (fun i => s (Sum.inr i))
  refine ⟨(a, b), ?_⟩
  ext i
  cases i with
  | inl i => exact congrFun ha i
  | inr i => exact congrFun hb i

theorem product_diagonal_kernel_pow_zero (p q : ℕ)
    (hf : RingHom.ker f.toRingHom ^ p = ⊥)
    (hg : RingHom.ker g.toRingHom ^ q = ⊥) :
    RingHom.ker (product_diagonal_augmentation f g).toRingHom ^ (p + q) = ⊥ := by
  apply ideal_power_zero_of_words _ (p + q)
  intro ds hlen hall
  apply Prod.ext
  · change (RingHom.fst L R) ds.prod = 0
    rw [map_list_prod]
    apply ideal_words_zero_of_power _ p hf
    · intro a ha
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
      change f d.1 = 0
      ext i
      exact congrFun (hall d hd) (Sum.inl i)
    · simp only [List.length_map, hlen]
      omega
  · change (RingHom.snd L R) ds.prod = 0
    rw [map_list_prod]
    apply ideal_words_zero_of_power _ q hg
    · intro a ha
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
      change g d.2 = 0
      ext i
      exact congrFun (hall d hd) (Sum.inr i)
    · simp only [List.length_map, hlen]
      omega

theorem product_diagonal_kernel_eq_radical (hf : Function.Surjective f)
    (hg : Function.Surjective g) (p q : ℕ)
    (hp : RingHom.ker f.toRingHom ^ p = ⊥)
    (hq : RingHom.ker g.toRingHom ^ q = ⊥) :
    RingHom.ker (product_diagonal_augmentation f g).toRingHom = Ring.jacobson (L × R) := by
  apply le_antisymm
  · exact nilpotent_ideal_le_jacobson _ (p + q) (product_diagonal_kernel_pow_zero f g p q hp hq)
  · let h := (product_diagonal_augmentation f g).toRingHom
    letI : RingHomSurjective h := ⟨product_diagonal_surjective f g hf hg⟩
    have hh := Ring.le_comap_jacobson h
    rw [IsSemisimpleRing.jacobson_eq_bot (R := Sum ι κ → k)] at hh
    exact hh

end Product

section NonzeroVertices
variable {k B C : Type u} [Field k] [Ring B] [Ring C] [Algebra k B] [Algebra k C]
variable {n : ℕ} (DB : DirectedBound.DirectedSystem k B 3)
    (DC : DirectedBound.DirectedSystem k C n)

theorem tensor_directed_vertex_nonzero
    (hb : ∀ i, DB.e i ≠ 0) (hc : ∀ i, DC.e i ≠ 0) (i : Fin (n * 3)) :
    TensorDirected.vertex DB DC i ≠ 0 := by
  let b := TensorDirected.bIndex i
  let c := TensorDirected.cIndex i
  let fb := (directed_vertex_character DB b (hb b)).toLinearMap
  let fc := (directed_vertex_character DC c (hc c)).toLinearMap
  let t := (TensorProduct.lid k k).toLinearMap.comp (TensorProduct.map fb fc)
  have hfb : fb (DB.e b) = 1 := by
    apply (directed_vertex_scalar_eq_iff DB b (hb b) _ _).mpr
    simp [DB.idem]
  have hfc : fc (DC.e c) = 1 := by
    apply (directed_vertex_scalar_eq_iff DC c (hc c) _ _).mpr
    simp [DC.idem]
  have ht : t (TensorDirected.vertex DB DC i) = 1 := by
    simp [t, TensorDirected.vertex, b, c, TensorProduct.map_tmul, hfb, hfc]
  intro hz
  have hh := congrArg t hz
  rw [ht, map_zero] at hh
  exact one_ne_zero hh

end NonzeroVertices

section ActualVertices
variable {k V W U : Type u} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)

theorem three_vertex_nonzero (i : Fin 3) : (ThreeVertexAlgebra.directedSystem μ).e i ≠ 0 := by
  fin_cases i <;> simp [ThreeVertexAlgebra.directedSystem, ThreeVertexAlgebra.vertex]

theorem chain_vertex_nonzero (l : ℕ) (i : Fin (l + 1)) :
    (ChainAlgebra.directedSystem k l).e i ≠ 0 := by
  intro h
  have hh := congrArg (fun x : ChainAlgebra k l => x.1 i) h
  change (Pi.single i (1 : k) : Fin (l + 1) → k) i = 0 at hh
  simpa using hh

theorem encoding_tensor_vertex_nonzero (l : ℕ) (i : Fin ((l + 1) * 3)) :
    (TensorDirected.directedSystem (ThreeVertexAlgebra.directedSystem μ)
      (ChainAlgebra.directedSystem k l)).e i ≠ 0 := by
  simpa only [TensorDirected.directedSystem] using
    tensor_directed_vertex_nonzero (ThreeVertexAlgebra.directedSystem μ)
      (ChainAlgebra.directedSystem k l) (three_vertex_nonzero μ) (chain_vertex_nonzero (k := k) l) i

end ActualVertices

/-- Reindexing a finite product of fields preserves its full algebra structure. -/
def field_product_reindex {k : Type u} {ι : Type v} {κ : Type w} [Field k] (e : ι ≃ κ) :
    (ι → k) ≃ₐ[k] (κ → k) where
  toFun f j := f (e.symm j)
  invFun f i := f (e i)
  left_inv f := by funext i; simp
  right_inv f := by funext i; simp
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

end
end Note198
