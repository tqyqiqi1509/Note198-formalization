import Note198.RadicalBase
import Note198.RadicalTensor
import Note198.RadicalBlockBridge

namespace Note198
noncomputable section
open scoped TensorProduct
open OAI.LittleFinitistic OAI.LittleFinitistic.OrdinarySimulation
universe u

theorem ideal_word_mem_power {A : Type u} [Ring A] (I : Ideal A) [I.IsTwoSided]
    (ds : List A) (hall : ∀ d ∈ ds, d ∈ I) : ds.prod ∈ I ^ ds.length := by
  induction ds with
  | nil =>
    rw [List.prod_nil, List.length_nil, Submodule.pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | cons a ds ih =>
    simp only [List.prod_cons, List.length_cons]
    rw [Ideal.IsTwoSided.pow_succ]
    exact Ideal.mul_mem_mul (hall a (by simp))
      (ih (fun d hd => hall d (List.mem_cons_of_mem a hd)))

theorem ideal_words_zero_of_power {A : Type u} [Ring A] (I : Ideal A) [I.IsTwoSided]
    (n : ℕ) (hzero : I ^ n = ⊥) (ds : List A)
    (hall : ∀ d ∈ ds, d ∈ I) (hlen : n ≤ ds.length) : ds.prod = 0 := by
  have hm := ideal_word_mem_power I ds hall
  have hz := (Ideal.pow_le_pow_right hlen) hm
  rw [hzero] at hz
  exact hz

section Constructed
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

/-- The exact J_A^7=0 assertion of Proposition 7.1 for the constructed
three-vertex encoding, chain algebra, and actual off-diagonal extension.
No radical nilpotence conclusion is assumed. The bimodules O and T may be
the manuscript's constructed bimodules; the bound holds for every bimodule
with these same off-diagonal actions. -/
theorem constructed_radical_pow_seven_zero :
    Ring.jacobson (TrivSqZeroExt
      (ThreeVertexAlgebra μ × (ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l))
      (OffDiagonal O T)) ^ 7 = ⊥ := by
  apply off_diagonal_radical_pow_seven_zero (k := k)
  · exact three_vertex_radical_words_zero μ
  · exact ideal_words_zero_of_power _ 4
      (tensor_chain_radical_pow_four_zero (ThreeVertexAlgebra.directedSystem μ) l)

end Constructed
end
end Note198
