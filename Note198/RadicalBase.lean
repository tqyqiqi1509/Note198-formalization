import OAI.Algebra.Finitistic.Encoding.ThreeVertexAlgebra
import OAI.Algebra.Finitistic.Ordinary.OrdinaryChainAlgebra
import Mathlib.RingTheory.Jacobson.Semiprimary
import Note198.RadicalWordPowers

namespace Note198
noncomputable section
open OAI.LittleFinitistic OAI.LittleFinitistic.OrdinarySimulation
universe u

section ThreeVertices
variable {k V W U : Type u} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)

/-- The actual three diagonal vertex coordinates of the encoding algebra. -/
def three_vertex_diagonal : ThreeVertexAlgebra μ →+* (k × k × k) where
  toFun x := (x.1, x.2.1, x.2.2.1)
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem three_vertex_radical_diagonal_zero (x : ThreeVertexAlgebra μ)
    (hx : x ∈ Ring.jacobson (ThreeVertexAlgebra μ)) :
    x.1 = 0 ∧ x.2.1 = 0 ∧ x.2.2.1 = 0 := by
  let f := three_vertex_diagonal μ
  letI : RingHomSurjective f :=
    ⟨fun d => ⟨(d.1, d.2.1, d.2.2, 0, 0, 0), rfl⟩⟩
  have hh := Ring.le_comap_jacobson f hx
  change f x ∈ Ring.jacobson (k × k × k) at hh
  rw [IsSemisimpleRing.jacobson_eq_bot] at hh
  have hz : f x = 0 := hh
  exact ⟨congrArg Prod.fst hz,
    congrArg (fun d : k × k × k => d.2.1) hz,
    congrArg (fun d : k × k × k => d.2.2) hz⟩

/-- Three actual radical elements of the three-vertex algebra multiply to zero. -/
theorem three_vertex_radical_triple_zero (x y z : ThreeVertexAlgebra μ)
    (hx : x ∈ Ring.jacobson (ThreeVertexAlgebra μ))
    (hy : y ∈ Ring.jacobson (ThreeVertexAlgebra μ))
    (hz : z ∈ Ring.jacobson (ThreeVertexAlgebra μ)) : x * y * z = 0 := by
  obtain ⟨hx0, hx1, hx2⟩ := three_vertex_radical_diagonal_zero μ x hx
  obtain ⟨hy0, hy1, hy2⟩ := three_vertex_radical_diagonal_zero μ y hy
  obtain ⟨hz0, hz1, hz2⟩ := three_vertex_radical_diagonal_zero μ z hz
  apply ThreeVertexAlgebra.ext
  all_goals simp [ThreeVertexAlgebra.mul_eq, ThreeVertexAlgebra.mul,
    hx0, hx1, hx2, hy0, hy1, hy2, hz0, hz1, hz2]

/-- J_B^3=0 in word form, for every quadratic relation quotient. -/
theorem three_vertex_radical_words_zero (ds : List (ThreeVertexAlgebra μ))
    (hall : ∀ d ∈ ds, d ∈ Ring.jacobson (ThreeVertexAlgebra μ))
    (hlen : 3 ≤ ds.length) : ds.prod = 0 := by
  cases ds with
  | nil => simp at hlen
  | cons x ds =>
    cases ds with
    | nil => simp at hlen
    | cons y ds =>
      cases ds with
      | nil => simp at hlen
      | cons z ds =>
        have hx := hall x (by simp)
        have hy := hall y (by simp)
        have hz := hall z (by simp)
        simp only [List.prod_cons]
        calc
          x * (y * (z * ds.prod)) = (x * y * z) * ds.prod := by
            simp only [mul_assoc]
          _ = 0 := by rw [three_vertex_radical_triple_zero μ x y z hx hy hz, zero_mul]

/-- The actual ideal-power formulation of J_B^3=0. -/
theorem three_vertex_radical_pow_three_zero :
    Ring.jacobson (ThreeVertexAlgebra μ) ^ 3 = ⊥ := by
  apply ideal_power_zero_of_words _ 3
  intro ds hlen hall
  exact three_vertex_radical_words_zero μ ds hall (by omega)

end ThreeVertices

section Chain
variable {k : Type u} [Field k] (l : ℕ)

/-- The actual chain-algebra diagonal quotient. -/
def chain_diagonal : ChainAlgebra k l →+* (Fin (l + 1) → k) where
  toFun x := x.1
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem chain_radical_diagonal_zero (x : ChainAlgebra k l)
    (hx : x ∈ Ring.jacobson (ChainAlgebra k l)) : x.1 = 0 := by
  let f := chain_diagonal (k := k) l
  letI : RingHomSurjective f := ⟨fun d => ⟨(d, 0), rfl⟩⟩
  have hh := Ring.le_comap_jacobson f hx
  change f x ∈ Ring.jacobson (Fin (l + 1) → k) at hh
  rw [IsSemisimpleRing.jacobson_eq_bot] at hh
  exact hh

/-- J_C^2=0 for the manuscript's actual radical-square-zero chain algebra. -/
theorem chain_radical_pair_zero (x y : ChainAlgebra k l)
    (hx : x ∈ Ring.jacobson (ChainAlgebra k l))
    (hy : y ∈ Ring.jacobson (ChainAlgebra k l)) : x * y = 0 := by
  have hx0 := chain_radical_diagonal_zero l x hx
  have hy0 := chain_radical_diagonal_zero l y hy
  apply Prod.ext <;> funext i
  · simp [ChainAlgebra.mul_diagonal, hx0, hy0]
  · simp [ChainAlgebra.mul_radical, hx0, hy0]

/-- Every chain-radical word of length at least two vanishes. -/
theorem chain_radical_words_zero (ds : List (ChainAlgebra k l))
    (hall : ∀ d ∈ ds, d ∈ Ring.jacobson (ChainAlgebra k l))
    (hlen : 2 ≤ ds.length) : ds.prod = 0 := by
  cases ds with
  | nil => simp at hlen
  | cons x ds =>
    cases ds with
    | nil => simp at hlen
    | cons y ds =>
      have hx := hall x (by simp)
      have hy := hall y (by simp)
      simp only [List.prod_cons]
      rw [← mul_assoc, chain_radical_pair_zero l x y hx hy, zero_mul]

/-- The actual ideal-power formulation of J_C^2=0. -/
theorem chain_radical_pow_two_zero : Ring.jacobson (ChainAlgebra k l) ^ 2 = ⊥ := by
  apply ideal_power_zero_of_words _ 2
  intro ds hlen hall
  exact chain_radical_words_zero l ds hall (by omega)

end Chain
end
end Note198
