import Note198.DirectedRadical
import Note198.RadicalWordPowers
import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorDirected

namespace Note198
noncomputable section
open scoped BigOperators TensorProduct
open OAI.LittleFinitistic OAI.LittleFinitistic.OrdinarySimulation
universe u

section TensorChain
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (DB : DirectedBound.DirectedSystem k B 3) (l : ℕ)

def tensor_chain_height (i : Fin ((l + 1) * 3)) : ℕ :=
  (TensorDirected.bIndex i).val + (TensorDirected.cIndex i).val

theorem chain_far_corner_zero (i j : Fin (l + 1)) (hij : j.val + 1 < i.val)
    (c : ChainAlgebra k l) :
    ChainAlgebra.vertex k l i * c * ChainAlgebra.vertex k l j = 0 := by
  apply Prod.ext
  · funext t
    change ((Pi.single i (1 : k) : Fin (l + 1) → k) t * c.1 t) *
      (Pi.single j (1 : k) : Fin (l + 1) → k) t = 0
    by_cases ht : t = i
    · subst t
      have hne : i ≠ j := by intro h; subst j; omega
      simp [hne]
    · simp [ht]
  · funext t
    change ((Pi.single i (1 : k) : Fin (l + 1) → k) t.succ * c.1 t.succ) * 0 +
      ((Pi.single i (1 : k) : Fin (l + 1) → k) t.succ * c.2 t +
        0 * c.1 t.castSucc) *
      (Pi.single j (1 : k) : Fin (l + 1) → k) t.castSucc = 0
    by_cases ht : t.succ = i
    · have hne : t.castSucc ≠ j := by
        intro h
        have hs := congrArg Fin.val ht
        have hc := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_castSucc] at hs hc
        omega
      simp [hne]
    · simp [ht]

theorem tensor_chain_corner_downward (i j : Fin ((l + 1) * 3))
    (hheight : tensor_chain_height l i ≤ tensor_chain_height l j) (hne : i ≠ j)
    (a : B ⊗[k] ChainAlgebra k l) :
    TensorDirected.vertex DB (ChainAlgebra.directedSystem k l) i * a *
      TensorDirected.vertex DB (ChainAlgebra.directedSystem k l) j = 0 := by
  have hcomp : TensorDirected.bIndex i < TensorDirected.bIndex j ∨
      TensorDirected.cIndex i < TensorDirected.cIndex j := by
    by_contra h
    simp only [not_or, not_lt] at h
    have heB : TensorDirected.bIndex i = TensorDirected.bIndex j := by
      apply Fin.ext
      dsimp [tensor_chain_height] at hheight
      omega
    have heC : TensorDirected.cIndex i = TensorDirected.cIndex j := by
      apply Fin.ext
      dsimp [tensor_chain_height] at hheight
      omega
    apply hne
    apply Fin.ext
    have hi := TensorDirected.index_value i
    have hj := TensorDirected.index_value j
    rw [heB, heC] at hi
    omega
  induction a using TensorProduct.inductionOn with
  | tmul b c =>
    simp only [TensorDirected.vertex, Algebra.TensorProduct.tmul_mul_tmul]
    rcases hcomp with hb | hc
    · rw [DB.directed _ _ hb, TensorProduct.zero_tmul]
    · rw [(ChainAlgebra.directedSystem k l).directed _ _ hc, TensorProduct.tmul_zero]
  | add a b ha hb => rw [mul_add, add_mul, ha, hb, add_zero]

theorem tensor_chain_far_corner_zero (i j : Fin ((l + 1) * 3))
    (hfar : (TensorDirected.cIndex j).val + 1 < (TensorDirected.cIndex i).val)
    (a : B ⊗[k] ChainAlgebra k l) :
    TensorDirected.vertex DB (ChainAlgebra.directedSystem k l) i * a *
      TensorDirected.vertex DB (ChainAlgebra.directedSystem k l) j = 0 := by
  induction a using TensorProduct.inductionOn with
  | tmul b c =>
    simp only [TensorDirected.vertex, Algebra.TensorProduct.tmul_mul_tmul]
    change _ ⊗ₜ[k] (ChainAlgebra.vertex k l _ * c * ChainAlgebra.vertex k l _) = 0
    rw [chain_far_corner_zero l _ _ hfar, TensorProduct.tmul_zero]
  | add a b ha hb => rw [mul_add, add_mul, ha, hb, add_zero]

/-- Multiplication by each radical factor strictly increases the sum of
the two vertex indices. The assertion refers to the actual tensor algebra. -/
theorem tensor_chain_radical_word_corner_zero
    (ds : List (B ⊗[k] ChainAlgebra k l))
    (hall : ∀ a ∈ ds, a ∈ Ring.jacobson (B ⊗[k] ChainAlgebra k l))
    (i j : Fin ((l + 1) * 3))
    (hheight : tensor_chain_height l i < tensor_chain_height l j + ds.length) :
    TensorDirected.vertex DB (ChainAlgebra.directedSystem k l) i * ds.prod *
      TensorDirected.vertex DB (ChainAlgebra.directedSystem k l) j = 0 := by
  let D := TensorDirected.directedSystem DB (ChainAlgebra.directedSystem k l)
  induction ds generalizing i j with
  | nil =>
    have hne : i ≠ j := by intro h; subst j; simp at hheight
    simpa only [List.prod_nil, mul_one, D, TensorDirected.directedSystem]
      using D.orthogonal i j hne
  | cons a ds ih =>
    simp only [List.prod_cons]
    have hm := directed_corner_mul D a ds.prod i j
    simp only [D, TensorDirected.directedSystem] at hm
    rw [hm]
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : tensor_chain_height l s < tensor_chain_height l j + ds.length
    · rw [ih (fun b hb => hall b (List.mem_cons_of_mem a hb)) s j hs, mul_zero]
    · have hh : tensor_chain_height l i ≤ tensor_chain_height l s := by
        simp only [List.length_cons] at hheight
        omega
      by_cases he : i = s
      · subst s
        have hz := directed_radical_diagonal_zero D a (hall a (by simp)) i
        simp only [D, TensorDirected.directedSystem] at hz
        rw [hz, zero_mul]
      · rw [tensor_chain_corner_downward DB l i s hh he a, zero_mul]

include DB

/-- The sharp fourth-power bound for B tensor the chain algebra C,
using the actual directed three-vertex B and the actual C multiplication. -/
theorem tensor_chain_radical_pow_four_zero :
    Ring.jacobson (B ⊗[k] ChainAlgebra k l) ^ 4 = ⊥ := by
  apply ideal_power_zero_of_words _ 4
  intro ds hlen hall
  let D := TensorDirected.directedSystem DB (ChainAlgebra.directedSystem k l)
  have hcorner (i j : Fin ((l + 1) * 3)) : D.e i * ds.prod * D.e j = 0 := by
    by_cases hh : tensor_chain_height l i < tensor_chain_height l j + 4
    · simpa only [D, TensorDirected.directedSystem] using
        tensor_chain_radical_word_corner_zero DB l ds hall i j (by simpa [hlen] using hh)
    · have hfar : (TensorDirected.cIndex j).val + 1 < (TensorDirected.cIndex i).val := by
        have hi := (TensorDirected.bIndex i).isLt
        have hj := (TensorDirected.bIndex j).isLt
        dsimp [tensor_chain_height] at hh
        omega
      simpa only [D, TensorDirected.directedSystem] using
        tensor_chain_far_corner_zero DB l i j hfar ds.prod
  have hz : (∑ i, D.e i) * ds.prod * (∑ j, D.e j) = 0 := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro i _
    exact hcorner i j
  simpa [D.complete] using hz

end TensorChain
end
end Note198
