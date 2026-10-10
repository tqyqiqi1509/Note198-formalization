import Note198.RadicalTensor

namespace Note198
noncomputable section
open scoped TensorProduct BigOperators
open TensorProduct CategoryTheory
open OAI.LittleFinitistic OAI.LittleFinitistic.DirectedBound
universe u v
section Heights
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] {n : ℕ}
variable (D : DirectedSystem k A n) (h : Fin n → ℕ) (q : ℕ)
variable (hd : ∀ i j, h i ≤ h j → i ≠ j → ∀ a : A, D.e i * a * D.e j = 0)
  (hq : ∀ i, h i < q)

def HeightSupported (M : Type v) [AddCommGroup M] [Module A M] (p : ℕ) : Prop :=
  ∀ j, h j < p → ∀ m : M, D.e j • m = 0

variable (M : Type v) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]

include hd in
theorem height_low_tensor {p : ℕ} (hM : HeightSupported D h M p)
    (j : Fin n) (hj : h j ≤ p) (i : Fin n) (a : A) (m : M) :
    (D.e j * a * D.e i) ⊗ₜ[k] (D.e i • m) =
      D.e j ⊗ₜ[k] ((D.e j * a * D.e i) • (D.e i • m)) := by
  by_cases hij : i = j
  · subst i
    obtain ⟨c,hc⟩ := D.diagonal j a
    rw [hc,smul_tmul,smul_assoc,← mul_smul,D.idem,tmul_smul]
  · by_cases hh : h i < p
    · rw [hM i hh m]
      simp
    · rw [hd j i (by omega) (Ne.symm hij) a]
      simp

include hd in
theorem height_low_projection {p : ℕ} (hM : HeightSupported D h M p)
    (j : Fin n) (hj : h j ≤ p) (x : A ⊗[k] M) :
    D.e j • D.projection M x =
      D.e j ⊗ₜ[k] DirectedSystem.evaluation M D (D.e j • D.projection M x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    simp only [DirectedSystem.projection_tmul,Finset.smul_sum,smul_tmul',smul_eq_mul,
      map_sum,DirectedSystem.evaluation_tmul,tmul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [← mul_assoc] using height_low_tensor D h hd M hM j hj i a m
  | add x y hx hy =>
    simp only [map_add,smul_add,tmul_add]
    exact congrArg₂ (· + ·) hx hy

include hd in
theorem height_kernel_supported {p : ℕ} (hM : HeightSupported D h M p) :
    HeightSupported D h (LinearMap.ker (D.coverMap M)) (p+1) := by
  intro j hj x
  apply Subtype.ext
  apply Subtype.ext
  change D.e j • x.val.val = 0
  obtain ⟨t,ht⟩ := x.val.property
  have hh := height_low_projection D h hd M hM j (by omega) t
  rw [ht] at hh
  rw [hh,map_smul]
  have hz : DirectedSystem.evaluation M D x.val.val = 0 := x.property
  rw [hz,smul_zero,tmul_zero]

omit [Module k M] [IsScalarTower k A M] in
include hq in
theorem height_supported_subsingleton (hM : HeightSupported D h M q) : Subsingleton M := by
  have hz (m : M) : m = 0 := by
    calc
      m = (1 : A) • m := (one_smul A m).symm
      _ = (∑ i,D.e i) • m := by rw [D.complete]
      _ = ∑ i,D.e i • m := Finset.sum_smul
      _ = 0 := Finset.sum_eq_zero (fun i _ => hM i (hq i) m)
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

include hd hq in
theorem height_supported_projectiveDimensionLT (r : ℕ) :
    ∀ p, p+r=q → ∀ (N : Type (max u v)) [AddCommGroup N] [Module A N]
      [Module k N] [IsScalarTower k A N], HeightSupported D h N p →
        HasProjectiveDimensionLT (ModuleCat.of A N) r := by
  induction r with
  | zero =>
    intro p hp N _ _ _ _ hN
    have hp' : p=q := by omega
    subst p
    letI := height_supported_subsingleton D h q hq N hN
    exact (ModuleCat.isZero_iff_subsingleton.mpr inferInstance).hasProjectiveDimensionLT_zero
  | succ r ih =>
    intro p hp N _ _ _ _ hN
    have hK := ih (p+1) (by omega) (LinearMap.ker (D.coverMap N))
      (height_kernel_supported D h hd N hN)
    have hP : HasProjectiveDimensionLT (ModuleCat.of A (D.Cover N)) (r+1) :=
      hasProjectiveDimensionLT_of_ge _ 1 (r+1) (by omega)
    exact (LinearMap.shortExact_shortComplexKer (D.coverMap_surjective N)).hasProjectiveDimensionLT_X₃ r hK hP

include hd hq
theorem height_all_modules_projectiveDimension_le (N : ModuleCat.{max u v} A) :
    projectiveDimension N ≤ (q-1 : ℕ) := by
  let : Module k N := Module.compHom N (algebraMap k A)
  let : IsScalarTower k A N := IsScalarTower.of_compHom k A N
  letI hh : HasProjectiveDimensionLT N q :=
    height_supported_projectiveDimensionLT D h q hd hq q 0 (by omega) N
      (by intro j hj; omega)
  apply (projectiveDimension_le_iff N (q-1)).mpr
  exact hasProjectiveDimensionLT_of_ge N q ((q-1)+1) (by omega)

end Heights

section ActualTensor
open OAI.LittleFinitistic.OrdinarySimulation
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (DB : DirectedSystem k B 3) (l : ℕ)

theorem tensor_chain_height_bound (i : Fin ((l+1)*3)) : tensor_chain_height l i < l+3 := by
  have hb := (TensorDirected.bIndex i).isLt
  have hc := (TensorDirected.cIndex i).isLt
  dsimp [tensor_chain_height]
  omega

include DB in
theorem tensor_chain_module_projectiveDimension_le
    (N : ModuleCat.{max u v} (B ⊗[k] ChainAlgebra k l)) :
    projectiveDimension N ≤ (l+2 : ℕ) := by
  let D := TensorDirected.directedSystem DB (ChainAlgebra.directedSystem k l)
  have hd : ∀ i j, tensor_chain_height l i ≤ tensor_chain_height l j → i ≠ j →
      ∀ a, D.e i * a * D.e j = 0 := by
    intro i j hh hn a
    exact tensor_chain_corner_downward DB l i j hh hn a
  have hh := height_all_modules_projectiveDimension_le D (tensor_chain_height l) (l+3)
    hd (tensor_chain_height_bound l) N
  simpa only [show l+3-1 = l+2 by omega] using hh

include DB in
theorem tensor_chain_globalDimension_le :
    (⨆ N : ModuleCat.{max u v} (B ⊗[k] ChainAlgebra k l),projectiveDimension N) ≤ (l+2 : ℕ) :=
  iSup_le (tensor_chain_module_projectiveDimension_le DB l)

include DB in
theorem tensor_chain_opposite_module_projectiveDimension_le
    (N : ModuleCat.{max u v} (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ) :
    projectiveDimension N ≤ (l+2 : ℕ) := by
  let D := TensorDirected.directedSystem DB (ChainAlgebra.directedSystem k l)
  let ho : Fin ((l+1)*3) → ℕ := fun i => (l+2)-tensor_chain_height l i.rev
  have hd : ∀ i j, ho i ≤ ho j → i ≠ j →
      ∀ a, D.opposite.e i * a * D.opposite.e j = 0 := by
    intro i j hij hne a
    have hi := tensor_chain_height_bound l i.rev
    have hj := tensor_chain_height_bound l j.rev
    have hh : tensor_chain_height l j.rev ≤ tensor_chain_height l i.rev := by
      dsimp [ho] at hij
      omega
    have hn : j.rev ≠ i.rev := fun he => hne (Fin.rev_injective he.symm)
    have ht := tensor_chain_corner_downward DB l j.rev i.rev hh hn a.unop
    apply MulOpposite.unop_injective
    change TensorDirected.vertex DB (ChainAlgebra.directedSystem k l) j.rev *
      (a.unop * TensorDirected.vertex DB (ChainAlgebra.directedSystem k l) i.rev) = 0
    simpa only [mul_assoc] using ht
  have hq : ∀ i, ho i < l+3 := by
    intro i
    dsimp [ho]
    have hh := Nat.sub_le (l+2) (tensor_chain_height l i.rev)
    omega
  have hh := height_all_modules_projectiveDimension_le D.opposite ho (l+3) hd hq N
  simpa only [show l+3-1 = l+2 by omega] using hh

include DB in
theorem tensor_chain_opposite_globalDimension_le :
    (⨆ N : ModuleCat.{max u v} (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ,projectiveDimension N) ≤ (l+2 : ℕ) :=
  iSup_le (tensor_chain_opposite_module_projectiveDimension_le DB l)

end ActualTensor
end
end Note198
