import Note198.DirectedRadical
import Note198.RadicalWordPowers
import Mathlib.RingTheory.Nilpotent.Basic
import Note198.NoncommutativeQuotient

namespace Note198
noncomputable section
open scoped BigOperators
open OAI.LittleFinitistic.DirectedBound
universe u

/-- A nilpotent ideal lies in the actual noncommutative Jacobson radical. -/
theorem nilpotent_ideal_le_jacobson {A : Type u} [Ring A] (I : Ideal A)
    (m : ℕ) (hm : I ^ m = ⊥) : I ≤ Ring.jacobson A := by
  apply le_sInf
  intro L hL
  by_contra hn
  have hlt : L < L ⊔ I := lt_of_le_of_ne le_sup_left
    (fun he => hn (he ▸ le_sup_right))
  have htop : L ⊔ I = ⊤ := hL.2 _ hlt
  have hone : (1 : A) ∈ L ⊔ I := htop.symm ▸ Submodule.mem_top
  obtain ⟨a, ha, x, hx, hax⟩ := Submodule.mem_sup.mp hone
  have hxn : x ^ m = 0 := by
    have hp := Ideal.pow_mem_pow hx m
    rw [hm] at hp
    exact hp
  have hnil : IsNilpotent x := ⟨m, hxn⟩
  have heq : a = 1 - x := eq_sub_iff_add_eq.mpr hax
  have hunit : IsUnit a := by rw [heq]; exact hnil.isUnit_one_sub
  exact hL.1 (Ideal.eq_top_of_isUnit_mem L ha hunit)

section Directed
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] {n : ℕ}
variable (D : DirectedSystem k A n) (hne : ∀ i, D.e i ≠ 0)

/-- The actual simultaneous diagonal characters at all nonzero vertices. -/
def directed_augmentation : A →ₐ[k] (Fin n → k) where
  toFun a i := directed_vertex_scalar D i a
  map_zero' := by ext i; exact (directed_vertex_character D i (hne i)).map_zero
  map_one' := by ext i; exact (directed_vertex_character D i (hne i)).map_one
  map_add' a b := by ext i; exact (directed_vertex_character D i (hne i)).map_add a b
  map_mul' a b := by ext i; exact (directed_vertex_character D i (hne i)).map_mul a b
  commutes' c := by ext i; exact (directed_vertex_character D i (hne i)).commutes c

@[simp] theorem directed_augmentation_vertex (i j : Fin n) :
    directed_augmentation D hne (D.e j) i = if i = j then 1 else 0 := by
  classical
  apply (directed_vertex_scalar_eq_iff D i (hne i) _ _).mpr
  split_ifs with h
  · subst j; simp [D.idem]
  · rw [D.orthogonal i j h, zero_mul, zero_smul]

theorem directed_augmentation_surjective : Function.Surjective (directed_augmentation D hne) := by
  classical
  intro s
  refine ⟨∑ i, s i • D.e i, ?_⟩
  ext j
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    directed_augmentation_vertex]
  simp

theorem directed_kernel_diagonal_zero (a : A)
    (ha : a ∈ RingHom.ker (directed_augmentation D hne).toRingHom) (i : Fin n) :
    D.e i * a * D.e i = 0 := by
  have hz : directed_vertex_scalar D i a = 0 := congrFun ha i
  rw [directed_vertex_scalar_spec D, hz, zero_smul]

theorem directed_kernel_word_corner_zero (ds : List A)
    (hall : ∀ a ∈ ds, a ∈ RingHom.ker (directed_augmentation D hne).toRingHom)
    (i j : Fin n) (hheight : i.val < j.val + ds.length) :
    D.e i * ds.prod * D.e j = 0 := by
  induction ds generalizing i j with
  | nil =>
    have hij : i ≠ j := by intro h; subst j; simp at hheight
    simpa only [List.prod_nil, mul_one] using D.orthogonal i j hij
  | cons a ds ih =>
    simp only [List.prod_cons]
    rw [directed_corner_mul D]
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : s.val < j.val + ds.length
    · rw [ih (fun b hb => hall b (List.mem_cons_of_mem a hb)) s j hs, mul_zero]
    · have hh : i.val ≤ s.val := by
        simp only [List.length_cons] at hheight
        omega
      by_cases he : i = s
      · subst s
        rw [directed_kernel_diagonal_zero D hne a (hall a (by simp)) i, zero_mul]
      · have hi : i < s := by
          have hv : i.val ≠ s.val := fun h => he (Fin.ext h)
          omega
        rw [D.directed s i hi a, zero_mul]

theorem directed_kernel_pow_zero :
    RingHom.ker (directed_augmentation D hne).toRingHom ^ n = ⊥ := by
  apply ideal_power_zero_of_words _ n
  intro ds hlen hall
  have hc (i j : Fin n) : D.e i * ds.prod * D.e j = 0 :=
    directed_kernel_word_corner_zero D hne ds hall i j (by have hi := i.isLt; omega)
  have hz : (∑ i, D.e i) * ds.prod * (∑ j, D.e j) = 0 := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro i _
    exact hc i j
  simpa [D.complete] using hz

theorem directed_kernel_eq_radical :
    RingHom.ker (directed_augmentation D hne).toRingHom = Ring.jacobson A := by
  apply le_antisymm
  · exact nilpotent_ideal_le_jacobson _ n (directed_kernel_pow_zero D hne)
  · let f := (directed_augmentation D hne).toRingHom
    letI : RingHomSurjective f := ⟨directed_augmentation_surjective D hne⟩
    have h := Ring.le_comap_jacobson f
    rw [IsSemisimpleRing.jacobson_eq_bot (R := Fin n → k)] at h
    exact h

/-- The quotient by the actual radical is the product of the vertex fields,
as a k-algebra. This simultaneously proves the split-basic residue assertion. -/
def directed_residue_equiv : NoncommutativeQuotient (Ring.jacobson A) ≃ₐ[k] (Fin n → k) :=
  noncommutative_quotient_equiv (Ring.jacobson A) (directed_augmentation D hne)
    (directed_kernel_eq_radical D hne).symm (directed_augmentation_surjective D hne)

end Directed
end
end Note198
