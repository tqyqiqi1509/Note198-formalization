import OAI.Algebra.Finitistic.Encoding.DirectedBound
import Mathlib.RingTheory.Jacobson.Semiprimary

namespace Note198
noncomputable section
open scoped BigOperators
open OAI.LittleFinitistic.DirectedBound
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] {n : ℕ}
variable (D : DirectedSystem k A n)

theorem directed_corner_mul (a b : A) (i j : Fin n) :
    D.e i * (a * b) * D.e j =
      ∑ l, (D.e i * a * D.e l) * (D.e l * b * D.e j) := by
  conv_rhs => arg 2; ext l; rw [mul_assoc, ← mul_assoc (D.e l),
    ← mul_assoc (D.e l), D.idem]
  simp only [← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, D.complete]
  simp [mul_assoc]

theorem directed_diagonal_mul (a b : A) (i : Fin n) :
    D.e i * (a * b) * D.e i =
      (D.e i * a * D.e i) * (D.e i * b * D.e i) := by
  classical
  rw [directed_corner_mul D, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hji | hij
    · rw [D.directed i j hji b, mul_zero]
    · rw [D.directed j i hij a, zero_mul]
  · simp

def directed_vertex_scalar (i : Fin n) (a : A) : k := (D.diagonal i a).choose

theorem directed_vertex_scalar_spec (i : Fin n) (a : A) :
    D.e i * a * D.e i = directed_vertex_scalar D i a • D.e i :=
  (D.diagonal i a).choose_spec

theorem directed_vertex_scalar_eq_iff (i : Fin n) (hi : D.e i ≠ 0)
    (a : A) (c : k) :
    directed_vertex_scalar D i a = c ↔ D.e i * a * D.e i = c • D.e i := by
  rw [directed_vertex_scalar_spec D]
  exact (smul_left_injective k hi).eq_iff.symm

/-- The scalar action at a nonzero directed vertex is an actual algebra character. -/
def directed_vertex_character (i : Fin n) (hi : D.e i ≠ 0) : A →ₐ[k] k where
  toFun := directed_vertex_scalar D i
  map_zero' := by
    apply (directed_vertex_scalar_eq_iff D i hi _ _).mpr
    simp
  map_one' := by
    apply (directed_vertex_scalar_eq_iff D i hi _ _).mpr
    simp [D.idem]
  map_add' a b := by
    apply (directed_vertex_scalar_eq_iff D i hi _ _).mpr
    simp [mul_add, add_mul, directed_vertex_scalar_spec D, add_smul]
  map_mul' a b := by
    apply (directed_vertex_scalar_eq_iff D i hi _ _).mpr
    rw [directed_diagonal_mul D, directed_vertex_scalar_spec D,
      directed_vertex_scalar_spec D, smul_mul_smul_comm, D.idem]
  commutes' c := by
    apply (directed_vertex_scalar_eq_iff D i hi _ _).mpr
    rw [← (Algebra.commutes c (D.e i)), ← Algebra.smul_def,
      smul_mul_assoc, D.idem]
    rfl

/-- The actual ring radical has zero diagonal corner at every directed vertex. -/
theorem directed_radical_diagonal_zero (a : A) (ha : a ∈ Ring.jacobson A)
    (i : Fin n) : D.e i * a * D.e i = 0 := by
  by_cases hi : D.e i = 0
  · simp [hi]
  · let f := (directed_vertex_character D i hi).toRingHom
    letI : RingHomSurjective f := ⟨fun c =>
      ⟨algebraMap k A c, by simp [f]⟩⟩
    have hh := Ring.le_comap_jacobson f ha
    change f a ∈ Ring.jacobson k at hh
    rw [IsSemisimpleRing.jacobson_eq_bot] at hh
    have hz : directed_vertex_scalar D i a = 0 := hh
    rw [directed_vertex_scalar_spec D, hz, zero_smul]

end
end Note198
