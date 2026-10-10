import Note198.PrimeGroup
import Note198.Selection
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel

namespace Note198.GroupAlgebraSelection
noncomputable section
open MonoidAlgebra
universe u
variable (k : Type u) [Field k]

abbrev Ring (p : ℕ) := MonoidAlgebra k (PrimeGroup.Presentation.AuxiliaryGroup p)

def centralElement (p : ℕ) (q : ℤ) : Ring k p :=
  single (PrimeGroup.Presentation.z p q) 1

theorem centralElement_power (p : ℕ) (q : ℤ) :
    centralElement k p q ^ p = 1 := by
  simp [centralElement, single_pow, PrimeGroup.Presentation.z_power]
  rfl

theorem centralElement_central (p : ℕ) (q : ℤ) (a : Ring k p) :
    Commute (centralElement k p q) a :=
  MonoidAlgebra.single_commute (PrimeGroup.Presentation.z_central p q) Commute.one_left a

def automorphism (p : ℕ) (t : ℤ) : Ring k p ≃ₐ[k] Ring k p :=
  MonoidAlgebra.domCongr k k (PrimeGroup.Presentation.shiftAut p t)

theorem automorphism_centralElement (p : ℕ) (t q : ℤ) :
    automorphism k p t (centralElement k p q) = centralElement k p (q + t) := by
  simp [automorphism, centralElement, PrimeGroup.Presentation.shiftAut_z]

def idempotentTwo (q : ℤ) : Ring k 2 :=
  (2 : k)⁻¹ • (1 + centralElement k 2 q)

def idempotentThree (q : ℤ) : Ring k 3 :=
  (3 : k)⁻¹ • (1 + centralElement k 3 q + centralElement k 3 q ^ 2)

theorem idempotentTwo_square (h : (2 : k) ≠ 0) (q : ℤ) :
    idempotentTwo k q * idempotentTwo k q = idempotentTwo k q := by
  have hz : centralElement k 2 q * centralElement k 2 q = 1 := by
    simpa only [pow_two] using centralElement_power k 2 q
  have hs : (1 + centralElement k 2 q) * (1 + centralElement k 2 q) =
      (2 : k) • (1 + centralElement k 2 q) := by
    simp only [mul_add, add_mul, one_mul, mul_one, hz]
    rw [show (2 : k) = 1 + 1 by norm_num, add_smul, one_smul]
    abel
  unfold idempotentTwo
  rw [smul_mul_smul, hs, smul_smul]
  congr 1
  rw [mul_assoc, inv_mul_cancel₀ h, mul_one]

theorem idempotentThree_square (h : (3 : k) ≠ 0) (q : ℤ) :
    idempotentThree k q * idempotentThree k q = idempotentThree k q := by
  let z := centralElement k 3 q
  have hz3 : z * z * z = 1 := by
    simpa only [z, pow_succ, pow_zero, one_mul] using centralElement_power k 3 q
  have hz4 : z * z * z * z = z := by rw [hz3, one_mul]
  have hs : (1 + z + z ^ 2) * (1 + z + z ^ 2) =
      (3 : k) • (1 + z + z ^ 2) := by
    rw [show (3 : k) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
    calc
      _ = 1 + (z + z) + (z * z + z * z + z * z) +
          (z * z * z + z * z * z) + z * z * z * z := by noncomm_ring
      _ = _ := by rw [hz4, hz3]; noncomm_ring
  unfold idempotentThree
  change ((3 : k)⁻¹ • (1 + z + z ^ 2)) * ((3 : k)⁻¹ • (1 + z + z ^ 2)) = _
  rw [smul_mul_smul, hs, smul_smul]
  congr 1
  rw [mul_assoc, inv_mul_cancel₀ h, mul_one]

theorem idempotentTwo_central (q : ℤ) (a : Ring k 2) :
    Commute (idempotentTwo k q) a := by
  show idempotentTwo k q * a = a * idempotentTwo k q
  unfold idempotentTwo
  rw [smul_mul_assoc, mul_smul_comm]
  congr 1
  simp only [add_mul, mul_add, one_mul, mul_one, (centralElement_central k 2 q a).eq]

theorem idempotentThree_central (q : ℤ) (a : Ring k 3) :
    Commute (idempotentThree k q) a := by
  show idempotentThree k q * a = a * idempotentThree k q
  unfold idempotentThree
  rw [smul_mul_assoc, mul_smul_comm]
  congr 1
  simp only [add_mul, mul_add, one_mul, mul_one,
    (centralElement_central k 3 q a).eq, ((centralElement_central k 3 q a).pow_left 2).eq]

theorem automorphism_idempotentTwo (t q : ℤ) :
    automorphism k 2 t (idempotentTwo k q) = idempotentTwo k (q + t) := by
  simp [idempotentTwo, automorphism_centralElement]

theorem automorphism_idempotentThree (t q : ℤ) :
    automorphism k 3 t (idempotentThree k q) = idempotentThree k (q + t) := by
  simp [idempotentThree, automorphism_centralElement]

def dataTwo (h : (2 : k) ≠ 0) : Selection.Data k (Ring k 2) where
  e := idempotentTwo k 0
  idempotent := idempotentTwo_square k h 0
  central := idempotentTwo_central k 0
  α := automorphism k 2 1

def dataThree (h : (3 : k) ≠ 0) : Selection.Data k (Ring k 3) where
  e := idempotentThree k 0
  idempotent := idempotentThree_square k h 0
  central := idempotentThree_central k 0
  α := automorphism k 3 1

theorem two_or_three_invertible : (2 : k) ≠ 0 ∨ (3 : k) ≠ 0 := by
  by_cases h : (2 : k) = 0
  · right
    rw [show (3 : k) = (2 : k) + 1 by norm_num, h, zero_add]
    exact one_ne_zero
  · exact Or.inl h

end
end Note198.GroupAlgebraSelection
