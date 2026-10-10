import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.CharP.Algebra
import Note198.PrimeGroup
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel

namespace Note198
/-!
Exact prerequisites for Section 2 of v5s9.15.

These are the variable-coefficient elementary-matrix calculations in the
finite-quotient construction, over the actual rings F_p[t]/(t^m - 1).
They do not establish the paper's main homological theorem.
-/

open Matrix Polynomial

namespace PrimeGroup

section ElementaryMatrices

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def transvection (i j : ι) (a : R) : Matrix ι ι R := 1 + Matrix.single i j a

theorem single_square_zero (i j : ι) (hij : i ≠ j) (a : R) :
    (Matrix.single i j a : Matrix ι ι R) * Matrix.single i j a = 0 := by
  exact Matrix.single_mul_single_of_ne a i j i (Ne.symm hij) a

theorem transvection_mul_neg (i j : ι) (hij : i ≠ j) (a : R) :
    transvection i j a * transvection i j (-a) = 1 := by
  simp only [transvection, ← Matrix.single_neg, mul_add, add_mul, mul_one, one_mul,
    mul_neg, single_square_zero i j hij]
  abel

def transvectionUnit (i j : ι) (hij : i ≠ j) (a : R) : (Matrix ι ι R)ˣ where
  val := transvection i j a
  inv := transvection i j (-a)
  val_inv := transvection_mul_neg i j hij a
  inv_val := by simpa using transvection_mul_neg i j hij (-a)

theorem transvection_same (i j : ι) (hij : i ≠ j) (a b : R) :
    transvection i j a * transvection i j b = transvection i j (a + b) := by
  simp only [transvection, mul_add, add_mul, mul_one, one_mul,
    Matrix.single_mul_single_of_ne a i j i (Ne.symm hij) b, Matrix.single_add]
  abel

theorem nilpotent_commutator {A : Type*} [Ring A] (a b : A)
    (haa : a * a = 0) (hbb : b * b = 0) (hba : b * a = 0) :
    (1+a)*(1+b)*(1-a)*(1-b) = 1+a*b := by
  calc
    (1+a)*(1+b)*(1-a)*(1-b) =
        1 + a*b - a*a - b*a - a*b*a - b*b - a*b*b + a*a*b + b*a*b + a*b*a*b := by
          noncomm_ring
    _ = 1 + a*b := by
      simp [haa, hbb, hba, mul_assoc]

theorem transvection_commutator (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    transvection i j a * transvection j k b *
      transvection i j (-a) * transvection j k (-b) =
      transvection i k (a*b) := by
  have haa := single_square_zero i j hij a
  have hbb := single_square_zero j k hjk b
  have hba : (Matrix.single j k b : Matrix ι ι R) * Matrix.single i j a = 0 :=
    Matrix.single_mul_single_of_ne b j k i (Ne.symm hik) a
  simpa [transvection, ← Matrix.single_neg, sub_eq_add_neg] using
    nilpotent_commutator (Matrix.single i j a) (Matrix.single j k b) haa hbb hba

theorem transvection_commute (i j k l : ι)
    (hjk : j ≠ k) (hli : l ≠ i) (a b : R) :
    Commute (transvection i j a) (transvection k l b) := by
  show transvection i j a * transvection k l b =
    transvection k l b * transvection i j a
  simp only [transvection, mul_add, add_mul, mul_one, one_mul,
    Matrix.single_mul_single_of_ne a i j k hjk b,
    Matrix.single_mul_single_of_ne b k l i hli a]
  abel

omit [Fintype ι] in
theorem transvection_injective (i j : ι) (hij : i ≠ j) :
    Function.Injective (transvection (R := R) i j) := by
  intro a b h
  have := congrArg (fun M : Matrix ι ι R => M i j) h
  simpa [transvection, Matrix.single, Matrix.one_apply, hij] using this

def diagonalUnit (d : ι → Rˣ) : (Matrix ι ι R)ˣ where
  val := Matrix.diagonal (fun i => (d i : R))
  inv := Matrix.diagonal (fun i => ((d i)⁻¹ : Rˣ))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp

theorem diagonal_single_conjugation (d : ι → Rˣ) (i j : ι) (a : R) :
    (diagonalUnit d : Matrix ι ι R) * Matrix.single i j a *
      ((diagonalUnit d)⁻¹ : (Matrix ι ι R)ˣ) =
      Matrix.single i j ((d i : R) * a * ((d j)⁻¹ : Rˣ)) := by
  ext k l
  change (Matrix.diagonal (fun s => (d s : R)) * Matrix.single i j a *
      Matrix.diagonal (fun s => (((d s)⁻¹ : Rˣ) : R))) k l = _
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases hi : i=k <;> by_cases hj : j=l <;>
    simp [hi, hj]

theorem diagonal_transvection_conjugation (d : ι → Rˣ) (i j : ι) (a : R) :
    (diagonalUnit d : Matrix ι ι R) * transvection i j a *
      ((diagonalUnit d)⁻¹ : (Matrix ι ι R)ˣ) =
      transvection i j ((d i : R) * a * ((d j)⁻¹ : Rˣ)) := by
  simp only [transvection,mul_add,add_mul,mul_one,Units.mul_inv,diagonal_single_conjugation]

theorem diagonalUnit_commute (d e : ι → Rˣ) : Commute (diagonalUnit d) (diagonalUnit e) := by
  apply Units.ext
  exact (Matrix.commute_diagonal (d₁ := fun i => (d i : R))
    (d₂ := fun i => (e i : R))).eq

theorem transvectionUnit_commute (i j k l : ι) (hij : i≠j) (hkl : k≠l)
    (hjk : j≠k) (hli : l≠i) (a b : R) :
    Commute (transvectionUnit i j hij a) (transvectionUnit k l hkl b) := by
  apply Units.ext
  exact (transvection_commute i j k l hjk hli a b).eq

open scoped commutatorElement in
theorem transvectionUnit_commutator (i j k : ι)
    (hij : i≠j) (hjk : j≠k) (hik : i≠k) (a b : R) :
    ⁅transvectionUnit i j hij a,transvectionUnit j k hjk b⁆ =
      transvectionUnit i k hik (a*b) := by
  apply Units.ext
  exact transvection_commutator i j k hij hjk hik a b

theorem transvectionUnit_conjugation (d : ι → Rˣ) (i j : ι) (hij : i≠j) (a : R) :
    diagonalUnit d * transvectionUnit i j hij a * (diagonalUnit d)⁻¹ =
      transvectionUnit i j hij ((d i : R) * a * ((d j)⁻¹ : Rˣ)) := by
  apply Units.ext
  exact diagonal_transvection_conjugation d i j a

end ElementaryMatrices

variable (p : ℕ) [Fact p.Prime]

noncomputable def cyclicPolynomial (m : ℕ) : Polynomial (ZMod p) := X^m - C 1
abbrev CyclicRing (m : ℕ) := AdjoinRoot (cyclicPolynomial p m)

theorem cyclicPolynomial_monic (m : ℕ) (hm : m ≠ 0) :
    (cyclicPolynomial p m).Monic := Polynomial.monic_X_pow_sub_C 1 hm

theorem cyclicPolynomial_degree (m : ℕ) :
    (cyclicPolynomial p m).natDegree = m := Polynomial.natDegree_X_pow_sub_C

noncomputable def cyclicBasis (m : ℕ) (hm : m ≠ 0) :
    Module.Basis (Fin m) (ZMod p) (CyclicRing p m) :=
  ((AdjoinRoot.powerBasis' (cyclicPolynomial_monic p m hm)).basis).reindex
    (finCongr (cyclicPolynomial_degree p m))

theorem cyclicRing_finite (m : ℕ) (hm : m ≠ 0) : Finite (CyclicRing p m) := by
  exact Finite.of_injective (cyclicBasis p m hm).repr (cyclicBasis p m hm).repr.injective

theorem cyclic_root_pow (m : ℕ) :
    AdjoinRoot.root (cyclicPolynomial p m) ^ m = (1 : CyclicRing p m) := by
  have h : AdjoinRoot.mk (cyclicPolynomial p m) (X^m - C 1) = 0 :=
    AdjoinRoot.mk_eq_zero.mpr (dvd_refl _)
  rw [map_sub, map_pow, AdjoinRoot.mk_X, Polynomial.C_1, map_one] at h
  exact sub_eq_zero.mp h

theorem cyclic_root_isUnit (m : ℕ) (hm : 0 < m) :
    IsUnit (AdjoinRoot.root (cyclicPolynomial p m)) := by
  exact IsUnit.of_pow_eq_one (cyclic_root_pow p m) (Nat.ne_of_gt hm)

theorem cyclicBasis_apply (m : ℕ) (hm : m ≠ 0) (i : Fin m) :
    cyclicBasis p m hm i = AdjoinRoot.root (cyclicPolynomial p m) ^ (i : ℕ) := by
  simp only [cyclicBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
    AdjoinRoot.powerBasis'_gen]
  rfl

theorem cyclic_powers_independent (m : ℕ) (hm : m ≠ 0) :
    LinearIndependent (ZMod p)
      (fun i : Fin m => AdjoinRoot.root (cyclicPolynomial p m) ^ (i : ℕ)) := by
  have h : (fun i : Fin m => cyclicBasis p m hm i) =
      (fun i : Fin m => AdjoinRoot.root (cyclicPolynomial p m) ^ (i : ℕ)) :=
    funext (cyclicBasis_apply p m hm)
  rw [← h]
  exact (cyclicBasis p m hm).linearIndependent

/-- The central coefficient embedding in the displayed 5-by-5 matrix model. -/
noncomputable def centralMatrix (m : ℕ) (c : Fin m → ZMod p) :
    Matrix (Fin 5) (Fin 5) (CyclicRing p m) :=
  transvection 0 4 (∑ i, c i • AdjoinRoot.root (cyclicPolynomial p m) ^ (i : ℕ))

theorem centralMatrix_zero (m : ℕ) : centralMatrix p m 0 = 1 := by
  simp [centralMatrix, transvection]

theorem centralMatrix_add (m : ℕ) (c d : Fin m → ZMod p) :
    centralMatrix p m (c + d) = centralMatrix p m c * centralMatrix p m d := by
  rw [centralMatrix, centralMatrix, centralMatrix,
    transvection_same 0 4 (by decide)]
  congr 1
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem centralMatrix_injective (m : ℕ) (hm : m ≠ 0) :
    Function.Injective (centralMatrix p m) := by
  intro c d h
  have hs := transvection_injective (R := CyclicRing p m) (0 : Fin 5) 4 (by decide) h
  have hz : ∑ i : Fin m, (c i - d i) •
      AdjoinRoot.root (cyclicPolynomial p m) ^ (i : ℕ) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hs, sub_self]
  have hc := (linearIndependent_iff'.mp (cyclic_powers_independent p m hm))
    Finset.univ (fun i => c i - d i) (by simpa using hz)
  funext i
  exact sub_eq_zero.mp (hc i (Finset.mem_univ i))

/-- The coefficient group embeds by central transvections over the actual cyclic ring. -/
noncomputable def centralEmbedding (m : ℕ) :
    Multiplicative (Fin m → ZMod p) →* (Matrix (Fin 5) (Fin 5) (CyclicRing p m))ˣ where
  toFun c := transvectionUnit 0 4 (by decide)
    (∑ i, c.toAdd i • AdjoinRoot.root (cyclicPolynomial p m) ^ (i : ℕ))
  map_one' := by
    apply Units.ext
    exact centralMatrix_zero p m
  map_mul' c d := by
    apply Units.ext
    exact centralMatrix_add p m c.toAdd d.toAdd

theorem centralEmbedding_injective (m : ℕ) (hm : m ≠ 0) :
    Function.Injective (centralEmbedding p m) := by
  intro c d h
  exact (centralMatrix_injective p m hm) (congrArg Units.val h)

end PrimeGroup

end Note198

namespace Note198
open scoped commutatorElement

namespace PrimeGroup

def internalIndex (i : Fin 3) : Fin 5 := ⟨i.val+1,by omega⟩

@[simp] theorem internalIndex_ne_zero (i : Fin 3) : internalIndex i ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  change i.val+1=0 at hv
  omega
@[simp] theorem internalIndex_ne_four (i : Fin 3) : internalIndex i ≠ 4 := by
  intro h
  have hv := congrArg Fin.val h
  change i.val+1=4 at hv
  omega
@[simp] theorem internalIndex_inj (i j : Fin 3) : internalIndex i = internalIndex j ↔ i=j := by
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change i.val+1=j.val+1 at hv
    omega
  · rintro rfl
    rfl

section MatrixRepresentation

variable {R : Type*} [CommRing R]


def matrixU (r : Rˣ) (i : Fin 3) (a : ℤ) : (Matrix (Fin 5) (Fin 5) R)ˣ :=
  transvectionUnit 0 (internalIndex i) (Ne.symm (internalIndex_ne_zero i)) (↑(r^a) : R)

def matrixV (r : Rˣ) (i : Fin 3) (a : ℤ) : (Matrix (Fin 5) (Fin 5) R)ˣ :=
  transvectionUnit (internalIndex i) 4 (internalIndex_ne_four i) (↑(r^a) : R)

def matrixW (r : Rˣ) (i j : Fin 3) (a : ℤ) : (Matrix (Fin 5) (Fin 5) R)ˣ :=
  if h : i=j then 1 else
    transvectionUnit (internalIndex i) (internalIndex j) (by simpa using h) (↑(r^a) : R)

def matrixT (r : Rˣ) (i : Fin 3) : (Matrix (Fin 5) (Fin 5) R)ˣ :=
  diagonalUnit (fun j => if j=internalIndex i then r else 1)

theorem transvectionUnit_pow (i j : Fin 5) (hij : i ≠ j) (a : R) (n : ℕ) :
    transvectionUnit i j hij a ^ n = transvectionUnit i j hij (n • a) := by
  induction n with
  | zero =>
      apply Units.ext
      simp [transvectionUnit, transvection]
  | succ n ih =>
      rw [pow_succ, ih]
      apply Units.ext
      change transvection i j (n • a) * transvection i j a =
        transvection i j ((n + 1) • a)
      rw [transvection_same i j hij, succ_nsmul]

variable (p : ℕ)
theorem matrixU_power [CharP R p] (r : Rˣ) (i : Fin 3) (a : ℤ) :
    matrixU r i a ^ p = 1 := by
  unfold matrixU
  rw [transvectionUnit_pow]
  apply Units.ext
  simp [transvectionUnit, transvection, nsmul_eq_mul, CharP.cast_eq_zero R p]

theorem matrix_UU_commute (r : Rˣ) (i j : Fin 3) (a b : ℤ) :
    Commute (matrixU r i a) (matrixU r j b) := by
  exact transvectionUnit_commute _ _ _ _ _ _
    (internalIndex_ne_zero i) (internalIndex_ne_zero j) _ _

theorem matrix_VV_commute (r : Rˣ) (i j : Fin 3) (a b : ℤ) :
    Commute (matrixV r i a) (matrixV r j b) := by
  exact transvectionUnit_commute _ _ _ _ _ _
    (Ne.symm (internalIndex_ne_four j)) (Ne.symm (internalIndex_ne_four i)) _ _

theorem matrix_UV_commute (r : Rˣ) (i j : Fin 3) (a b : ℤ) (hij : i≠j) :
    Commute (matrixU r i a) (matrixV r j b) := by
  exact transvectionUnit_commute _ _ _ _ _ _ (by simpa using hij) (by decide) _ _

theorem matrix_WU_commute (r : Rˣ) (i j h : Fin 3) (a b : ℤ) (hhi : h≠i) :
    Commute (matrixW r i j a) (matrixU r h b) := by
  unfold matrixW
  split_ifs with hij
  · exact Commute.one_left _
  · exact transvectionUnit_commute _ _ _ _ _ _
      (internalIndex_ne_zero j) (by simpa using hhi) _ _

theorem matrix_WV_commute (r : Rˣ) (i j h : Fin 3) (a b : ℤ) (hhj : h≠j) :
    Commute (matrixW r i j a) (matrixV r h b) := by
  unfold matrixW
  split_ifs with hij
  · exact Commute.one_left _
  · exact transvectionUnit_commute _ _ _ _ _ _
      (by simpa using hhj.symm) (Ne.symm (internalIndex_ne_four i)) _ _

theorem matrix_UW_commutator (r : Rˣ) (i j : Fin 3) (a b : ℤ) (hij : i≠j) :
    ⁅matrixU r i a,matrixW r i j b⁆ = matrixU r j (a+b) := by
  unfold matrixW matrixU
  rw [dite_eq_right hij]
  simpa only [zpow_add,Units.val_mul] using
    transvectionUnit_commutator (R := R) 0 (internalIndex i) (internalIndex j)
      (Ne.symm (internalIndex_ne_zero i)) (by simpa using hij)
      (Ne.symm (internalIndex_ne_zero j)) (↑(r^a) : R) (↑(r^b) : R)

theorem matrix_WV_commutator (r : Rˣ) (i j : Fin 3) (a b : ℤ) (hij : i≠j) :
    ⁅matrixW r i j a,matrixV r j b⁆ = matrixV r i (a+b) := by
  unfold matrixW matrixV
  rw [dite_eq_right hij]
  simpa only [zpow_add,Units.val_mul] using
    transvectionUnit_commutator (R := R) (internalIndex i) (internalIndex j) 4
      (by simpa using hij) (internalIndex_ne_four j)
      (internalIndex_ne_four i) (↑(r^a) : R) (↑(r^b) : R)

theorem matrix_TT_commute (r : Rˣ) (i j : Fin 3) : Commute (matrixT r i) (matrixT r j) :=
  diagonalUnit_commute _ _

theorem matrix_W_diagonal (r : Rˣ) (i : Fin 3) (a : ℤ) : matrixW r i i a = 1 := by
  simp [matrixW]

theorem matrix_TU_conjugation (r : Rˣ) (l i : Fin 3) (a : ℤ) :
    matrixT r l * matrixU r i a * (matrixT r l)⁻¹ =
      matrixU r i (a-if l=i then 1 else 0) := by
  unfold matrixT matrixU
  rw [transvectionUnit_conjugation]
  have h0 : (0 : Fin 5) ≠ internalIndex l := (internalIndex_ne_zero l).symm
  by_cases h : l=i
  · subst l
    simp [h0,zpow_sub]
  · have hi : internalIndex i ≠ internalIndex l := by simpa using Ne.symm h
    simp [h0,hi,h]

theorem matrix_TV_conjugation (r : Rˣ) (l i : Fin 3) (a : ℤ) :
    matrixT r l * matrixV r i a * (matrixT r l)⁻¹ =
      matrixV r i (a+if l=i then 1 else 0) := by
  unfold matrixT matrixV
  rw [transvectionUnit_conjugation]
  have h4 : (4 : Fin 5) ≠ internalIndex l := (internalIndex_ne_four l).symm
  by_cases h : l=i
  · subst l
    simp [h4,zpow_add,mul_comm]
  · have hi : internalIndex i ≠ internalIndex l := by simpa using Ne.symm h
    simp [h4,hi,h]

theorem matrix_TW_conjugation (r : Rˣ) (l i j : Fin 3) (a : ℤ) :
    matrixT r l * matrixW r i j a * (matrixT r l)⁻¹ =
      matrixW r i j (a+(if l=i then 1 else 0)-if l=j then 1 else 0) := by
  by_cases hij : i=j
  · subst j
    simp [matrix_W_diagonal]
  · simp only [matrixW,dite_eq_right hij,matrixT]
    rw [transvectionUnit_conjugation]
    by_cases hli : l=i <;> by_cases hlj : l=j
    · exact False.elim (hij (hli.symm.trans hlj))
    · subst l
      have hji : internalIndex j ≠ internalIndex i := by simpa using Ne.symm hij
      simp [hji,hlj,zpow_add,mul_comm]
    · subst l
      have hij' : internalIndex i ≠ internalIndex j := by simpa using hij
      simp [hij',hli,zpow_sub]
    · have hi : internalIndex i ≠ internalIndex l := by simpa using Ne.symm hli
      have hj : internalIndex j ≠ internalIndex l := by simpa using Ne.symm hlj
      simp [hi,hj,hli,hlj]

def matrixData [CharP R p] (r : Rˣ) : SelectionGroupData p (Matrix (Fin 5) (Fin 5) R)ˣ where
  T := matrixT r
  U := matrixU r
  V := matrixV r
  W := matrixW r
  power_U := matrixU_power p r
  commute_UU i j a b _ := matrix_UU_commute r i j a b
  commute_VV i j a b _ := matrix_VV_commute r i j a b
  commute_UV := matrix_UV_commute r
  commute_WU := matrix_WU_commute r
  commute_WV := matrix_WV_commute r
  commutator_UW := matrix_UW_commutator r
  commutator_WV := matrix_WV_commutator r
  commute_TT := matrix_TT_commute r
  conj_TU := matrix_TU_conjugation r
  conj_TV := matrix_TV_conjugation r
  conj_TW := matrix_TW_conjugation r
  diagonal_W := matrix_W_diagonal r

def matrixRepresentation [CharP R p] (r : Rˣ) : (Presentation.AuxiliaryGroup p) →*
    (Matrix (Fin 5) (Fin 5) R)ˣ := Presentation.ofData p (matrixData p r)

theorem matrixRepresentation_z [CharP R p] (r : Rˣ) (N : ℤ) :
    matrixRepresentation p r (Presentation.z p N) = transvectionUnit 0 4 (by decide) (↑(r^N) : R) := by
  change Presentation.ofData p (matrixData p r)
    ⁅PresentedGroup.of (Presentation.Generator.U 0 0),PresentedGroup.of (Presentation.Generator.V 0 N)⁆ = _
  rw [map_commutatorElement,Presentation.ofData_of p,Presentation.ofData_of p]
  change ⁅matrixU r 0 0,matrixV r 0 N⁆ = _
  unfold matrixU matrixV
  rw [transvectionUnit_commutator 0 (internalIndex 0) 4 _ _ (by decide)]
  simp only [zpow_zero,Units.val_one,one_mul]


end MatrixRepresentation

variable (p : ℕ) [Fact p.Prime]

instance cyclicRing_nontrivial (m : ℕ) [NeZero m] : Nontrivial (CyclicRing p m) := by
  let i : Fin m := ⟨0,Nat.pos_of_ne_zero (NeZero.ne m)⟩
  exact ⟨⟨cyclicBasis p m (NeZero.ne m) i,0,(cyclicBasis p m (NeZero.ne m)).ne_zero i⟩⟩

instance cyclicRing_finiteInst (m : ℕ) [NeZero m] : Finite (CyclicRing p m) :=
  cyclicRing_finite p m (NeZero.ne m)

instance cyclicRing_charP (m : ℕ) [NeZero m] : CharP (CyclicRing p m) p :=
  charP_of_injective_algebraMap (algebraMap (ZMod p) (CyclicRing p m)).injective p

noncomputable def cyclicUnit (m : ℕ) [NeZero m] : (CyclicRing p m)ˣ :=
  (cyclic_root_isUnit p m (Nat.pos_of_ne_zero (NeZero.ne m))).unit

@[simp] theorem cyclicUnit_val (m : ℕ) [NeZero m] :
    (cyclicUnit p m : CyclicRing p m) = AdjoinRoot.root (cyclicPolynomial p m) :=
  IsUnit.unit_spec _

noncomputable def cyclicRepresentation (m : ℕ) [NeZero m] : (Presentation.AuxiliaryGroup p) →*
    (Matrix (Fin 5) (Fin 5) (CyclicRing p m))ˣ := matrixRepresentation p (cyclicUnit p m)

theorem cyclicRepresentation_z (m : ℕ) [NeZero m] (i : ℕ) :
    cyclicRepresentation p m (Presentation.z p i) = transvectionUnit 0 4 (by decide)
      (AdjoinRoot.root (cyclicPolynomial p m)^i) := by
  unfold cyclicRepresentation
  rw [matrixRepresentation_z]
  simp only [zpow_natCast,Units.val_pow_eq_pow_val,cyclicUnit_val]

theorem centralEmbedding_basis (m : ℕ) [NeZero m] (i : Fin m) :
    centralEmbedding p m (Multiplicative.ofAdd (Pi.single i 1)) =
      cyclicRepresentation p m (Presentation.z p i.val) := by
  rw [cyclicRepresentation_z]
  apply Units.ext
  change transvection (R := CyclicRing p m) (0 : Fin 5) 4 (∑ j : Fin m, (Pi.single i (1 : ZMod p) : Fin m → ZMod p) j •
      AdjoinRoot.root (cyclicPolynomial p m) ^ (j : ℕ)) = _
  simp [Pi.single_apply, transvectionUnit]

noncomputable abbrev FiniteQuotientGroup (m : ℕ) [NeZero m] := (cyclicRepresentation p m).range

instance finiteQuotientGroup_finite (m : ℕ) [NeZero m] : Finite (FiniteQuotientGroup p m) :=
  inferInstance

noncomputable def finiteQuotientMap (m : ℕ) [NeZero m] :
    (Presentation.AuxiliaryGroup p) →* FiniteQuotientGroup p m := (cyclicRepresentation p m).rangeRestrict

theorem finiteQuotientMap_surjective (m : ℕ) [NeZero m] :
    Function.Surjective (finiteQuotientMap p m) := (cyclicRepresentation p m).rangeRestrict_surjective

theorem centralEmbedding_mem_center_map (m : ℕ) [NeZero m]
    (c : Fin m → ZMod p) : centralEmbedding p m (Multiplicative.ofAdd c) ∈
      (Subgroup.center (Presentation.AuxiliaryGroup p)).map (cyclicRepresentation p m) := by
  classical
  let S := (Subgroup.center (Presentation.AuxiliaryGroup p)).map (cyclicRepresentation p m)
  apply Pi.single_induction (fun c => centralEmbedding p m (Multiplicative.ofAdd c) ∈ S) c
  · simp
  · intro f g hf hg
    change centralEmbedding p m (Multiplicative.ofAdd f * Multiplicative.ofAdd g) ∈ S
    rw [map_mul]
    exact S.mul_mem hf hg
  · intro i a
    have ha : Multiplicative.ofAdd (Pi.single i a : Fin m → ZMod p) =
        (Multiplicative.ofAdd (Pi.single i (1 : ZMod p) : Fin m → ZMod p)) ^ a.val := by
      change (Pi.single i a : Fin m → ZMod p) = a.val • (Pi.single i (1 : ZMod p) : Fin m → ZMod p)
      ext j
      by_cases h : i = j
      · subst j
        simp [Pi.single_apply, nsmul_eq_mul]
      · simp [Pi.single_apply, h]
    rw [ha, map_pow, centralEmbedding_basis]
    apply S.pow_mem
    apply Subgroup.mem_map_of_mem
    exact Subgroup.mem_center_iff.mpr
      (fun g => (Presentation.z_central p i.val g).eq.symm)

theorem centralEmbedding_mem_range (m : ℕ) [NeZero m]
    (c : Multiplicative (Fin m → ZMod p)) :
    centralEmbedding p m c ∈ (cyclicRepresentation p m).range := by
  obtain ⟨g, _, hg⟩ := centralEmbedding_mem_center_map p m c.toAdd
  exact ⟨g,hg⟩

noncomputable def quotientCentralEmbedding (m : ℕ) [NeZero m] :
    Multiplicative (Fin m → ZMod p) →* FiniteQuotientGroup p m where
  toFun c := ⟨centralEmbedding p m c, centralEmbedding_mem_range p m c⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)

theorem quotientCentralEmbedding_injective (m : ℕ) [NeZero m] :
    Function.Injective (quotientCentralEmbedding p m) := by
  intro a b h
  exact centralEmbedding_injective p m (NeZero.ne m) (congrArg Subtype.val h)

theorem quotientCentralEmbedding_basis (m : ℕ) [NeZero m] (i : Fin m) :
    quotientCentralEmbedding p m (Multiplicative.ofAdd (Pi.single i 1)) =
      finiteQuotientMap p m (Presentation.z p i.val) :=
  Subtype.ext (centralEmbedding_basis p m i)

theorem quotientCentralEmbedding_central (m : ℕ) [NeZero m]
    (c : Multiplicative (Fin m → ZMod p)) (g : FiniteQuotientGroup p m) :
    Commute (quotientCentralEmbedding p m c) g := by
  obtain ⟨x, hx, hxval⟩ := centralEmbedding_mem_center_map p m c.toAdd
  obtain ⟨y, hy⟩ := finiteQuotientMap_surjective p m g
  subst g
  apply Subtype.ext
  change centralEmbedding p m c * cyclicRepresentation p m y =
    cyclicRepresentation p m y * centralEmbedding p m c
  change cyclicRepresentation p m x = centralEmbedding p m c at hxval
  rw [← hxval, ← map_mul, ← map_mul]
  exact congrArg (cyclicRepresentation p m) (Subgroup.mem_center_iff.mp hx y).symm

/-- Every embedded coefficient vector is generated by the prescribed z_i images. -/
theorem quotientCentralEmbedding_mem_basis_closure (m : ℕ) [NeZero m]
    (c : Fin m → ZMod p) : quotientCentralEmbedding p m (Multiplicative.ofAdd c) ∈
      Subgroup.closure (Set.range (fun i : Fin m => finiteQuotientMap p m (Presentation.z p i.val))) := by
  classical
  let S := Subgroup.closure
    (Set.range (fun i : Fin m => finiteQuotientMap p m (Presentation.z p i.val)))
  apply Pi.single_induction
    (fun c => quotientCentralEmbedding p m (Multiplicative.ofAdd c) ∈ S) c
  · simp
  · intro f g hf hg
    change quotientCentralEmbedding p m (Multiplicative.ofAdd f * Multiplicative.ofAdd g) ∈ S
    rw [map_mul]
    exact S.mul_mem hf hg
  · intro i a
    have ha : Multiplicative.ofAdd (Pi.single i a : Fin m → ZMod p) =
        (Multiplicative.ofAdd (Pi.single i (1 : ZMod p) : Fin m → ZMod p)) ^ a.val := by
      change (Pi.single i a : Fin m → ZMod p) = a.val • (Pi.single i (1 : ZMod p) : Fin m → ZMod p)
      ext j
      by_cases h : i = j
      · subst j
        simp [Pi.single_apply, nsmul_eq_mul]
      · simp [Pi.single_apply, h]
    rw [ha, map_pow, quotientCentralEmbedding_basis]
    exact S.pow_mem (Subgroup.subset_closure ⟨i, rfl⟩) _

/-- The image of the coefficient embedding is exactly the subgroup generated
by z_0,...,z_(m-1), rather than only a subgroup containing those elements. -/
theorem quotientCentralEmbedding_range_eq_basis_closure (m : ℕ) [NeZero m] :
    (quotientCentralEmbedding p m).range =
      Subgroup.closure (Set.range (fun i : Fin m => finiteQuotientMap p m (Presentation.z p i.val))) := by
  apply le_antisymm
  · rintro x ⟨c, rfl⟩
    exact quotientCentralEmbedding_mem_basis_closure p m c.toAdd
  · apply (Subgroup.closure_le ((quotientCentralEmbedding p m).range)).mpr
    rintro x ⟨i, rfl⟩
    exact ⟨Multiplicative.ofAdd (Pi.single i 1), quotientCentralEmbedding_basis p m i⟩

/-- The explicit isomorphism from the elementary abelian p-group to its image. -/
noncomputable def quotientCentralSubgroupEquiv (m : ℕ) [NeZero m] :
    Multiplicative (Fin m → ZMod p) ≃* (quotientCentralEmbedding p m).range :=
  MulEquiv.ofBijective (quotientCentralEmbedding p m).rangeRestrict
    ⟨fun a b h => quotientCentralEmbedding_injective p m (congrArg Subtype.val h),
      (quotientCentralEmbedding p m).rangeRestrict_surjective⟩

/-- The actual finite quotient in the manuscript, including the embedded elementary
abelian central subgroup and the prescribed images of all its basis elements. -/
theorem finite_central_quotient (m : ℕ) [NeZero m] :
    Function.Surjective (finiteQuotientMap p m) ∧
    Function.Injective (quotientCentralEmbedding p m) ∧
    (∀ c g, Commute (quotientCentralEmbedding p m c) g) ∧
    (∀ i : Fin m, quotientCentralEmbedding p m (Multiplicative.ofAdd (Pi.single i 1)) =
      finiteQuotientMap p m (Presentation.z p i.val)) :=
  ⟨finiteQuotientMap_surjective p m,quotientCentralEmbedding_injective p m,
    quotientCentralEmbedding_central p m,quotientCentralEmbedding_basis p m⟩

end PrimeGroup

end Note198
