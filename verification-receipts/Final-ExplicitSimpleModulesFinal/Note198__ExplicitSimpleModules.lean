import Note198.FiniteSelectionRestriction
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.CharP.Pi

/-! Section 7.2: the concrete complex vector space and its generators.
This file builds the operators on the full space indexed by S_m^3.
The simplicity proof uses the actual coefficient pairing and Fourier projectors.
Comparator validation is recorded separately; the full space is retained. -/
namespace Note198.ExplicitSimpleModules
open scoped commutatorElement
noncomputable section
open scoped BigOperators
universe u
variable (m : ℕ) [NeZero m]
abbrev Ring := PrimeGroup.CyclicRing 2 m
noncomputable instance : Fintype (Ring m) := Fintype.ofFinite _
abbrev State := Fin 3 → Ring m
abbrev Space := State m → ℂ

def basisVector (x : State m) : Space m := Pi.single x 1

def coefficient (x : Ring m) : ZMod 2 :=
  (PrimeGroup.cyclicBasis 2 m (NeZero.ne m)).repr x (FiniteSelectionSource.lastIndex m)

theorem coefficient_add (x y : Ring m) : coefficient m (x + y) = coefficient m x + coefficient m y := by
  simp [coefficient]

theorem coefficient_smul (a : ZMod 2) (x : Ring m) :
    coefficient m (a • x) = a * coefficient m x := by
  simp [coefficient, smul_eq_mul]

@[simp] theorem coefficient_zero : coefficient m 0 = 0 := by simp [coefficient]

def parityValue (a : ZMod 2) : ℂˣ := if a = 0 then 1 else -1
@[simp] theorem parityValue_zero : parityValue 0 = 1 := by simp [parityValue]
@[simp] theorem parityValue_one : parityValue 1 = -1 := by norm_num [parityValue]
theorem parityValue_add (a b : ZMod 2) : parityValue (a + b) = parityValue a * parityValue b := by
  have hc : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hc a with rfl | rfl <;> rcases hc b with rfl | rfl
  · simp
  · simp
  · simp
  · rw [show (1 : ZMod 2) + 1 = 0 from rfl, parityValue_zero, parityValue_one]
    simp

@[simp] theorem parityValue_square (a : ZMod 2) : parityValue a * parityValue a = 1 := by
  rw [← parityValue_add, CharTwo.add_self_eq_zero, parityValue_zero]

def phase (weight : State m → ℂˣ) : Space m ≃ₗ[ℂ] Space m where
  toFun f x := (weight x : ℂ) * f x
  invFun f x := ((weight x)⁻¹ : ℂˣ) * f x
  left_inv f := by ext x; simp [mul_assoc]
  right_inv f := by ext x; simp [mul_assoc]
  map_add' f g := by ext x; simp [mul_add]
  map_smul' c f := by ext x; simp [mul_left_comm]

def permute (e : State m ≃ State m) : Space m ≃ₗ[ℂ] Space m :=
  LinearEquiv.funCongrLeft ℂ ℂ e.symm

theorem permute_basisVector (e : State m ≃ State m) (x : State m) :
    permute m e (basisVector m x) = basisVector m (e x) := by
  ext y
  change (Pi.single x (1 : ℂ) : Space m) (e.symm y) = (Pi.single (e x) (1 : ℂ) : Space m) y
  by_cases hy : e x = y
  · subst y; simp
  · have hx : x ≠ e.symm y := by
      intro h
      apply hy
      rw [h, Equiv.apply_symm_apply]
    simp [Pi.single_apply, hx, hy]

theorem phase_basisVector (weight : State m → ℂˣ) (x : State m) :
    phase m weight (basisVector m x) = (weight x : ℂ) • basisVector m x := by
  ext y
  by_cases hy : x = y
  · subst y; simp [phase, basisVector]
  · simp [phase, basisVector, Pi.single_apply, hy]

def scaleCoordinate (i : Fin 3) : State m ≃ State m where
  toFun x := Function.update x i ((PrimeGroup.cyclicUnit 2 m : Ring m) * x i)
  invFun x := Function.update x i (((PrimeGroup.cyclicUnit 2 m)⁻¹ : (Ring m)ˣ) * x i)
  left_inv x := by
    ext j
    by_cases h : j = i
    · subst j
      simp only [Function.update_self]
      change (↑((PrimeGroup.cyclicUnit 2 m)⁻¹) : Ring m) *
        ((PrimeGroup.cyclicUnit 2 m : Ring m) * x i) = x i
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    · simp [Function.update_of_ne h]
  right_inv x := by
    ext j
    by_cases h : j = i
    · subst j
      simp only [Function.update_self]
      change (PrimeGroup.cyclicUnit 2 m : Ring m) *
        ((↑((PrimeGroup.cyclicUnit 2 m)⁻¹) : Ring m) * x i) = x i
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    · simp [Function.update_of_ne h]

def translateCoordinate (i : Fin 3) (r : ℤ) : State m ≃ State m :=
  Equiv.addLeft (Pi.single i (↑(PrimeGroup.cyclicUnit 2 m ^ r) : Ring m))

def shearCoordinate (i j : Fin 3) (hij : i ≠ j) (r : ℤ) : State m ≃ State m where
  toFun x := x + Pi.single i ((↑(PrimeGroup.cyclicUnit 2 m ^ r) : Ring m) * x j)
  invFun x := x - Pi.single i ((↑(PrimeGroup.cyclicUnit 2 m ^ r) : Ring m) * x j)
  left_inv x := by
    ext h
    by_cases hi : i = h
    · subst h; simp [Pi.single_apply, hij, (Ne.symm hij)]
    · simp [Pi.single_apply, hi]
  right_inv x := by
    ext h
    by_cases hi : i = h
    · subst h; simp [Pi.single_apply, hij, (Ne.symm hij)]
    · simp [Pi.single_apply, hi]

def T (i : Fin 3) : Space m ≃ₗ[ℂ] Space m := permute m (scaleCoordinate m i)
def U (i : Fin 3) (r : ℤ) : Space m ≃ₗ[ℂ] Space m :=
  phase m (fun x => parityValue (coefficient m ((↑(PrimeGroup.cyclicUnit 2 m ^ r) : Ring m) * x i)))
def V (i : Fin 3) (r : ℤ) : Space m ≃ₗ[ℂ] Space m :=
  permute m (translateCoordinate m i r)
def W (i j : Fin 3) (r : ℤ) : Space m ≃ₗ[ℂ] Space m :=
  if h : i = j then 1 else permute m (shearCoordinate m i j h r)

theorem U_basisVector (i : Fin 3) (r : ℤ) (x : State m) :
    U m i r (basisVector m x) =
      (parityValue (coefficient m ((↑(PrimeGroup.cyclicUnit 2 m ^ r) : Ring m) * x i)) : ℂ) •
        basisVector m x := phase_basisVector m _ x

theorem T_basisVector (i : Fin 3) (x : State m) :
    T m i (basisVector m x) = basisVector m (scaleCoordinate m i x) := permute_basisVector m _ x

theorem V_basisVector (i : Fin 3) (r : ℤ) (x : State m) :
    V m i r (basisVector m x) = basisVector m
      (Pi.single i (↑(PrimeGroup.cyclicUnit 2 m ^ r) : Ring m) + x) := permute_basisVector m _ x

theorem W_basisVector (i j : Fin 3) (hij : i ≠ j) (r : ℤ) (x : State m) :
    W m i j r (basisVector m x) = basisVector m
      (x + Pi.single i ((↑(PrimeGroup.cyclicUnit 2 m ^ r) : Ring m) * x j)) := by
  rw [W, dite_eq_right hij]
  exact permute_basisVector m _ x

theorem U_power (i : Fin 3) (r : ℤ) : U m i r ^ 2 = 1 := by
  ext f x
  change (parityValue (coefficient m ((↑(PrimeGroup.cyclicUnit 2 m ^ r) : Ring m) * x i)) : ℂ) *
    ((parityValue (coefficient m ((↑(PrimeGroup.cyclicUnit 2 m ^ r) : Ring m) * x i)) : ℂ) * f x) = f x
  rw [← mul_assoc, ← Units.val_mul, parityValue_square, Units.val_one, one_mul]

theorem ring_card : Fintype.card (Ring m) = 2 ^ m := by
  let e : Ring m ≃ (Fin m → ZMod 2) :=
    (PrimeGroup.cyclicBasis 2 m (NeZero.ne m)).repr.toEquiv.trans
      Finsupp.equivFunOnFinite
  calc
    _ = Fintype.card (Fin m → ZMod 2) := Fintype.card_congr e
    _ = _ := by simp

theorem space_dimension : Module.finrank ℂ (Space m) = 2 ^ (3 * m) := by
  rw [Module.finrank_fintype_fun_eq_card]
  change Fintype.card (Fin 3 → Ring m) = _
  simp only [Fintype.card_fun, Fintype.card_fin, ring_card, ← pow_mul]
  rw [Nat.mul_comm]


theorem state_card : Fintype.card (State m) = 2 ^ (3 * m) := by
  change Fintype.card (Fin 3 → Ring m) = _
  simp only [Fintype.card_fun, Fintype.card_fin, ring_card, ← pow_mul]
  rw [Nat.mul_comm]
theorem coefficient_sum {ι : Type*} (s : Finset ι) (f : ι → Ring m) :
    coefficient m (∑ i ∈ s, f i) = ∑ i ∈ s, coefficient m (f i) := by
  simp [coefficient, Finset.sum_apply]

/-! The coefficient pairing is proved in the original quotient ring. -/
abbrev root : Ring m := AdjoinRoot.root (PrimeGroup.cyclicPolynomial 2 m)


theorem scaleCoordinate_formula (i : Fin 3) (x : State m) :
    scaleCoordinate m i x = x + Pi.single i ((root m - 1) * x i) := by
  ext j
  by_cases hij : i = j
  · subst j
    simp [scaleCoordinate, root, PrimeGroup.cyclicUnit_val]
    ring
  · simp [scaleCoordinate, Function.update_of_ne (Ne.symm hij),
      Pi.single_apply, hij]

/-- T in the exact coordinate formula displayed in the manuscript. -/
theorem T_original_basisVector (i : Fin 3) (x : State m) :
    T m i (basisVector m x) = basisVector m
      (x + Pi.single i ((root m - 1) * x i)) := by
  rw [T_basisVector, scaleCoordinate_formula]

/-- V with the original order x+t^r e_i. -/
theorem V_original_basisVector (i : Fin 3) (r : ℤ) (x : State m) :
    V m i r (basisVector m x) = basisVector m
      (x + Pi.single i (↑(PrimeGroup.cyclicUnit 2 m ^ r) : Ring m)) := by
  simpa only [add_comm] using V_basisVector m i r x


@[simp] theorem coefficient_basis (i : Fin m) :
    coefficient m (PrimeGroup.cyclicBasis 2 m (NeZero.ne m) i) =
      if i = FiniteSelectionSource.lastIndex m then 1 else 0 := by
  simp [coefficient, Finsupp.single_apply]

theorem root_pow_mod (n : ℕ) : root m ^ n = root m ^ (n % m) := by
  calc
    _ = root m ^ (n % m + m * (n / m)) := congrArg (fun n => root m ^ n) (Nat.mod_add_div n m).symm
    _ = _ := by rw [pow_add, pow_mul, PrimeGroup.cyclic_root_pow, one_pow, mul_one]

theorem coefficient_root_pow (n : ℕ) :
    coefficient m (root m ^ n) = if n % m = m - 1 then 1 else 0 := by
  rw [root_pow_mod]
  let i : Fin m := ⟨n % m, Nat.mod_lt n (Nat.pos_of_ne_zero (NeZero.ne m))⟩
  have hb : root m ^ (n % m) = PrimeGroup.cyclicBasis 2 m (NeZero.ne m) i :=
    (PrimeGroup.cyclicBasis_apply 2 m (NeZero.ne m) i).symm
  rw [hb, coefficient_basis]
  simp [i, FiniteSelectionSource.lastIndex, Fin.ext_iff]

theorem reflected_mod (i j : Fin m) :
    (m - 1 - j.val + i.val) % m = m - 1 ↔ i = j := by
  have hm := NeZero.ne m
  have hi := i.isLt
  have hj := j.isLt
  by_cases h : m - 1 - j.val + i.val < m
  · rw [Nat.mod_eq_of_lt h]
    rw [Fin.ext_iff]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [Fin.ext_iff]
    omega

theorem coefficient_reflected_basis (i j : Fin m) :
    coefficient m (root m ^ (m - 1 - j.val) *
      PrimeGroup.cyclicBasis 2 m (NeZero.ne m) i) = if i = j then 1 else 0 := by
  rw [PrimeGroup.cyclicBasis_apply, ← pow_add, coefficient_root_pow]
  simp only [reflected_mod]

/-- Multiplication by the reflected monomial extracts exactly the j-th coefficient. -/
theorem coefficient_reflected (x : Ring m) (j : Fin m) :
    coefficient m (root m ^ (m - 1 - j.val) * x) =
      (PrimeGroup.cyclicBasis 2 m (NeZero.ne m)).repr x j := by
  classical
  conv_lhs => rw [← (PrimeGroup.cyclicBasis 2 m (NeZero.ne m)).sum_repr x]
  rw [Finset.mul_sum, coefficient_sum]
  simp [mul_smul_comm, coefficient_smul, coefficient_reflected_basis]

/-- The actual coefficient functional has nondegenerate multiplication pairing. -/
theorem coefficient_pairing_nondegenerate (x : Ring m) (hx : x ≠ 0) :
    ∃ a : Ring m, coefficient m (a * x) = 1 := by
  have hrepr : (PrimeGroup.cyclicBasis 2 m (NeZero.ne m)).repr x ≠ 0 := by
    intro h
    exact hx ((PrimeGroup.cyclicBasis 2 m (NeZero.ne m)).repr.injective (by simpa using h))
  have hi : ∃ i : Fin m, (PrimeGroup.cyclicBasis 2 m (NeZero.ne m)).repr x i ≠ 0 := by
    by_contra h
    apply hrepr
    ext i
    exact not_ne_iff.mp (not_exists.mp h i)
  obtain ⟨i, hi⟩ := hi
  have hbinary : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hone := (hbinary ((PrimeGroup.cyclicBasis 2 m (NeZero.ne m)).repr x i)).resolve_left hi
  exact ⟨root m ^ (m - 1 - i.val), (coefficient_reflected m x i).trans hone⟩


def pairing (a x : State m) : ZMod 2 := coefficient m (∑ i : Fin 3, a i * x i)


theorem pairing_add_left (a b x : State m) :
    pairing m (a + b) x = pairing m a x + pairing m b x := by
  simp only [pairing, Pi.add_apply, add_mul, Finset.sum_add_distrib, coefficient_add]

theorem pairing_add_right (a x y : State m) :
    pairing m a (x + y) = pairing m a x + pairing m a y := by
  simp only [pairing, Pi.add_apply, mul_add, Finset.sum_add_distrib, coefficient_add]

theorem pairing_single (i : Fin 3) (a : Ring m) (x : State m) :
    pairing m (Pi.single i a) x = coefficient m (a * x i) := by
  classical
  simp [pairing, Pi.single_apply, ite_mul]

/-- Each nonzero state is separated by the actual quotient-ring coefficient pairing. -/
theorem pairing_separates (x : State m) (hx : x ≠ 0) :
    ∃ a : State m, pairing m a x = 1 := by
  have hi : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  obtain ⟨i, hi⟩ := hi
  obtain ⟨a, ha⟩ := coefficient_pairing_nondegenerate m (x i) hi
  exact ⟨Pi.single i a, (pairing_single m i a x).trans ha⟩

def pairingCharacter (x : State m) : AddChar (State m) ℂ where
  toFun a := (parityValue (pairing m a x) : ℂ)
  map_zero_eq_one' := by simp [pairing]
  map_add_eq_mul' a b := by rw [pairing_add_left, parityValue_add, Units.val_mul]

theorem pairingCharacter_ne_one (x : State m) (hx : x ≠ 0) :
    pairingCharacter m x ≠ 1 := by
  obtain ⟨a, ha⟩ := pairing_separates m x hx
  intro h
  have he := congrArg (fun ψ : AddChar (State m) ℂ => ψ a) h
  change (parityValue (pairing m a x) : ℂ) = 1 at he
  rw [ha, parityValue_one] at he
  norm_num at he

theorem character_sum (x : State m) :
    (∑ a : State m, (parityValue (pairing m a x) : ℂ)) =
      if x = 0 then (Fintype.card (State m) : ℂ) else 0 := by
  classical
  by_cases hx : x = 0
  · subst x
    simp [pairing]
  · simp only [hx, if_false]
    exact AddChar.sum_eq_zero_of_ne_one (pairingCharacter_ne_one m x hx)

/-- The Fourier projector in the manuscript, on the full coordinate space. -/
def fourierProjector (x : State m) : Space m →ₗ[ℂ] Space m :=
  (Fintype.card (State m) : ℂ)⁻¹ •
    ∑ a : State m, (parityValue (pairing m a x) : ℂ) •
      (phase m (fun y => parityValue (pairing m a y))).toLinearMap

/-- The Fourier scalar is exactly 2^(-3m), as displayed in the manuscript. -/
theorem fourierProjector_normalization (x : State m) :
    fourierProjector m x = ((2 : ℂ) ^ (3 * m))⁻¹ •
      ∑ a : State m, (parityValue (pairing m a x) : ℂ) •
        (phase m (fun y => parityValue (pairing m a y))).toLinearMap := by
  unfold fourierProjector
  rw [state_card]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
/-- The displayed Fourier sum selects exactly the x-coordinate. -/
theorem fourierProjector_apply (x : State m) (f : Space m) :
    fourierProjector m x f = f x • basisVector m x := by
  classical
  ext y
  have hc : (Fintype.card (State m) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hs : (∑ a : State m, (parityValue (pairing m a x) : ℂ) *
      ((parityValue (pairing m a y) : ℂ) * f y)) =
      (if x + y = 0 then (Fintype.card (State m) : ℂ) else 0) * f y := by
    simp only [← mul_assoc, ← Units.val_mul, ← parityValue_add, ← pairing_add_right]
    rw [← Finset.sum_mul, character_sum]
  simp only [fourierProjector, LinearMap.smul_apply, LinearMap.sum_apply,
    Finset.sum_apply, Pi.smul_apply]
  change (Fintype.card (State m) : ℂ)⁻¹ *
    (∑ a : State m, (parityValue (pairing m a x) : ℂ) *
      ((parityValue (pairing m a y) : ℂ) * f y)) = _
  rw [hs]
  have hxy : x + y = 0 ↔ x = y := by
    constructor
    · intro h
      have he : x = -y := eq_neg_of_add_eq_zero_left h
      simpa only [CharTwo.neg_eq] using he
    · rintro rfl
      exact CharTwo.add_self_eq_zero x
  by_cases h : x = y
  · subst y
    simp [hxy, hc, basisVector]
  · simp [hxy, h, basisVector, Pi.single_apply]


def translation (b : State m) : Space m ≃ₗ[ℂ] Space m := permute m (Equiv.addLeft b)

theorem translation_basisVector (b x : State m) :
    translation m b (basisVector m x) = basisVector m (b + x) := permute_basisVector m _ x

theorem fourierProjector_mem (P : Submodule ℂ (Space m))
    (hphase : ∀ a : State m, ∀ f ∈ P,
      phase m (fun y => parityValue (pairing m a y)) f ∈ P)
    (x : State m) (f : Space m) (hf : f ∈ P) : fourierProjector m x f ∈ P := by
  classical
  simp only [fourierProjector, LinearMap.smul_apply, LinearMap.sum_apply]
  change (Fintype.card (State m) : ℂ)⁻¹ •
    (∑ a : State m, (parityValue (pairing m a x) : ℂ) •
      phase m (fun y => parityValue (pairing m a y)) f) ∈ P
  apply P.smul_mem
  apply P.sum_mem
  intro a _
  exact P.smul_mem _ (hphase a f hf)

/-- Fourier projection and translations prove irreducibility once the actual
phase and translation operators are present. The generator-to-operator bridge
is a separate obligation below. -/
theorem phase_translation_irreducible (P : Submodule ℂ (Space m))
    (hphase : ∀ a : State m, ∀ f ∈ P,
      phase m (fun y => parityValue (pairing m a y)) f ∈ P)
    (htranslation : ∀ b : State m, ∀ f ∈ P, translation m b f ∈ P) :
    P = ⊥ ∨ P = ⊤ := by
  classical
  by_cases hp : P = ⊥
  · exact Or.inl hp
  right
  obtain ⟨f, hf, hfn⟩ := (Submodule.ne_bot_iff P).mp hp
  have hcoord : ∃ x : State m, f x ≠ 0 := by
    by_contra h
    apply hfn
    funext x
    exact not_ne_iff.mp (not_exists.mp h x)
  obtain ⟨x, hx⟩ := hcoord
  have hbasex : basisVector m x ∈ P := by
    have hproj := fourierProjector_mem m P hphase x f hf
    rw [fourierProjector_apply] at hproj
    have hscale := P.smul_mem (f x)⁻¹ hproj
    simpa [smul_smul, hx] using hscale
  have hbasis (y : State m) : basisVector m y ∈ P := by
    have ht := htranslation (y - x) (basisVector m x) hbasex
    rw [translation_basisVector, sub_add_cancel] at ht
    exact ht
  apply Submodule.eq_top_iff'.mpr
  intro g
  have hsum : (∑ y : State m, g y • basisVector m y) = g := by
    ext z
    simp [basisVector, Pi.single_apply]
  rw [← hsum]
  exact P.sum_mem (fun y _ => P.smul_mem _ (hbasis y))


/-- Extensionality on the displayed basis of the full space. -/
theorem operator_ext {A B : Space m ≃ₗ[ℂ] Space m}
    (h : ∀ x, A (basisVector m x) = B (basisVector m x)) : A = B := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.pi_ext
  intro x c
  have hs : Pi.single x c = c • basisVector m x := by
    ext y
    simp [basisVector, Pi.single_apply, mul_ite]
  rw [hs, map_smul, map_smul]
  exact congrArg (fun y : Space m => c • y) (h x)

theorem U_commute (i j : Fin 3) (r s : ℤ) : Commute (U m i r) (U m j s) := by
  change _ * _ = _ * _
  ext f x
  change (parityValue (coefficient m ((↑(PrimeGroup.cyclicUnit 2 m ^ r) : Ring m) * x i)) : ℂ) *
    ((parityValue (coefficient m ((↑(PrimeGroup.cyclicUnit 2 m ^ s) : Ring m) * x j)) : ℂ) * f x) =
    (parityValue (coefficient m ((↑(PrimeGroup.cyclicUnit 2 m ^ s) : Ring m) * x j)) : ℂ) *
    ((parityValue (coefficient m ((↑(PrimeGroup.cyclicUnit 2 m ^ r) : Ring m) * x i)) : ℂ) * f x)
  ring

theorem V_commute (i j : Fin 3) (r s : ℤ) : Commute (V m i r) (V m j s) := by
  change _ * _ = _ * _
  apply operator_ext m
  intro x
  change V m i r (V m j s (basisVector m x)) = V m j s (V m i r (basisVector m x))
  rw [V_basisVector, V_basisVector, V_basisVector, V_basisVector]
  congr 1
  abel

theorem U_V_commute (i j : Fin 3) (hij : i ≠ j) (r s : ℤ) :
    Commute (U m i r) (V m j s) := by
  change _ * _ = _ * _
  apply operator_ext m
  intro x
  change U m i r (V m j s (basisVector m x)) = V m j s (U m i r (basisVector m x))
  rw [V_basisVector, U_basisVector, U_basisVector, map_smul, V_basisVector]
  simp [Pi.single_apply, hij, (Ne.symm hij)]


theorem W_U_commute (i j h : Fin 3) (hhi : h ≠ i) (r s : ℤ) :
    Commute (W m i j r) (U m h s) := by
  classical
  by_cases hij : i = j
  · simp [W, hij]
  change _ * _ = _ * _
  apply operator_ext m
  intro x
  change W m i j r (U m h s (basisVector m x)) = U m h s (W m i j r (basisVector m x))
  simp only [U_basisVector, map_smul, W_basisVector m i j hij]
  simp [Pi.single_apply, hhi, hhi.symm]

theorem W_V_commute (i j h : Fin 3) (hhj : h ≠ j) (r s : ℤ) :
    Commute (W m i j r) (V m h s) := by
  classical
  by_cases hij : i = j
  · simp [W, hij]
  change _ * _ = _ * _
  apply operator_ext m
  intro x
  change W m i j r (V m h s (basisVector m x)) = V m h s (W m i j r (basisVector m x))
  rw [V_basisVector, W_basisVector m i j hij,
    W_basisVector m i j hij, V_basisVector]
  congr 1
  ext k
  by_cases hik : i = k <;> by_cases hhk : h = k <;>
    simp_all [Pi.single_apply]
  <;> ring

theorem W_V_commutator (i j : Fin 3) (hij : i ≠ j) (r s : ℤ) :
    ⁅W m i j r, V m j s⁆ = V m i (r + s) := by
  have hprod : W m i j r * V m j s = V m i (r + s) * V m j s * W m i j r := by
    apply operator_ext m
    intro x
    change W m i j r (V m j s (basisVector m x)) =
      V m i (r + s) (V m j s (W m i j r (basisVector m x)))
    rw [V_basisVector, W_basisVector m i j hij,
      W_basisVector m i j hij, V_basisVector, V_basisVector]
    congr 1
    ext k
    by_cases hik : i = k <;> by_cases hjk : j = k <;>
      simp [Pi.single_apply, hik, hjk, hij, (Ne.symm hij),
        zpow_add, Units.val_mul, mul_add]
    <;> ring
  rw [commutatorElement_def, hprod]
  group

theorem U_W_commutator (i j : Fin 3) (hij : i ≠ j) (r s : ℤ) :
    ⁅U m i r, W m i j s⁆ = U m j (r + s) := by
  have hprod : U m i r * W m i j s = U m j (r + s) * W m i j s * U m i r := by
    apply operator_ext m
    intro x
    change U m i r (W m i j s (basisVector m x)) =
      U m j (r + s) (W m i j s (U m i r (basisVector m x)))
    rw [W_basisVector m i j hij, U_basisVector, U_basisVector,
      map_smul, W_basisVector m i j hij, map_smul, U_basisVector]
    simp [Pi.single_apply, hij, (Ne.symm hij), mul_add, coefficient_add,
      parityValue_add, zpow_add, Units.val_mul, smul_smul, mul_assoc, mul_left_comm, mul_comm]
  rw [commutatorElement_def, hprod]
  group


theorem T_commute (i j : Fin 3) : Commute (T m i) (T m j) := by
  by_cases hij : i = j
  · subst j; exact Commute.refl _
  change _ * _ = _ * _
  apply operator_ext m
  intro x
  change T m i (T m j (basisVector m x)) = T m j (T m i (basisVector m x))
  rw [T_basisVector, T_basisVector, T_basisVector, T_basisVector]
  congr 1
  ext k
  by_cases hik : k = i <;> by_cases hjk : k = j <;>
    simp [scaleCoordinate, Function.update_apply, hik, hjk, hij, (Ne.symm hij)]
  <;> ring

theorem cyclicPower_mul_unit (r : ℤ) :
    (↑(PrimeGroup.cyclicUnit 2 m ^ (r - 1)) : Ring m) *
      (PrimeGroup.cyclicUnit 2 m : Ring m) = ↑(PrimeGroup.cyclicUnit 2 m ^ r) := by
  rw [← Units.val_mul]
  apply congrArg Units.val
  calc
    _ = PrimeGroup.cyclicUnit 2 m ^ (r - 1) * PrimeGroup.cyclicUnit 2 m ^ (1 : ℤ) := by rw [zpow_one]
    _ = _ := by rw [← zpow_add]; congr 1; omega

/-- The inverse shift in U is fixed by conjugation, as in the manuscript. -/
theorem T_U_conjugate (l i : Fin 3) (r : ℤ) :
    T m l * U m i r * (T m l)⁻¹ = U m i (r - if l = i then 1 else 0) := by
  classical
  have hprod : T m l * U m i r = U m i (r - if l = i then 1 else 0) * T m l := by
    apply operator_ext m
    intro x
    change T m l (U m i r (basisVector m x)) =
      U m i (r - if l = i then 1 else 0) (T m l (basisVector m x))
    simp only [U_basisVector, map_smul, T_basisVector]
    by_cases h : l = i
    · subst l
      simp only [if_true, scaleCoordinate, Equiv.coe_fn_mk, Function.update_self]
      rw [← mul_assoc, cyclicPower_mul_unit]
    · simp [h, scaleCoordinate, Function.update_of_ne (Ne.symm h)]
  rw [hprod]
  group

theorem T_V_conjugate (l i : Fin 3) (r : ℤ) :
    T m l * V m i r * (T m l)⁻¹ = V m i (r + if l = i then 1 else 0) := by
  classical
  have hprod : T m l * V m i r = V m i (r + if l = i then 1 else 0) * T m l := by
    apply operator_ext m
    intro x
    change T m l (V m i r (basisVector m x)) =
      V m i (r + if l = i then 1 else 0) (T m l (basisVector m x))
    simp only [V_basisVector, T_basisVector]
    congr 1
    by_cases hli : l = i
    · subst l
      simp only [ite_true]
      ext k
      by_cases hki : k = i
      · subst k
        simp only [scaleCoordinate, Equiv.coe_fn_mk, Function.update_self,
          Pi.add_apply, Pi.single_apply, ite_true, zpow_add, zpow_one, Units.val_mul]
        ring
      · simp [scaleCoordinate, Function.update_of_ne hki,
          Pi.single_apply, hki, Ne.symm hki]
    · simp only [ite_eq_right hli, add_zero]
      ext k
      by_cases hkl : k = l
      · subst k
        simp [scaleCoordinate, Pi.single_apply, hli, Ne.symm hli]
      · simp [scaleCoordinate, Function.update_of_ne hkl]
  rw [hprod]
  group

@[simp] theorem W_diagonal (i : Fin 3) (r : ℤ) : W m i i r = 1 := by simp [W]


theorem T_W_conjugate (l i j : Fin 3) (r : ℤ) :
    T m l * W m i j r * (T m l)⁻¹ =
      W m i j (r + (if l = i then 1 else 0) - if l = j then 1 else 0) := by
  classical
  by_cases hij : i = j
  · subst j
    simp
  have hprod : T m l * W m i j r =
      W m i j (r + (if l = i then 1 else 0) - if l = j then 1 else 0) * T m l := by
    apply operator_ext m
    intro x
    change T m l (W m i j r (basisVector m x)) =
      W m i j (r + (if l = i then 1 else 0) - if l = j then 1 else 0)
        (T m l (basisVector m x))
    rw [W_basisVector m i j hij, T_basisVector, T_basisVector, W_basisVector m i j hij]
    congr 1
    by_cases hli : l = i
    · subst l
      simp only [ite_true, ite_eq_right hij, sub_zero]
      ext k
      by_cases hik : k = i <;> by_cases hjk : j = k <;>
        simp_all [scaleCoordinate, Function.update_apply, Pi.single_apply, hik, hjk,
          hij, (Ne.symm hij), zpow_add, zpow_one, Units.val_mul]
      <;> ring
    · by_cases hlj : l = j
      · subst l
        simp only [ite_eq_right (Ne.symm hij), ite_true, add_zero]
        ext k
        by_cases hik : i = k <;> by_cases hjk : k = j <;>
          simp_all [scaleCoordinate, Function.update_apply, Pi.single_apply, hik, hjk,
            hij, (Ne.symm hij), mul_assoc, ← cyclicPower_mul_unit m r]
        <;> ring
      · simp only [ite_eq_right hli, ite_eq_right hlj, add_zero, sub_zero]
        ext k
        by_cases hik : i = k <;> by_cases hkl : k = l <;>
          simp_all [scaleCoordinate, Function.update_apply, Pi.single_apply, hik, hkl,
            hli, (Ne.symm hli), hlj, (Ne.symm hlj)]
        <;> ring
  rw [hprod]
  group

/-- All displayed relators, on the full explicit coordinate space. -/
def operatorData : PrimeGroup.SelectionGroupData 2 (Space m ≃ₗ[ℂ] Space m) where
  T := T m
  U := U m
  V := V m
  W := W m
  power_U := U_power m
  commute_UU := fun i j a b _ => U_commute m i j a b
  commute_VV := fun i j a b _ => V_commute m i j a b
  commute_UV := fun i j a b h => U_V_commute m i j h a b
  commute_WU := fun i j h a b hhi => W_U_commute m i j h hhi a b
  commute_WV := fun i j h a b hhj => W_V_commute m i j h hhj a b
  commutator_UW := fun i j a b h => U_W_commutator m i j h a b
  commutator_WV := fun i j a b h => W_V_commutator m i j h a b
  commute_TT := T_commute m
  conj_TU := T_U_conjugate m
  conj_TV := T_V_conjugate m
  conj_TW := T_W_conjugate m
  diagonal_W := W_diagonal m


/-- The concrete operators satisfy the manuscript's entire group presentation. -/
theorem explicit_operator_relators :
    ∃ D : PrimeGroup.SelectionGroupData 2 (Space m ≃ₗ[ℂ] Space m),
      D.T = T m ∧ D.U = U m ∧ D.V = V m ∧ D.W = W m := by
  exact ⟨operatorData m, rfl, rfl, rfl, rfl⟩

/-- The actual homomorphism from the infinite presented group. -/
def groupAction : PrimeGroup.Presentation.AuxiliaryGroup 2 →* (Space m ≃ₗ[ℂ] Space m) :=
  PrimeGroup.Presentation.ofData 2 (operatorData m)

/-- The linear representation, obtained from the proved presentation relations. -/
def representation : Representation ℂ (PrimeGroup.Presentation.AuxiliaryGroup 2) (Space m) :=
  (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ℂ) (M := Space m)).comp (groupAction m)

/-- The full explicit group-algebra module; its underlying vector space is S_m³-indexed. -/
abbrev ExplicitModule := (representation m).asModule

theorem explicitModule_finiteDimensional : FiniteDimensional ℂ (ExplicitModule m) := inferInstance

/-- It has the required dimension before taking any quotient. -/
theorem explicitModule_dimension : Module.finrank ℂ (ExplicitModule m) = 2 ^ (3 * m) := by
  rw [LinearEquiv.finrank_eq (representation m).asModuleEquiv]
  exact space_dimension m


/-- The scalar restriction used by Selection is the standard coordinate space. -/
def explicitVectorEquiv :
    Selection.vectorObject (k := ℂ)
      (ModuleCat.of (GroupAlgebraSelection.Ring ℂ 2) (ExplicitModule m)) ≃ₗ[ℂ] Space m where
  toFun x := (representation m).asModuleEquiv x
  invFun x := (representation m).asModuleEquiv.symm x
  left_inv x := (representation m).asModuleEquiv.left_inv x
  right_inv x := (representation m).asModuleEquiv.right_inv x
  map_add' x y := (representation m).asModuleEquiv.map_add x y
  map_smul' c x := by
    change (representation m).asModuleEquiv
      (algebraMap ℂ (GroupAlgebraSelection.Ring ℂ 2) c • (show ExplicitModule m from x)) =
        c • (representation m).asModuleEquiv x
    apply (representation m).asModuleEquiv.symm.injective
    rw [LinearEquiv.symm_apply_apply,
      Representation.asModuleEquiv_symm_map_smul (representation m)]
    rfl

theorem explicitVector_finiteDimensional :
    FiniteDimensional ℂ (Selection.vectorObject (k := ℂ)
      (ModuleCat.of (GroupAlgebraSelection.Ring ℂ 2) (ExplicitModule m))) :=
  Module.Finite.equiv (explicitVectorEquiv m).symm

theorem explicitVector_dimension :
    Module.finrank ℂ (Selection.vectorObject (k := ℂ)
      (ModuleCat.of (GroupAlgebraSelection.Ring ℂ 2) (ExplicitModule m))) = 2 ^ (3 * m) := by
  rw [LinearEquiv.finrank_eq (explicitVectorEquiv m)]
  exact space_dimension m


def fullPhase (a : State m) : Space m ≃ₗ[ℂ] Space m :=
  phase m (fun x => parityValue (pairing m a x))

@[simp] theorem fullPhase_zero : fullPhase m 0 = 1 := by
  ext f x
  simp [fullPhase, phase, pairing]

theorem fullPhase_add (a b : State m) : fullPhase m (a + b) = fullPhase m a * fullPhase m b := by
  ext f x
  change (parityValue (pairing m (a + b) x) : ℂ) * f x =
    (parityValue (pairing m a x) : ℂ) * ((parityValue (pairing m b x) : ℂ) * f x)
  rw [pairing_add_left, parityValue_add, Units.val_mul, mul_assoc]

@[simp] theorem translation_zero : translation m 0 = 1 := by
  ext f x
  change f (-(0 : State m) + x) = f x
  simp

theorem translation_add (a b : State m) : translation m (a + b) = translation m a * translation m b := by
  apply operator_ext m
  intro x
  change translation m (a + b) (basisVector m x) =
    translation m a (translation m b (basisVector m x))
  rw [translation_basisVector, translation_basisVector, translation_basisVector, add_assoc]

theorem fullPhase_single_basis (i : Fin 3) (r : Fin m) :
    fullPhase m (Pi.single i (PrimeGroup.cyclicBasis 2 m (NeZero.ne m) r)) = U m i r.val := by
  ext f x
  change (parityValue (pairing m (Pi.single i (PrimeGroup.cyclicBasis 2 m (NeZero.ne m) r)) x) : ℂ) * f x = _
  rw [pairing_single, PrimeGroup.cyclicBasis_apply]
  simp [U, phase, zpow_natCast, Units.val_pow_eq_pow_val, PrimeGroup.cyclicUnit_val]

theorem translation_single_basis (i : Fin 3) (r : Fin m) :
    translation m (Pi.single i (PrimeGroup.cyclicBasis 2 m (NeZero.ne m) r)) = V m i r.val := by
  apply operator_ext m
  intro x
  rw [translation_basisVector, V_basisVector, PrimeGroup.cyclicBasis_apply]
  simp [zpow_natCast, Units.val_pow_eq_pow_val, PrimeGroup.cyclicUnit_val]

theorem state_expansion (a : State m) :
    (∑ i : Fin 3, ∑ r : Fin m,
      (PrimeGroup.cyclicBasis 2 m (NeZero.ne m)).repr (a i) r •
        (Pi.single i (PrimeGroup.cyclicBasis 2 m (NeZero.ne m) r) : State m)) = a := by
  classical
  ext j
  simp [Finset.sum_apply, Pi.single_apply, smul_ite,
    (PrimeGroup.cyclicBasis 2 m (NeZero.ne m)).sum_repr]

/-- Parameters whose phase operators preserve a fixed complex subspace. -/
def phaseStable (P : Submodule ℂ (Space m)) : Submodule (ZMod 2) (State m) where
  carrier := {a | ∀ f ∈ P, fullPhase m a f ∈ P}
  zero_mem' := by intro f hf; simpa using hf
  add_mem' := by
    intro a b ha hb f hf
    rw [fullPhase_add]
    exact ha _ (hb f hf)
  smul_mem' := by
    intro c a ha
    have hc : c = 0 ∨ c = 1 := by
      have hbinary : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      exact hbinary c
    rcases hc with rfl | rfl
    · intro f hf
      simpa using hf
    · simpa using ha

/-- Parameters whose translations preserve a fixed complex subspace. -/
def translationStable (P : Submodule ℂ (Space m)) : Submodule (ZMod 2) (State m) where
  carrier := {a | ∀ f ∈ P, translation m a f ∈ P}
  zero_mem' := by intro f hf; simpa using hf
  add_mem' := by
    intro a b ha hb f hf
    rw [translation_add]
    exact ha _ (hb f hf)
  smul_mem' := by
    intro c a ha
    have hc : c = 0 ∨ c = 1 := by
      have hbinary : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      exact hbinary c
    rcases hc with rfl | rfl
    · intro f hf
      simpa using hf
    · simpa using ha

/-- The finite U-generators generate all Fourier phase operators. -/
theorem U_stable_fullPhase (P : Submodule ℂ (Space m))
    (hU : ∀ i : Fin 3, ∀ r : Fin m, ∀ f ∈ P, U m i r.val f ∈ P)
    (a : State m) (f : Space m) (hf : f ∈ P) : fullPhase m a f ∈ P := by
  have ha : a ∈ phaseStable m P := by
    rw [← state_expansion m a]
    apply (phaseStable m P).sum_mem
    intro i _
    apply (phaseStable m P).sum_mem
    intro r _
    apply (phaseStable m P).smul_mem
    change ∀ f ∈ P, fullPhase m (Pi.single i (PrimeGroup.cyclicBasis 2 m (NeZero.ne m) r)) f ∈ P
    rw [fullPhase_single_basis]
    exact hU i r
  exact ha f hf

/-- The finite V-generators generate all translations of the full state space. -/
theorem V_stable_translation (P : Submodule ℂ (Space m))
    (hV : ∀ i : Fin 3, ∀ r : Fin m, ∀ f ∈ P, V m i r.val f ∈ P)
    (a : State m) (f : Space m) (hf : f ∈ P) : translation m a f ∈ P := by
  have ha : a ∈ translationStable m P := by
    rw [← state_expansion m a]
    apply (translationStable m P).sum_mem
    intro i _
    apply (translationStable m P).sum_mem
    intro r _
    apply (translationStable m P).smul_mem
    change ∀ f ∈ P, translation m (Pi.single i (PrimeGroup.cyclicBasis 2 m (NeZero.ne m) r)) f ∈ P
    rw [translation_single_basis]
    exact hV i r
  exact ha f hf

/-- The explicitly displayed U,V generators act irreducibly on the full space. -/
theorem U_V_irreducible (P : Submodule ℂ (Space m))
    (hU : ∀ i : Fin 3, ∀ r : Fin m, ∀ f ∈ P, U m i r.val f ∈ P)
    (hV : ∀ i : Fin 3, ∀ r : Fin m, ∀ f ∈ P, V m i r.val f ∈ P) :
    P = ⊥ ∨ P = ⊤ :=
  phase_translation_irreducible m P (U_stable_fullPhase m P hU) (V_stable_translation m P hV)


@[simp] theorem representation_U (i : Fin 3) (r : ℤ) :
    representation m (PresentedGroup.of (PrimeGroup.Presentation.Generator.U i r)) =
      (U m i r).toLinearMap := by
  simp [representation, groupAction, PrimeGroup.Presentation.evaluate, operatorData]

@[simp] theorem representation_V (i : Fin 3) (r : ℤ) :
    representation m (PresentedGroup.of (PrimeGroup.Presentation.Generator.V i r)) =
      (V m i r).toLinearMap := by
  simp [representation, groupAction, PrimeGroup.Presentation.evaluate, operatorData]

instance explicitModule_nontrivial : Nontrivial (ExplicitModule m) :=
  (representation m).asModuleEquiv.toEquiv.nontrivial

/-- Simplicity of the full module in §7.2, with no quotient replacing its space. -/
theorem explicitModule_simple :
    IsSimpleModule (MonoidAlgebra ℂ (PrimeGroup.Presentation.AuxiliaryGroup 2)) (ExplicitModule m) where
  eq_bot_or_eq_top P := by
    let e := (representation m).asModuleEquiv
    let Q : Submodule ℂ (Space m) := (P.restrictScalars ℂ).map e.toLinearMap
    have hU : ∀ i : Fin 3, ∀ r : Fin m, ∀ f ∈ Q, U m i r.val f ∈ Q := by
      intro i r f hf
      obtain ⟨y, hy, rfl⟩ := hf
      refine ⟨MonoidAlgebra.single (PresentedGroup.of (PrimeGroup.Presentation.Generator.U i r.val)) 1 • y,
        P.smul_mem _ hy, ?_⟩
      change (representation m).asModuleEquiv
        (MonoidAlgebra.single (PresentedGroup.of (PrimeGroup.Presentation.Generator.U i r.val)) 1 • y) =
          U m i r.val ((representation m).asModuleEquiv y)
      rw [Representation.asModuleEquiv_map_smul (representation m),
        Representation.asAlgebraHom_single_one, representation_U]
      rfl
    have hV : ∀ i : Fin 3, ∀ r : Fin m, ∀ f ∈ Q, V m i r.val f ∈ Q := by
      intro i r f hf
      obtain ⟨y, hy, rfl⟩ := hf
      refine ⟨MonoidAlgebra.single (PresentedGroup.of (PrimeGroup.Presentation.Generator.V i r.val)) 1 • y,
        P.smul_mem _ hy, ?_⟩
      change (representation m).asModuleEquiv
        (MonoidAlgebra.single (PresentedGroup.of (PrimeGroup.Presentation.Generator.V i r.val)) 1 • y) =
          V m i r.val ((representation m).asModuleEquiv y)
      rw [Representation.asModuleEquiv_map_smul (representation m),
        Representation.asAlgebraHom_single_one, representation_V]
      rfl
    rcases U_V_irreducible m Q hU hV with hQ | hQ
    · left
      have h : P.restrictScalars ℂ = ⊥ := by simpa [Q] using hQ
      exact (Submodule.restrictScalars_eq_bot_iff ℂ _ _).mp h
    · right
      have h : P.restrictScalars ℂ = ⊤ := by simpa [Q] using hQ
      exact (Submodule.restrictScalars_eq_top_iff ℂ _ _).mp h


theorem U_V_commutator (i : Fin 3) (r s : ℤ) :
    ⁅U m i r, V m i s⁆ =
      phase m (fun _ => parityValue (coefficient m (↑(PrimeGroup.cyclicUnit 2 m ^ (r + s)) : Ring m))) := by
  let δ := parityValue (coefficient m (↑(PrimeGroup.cyclicUnit 2 m ^ (r + s)) : Ring m))
  have hprod : U m i r * V m i s = phase m (fun _ => δ) * V m i s * U m i r := by
    apply operator_ext m
    intro x
    change U m i r (V m i s (basisVector m x)) =
      phase m (fun _ => δ) (V m i s (U m i r (basisVector m x)))
    rw [V_basisVector, U_basisVector, U_basisVector, map_smul, V_basisVector,
      map_smul, phase_basisVector]
    simp [δ, Pi.single_apply, mul_add, coefficient_add, parityValue_add,
      zpow_add, Units.val_mul, smul_smul, mul_assoc, mul_left_comm, mul_comm]
  change ⁅U m i r, V m i s⁆ = phase m (fun _ => δ)
  rw [commutatorElement_def, hprod]
  group

/-- The central elements act by exactly the manuscript's coefficient character. -/
theorem groupAction_z (q : ℤ) :
    groupAction m (PrimeGroup.Presentation.z 2 q) =
      phase m (fun _ => parityValue (coefficient m (↑(PrimeGroup.cyclicUnit 2 m ^ q) : Ring m))) := by
  change groupAction m
    ⁅PresentedGroup.of (PrimeGroup.Presentation.Generator.U 0 0),
      PresentedGroup.of (PrimeGroup.Presentation.Generator.V 0 q)⁆ = _
  rw [map_commutatorElement]
  simp only [groupAction, PrimeGroup.Presentation.ofData_of,
    PrimeGroup.Presentation.evaluate, operatorData]
  simpa using U_V_commutator m 0 0 q


/-- The early central generators act by +1 and the last by -1. -/
theorem explicitModule_central_action (i : Fin m) (x : ExplicitModule m) :
    GroupAlgebraSelection.centralElement ℂ 2 i.val • x =
      (if i = FiniteSelectionSource.lastIndex m then (-1 : ℂ) else 1) • x := by
  apply (representation m).asModuleEquiv.injective
  rw [Representation.asModuleEquiv_map_smul]
  simp only [GroupAlgebraSelection.centralElement,
    Representation.asAlgebraHom_single_one]
  change groupAction m (PrimeGroup.Presentation.z 2 i.val)
    ((representation m).asModuleEquiv x) = _
  rw [groupAction_z]
  have hc : coefficient m (↑(PrimeGroup.cyclicUnit 2 m ^ (i.val : ℤ)) : Ring m) =
      if i = FiniteSelectionSource.lastIndex m then 1 else 0 := by
    simp only [zpow_natCast, Units.val_pow_eq_pow_val, PrimeGroup.cyclicUnit_val]
    rw [← PrimeGroup.cyclicBasis_apply 2 m (NeZero.ne m) i, coefficient_basis]
  simp only [map_smul]
  ext y
  change (parityValue (coefficient m (↑(PrimeGroup.cyclicUnit 2 m ^ (i.val : ℤ)) : Ring m)) : ℂ) *
    (representation m).asModuleEquiv x y =
      (if i = FiniteSelectionSource.lastIndex m then (-1 : ℂ) else 1) *
        (representation m).asModuleEquiv x y
  rw [hc]
  by_cases hi : i = FiniteSelectionSource.lastIndex m <;> simp [hi]

theorem explicitModule_idempotent_action (i : Fin m) (x : ExplicitModule m) :
    GroupAlgebraSelection.idempotentTwo ℂ i.val • x =
      if i = FiniteSelectionSource.lastIndex m then 0 else x := by
  unfold GroupAlgebraSelection.idempotentTwo
  rw [smul_assoc, add_smul, one_smul, explicitModule_central_action]
  by_cases h : i = FiniteSelectionSource.lastIndex m
  · simp [h]
  · simp [h, ← two_smul ℂ x, smul_smul]

/-- Exact extinction at the m-th iteration for this full explicit simple module. -/
theorem explicitModule_extinction :
    (∀ n < m, Nontrivial (Selection.iterate (GroupAlgebraSelection.dataTwo ℂ (by norm_num))
      (ModuleCat.of (GroupAlgebraSelection.Ring ℂ 2) (ExplicitModule m)) n)) ∧
    Subsingleton (Selection.iterate (GroupAlgebraSelection.dataTwo ℂ (by norm_num))
      (ModuleCat.of (GroupAlgebraSelection.Ring ℂ 2) (ExplicitModule m)) m) := by
  apply Selection.extinction_criterion (GroupAlgebraSelection.dataTwo ℂ (by norm_num))
    (ModuleCat.of (GroupAlgebraSelection.Ring ℂ 2) (ExplicitModule m)) m
    (Nat.pos_of_ne_zero (NeZero.ne m))
  · intro q hq x
    rw [FiniteSelectionRestriction.eAtTwo]
    have hqm : q < m := by omega
    have hne : (⟨q, hqm⟩ : Fin m) ≠ FiniteSelectionSource.lastIndex m := by
      intro h
      have hv := congrArg Fin.val h
      simp [FiniteSelectionSource.lastIndex] at hv
      omega
    simpa [hne] using explicitModule_idempotent_action m ⟨q, hqm⟩ x
  · intro x
    rw [FiniteSelectionRestriction.eAtTwo]
    simpa [FiniteSelectionSource.lastIndex] using
      explicitModule_idempotent_action m (FiniteSelectionSource.lastIndex m) x


/-- Proposition 7.2, for the constructed full coordinate module. -/
theorem proposition_7_2 :
    IsSimpleModule (GroupAlgebraSelection.Ring ℂ 2) (ExplicitModule m) ∧
    FiniteDimensional ℂ (Selection.vectorObject (k := ℂ)
      (ModuleCat.of (GroupAlgebraSelection.Ring ℂ 2) (ExplicitModule m))) ∧
    Module.finrank ℂ (Selection.vectorObject (k := ℂ)
      (ModuleCat.of (GroupAlgebraSelection.Ring ℂ 2) (ExplicitModule m))) = 2 ^ (3 * m) ∧
    (∀ n < m, Nontrivial (Selection.iterate (GroupAlgebraSelection.dataTwo ℂ (by norm_num))
      (ModuleCat.of (GroupAlgebraSelection.Ring ℂ 2) (ExplicitModule m)) n)) ∧
    Subsingleton (Selection.iterate (GroupAlgebraSelection.dataTwo ℂ (by norm_num))
      (ModuleCat.of (GroupAlgebraSelection.Ring ℂ 2) (ExplicitModule m)) m) :=
  ⟨explicitModule_simple m, explicitVector_finiteDimensional m, explicitVector_dimension m,
    (explicitModule_extinction m).1, (explicitModule_extinction m).2⟩

end
end Note198.ExplicitSimpleModules


































