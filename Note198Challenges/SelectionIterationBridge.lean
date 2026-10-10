import Note198.Selection
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Note198.Selection
noncomputable section
open CategoryTheory
open scoped BigOperators
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (S : Data k R)

theorem alphaPow_succ (n : ℕ) (r : R) :
    (S.α ^ (n + 1)) r = (S.α ^ n) (S.α r) := by
  rw [pow_succ]
  rfl

theorem eAt_eq_pow (n : ℕ) : eAt S n = (S.α ^ n) S.e := by
  sorry

def iterateEmbedding (M : ModuleCat.{u} R) : (n : ℕ) → iterate S M n → M
  | 0 => fun x => x
  | n + 1 => fun x => iterateEmbedding M n x.val

theorem iterateEmbedding_injective (M : ModuleCat.{u} R) (n : ℕ) :
    Function.Injective (iterateEmbedding S M n) := by
  induction n with
  | zero => exact Function.injective_id
  | succ n ih =>
    intro x y h
    exact Subtype.ext (ih h)

theorem iterateEmbedding_add (M : ModuleCat.{u} R) (n : ℕ)
    (x y : iterate S M n) :
    iterateEmbedding S M n (x + y) = iterateEmbedding S M n x + iterateEmbedding S M n y := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih x.val y.val

theorem iterateEmbedding_smul (M : ModuleCat.{u} R) (n : ℕ)
    (r : R) (x : iterate S M n) :
    iterateEmbedding S M n (r • x) = (S.α ^ n) r • iterateEmbedding S M n x := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    change iterateEmbedding S M n (S.α r • x.val) = (S.α ^ (n+1)) r • iterateEmbedding S M n x.val
    rw [alphaPow_succ]
    exact ih (S.α r) x.val

theorem iterateEmbedding_range (M : ModuleCat.{u} R) (n : ℕ) (y : M) :
    (∃ x : iterate S M n, iterateEmbedding S M n x = y) ↔
      ∀ i < n, eAt S i • y = y := by
  induction n generalizing y with
  | zero =>
    constructor
    · intro _ i hi; omega
    · intro _; exact ⟨y, rfl⟩
  | succ n ih =>
    constructor
    · rintro ⟨x, rfl⟩ i hi
      by_cases hin : i < n
      · exact (ih _).mp ⟨x.val, rfl⟩ i hin
      · have he : i = n := by omega
        subst i
        have he : S.e • (x.val : iterate S M n) = x.val := x.property
        have hx := congrArg (iterateEmbedding S M n) he
        rw [eAt_eq_pow]
        exact (iterateEmbedding_smul S M n S.e (x.val : iterate S M n)).symm.trans hx
    · intro hy
      obtain ⟨x, hx⟩ := (ih y).mpr (fun i hi => hy i (by omega))
      have he : S.e • x = x := by
        apply iterateEmbedding_injective S M n
        rw [iterateEmbedding_smul, ← eAt_eq_pow, hx]
        exact hy n (by omega)
      exact ⟨⟨x, he⟩, hx⟩

theorem eAt_idempotent (n : ℕ) : eAt S n * eAt S n = eAt S n := by
  rw [eAt_eq_pow, ← map_mul, S.idempotent]

theorem eAt_central (n : ℕ) (r : R) : Commute (eAt S n) r := by
  obtain ⟨s, rfl⟩ := (S.α ^ n).surjective r
  rw [eAt_eq_pow]
  exact (S.central s).map (S.α ^ n).toMonoidHom

def iterationProduct : ℕ → R
  | 0 => 1
  | n + 1 => iterationProduct n * eAt S n

theorem iterationProduct_eq_finset (n : ℕ) :
    iterationProduct S n = ((List.range n).map (eAt S)).prod := by
  sorry

theorem iterationProduct_central (n : ℕ) (r : R) : Commute (iterationProduct S n) r := by
  induction n with
  | zero => exact Commute.one_left r
  | succ n ih => exact ih.mul_left (eAt_central S n r)

theorem iterationProduct_idempotent (n : ℕ) :
    iterationProduct S n * iterationProduct S n = iterationProduct S n := by
  induction n with
  | zero => simp [iterationProduct]
  | succ n ih =>
    change (iterationProduct S n * eAt S n) * (iterationProduct S n * eAt S n) = _
    rw [mul_assoc, ← mul_assoc (eAt S n), (eAt_central S n _).eq,
      mul_assoc (iterationProduct S n), ← mul_assoc, ih, eAt_idempotent]
    rfl

theorem iterationProduct_fixed_iff (M : ModuleCat.{u} R) (n : ℕ) (y : M) :
    iterationProduct S n • y = y ↔ ∀ i < n, eAt S i • y = y := by
  induction n with
  | zero => simp [iterationProduct]
  | succ n ih =>
    constructor
    · intro h i hi
      have ha : iterationProduct S n • y = y := by
        calc
          _ = iterationProduct S n • (iterationProduct S (n+1) • y) := congrArg _ h.symm
          _ = iterationProduct S (n+1) • y := by
            simp only [iterationProduct, ← mul_smul, ← mul_assoc, iterationProduct_idempotent]
          _ = y := h
      have hb : eAt S n • y = y := by
        calc
          _ = eAt S n • (iterationProduct S (n+1) • y) := congrArg _ h.symm
          _ = iterationProduct S (n+1) • y := by
            simp only [iterationProduct, ← mul_smul]
            rw [← mul_assoc, (eAt_central S n _).eq, mul_assoc, eAt_idempotent]
          _ = y := h
      by_cases hin : i < n
      · exact ih.mp ha i hin
      · have : i = n := by omega
        simpa [this] using hb
    · intro h
      change (iterationProduct S n * eAt S n) • y = y
      rw [mul_smul, h n (by omega)]
      exact ih.mpr (fun i hi => h i (by omega))

def productSelected (M : ModuleCat.{u} R) (n : ℕ) : Submodule R M where
  carrier := {y | iterationProduct S n • y = y}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change iterationProduct S n • x = x at hx
    change iterationProduct S n • y = y at hy
    change iterationProduct S n • (x+y) = x+y
    rw [smul_add, hx, hy]
  smul_mem' := by
    intro r y hy
    change iterationProduct S n • (r • y) = r • y
    rw [← mul_smul, (iterationProduct_central S n r).eq, mul_smul, hy]

def productPullback (M : ModuleCat.{u} R) (n : ℕ) : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars (S.α ^ n).toRingHom).obj
    (ModuleCat.of R (productSelected S M n))

theorem productSelected_eq_image (M : ModuleCat.{u} R) (n : ℕ) (y : M) :
    y ∈ productSelected S M n ↔ ∃ x : M, iterationProduct S n • x = y := by
  sorry

def iterateProductMap (M : ModuleCat.{u} R) (n : ℕ) :
    iterate S M n →ₗ[R] productPullback S M n where
  toFun x := ⟨iterateEmbedding S M n x,
    (iterationProduct_fixed_iff S M n _).mpr ((iterateEmbedding_range S M n _).mp ⟨x, rfl⟩)⟩
  map_add' x y := Subtype.ext (iterateEmbedding_add S M n x y)
  map_smul' r x := Subtype.ext (iterateEmbedding_smul S M n r x)

theorem iterateProductMap_bijective (M : ModuleCat.{u} R) (n : ℕ) :
    Function.Bijective (iterateProductMap S M n) := by
  sorry

/-- Equation (2.4): the actual recursive selection is the product submodule
with scalars pulled back along alpha^n, including the empty product at n=0. -/
def iterateProductEquiv (M : ModuleCat.{u} R) (n : ℕ) :
    iterate S M n ≃ₗ[R] productPullback S M n :=
  LinearEquiv.ofBijective (iterateProductMap S M n) (iterateProductMap_bijective S M n)

theorem selection_iteration_formula (M : ModuleCat.{u} R) (n : ℕ) :
    Nonempty (iterate S M n ≃ₗ[R] productPullback S M n) := by
  sorry

end
end Note198.Selection
