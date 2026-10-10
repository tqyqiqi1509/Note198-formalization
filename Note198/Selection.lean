import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Lean.Elab.Tactic.Omega

/-! The selection operation from Section 2, over an arbitrary field.
This proves the extinction criterion for modules having the specified
idempotent actions. It does not yet construct the finite group quotients
or simple modules of Proposition 2.1.
-/
namespace Note198.Selection
noncomputable section
open CategoryTheory
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]

/-- The actual inputs of H: a central idempotent and a k-algebra automorphism. -/
structure Data (k R : Type u) [Field k] [Ring R] [Algebra k R] where
  e : R
  idempotent : e * e = e
  central : ∀ r : R, Commute e r
  α : R ≃ₐ[k] R

variable (S : Data k R)

/-- eY represented by the fixed vectors of e. -/
def selected (M : ModuleCat.{u} R) : Submodule R M where
  carrier := {x | S.e • x = x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change S.e • (x + y) = x + y
    rw [smul_add, hx, hy]
  smul_mem' := by
    intro r x hx
    change S.e • (r • x) = r • x
    rw [← mul_smul, (S.central r).eq, mul_smul, hx]

theorem selected_eq_image (M : ModuleCat.{u} R) (x : M) :
    x ∈ selected S M ↔ ∃ y : M, S.e • y = x := by
  constructor
  · intro hx; exact ⟨x, hx⟩
  · rintro ⟨y, rfl⟩
    change S.e • (S.e • y) = S.e • y
    rw [← mul_smul, S.idempotent]

/-- H(Y) = restriction of scalars along α on the selected submodule.
This is α and not α inverse. -/
def H (M : ModuleCat.{u} R) : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars S.α.toRingHom).obj (ModuleCat.of R (selected S M))

def iterate (M : ModuleCat.{u} R) (n : ℕ) : ModuleCat.{u} R :=
  Nat.rec M (fun _ previous => H S previous) n

/-- e_q = α^q(e), with q a nonnegative integer. -/
def eAt : ℕ → R
  | 0 => S.e
  | q + 1 => S.α (eAt q)

/-- The underlying k-vector space, using the given k-algebra structure on R. -/
def vectorObject (M : ModuleCat.{u} R) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (algebraMap k R)).obj M

def H_inclusion (M : ModuleCat.{u} R) :
    vectorObject (k := k) (H S M) →ₗ[k] vectorObject (k := k) M where
  toFun x := x.val
  map_add' _ _ := rfl
  map_smul' c x := by
    change S.α (algebraMap k R c) • x.val = algebraMap k R c • x.val
    rw [AlgEquiv.commutes]

theorem H_finiteDimensional (M : ModuleCat.{u} R)
    [FiniteDimensional k (vectorObject (k := k) M)] :
    FiniteDimensional k (vectorObject (k := k) (H S M)) :=
  FiniteDimensional.of_injective (H_inclusion S M) Subtype.val_injective

theorem iterate_finiteDimensional (M : ModuleCat.{u} R)
    [FiniteDimensional k (vectorObject (k := k) M)] (n : ℕ) :
    FiniteDimensional k (vectorObject (k := k) (iterate S M n)) := by
  induction n with
  | zero =>
    change FiniteDimensional k (vectorObject (k := k) M)
    exact inferInstance
  | succ n ih =>
    let := ih
    exact H_finiteDimensional S (iterate S M n)

def IdentityAt (M : ModuleCat.{u} R) (q : ℕ) : Prop :=
  ∀ x : M, eAt S q • x = x

def ZeroAt (M : ModuleCat.{u} R) (q : ℕ) : Prop :=
  ∀ x : M, eAt S q • x = 0

theorem identityAt_step (M : ModuleCat.{u} R) (q : ℕ)
    (h : IdentityAt S M (q + 1)) : IdentityAt S (H S M) q := by
  intro x
  apply Subtype.ext
  change S.α (eAt S q) • x.val = x.val
  exact h x.val

theorem zeroAt_step (M : ModuleCat.{u} R) (q : ℕ)
    (h : ZeroAt S M (q + 1)) : ZeroAt S (H S M) q := by
  intro x
  apply Subtype.ext
  change S.α (eAt S q) • x.val = 0
  exact h x.val

theorem H_nontrivial (M : ModuleCat.{u} R) [Nontrivial M]
    (h : IdentityAt S M 0) : Nontrivial (H S M) := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne M
  exact ⟨⟨⟨x, h x⟩, ⟨y, h y⟩, fun he => hxy (congrArg Subtype.val he)⟩⟩

theorem H_subsingleton (M : ModuleCat.{u} R)
    (h : ZeroAt S M 0) : Subsingleton (H S M) := by
  refine ⟨fun x y => Subtype.ext ?_⟩
  have hx : x.val = 0 := x.property.symm.trans (h x.val)
  have hy : y.val = 0 := y.property.symm.trans (h y.val)
  exact hx.trans hy.symm

theorem identityAt_iterate (M : ModuleCat.{u} R) (n q : ℕ)
    (h : IdentityAt S M (q + n)) : IdentityAt S (iterate S M n) q := by
  induction n generalizing q with
  | zero => simpa [iterate] using h
  | succ n ih =>
    apply identityAt_step S
    apply ih
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem zeroAt_iterate (M : ModuleCat.{u} R) (n q : ℕ)
    (h : ZeroAt S M (q + n)) : ZeroAt S (iterate S M n) q := by
  induction n generalizing q with
  | zero => simpa [iterate] using h
  | succ n ih =>
    apply zeroAt_step S
    apply ih
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- The induction used at the end of the proof of Proposition 2.1.
Nontrivial means the module is not the zero module; subsingleton is the
zero-module condition. The positive m and all action hypotheses are explicit. -/
theorem extinction_criterion (M : ModuleCat.{u} R) [Nontrivial M]
    (m : ℕ) (hm : 0 < m)
    (hid : ∀ q < m - 1, IdentityAt S M q)
    (hzero : ZeroAt S M (m - 1)) :
    (∀ n < m, Nontrivial (iterate S M n)) ∧
    Subsingleton (iterate S M m) := by
  constructor
  · intro n hn
    induction n with
    | zero =>
      change Nontrivial M
      exact inferInstance
    | succ n ih =>
      letI : Nontrivial (iterate S M n) := ih (by omega)
      change Nontrivial (H S (iterate S M n))
      apply H_nontrivial S
      apply identityAt_iterate S
      simpa only [Nat.zero_add] using hid n (by omega)
  · have hz : ZeroAt S (iterate S M (m - 1)) 0 :=
      zeroAt_iterate S M (m - 1) 0 (by simpa using hzero)
    have h := H_subsingleton S (iterate S M (m - 1)) hz
    change Subsingleton (iterate S M ((m - 1) + 1)) at h
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ m)] using h

end
end Note198.Selection
