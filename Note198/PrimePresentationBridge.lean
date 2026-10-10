import Note198.PrimeFinitePresentation

/-! Eliminate the redundant diagonal W generators. The reduced relator set
is the image of the original relator set under the substitution W_ii(a)=1.
Consequently it presents precisely the manuscript's off-diagonal equations:
diagonal equations and their commutation/conjugation instances become tautologies.
This file concerns the infinite presentation, not the count of finite seed relators. -/
namespace Note198.PrimeGroup.PresentationBridge
open scoped commutatorElement
open Presentation

inductive OffGenerator where
  | T : Fin 3 → OffGenerator
  | U : Fin 3 → ℤ → OffGenerator
  | V : Fin 3 → ℤ → OffGenerator
  | W (i j : Fin 3) (h : i ≠ j) (a : ℤ) : OffGenerator

def includeGenerator : OffGenerator → Generator
  | .T i => .T i
  | .U i a => .U i a
  | .V i a => .V i a
  | .W i j _ a => .W i j a

def eraseGenerator : Generator → FreeGroup OffGenerator
  | .T i => FreeGroup.of (.T i)
  | .U i a => FreeGroup.of (.U i a)
  | .V i a => FreeGroup.of (.V i a)
  | .W i j a => if h : i = j then 1 else FreeGroup.of (.W i j h a)

def eraseHom : FreeGroup Generator →* FreeGroup OffGenerator :=
  FreeGroup.lift eraseGenerator

variable (p : ℕ)
def offRelators : Set (FreeGroup OffGenerator) := eraseHom '' relators p
abbrev OffGroup := PresentedGroup (offRelators p)

def forwardValues : OffGenerator → AuxiliaryGroup p :=
  fun s => PresentedGroup.of (includeGenerator s)

theorem forward_free :
    (FreeGroup.lift (forwardValues p)).comp eraseHom = PresentedGroup.mk (relators p) := by
  apply FreeGroup.ext_hom
  intro s
  cases s with
  | T i => rfl
  | U i a => rfl
  | V i a => rfl
  | W i j a =>
      by_cases h : i = j
      · subst j
        simp only [MonoidHom.comp_apply, eraseHom, FreeGroup.lift_apply_of]
        change FreeGroup.lift (forwardValues p) (eraseGenerator (.W i i a)) =
          (data p).W i i a
        simp only [eraseGenerator, dif_pos rfl, map_one]
        exact ((data p).diagonal_W i a).symm
      · simp [eraseHom, eraseGenerator, h, forwardValues, includeGenerator,
          MonoidHom.comp_apply, PresentedGroup.of]

def forward : OffGroup p →* AuxiliaryGroup p :=
  PresentedGroup.toGroup (f := forwardValues p) (by
    intro r hr
    obtain ⟨s, hs, rfl⟩ := hr
    have h := DFunLike.congr_fun (forward_free p) s
    rw [MonoidHom.comp_apply] at h
    rw [h]
    exact PresentedGroup.one_of_mem hs)

@[simp] theorem forward_of (s : OffGenerator) :
    forward p (PresentedGroup.of s) = PresentedGroup.of (includeGenerator s) :=
  PresentedGroup.toGroup.of _

def reverseValues : Generator → OffGroup p :=
  fun s => PresentedGroup.mk (offRelators p) (eraseGenerator s)

theorem reverse_free :
    FreeGroup.lift (reverseValues p) =
      (PresentedGroup.mk (offRelators p)).comp eraseHom := by
  apply FreeGroup.ext_hom
  intro s
  rfl

def reverse : AuxiliaryGroup p →* OffGroup p :=
  PresentedGroup.toGroup (f := reverseValues p) (by
    intro r hr
    rw [reverse_free p, MonoidHom.comp_apply]
    exact PresentedGroup.one_of_mem ⟨r, hr, rfl⟩)

@[simp] theorem reverse_of (s : Generator) :
    reverse p (PresentedGroup.of s) =
      PresentedGroup.mk (offRelators p) (eraseGenerator s) :=
  PresentedGroup.toGroup.of _

theorem reverse_forward : (reverse p).comp (forward p) = MonoidHom.id (OffGroup p) := by
  apply PresentedGroup.ext
  intro s
  cases s with
  | T i =>
      simp only [MonoidHom.comp_apply, forward_of, reverse_of, includeGenerator, eraseGenerator,
        MonoidHom.id_apply]
      rfl
  | U i a =>
      simp only [MonoidHom.comp_apply, forward_of, reverse_of, includeGenerator, eraseGenerator,
        MonoidHom.id_apply]
      rfl
  | V i a =>
      simp only [MonoidHom.comp_apply, forward_of, reverse_of, includeGenerator, eraseGenerator,
        MonoidHom.id_apply]
      rfl
  | W i j h a =>
      simp only [MonoidHom.comp_apply, forward_of, reverse_of, includeGenerator, eraseGenerator,
        MonoidHom.id_apply, dite_eq_right h]
      rfl

theorem forward_reverse :
    (forward p).comp (reverse p) = MonoidHom.id (AuxiliaryGroup p) := by
  apply PresentedGroup.ext
  intro s
  cases s with
  | T i =>
      simp only [MonoidHom.comp_apply, reverse_of, eraseGenerator, MonoidHom.id_apply]
      exact forward_of p (.T i)
  | U i a =>
      simp only [MonoidHom.comp_apply, reverse_of, eraseGenerator, MonoidHom.id_apply]
      exact forward_of p (.U i a)
  | V i a =>
      simp only [MonoidHom.comp_apply, reverse_of, eraseGenerator, MonoidHom.id_apply]
      exact forward_of p (.V i a)
  | W i j a =>
      by_cases h : i = j
      · subst j
        simp only [MonoidHom.comp_apply, reverse_of, eraseGenerator, dite_eq_left rfl,
          map_one, MonoidHom.id_apply]
        exact ((data p).diagonal_W i a).symm
      · simp only [MonoidHom.comp_apply, reverse_of, eraseGenerator, dite_eq_right h,
          MonoidHom.id_apply]
        exact forward_of p (.W i j h a)

/-- Two-way elimination of the redundant diagonal generators. -/
def offDiagonalEquiv : OffGroup p ≃* AuxiliaryGroup p where
  toFun := forward p
  invFun := reverse p
  left_inv x := DFunLike.congr_fun (reverse_forward p) x
  right_inv x := DFunLike.congr_fun (forward_reverse p) x
  map_mul' := (forward p).map_mul

/-- Finite presentability transfers to the presentation with only off-diagonal W. -/
theorem offGroup_isFinitelyPresented : Group.IsFinitelyPresented (OffGroup p) := by
  letI := FinitePresentation.auxiliaryGroup_isFinitelyPresented p
  exact Group.IsFinitelyPresented.equiv (offDiagonalEquiv p).symm

end Note198.PrimeGroup.PresentationBridge
