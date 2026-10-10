import Note198.PrimeFinitePresentation

/-! Lemma 2.2: delete the three diagonal W seeds from the finite presentation.
The remaining presentation has exactly 15 generators and finitely many relations. -/
namespace Note198.PrimeGroup.FifteenPresentation
open scoped commutatorElement
open FinitePresentation

inductive OffSeedGenerator where
  | T : Fin 3 → OffSeedGenerator
  | U : Fin 3 → OffSeedGenerator
  | V : Fin 3 → OffSeedGenerator
  | W (i j : Fin 3) (h : i ≠ j) : OffSeedGenerator
  deriving DecidableEq, Fintype

def includeGenerator : OffSeedGenerator → SeedGenerator
  | .T i => .T i
  | .U i => .U i
  | .V i => .V i
  | .W i j _ => .W i j

def eraseGenerator : SeedGenerator → FreeGroup OffSeedGenerator
  | .T i => FreeGroup.of (.T i)
  | .U i => FreeGroup.of (.U i)
  | .V i => FreeGroup.of (.V i)
  | .W i j => if h : i = j then 1 else FreeGroup.of (.W i j h)

def eraseHom : FreeGroup SeedGenerator →* FreeGroup OffSeedGenerator :=
  FreeGroup.lift eraseGenerator

variable (p : ℕ)
def offRelators : Set (FreeGroup OffSeedGenerator) := eraseHom '' finiteRelators p
abbrev OffGroup := PresentedGroup (offRelators p)

def forwardValues : OffSeedGenerator → Model p :=
  fun s => PresentedGroup.of (includeGenerator s)

theorem forward_free :
    (FreeGroup.lift (forwardValues p)).comp eraseHom = PresentedGroup.mk (finiteRelators p) := by
  apply FreeGroup.ext_hom
  intro s
  cases s with
  | T i => rfl
  | U i => rfl
  | V i => rfl
  | W i j =>
      by_cases h : i = j
      · subst j
        simp only [MonoidHom.comp_apply, eraseHom, FreeGroup.lift_apply_of]
        change FreeGroup.lift (forwardValues p) (eraseGenerator (.W i i)) =
          (modelValues p).w i i
        simp only [eraseGenerator, dif_pos rfl, map_one]
        exact ((modelSeedData p).diagonal i).symm
      · simp [eraseHom, eraseGenerator, h, forwardValues, includeGenerator,
          MonoidHom.comp_apply, PresentedGroup.of]

def forward : OffGroup p →* Model p :=
  PresentedGroup.toGroup (f := forwardValues p) (by
    intro r hr
    obtain ⟨s, hs, rfl⟩ := hr
    have h := DFunLike.congr_fun (forward_free p) s
    rw [MonoidHom.comp_apply] at h
    rw [h]
    exact PresentedGroup.one_of_mem hs)

@[simp] theorem forward_of (s : OffSeedGenerator) :
    forward p (PresentedGroup.of s) = PresentedGroup.of (includeGenerator s) :=
  PresentedGroup.toGroup.of _

def reverseValues : SeedGenerator → OffGroup p :=
  fun s => PresentedGroup.mk (offRelators p) (eraseGenerator s)

theorem reverse_free :
    FreeGroup.lift (reverseValues p) =
      (PresentedGroup.mk (offRelators p)).comp eraseHom := by
  apply FreeGroup.ext_hom
  intro s
  rfl

def reverse : Model p →* OffGroup p :=
  PresentedGroup.toGroup (f := reverseValues p) (by
    intro r hr
    rw [reverse_free p, MonoidHom.comp_apply]
    exact PresentedGroup.one_of_mem ⟨r, hr, rfl⟩)

@[simp] theorem reverse_of (s : SeedGenerator) :
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
  | U i =>
      simp only [MonoidHom.comp_apply, forward_of, reverse_of, includeGenerator, eraseGenerator,
        MonoidHom.id_apply]
      rfl
  | V i =>
      simp only [MonoidHom.comp_apply, forward_of, reverse_of, includeGenerator, eraseGenerator,
        MonoidHom.id_apply]
      rfl
  | W i j h =>
      simp only [MonoidHom.comp_apply, forward_of, reverse_of, includeGenerator, eraseGenerator,
        MonoidHom.id_apply, dite_eq_right h]
      rfl

theorem forward_reverse :
    (forward p).comp (reverse p) = MonoidHom.id (Model p) := by
  apply PresentedGroup.ext
  intro s
  cases s with
  | T i =>
      simp only [MonoidHom.comp_apply, reverse_of, eraseGenerator, MonoidHom.id_apply]
      exact forward_of p (.T i)
  | U i =>
      simp only [MonoidHom.comp_apply, reverse_of, eraseGenerator, MonoidHom.id_apply]
      exact forward_of p (.U i)
  | V i =>
      simp only [MonoidHom.comp_apply, reverse_of, eraseGenerator, MonoidHom.id_apply]
      exact forward_of p (.V i)
  | W i j =>
      by_cases h : i = j
      · subst j
        simp only [MonoidHom.comp_apply, reverse_of, eraseGenerator, dite_eq_left rfl,
          map_one, MonoidHom.id_apply]
        exact ((modelSeedData p).diagonal i).symm
      · simp only [MonoidHom.comp_apply, reverse_of, eraseGenerator, dite_eq_right h,
          MonoidHom.id_apply]
        exact forward_of p (.W i j h)

/-- Two-way elimination of the redundant diagonal generators. -/
def offDiagonalEquiv : OffGroup p ≃* Model p where
  toFun := forward p
  invFun := reverse p
  left_inv x := DFunLike.congr_fun (reverse_forward p) x
  right_inv x := DFunLike.congr_fun (forward_reverse p) x
  map_mul' := (forward p).map_mul

/-- Finite presentability transfers to the presentation with only off-diagonal W. -/
theorem offGroup_isFinitelyPresented : Group.IsFinitelyPresented (OffGroup p) := by
  letI : Group.IsFinitelyPresented (Model p) := inferInstance
  exact Group.IsFinitelyPresented.equiv (offDiagonalEquiv p).symm




theorem offSeed_card : Fintype.card OffSeedGenerator = 15 := by decide

theorem offRelators_finite : Set.Finite (offRelators p) :=
  (Set.finite_range (FinitePresentation.relator p)).image eraseHom

/-- A concrete fifteen-generator finite presentation of the actual manuscript group. -/
def manuscriptEquiv : OffGroup p ≃* Presentation.AuxiliaryGroup p :=
  (offDiagonalEquiv p).trans (FinitePresentation.presentationEquiv p)

/-- The numerical generator assertion and actual presented-group equivalence of Lemma 2.2. -/
theorem lemma_2_2_fifteen :
    Fintype.card OffSeedGenerator = 15 ∧ Set.Finite (offRelators p) ∧
      Nonempty (OffGroup p ≃* Presentation.AuxiliaryGroup p)  := by
  sorry

end Note198.PrimeGroup.FifteenPresentation

