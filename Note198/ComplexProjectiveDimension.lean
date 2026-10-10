import OAI.Algebra.Finitistic.Dimension.PDMinimalData
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.CategoryTheory.Idempotents.HomologicalComplex
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Int.Interval
import OAI.Algebra.Finitistic.Dimension.PDDetection
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Order.Hom.WithTopBot
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Algebra.Order.Monoid.WithTop

/-! Signed projective dimension from the manuscript's projective representatives.
The value is an extended integer: negative integers are retained, zero objects
have lower bounds of every integer, and an empty set of bounds has infimum top.
Representatives are allowed arbitrary projective terms. The residue detection and existence of minimal bounded finite representatives are
further theorems; they are not part of this definition or assumed as certificates.
-/
namespace Note198.ComplexProjectiveDimension
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators ModuleCat.Algebra ZeroObject
universe u
variable {A : Type u} [Ring A]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} A)]

/-- A genuine bounded projective representative, zero below degree -d. Terms need not be finitely generated, as in the manuscript definition. -/
def HasSignedProjectiveBound (Z : DerivedCategory (ModuleCat.{u} A)) (d : ℤ) : Prop :=
  ∃ P : CochainComplex (ModuleCat.{u} A) ℤ,
    (∀ n, Module.Projective A (P.X n)) ∧
    (∃ lo hi : ℤ, ∀ n, n < lo ∨ hi < n → IsZero (P.X n)) ∧
    (∀ n, n < -d → IsZero (P.X n)) ∧
    Nonempty (DerivedCategory.Q.obj P ≅ Z)

/-- The infimum of actual representative bounds, not of residue cohomology. -/
def signedProjectiveDimension (Z : DerivedCategory (ModuleCat.{u} A)) :
    WithBot (WithTop ℤ) :=
  sInf ((fun d : ℤ => ((d : WithTop ℤ) : WithBot (WithTop ℤ))) ''
    {d | HasSignedProjectiveBound Z d})

theorem bound_mono {Z : DerivedCategory (ModuleCat.{u} A)} {d d' : ℤ}
    (h : HasSignedProjectiveBound Z d) (hdd' : d ≤ d') :
    HasSignedProjectiveBound Z d' := by
  obtain ⟨P, hp, hb, hl, he⟩ := h
  refine ⟨P, hp, hb, ?_, he⟩
  intro n hn
  exact hl n (lt_of_lt_of_le hn (neg_le_neg hdd'))

theorem bound_iso_iff {Z W : DerivedCategory (ModuleCat.{u} A)}
    (e : Z ≅ W) (d : ℤ) :
    HasSignedProjectiveBound Z d ↔ HasSignedProjectiveBound W d := by
  constructor
  · rintro ⟨P, hp, hb, hl, ⟨h⟩⟩
    exact ⟨P, hp, hb, hl, ⟨h ≪≫ e⟩⟩
  · rintro ⟨P, hp, hb, hl, ⟨h⟩⟩
    exact ⟨P, hp, hb, hl, ⟨h ≪≫ e.symm⟩⟩

theorem signedProjectiveDimension_iso {Z W : DerivedCategory (ModuleCat.{u} A)}
    (e : Z ≅ W) : signedProjectiveDimension Z = signedProjectiveDimension W := by
  unfold signedProjectiveDimension
  congr 1
  congr 1
  ext d
  exact bound_iso_iff e d

theorem signedProjectiveDimension_le_of_bound {Z : DerivedCategory (ModuleCat.{u} A)}
    {d : ℤ} (h : HasSignedProjectiveBound Z d) :
    signedProjectiveDimension Z ≤ ((d : WithTop ℤ) : WithBot (WithTop ℤ)) :=
  sInf_le ⟨d, h, rfl⟩

section ProjectiveCoverReduction
variable {Q E N : Type u} [AddCommGroup Q] [Module A Q]
  [AddCommGroup E] [Module A E] [AddCommGroup N] [Module A N]

/-- The quotient map from a projective term lifts surjectively to the actual
projective cover of its cokernel. This is the first step in removing a
contractible pair, using cover minimality rather than assuming a decomposition. -/
theorem cover_lift_surjective [Module.Projective A Q] [Module.Projective A E]
    (p : Q →ₗ[A] N) (hp : Function.Surjective p)
    (c : E →ₗ[A] N) (hc : Function.Surjective c)
    (hminimal : OAI.LittleFinitistic.PDCovers.RightMinimal c) :
    ∃ q : Q →ₗ[A] E, c.comp q = p ∧ Function.Surjective q := by
  obtain ⟨q, hq⟩ := Module.projective_lifting_property c p hc
  obtain ⟨t, ht⟩ := Module.projective_lifting_property p c hp
  have hcomp : c.comp (q.comp t) = c := by
    rw [← LinearMap.comp_assoc, hq, ht]
  have hs := hminimal (q.comp t) hcomp
  refine ⟨q, hq, ?_⟩
  intro x
  obtain ⟨y, hy⟩ := hs x
  exact ⟨t y, hy⟩

end ProjectiveCoverReduction

section KernelSplit
variable {Q E : Type u} [AddCommGroup Q] [Module A Q]
  [AddCommGroup E] [Module A E]

/-- Projection onto the actual kernel associated to a specified right inverse. -/
def kernelProjection (q : Q →ₗ[A] E) (s : E →ₗ[A] Q)
    (hs : q.comp s = LinearMap.id) : Q →ₗ[A] LinearMap.ker q :=
  LinearMap.codRestrict (LinearMap.ker q) (LinearMap.id - s.comp q) (by
    intro x
    change q (x - s (q x)) = 0
    rw [map_sub]
    have h := LinearMap.congr_fun hs (q x)
    simpa using sub_eq_zero.mpr h.symm)

theorem kernelProjection_subtype (q : Q →ₗ[A] E) (s : E →ₗ[A] Q)
    (hs : q.comp s = LinearMap.id) :
    (kernelProjection q s hs).comp (LinearMap.ker q).subtype = LinearMap.id := by
  ext x
  change x.val - s (q x.val) = x.val
  rw [x.property, map_zero, sub_zero]

theorem kernel_projective_of_section [Module.Projective A Q]
    (q : Q →ₗ[A] E) (s : E →ₗ[A] Q) (hs : q.comp s = LinearMap.id) :
    Module.Projective A (LinearMap.ker q) :=
  Module.Projective.of_split (LinearMap.ker q).subtype (kernelProjection q s hs)
    (kernelProjection_subtype q s hs)

end KernelSplit

section DifferentialReduction
variable {P Q E : Type u} [AddCommGroup P] [Module A P]
  [AddCommGroup Q] [Module A Q] [AddCommGroup E] [Module A E]

/-- For the actual cokernel cover of a differential, the kernel of the
surjective lift is a projective summand on which the differential splits.
These are actual linear maps, not an assumed contractible-pair certificate. -/
theorem differential_cover_split [Module.Projective A Q] [Module.Projective A E]
    (d : P →ₗ[A] Q) (c : E →ₗ[A] Q ⧸ LinearMap.range d)
    (hc : Function.Surjective c)
    (hminimal : OAI.LittleFinitistic.PDCovers.RightMinimal c) :
    ∃ q : Q →ₗ[A] E, c.comp q = (LinearMap.range d).mkQ ∧
      Function.Surjective q ∧
      ∃ s : E →ₗ[A] Q, ∃ hs : q.comp s = LinearMap.id,
        ∃ t : LinearMap.ker q →ₗ[A] P,
          d.comp t = (LinearMap.ker q).subtype ∧
          ((kernelProjection q s hs).comp d).comp t = LinearMap.id := by
  obtain ⟨q, hq, hsurj⟩ := cover_lift_surjective
    (LinearMap.range d).mkQ (LinearMap.range d).mkQ_surjective c hc hminimal
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q (LinearMap.id : E →ₗ[A] E) hsurj
  letI := kernel_projective_of_section q s hs
  have hmem (x : LinearMap.ker q) : x.val ∈ LinearMap.range d := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    have h := LinearMap.congr_fun hq x.val
    change c (q x.val) = (LinearMap.range d).mkQ x.val at h
    rw [x.property, map_zero] at h
    exact h.symm
  let j : LinearMap.ker q →ₗ[A] LinearMap.range d :=
    LinearMap.codRestrict (LinearMap.range d) (LinearMap.ker q).subtype hmem
  obtain ⟨t, ht⟩ := Module.projective_lifting_property d.rangeRestrict j
    (LinearMap.surjective_rangeRestrict d)
  have hdt : d.comp t = (LinearMap.ker q).subtype := by
    ext x
    exact congrArg Subtype.val (LinearMap.congr_fun ht x)
  refine ⟨q, hq, hsurj, s, hs, t, hdt, ?_⟩
  rw [LinearMap.comp_assoc, hdt]
  exact kernelProjection_subtype q s hs

/-- Actual contracting maps obtained from the cokernel cover. The two
adjacent components of the resulting null-homotopic endomorphism are
idempotents; no decomposition is postulated. -/
theorem differential_contraction_maps [Module.Projective A Q] [Module.Projective A E]
    (d : P →ₗ[A] Q) (c : E →ₗ[A] Q ⧸ LinearMap.range d)
    (hc : Function.Surjective c)
    (hminimal : OAI.LittleFinitistic.PDCovers.RightMinimal c) :
    ∃ h : Q →ₗ[A] P,
      h.comp (d.comp h) = h ∧
      (d.comp h).comp (d.comp h) = d.comp h ∧
      (h.comp d).comp (h.comp d) = h.comp d := by
  obtain ⟨q, hq, hsurj, s, hs, t, hdt, hpd⟩ :=
    differential_cover_split d c hc hminimal
  let p := kernelProjection q s hs
  let h := t.comp p
  have hcontract : h.comp (d.comp h) = h := by
    ext x
    change t (p (d (t (p x)))) = t (p x)
    exact congrArg t (LinearMap.congr_fun hpd (p x))
  refine ⟨h, hcontract, ?_, ?_⟩
  · ext x
    exact congrArg d (LinearMap.congr_fun hcontract x)
  · ext x
    exact LinearMap.congr_fun hcontract (d x)
/-- If the lift to the cokernel cover has no removable kernel, the actual
differential already has radical image. Thus a nonradical differential
forces a nonzero summand in the preceding contraction construction. -/
theorem differential_radical_of_injective_lift
    [Module.Finite A Q] [Module.Projective A Q]
    [Module.Finite A E] [Module.Projective A E]
    (d : P →ₗ[A] Q) (c : E →ₗ[A] Q ⧸ LinearMap.range d)
    (q : Q →ₗ[A] E) (hq : c.comp q = (LinearMap.range d).mkQ)
    (hinj : Function.Injective q) (s : E →ₗ[A] Q)
    (hs : q.comp s = LinearMap.id)
    (hr : LinearMap.ker c ≤ Ring.jacobson A • (⊤ : Submodule A E)) :
    LinearMap.range d ≤ Ring.jacobson A • (⊤ : Submodule A Q) := by
  rintro x ⟨y, rfl⟩
  have hker : q (d y) ∈ LinearMap.ker c := by
    change c (q (d y)) = 0
    have h := LinearMap.congr_fun hq (d y)
    change c (q (d y)) = (LinearMap.range d).mkQ (d y) at h
    rw [h]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩
  have hrad : q (d y) ∈ Module.jacobson A E := by
    rw [OAI.LittleFinitistic.PDRadical.jacobson_eq_smul E]
    exact hr hker
  have hsrad := Module.le_comap_jacobson s hrad
  have hsd : s (q (d y)) = d y := by
    apply hinj
    exact LinearMap.congr_fun hs (q (d y))
  change s (q (d y)) ∈ Module.jacobson A Q at hsrad
  rw [hsd, OAI.LittleFinitistic.PDRadical.jacobson_eq_smul Q] at hsrad
  exact hsrad
end DifferentialReduction
section ContractibleSummand
/-- A homotopy supported at precisely degree n+1 to n, with all
transports explicit. -/
def singleHomotopy (P : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (h : P.X (n+1) ⟶ P.X n) (i j : ℤ) : P.X i ⟶ P.X j :=
  if hi : i = n+1 then
    if hj : j = n then
      eqToHom (congrArg P.X hi) ≫ h ≫ eqToHom (congrArg P.X hj).symm
    else 0
  else 0

def singleBoundary (P : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (h : P.X (n+1) ⟶ P.X n) : P ⟶ P :=
  Homotopy.nullHomotopicMap (singleHomotopy P n h)

def singleBoundary_null (P : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (h : P.X (n+1) ⟶ P.X n) : Homotopy (singleBoundary P n h) 0 := by
  apply Homotopy.nullHomotopy
  intro i j hrel
  unfold singleHomotopy
  split_ifs with hi hj
  · subst i
    subst j
    exact False.elim (hrel (by change n + 1 = n + 1; rfl))
  · rfl
  · rfl

theorem singleBoundary_f_left (P : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (h : P.X (n+1) ⟶ P.X n) :
    (singleBoundary P n h).f n = P.d n (n+1) ≫ h := by
  unfold singleBoundary
  rw [Homotopy.nullHomotopicMap_f (k₂ := n-1) (k₀ := n+1)
    (by change n-1+1 = n; omega) (by change n+1 = n+1; rfl)]
  simp [singleHomotopy]

theorem singleBoundary_f_right (P : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (h : P.X (n+1) ⟶ P.X n) :
    (singleBoundary P n h).f (n+1) = h ≫ P.d n (n+1) := by
  unfold singleBoundary
  rw [Homotopy.nullHomotopicMap_f (k₂ := n) (k₀ := n+1+1)
    (by change n+1 = n+1; rfl) (by change n+1+1 = n+1+1; rfl)]
  simp [singleHomotopy]

theorem singleBoundary_f_other (P : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (h : P.X (n+1) ⟶ P.X n) (i : ℤ) (hi : i ≠ n) (hi' : i ≠ n+1) :
    (singleBoundary P n h).f i = 0 := by
  unfold singleBoundary
  rw [Homotopy.nullHomotopicMap_f (k₂ := i-1) (k₀ := i+1)
    (by change i-1+1 = i; omega) (by change i+1 = i+1; rfl)]
  have ht : i+1 ≠ n+1 := by omega
  simp [singleHomotopy, hi, hi', ht]

/-- The contraction built at one differential gives an actual
null-homotopic idempotent of the whole complex. -/
theorem singleBoundary_idempotent (P : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (h : P.X (n+1) ⟶ P.X n)
    (hcontract : h ≫ P.d n (n+1) ≫ h = h) :
    singleBoundary P n h ≫ singleBoundary P n h = singleBoundary P n h := by
  apply HomologicalComplex.hom_ext
  intro i
  change (singleBoundary P n h).f i ≫ (singleBoundary P n h).f i =
    (singleBoundary P n h).f i
  by_cases hi : i = n
  · subst i
    rw [singleBoundary_f_left]
    simpa only [Category.assoc] using congrArg (fun f => P.d n (n+1) ≫ f) hcontract
  · by_cases hi' : i = n+1
    · subst i
      rw [singleBoundary_f_right]
      simpa only [Category.assoc] using congrArg (fun f => f ≫ P.d n (n+1)) hcontract
    · rw [singleBoundary_f_other P n h i hi hi', comp_zero]

/-- A null-homotopic idempotent is genuinely removed by splitting its
complement in the category of complexes. This preserves the derived object;
the idempotent used for minimalization is constructed from the differential
and its cokernel cover by the preceding lemmas. -/
theorem remove_nullhomotopic_idempotent
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (p : P ⟶ P)
    (hp : p ≫ p = p) (hnull : Homotopy p 0) :
    ∃ Q : CochainComplex (ModuleCat.{u} A) ℤ,
      ∃ i : Q ⟶ P, ∃ e : P ⟶ Q,
        i ≫ e = 𝟙 Q ∧ e ≫ i = 𝟙 P - p ∧ Nonempty (HomotopyEquiv P Q) := by
  obtain ⟨Q, i, e, hie, hei⟩ :=
    IsIdempotentComplete.idempotents_split P (𝟙 P - p)
      (CategoryTheory.Idempotents.idem_of_id_sub_idem p hp)
  have hn : Homotopy (-p) 0 := by
    simpa only [zero_sub] using Homotopy.equivSubZero hnull.symm
  have hdifference : (𝟙 P - p) - 𝟙 P = -p := by abel
  have hcomplement : Homotopy (𝟙 P - p) (𝟙 P) :=
    Homotopy.equivSubZero.symm (by rw [hdifference]; exact hn)
  refine ⟨Q, i, e, hie, hei, ⟨?_⟩⟩
  exact {
    hom := e
    inv := i
    homotopyHomInvId := (Homotopy.ofEq hei).trans hcomplement
    homotopyInvHomId := Homotopy.ofEq hie }

/-- Termwise finiteness, projectivity, and a fixed support interval all
survive an actual split in the category of complexes. -/
theorem term_properties_of_split
    (P Q : CochainComplex (ModuleCat.{u} A) ℤ) (i : Q ⟶ P) (e : P ⟶ Q)
    (hsplit : i ≫ e = 𝟙 Q)
    (hP : ∀ n, Module.Finite A (P.X n) ∧ Module.Projective A (P.X n))
    (lo hi : ℤ) (hbound : ∀ n, n < lo ∨ hi < n → IsZero (P.X n)) :
    (∀ n, Module.Finite A (Q.X n) ∧ Module.Projective A (Q.X n)) ∧
      (∀ n, n < lo ∨ hi < n → IsZero (Q.X n)) := by
  have hs (n : ℤ) : (e.f n).hom.comp (i.f n).hom = LinearMap.id := by
    ext x
    exact congrArg (fun f => (f.f n).hom x) hsplit
  constructor
  · intro n
    letI := (hP n).1
    letI := (hP n).2
    have hsurj : Function.Surjective (e.f n).hom := by
      intro x
      exact ⟨(i.f n).hom x, LinearMap.congr_fun (hs n) x⟩
    exact ⟨Module.Finite.of_surjective (e.f n).hom hsurj,
      Module.Projective.of_split (i.f n).hom (e.f n).hom (hs n)⟩
  · intro n hn
    apply (IsZero.iff_id_eq_zero _).mpr
    have hh : i.f n ≫ e.f n = 𝟙 (Q.X n) :=
      congrArg (fun f => f.f n) hsplit
    rw [← hh, (hbound n hn).eq_of_tgt (i.f n) 0, zero_comp]
/-- Two actual splittings of the same projector identify their images. -/
def splittingIso {V : Type*} [Category V] {X Y Z : V}
    (i : Y ⟶ X) (e : X ⟶ Y) (s : Z ⟶ X) (q : X ⟶ Z)
    (hie : i ≫ e = 𝟙 Y) (hsq : s ≫ q = 𝟙 Z) (hprojector : e ≫ i = q ≫ s) : Y ≅ Z where
  hom := i ≫ q
  inv := s ≫ e
  hom_inv_id := by
    calc
      (i ≫ q) ≫ (s ≫ e) = i ≫ (q ≫ s) ≫ e := by simp only [Category.assoc]
      _ = i ≫ (e ≫ i) ≫ e := by rw [← hprojector]
      _ = (i ≫ e) ≫ (i ≫ e) := by simp only [Category.assoc]
      _ = 𝟙 Y := by rw [hie, Category.id_comp]
  inv_hom_id := by
    calc
      (s ≫ e) ≫ (i ≫ q) = s ≫ (e ≫ i) ≫ q := by simp only [Category.assoc]
      _ = s ≫ (q ≫ s) ≫ q := by rw [hprojector]
      _ = (s ≫ q) ≫ (s ≫ q) := by simp only [Category.assoc]
      _ = 𝟙 Z := by rw [hsq, Category.id_comp]
/-- One actual differential can be replaced by its cokernel cover without
changing the homotopy type. The next term of the new complex is identified
with the cover itself, so its dimension decreases whenever the lift has a
nonzero kernel. -/
theorem reduce_differential_to_cover
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (E : ModuleCat.{u} A) [Module.Projective A (P.X (n+1))]
    [Module.Projective A E]
    (c : E →ₗ[A] (P.X (n+1)) ⧸ LinearMap.range (P.d n (n+1)).hom)
    (hc : Function.Surjective c)
    (hminimal : OAI.LittleFinitistic.PDCovers.RightMinimal c) :
    ∃ Q : CochainComplex (ModuleCat.{u} A) ℤ,
      Nonempty (HomotopyEquiv P Q) ∧ Nonempty (Q.X (n+1) ≅ E) ∧
      ∃ i : Q ⟶ P, ∃ e : P ⟶ Q, i ≫ e = 𝟙 Q := by
  let d := (P.d n (n+1)).hom
  obtain ⟨q, hq, hsurj, s, hs, t, hdt, hpd⟩ :=
    differential_cover_split d c hc hminimal
  let projection := kernelProjection q s hs
  let hlin := t.comp projection
  let h : P.X (n+1) ⟶ P.X n := ModuleCat.ofHom hlin
  have hcontract : h ≫ P.d n (n+1) ≫ h = h := by
    ext x
    exact congrArg t (LinearMap.congr_fun hpd (projection x))
  obtain ⟨Q, i, e, hie, hei, hequiv⟩ :=
    remove_nullhomotopic_idempotent P (singleBoundary P n h)
      (singleBoundary_idempotent P n h hcontract) (singleBoundary_null P n h)
  have hcomponent : e.f (n+1) ≫ i.f (n+1) =
      ModuleCat.ofHom q ≫ ModuleCat.ofHom s := by
    have hh := congrArg (fun f => f.f (n+1)) hei
    have hb := singleBoundary_f_right P n h
    ext x
    change (i.f (n+1)).hom ((e.f (n+1)).hom x) = s (q x)
    have hx := congrArg (fun f => f.hom x) hh
    change (i.f (n+1)).hom ((e.f (n+1)).hom x) =
      x - ((singleBoundary P n h).f (n+1)).hom x at hx
    rw [hb] at hx
    rw [hx]
    change x - d (t (projection x)) = s (q x)
    have ht := LinearMap.congr_fun hdt (projection x)
    change d (t (projection x)) = (projection x).val at ht
    rw [ht]
    change x - (x - s (q x)) = s (q x)
    abel
  have hs' : ModuleCat.ofHom s ≫ ModuleCat.ofHom q = 𝟙 E := by
    ext x
    exact LinearMap.congr_fun hs x
  have hie' : i.f (n+1) ≫ e.f (n+1) = 𝟙 (Q.X (n+1)) :=
    congrArg (fun f => f.f (n+1)) hie
  exact ⟨Q, hequiv, ⟨splittingIso _ _ _ _ hie' hs' hcomponent⟩, i, e, hie⟩
end ContractibleSummand
section DimensionDecrease
/-- The quantitative decrease needed when an actual nonzero cokernel-cover
kernel is removed. It applies to the surjective lift used above. -/
theorem finrank_lt_of_surjective_noninjective
    {k V W : Type u} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V]
    (f : V →ₗ[k] W) (hsurj : Function.Surjective f)
    (hnot : ¬ Function.Injective f) : Module.finrank k W < Module.finrank k V := by
  letI : FiniteDimensional k W := Module.Finite.of_surjective f hsurj
  have hle := LinearMap.finrank_le_finrank_of_surjective hsurj
  have hne : Module.finrank k W ≠ Module.finrank k V := by
    intro heq
    exact hnot ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq.symm).mpr hsurj)
  exact lt_of_le_of_ne hle hne
end DimensionDecrease
section MinimalDimension
variable (k : Type u) [Field k] [Algebra k A]

/-- The actual finite sum of the vector-space dimensions of terms in a
specified integral support interval. -/
def totalTermDimension (P : CochainComplex (ModuleCat.{u} A) ℤ) (lo hi : ℤ) : ℕ :=
  ∑ n ∈ Finset.Icc lo hi, Module.finrank k (P.X n)

/-- The representative class over which the finite dimensional cancellation
argument minimizes; projective dimension itself still permits arbitrary
projective terms. -/
def FiniteRepresentativeIn (P Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (lo hi : ℤ) : Prop :=
  Nonempty (HomotopyEquiv P Q) ∧
  (∀ n, FiniteDimensional k (Q.X n) ∧ Module.Projective A (Q.X n)) ∧
  (∀ n, n < lo ∨ hi < n → IsZero (Q.X n))

/-- Existence of a dimension-minimal actual representative follows from
well-ordering of natural dimensions, with the original complex as witness. -/
theorem dimension_minimal_representative
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (lo hi : ℤ)
    (hP : ∀ n, FiniteDimensional k (P.X n) ∧ Module.Projective A (P.X n))
    (hbound : ∀ n, n < lo ∨ hi < n → IsZero (P.X n)) :
    ∃ Q : CochainComplex (ModuleCat.{u} A) ℤ,
      FiniteRepresentativeIn k P Q lo hi ∧
      ∀ R : CochainComplex (ModuleCat.{u} A) ℤ,
        FiniteRepresentativeIn k P R lo hi →
          totalTermDimension k Q lo hi ≤ totalTermDimension k R lo hi := by
  classical
  have hex : ∃ d : ℕ, ∃ Q : CochainComplex (ModuleCat.{u} A) ℤ,
      FiniteRepresentativeIn k P Q lo hi ∧ totalTermDimension k Q lo hi = d :=
    ⟨totalTermDimension k P lo hi, P,
      ⟨⟨HomotopyEquiv.refl P⟩, hP, hbound⟩, rfl⟩
  obtain ⟨Q, hQ, hdim⟩ := Nat.find_spec hex
  refine ⟨Q, hQ, ?_⟩
  intro R hR
  rw [hdim]
  exact Nat.find_min' hex ⟨R, hR, rfl⟩

theorem term_finrank_le_of_split
    (P Q : CochainComplex (ModuleCat.{u} A) ℤ) (i : Q ⟶ P) (e : P ⟶ Q)
    (hsplit : i ≫ e = 𝟙 Q) (n : ℤ) [FiniteDimensional k (P.X n)] :
    Module.finrank k (Q.X n) ≤ Module.finrank k (P.X n) := by
  let f := (i.f n).hom.restrictScalars k
  have hf : Function.Injective f := by
    intro x y hxy
    have hx : (e.f n).hom ((i.f n).hom x) = x :=
      congrArg (fun z => (z.f n).hom x) hsplit
    have hy : (e.f n).hom ((i.f n).hom y) = y :=
      congrArg (fun z => (z.f n).hom y) hsplit
    exact hx.symm.trans ((congrArg (e.f n).hom hxy).trans hy)
  exact LinearMap.finrank_le_finrank_of_injective hf

theorem totalTermDimension_le_of_split
    (P Q : CochainComplex (ModuleCat.{u} A) ℤ) (i : Q ⟶ P) (e : P ⟶ Q)
    (hsplit : i ≫ e = 𝟙 Q) (lo hi : ℤ)
    (hfinite : ∀ n, FiniteDimensional k (P.X n)) :
    totalTermDimension k Q lo hi ≤ totalTermDimension k P lo hi := by
  unfold totalTermDimension
  apply Finset.sum_le_sum
  intro n hn
  letI := hfinite n
  exact term_finrank_le_of_split k P Q i e hsplit n

/-- A strict decrease at one actual term, together with the retraction,
strictly decreases the finite total dimension used by the minimizer. -/
theorem totalTermDimension_lt_of_split
    (P Q : CochainComplex (ModuleCat.{u} A) ℤ) (i : Q ⟶ P) (e : P ⟶ Q)
    (hsplit : i ≫ e = 𝟙 Q) (lo hi : ℤ)
    (hfinite : ∀ n, FiniteDimensional k (P.X n)) (j : ℤ)
    (hj : j ∈ Finset.Icc lo hi)
    (hstrict : Module.finrank k (Q.X j) < Module.finrank k (P.X j)) :
    totalTermDimension k Q lo hi < totalTermDimension k P lo hi := by
  unfold totalTermDimension
  apply Finset.sum_lt_sum
  · intro n hn
    letI := hfinite n
    exact term_finrank_le_of_split k P Q i e hsplit n
  · exact ⟨j, hj, hstrict⟩
/-- Over a finite dimensional algebra, the dimension-minimal bounded
finite projective representative has genuinely radical differentials. -/
theorem dimension_minimal_differential_radical [FiniteDimensional k A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (lo hi : ℤ)
    (hP : ∀ n, FiniteDimensional k (P.X n) ∧ Module.Projective A (P.X n))
    (hbound : ∀ n, n < lo ∨ hi < n → IsZero (P.X n))
    (hmin : ∀ R : CochainComplex (ModuleCat.{u} A) ℤ,
      FiniteRepresentativeIn k P R lo hi →
        totalTermDimension k P lo hi ≤ totalTermDimension k R lo hi)
    (n : ℤ) :
    LinearMap.range (P.d n (n+1)).hom ≤
      Ring.jacobson A • (⊤ : Submodule A (P.X (n+1))) := by
  classical
  by_contra hbad
  letI := (hP (n+1)).1
  letI := (hP (n+1)).2
  letI : Module.Finite A (P.X (n+1)) :=
    Module.Finite.of_restrictScalars_finite k A _
  let d := (P.d n (n+1)).hom
  let M := OAI.LittleFinitistic.PDMinimal.FiniteModule.of (k := k) (A := A)
    ((P.X (n+1)) ⧸ LinearMap.range d)
  let cover := OAI.LittleFinitistic.PDMinimal.cover M
  let E := cover.source.cat
  letI : Module.Projective A E := cover.projective
  letI : Module.Finite A E := inferInstanceAs (Module.Finite A cover.source)
  letI : FiniteDimensional k E := Module.Finite.trans A E
  let c : E →ₗ[A] (P.X (n+1)) ⧸ LinearMap.range d := cover.π
  obtain ⟨q, hq, hsurj⟩ := cover_lift_surjective
    (LinearMap.range d).mkQ (LinearMap.range d).mkQ_surjective
    c cover.surjective cover.minimal
  have hnot : ¬ Function.Injective q := by
    intro hqi
    obtain ⟨s, hs⟩ := Module.projective_lifting_property q (LinearMap.id : E →ₗ[A] E) hsurj
    exact hbad (differential_radical_of_injective_lift d c q hq hqi s hs cover.radical)
  have hdrop : Module.finrank k E < Module.finrank k (P.X (n+1)) :=
    finrank_lt_of_surjective_noninjective (q.restrictScalars k) hsurj hnot
  obtain ⟨Q, hequiv, ⟨hterm⟩, i, e, hie⟩ :=
    reduce_differential_to_cover P n E c cover.surjective cover.minimal
  have hP' : ∀ j, Module.Finite A (P.X j) ∧ Module.Projective A (P.X j) := by
    intro j
    letI := (hP j).1
    exact ⟨Module.Finite.of_restrictScalars_finite k A _, (hP j).2⟩
  obtain ⟨hQ, hQbound⟩ := term_properties_of_split P Q i e hie hP' lo hi hbound
  have hQfinite : ∀ j, FiniteDimensional k (Q.X j) := by
    intro j
    letI := (hQ j).1
    exact Module.Finite.trans A (Q.X j)
  have hmember : n+1 ∈ Finset.Icc lo hi := by
    apply Finset.mem_Icc.mpr
    by_contra hn
    have hz := hbound (n+1) (by omega)
    have hd : P.d n (n+1) = 0 := hz.eq_of_tgt _ _
    apply hbad
    simp [hd]
  have hstrict : Module.finrank k (Q.X (n+1)) < Module.finrank k (P.X (n+1)) := by
    have heq := (hterm.toLinearEquiv.restrictScalars k).finrank_eq
    exact heq.symm ▸ hdrop
  have htotal := totalTermDimension_lt_of_split k P Q i e hie lo hi
    (fun j => (hP j).1) (n+1) hmember hstrict
  have hle := hmin Q ⟨hequiv, fun j => ⟨hQfinite j, (hQ j).2⟩, hQbound⟩
  exact (not_lt_of_ge hle) htotal

/-- The manuscript's bounded finite-projective minimalization step: actual
radical differentials are obtained, rather than assumed as input. -/
theorem exists_minimal_bounded_representative [FiniteDimensional k A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (lo hi : ℤ)
    (hP : ∀ n, FiniteDimensional k (P.X n) ∧ Module.Projective A (P.X n))
    (hbound : ∀ n, n < lo ∨ hi < n → IsZero (P.X n)) :
    ∃ Q : CochainComplex (ModuleCat.{u} A) ℤ,
      FiniteRepresentativeIn k P Q lo hi ∧
      ∀ n, LinearMap.range (Q.d n (n+1)).hom ≤
        Ring.jacobson A • (⊤ : Submodule A (Q.X (n+1))) := by
  obtain ⟨Q, hQ, hmin⟩ := dimension_minimal_representative k P lo hi hP hbound
  refine ⟨Q, hQ, ?_⟩
  intro n
  apply dimension_minimal_differential_radical k Q lo hi hQ.2.1 hQ.2.2
  intro R hR
  obtain ⟨ePQ⟩ := hQ.1
  obtain ⟨eQR⟩ := hR.1
  exact hmin R ⟨⟨ePQ.trans eQR⟩, hR.2⟩
end MinimalDimension
section ResidueDetection
variable (k : Type u) [Field k] [Algebra k A]
open OAI.LittleFinitistic

/-- The ordinary residue tensor of an actual projective representative.
Its identification with the derived tensor is a separate comparison step. -/
def residueComplex (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex (ModuleCat.{u} k) ℤ :=
  ((PDTensor.tensorFunctor k A (PDTensor.Residue (A := A))).mapHomologicalComplex _).obj P

/-- All differentials of the actual residue tensor vanish for a radical
complex, including the non-adjacent differentials. -/
theorem residueComplex_d_zero (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hminimal : ∀ n, LinearMap.range (P.d n (n+1)).hom ≤
      Ring.jacobson A • (⊤ : Submodule A (P.X (n+1)))) (i j : ℤ) :
    (residueComplex k P).d i j = 0 := by
  change (PDTensor.tensorFunctor k A (PDTensor.Residue (A := A))).map (P.d i j) = 0
  by_cases h : i+1 = j
  · subst j
    apply ModuleCat.hom_ext
    exact @PDTensor.mapRight_radical_zero k A _ _ _ (PDTensor.Residue (A := A)) _ _ _
      (PDTensor.ScalarModule k A (P.X i)) (PDTensor.ScalarModule k A (P.X (i+1)))
      _ _ _ (PDTensor.scalarModuleTower k A (P.X i))
      _ _ _ (PDTensor.scalarModuleTower k A (P.X (i+1)))
      PDTensor.residue_annihilated (P.d i (i+1)).hom (hminimal i)
  · rw [P.shape i j (by change ¬ i+1=j; exact h)]
    exact Functor.map_zero _ _ _

/-- Homology of the actual residue tensor is its term, because its actual
differentials have been proved zero. -/
def residueHomologyIsoTerm (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hminimal : ∀ n, LinearMap.range (P.d n (n+1)).hom ≤
      Ring.jacobson A • (⊤ : Submodule A (P.X (n+1)))) (n : ℤ) :
    (residueComplex k P).homology n ≅
      (PDTensor.tensorFunctor k A (PDTensor.Residue (A := A))).obj (P.X n) :=
  (ShortComplex.LeftHomologyData.ofZeros ((residueComplex k P).sc n)
    (residueComplex_d_zero k P hminimal _ _) (residueComplex_d_zero k P hminimal _ _)).homologyIso

/-- The finite-generation Nakayama detection applies to each actual
minimal term, with no residue detection postulate. -/
theorem residueHomology_isZero_iff (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hminimal : ∀ n, LinearMap.range (P.d n (n+1)).hom ≤
      Ring.jacobson A • (⊤ : Submodule A (P.X (n+1))))
    (n : ℤ) [Module.Finite A (P.X n)] :
    IsZero ((residueComplex k P).homology n) ↔ IsZero (P.X n) := by
  rw [(residueHomologyIsoTerm k P hminimal n).isZero_iff]
  change IsZero (ModuleCat.of k (BalancedTensor.Tensor k A (PDTensor.Residue (A := A))
    (PDTensor.ScalarModule k A (P.X n)))) ↔ IsZero (P.X n)
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  letI : Module.Finite A (PDTensor.ScalarModule k A (P.X n)) :=
    show Module.Finite A (P.X n) from inferInstance
  exact PDTensor.residueTensor_subsingleton_iff (k := k)
    (PDTensor.ScalarModule k A (P.X n))

end ResidueDetection
section ArbitraryProjectiveComparison
/-- Bounded projective representatives are K-projective even when their
terms are not finitely generated. This protects the manuscript's full
representative quantifier in the lower-bound comparison. -/
theorem bounded_projective_isKProjective
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hi : ℤ)
    (hprojective : ∀ n, Module.Projective A (P.X n))
    (hbound : ∀ n, hi < n → IsZero (P.X n)) : P.IsKProjective := by
  letI (n : ℤ) : Projective (P.X n) := by
    letI := hprojective n
    exact ModuleCat.projective_of_categoryTheory_projective _
  letI : CochainComplex.IsStrictlyLE P hi := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact hbound
  exact CochainComplex.isKProjective_of_projective P hi

/-- An actual derived isomorphism between arbitrary bounded projective
representatives lifts to an actual isomorphism in the homotopy category. -/
def projectiveHomotopyIso
    (P Q : CochainComplex (ModuleCat.{u} A) ℤ)
    [P.IsKProjective] [Q.IsKProjective]
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) :
    (HomotopyCategory.quotient _ _).obj P ≅ (HomotopyCategory.quotient _ _).obj Q := by
  let e' := (DerivedCategory.quotientCompQhIso _).app P ≪≫ e ≪≫
    ((DerivedCategory.quotientCompQhIso _).app Q).symm
  let hgExists := (CochainComplex.IsKProjective.Qh_map_bijective P
    ((HomotopyCategory.quotient _ _).obj Q)).surjective e'.hom
  let g := Classical.choose hgExists
  have hg := Classical.choose_spec hgExists
  let hhExists := (CochainComplex.IsKProjective.Qh_map_bijective Q
    ((HomotopyCategory.quotient _ _).obj P)).surjective e'.inv
  let h := Classical.choose hhExists
  have hh := Classical.choose_spec hhExists
  exact {
    hom := g
    inv := h
    hom_inv_id := by
      apply (CochainComplex.IsKProjective.Qh_map_bijective P
        ((HomotopyCategory.quotient _ _).obj P)).injective
      simp only [g, h, Functor.map_comp, hg, hh, Iso.hom_inv_id]
      exact (DerivedCategory.Qh.map_id _).symm
    inv_hom_id := by
      apply (CochainComplex.IsKProjective.Qh_map_bijective Q
        ((HomotopyCategory.quotient _ _).obj Q)).injective
      simp only [g, h, Functor.map_comp, hg, hh, Iso.inv_hom_id]
      exact (DerivedCategory.Qh.map_id _).symm }

end ArbitraryProjectiveComparison
section RepresentativeDetection
variable (k : Type u) [Field k] [Algebra k A]

/-- Residue homology of arbitrary bounded projective representatives is
invariant under their actual derived isomorphism, via K-projective full
faithfulness and the induced tensor functor on the homotopy category. -/
def residueHomologyIsoOfDerivedIso
    (P Q : CochainComplex (ModuleCat.{u} A) ℤ)
    [P.IsKProjective] [Q.IsKProjective]
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (n : ℤ) :
    (residueComplex k P).homology n ≅ (residueComplex k Q).homology n := by
  let F := OAI.LittleFinitistic.PDTensor.tensorFunctor k A
    (OAI.LittleFinitistic.PDTensor.Residue (A := A))
  let eH := projectiveHomotopyIso P Q e
  let eT := ((F.mapHomotopyCategoryFactors (.up ℤ)).app P).symm ≪≫
    (F.mapHomotopyCategory (.up ℤ)).mapIso eH ≪≫
    (F.mapHomotopyCategoryFactors (.up ℤ)).app Q
  exact ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} k) (.up ℤ) n).app
      (residueComplex k P)).symm ≪≫
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} k) (.up ℤ) n).mapIso eT ≪≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} k) (.up ℤ) n).app
      (residueComplex k Q)

theorem residueHomology_isZero_of_term_zero
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) (hz : IsZero (P.X n)) :
    IsZero ((residueComplex k P).homology n) := by
  let F := OAI.LittleFinitistic.PDTensor.tensorFunctor k A
    (OAI.LittleFinitistic.PDTensor.Residue (A := A))
  have hterm : IsZero ((residueComplex k P).X n) := F.map_isZero hz
  have hcycles : IsZero ((residueComplex k P).cycles n) :=
    IsZero.of_mono ((residueComplex k P).iCycles n) hterm
  exact IsZero.of_epi ((residueComplex k P).homologyπ n) hcycles

include k in
/-- A finite minimal term is forced to vanish whenever the same degree
of any derived-isomorphic projective representative vanishes. The comparison
representative is allowed infinite projective terms. -/
theorem minimal_term_isZero_of_representative_term_isZero
    (P Q : CochainComplex (ModuleCat.{u} A) ℤ)
    [P.IsKProjective] [Q.IsKProjective]
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q)
    (hminimal : ∀ j, LinearMap.range (P.d j (j+1)).hom ≤
      Ring.jacobson A • (⊤ : Submodule A (P.X (j+1))))
    (n : ℤ) [Module.Finite A (P.X n)] (hz : IsZero (Q.X n)) : IsZero (P.X n) := by
  apply (residueHomology_isZero_iff k P hminimal n).mp
  exact (residueHomologyIsoOfDerivedIso k P Q e n).isZero_iff.mpr
    (residueHomology_isZero_of_term_zero k Q n hz)

include k in
/-- The actual representative definition of signed projective dimension
is detected by the lower support of an actual finite minimal representative.
No finite-generation condition is imposed on comparison representatives. -/
theorem bound_iff_minimal_terms_zero
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (lo hi : ℤ)
    (hP : ∀ n, Module.Finite A (P.X n) ∧ Module.Projective A (P.X n))
    (hbound : ∀ n, n < lo ∨ hi < n → IsZero (P.X n))
    (hminimal : ∀ n, LinearMap.range (P.d n (n+1)).hom ≤
      Ring.jacobson A • (⊤ : Submodule A (P.X (n+1))))
    (Z : DerivedCategory (ModuleCat.{u} A)) (eP : DerivedCategory.Q.obj P ≅ Z) (d : ℤ) :
    HasSignedProjectiveBound Z d ↔ ∀ n, n < -d → IsZero (P.X n) := by
  letI := bounded_projective_isKProjective P hi (fun n => (hP n).2)
    (fun n hn => hbound n (Or.inr hn))
  constructor
  · rintro ⟨Q, hQ, ⟨qlo, qhi, hQbound⟩, hQlower, ⟨eQ⟩⟩ n hn
    letI := bounded_projective_isKProjective Q qhi hQ
      (fun n hn => hQbound n (Or.inr hn))
    letI := (hP n).1
    exact minimal_term_isZero_of_representative_term_isZero k P Q
      (eP ≪≫ eQ.symm) hminimal n (hQlower n hn)
  · intro h
    exact ⟨P, fun n => (hP n).2, ⟨lo, hi, hbound⟩, h, ⟨eP⟩⟩

/-- The residue vanishing criterion is proved from actual representatives
and minimalization, rather than used to define projective dimension. -/
theorem bound_iff_residueHomology_zero
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (lo hi : ℤ)
    (hP : ∀ n, Module.Finite A (P.X n) ∧ Module.Projective A (P.X n))
    (hbound : ∀ n, n < lo ∨ hi < n → IsZero (P.X n))
    (hminimal : ∀ n, LinearMap.range (P.d n (n+1)).hom ≤
      Ring.jacobson A • (⊤ : Submodule A (P.X (n+1))))
    (Z : DerivedCategory (ModuleCat.{u} A)) (eP : DerivedCategory.Q.obj P ≅ Z) (d : ℤ) :
    HasSignedProjectiveBound Z d ↔
      ∀ n, n < -d → IsZero ((residueComplex k P).homology n) := by
  rw [bound_iff_minimal_terms_zero k P lo hi hP hbound hminimal Z eP d]
  constructor
  · intro h n hn
    letI := (hP n).1
    exact (residueHomology_isZero_iff k P hminimal n).mpr (h n hn)
  · intro h n hn
    letI := (hP n).1
    exact (residueHomology_isZero_iff k P hminimal n).mp (h n hn)

end RepresentativeDetection
section SignedExtrema

theorem zero_has_every_bound (d : ℤ) :
    HasSignedProjectiveBound (0 : DerivedCategory (ModuleCat.{u} A)) d := by
  refine ⟨0, ?_, ⟨0, 0, ?_⟩, ?_, ⟨DerivedCategory.Q.mapZeroObject⟩⟩
  · intro n
    have hz : IsZero ((0 : CochainComplex (ModuleCat.{u} A) ℤ).X n) :=
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n).map_isZero (isZero_zero _)
    letI := hz.projective
    infer_instance
  · intro n hn
    exact (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n).map_isZero (isZero_zero _)
  · intro n hn
    exact (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n).map_isZero (isZero_zero _)

/-- The manuscript's zero convention follows from actual zero
representatives for every integral bound. -/
theorem signedProjectiveDimension_zero :
    signedProjectiveDimension (0 : DerivedCategory (ModuleCat.{u} A)) = ⊥ := by
  apply WithBot.eq_bot_iff_forall_le.mpr
  intro b
  induction b using WithTop.recTopCoe with
  | top => exact le_top
  | coe d => exact signedProjectiveDimension_le_of_bound (zero_has_every_bound d)

variable (k : Type u) [Field k] [Algebra k A]

include k in
/-- The first nonzero term of an actual finite minimal representative
gives the least signed representative bound, including negative values. -/
theorem signedProjectiveDimension_eq_of_minimal_edge
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (lo hi : ℤ)
    (hP : ∀ n, Module.Finite A (P.X n) ∧ Module.Projective A (P.X n))
    (hbound : ∀ n, n < lo ∨ hi < n → IsZero (P.X n))
    (hminimal : ∀ n, LinearMap.range (P.d n (n+1)).hom ≤
      Ring.jacobson A • (⊤ : Submodule A (P.X (n+1))))
    (Z : DerivedCategory (ModuleCat.{u} A)) (eP : DerivedCategory.Q.obj P ≅ Z)
    (d : ℤ) (hlower : ∀ n, n < -d → IsZero (P.X n))
    (hedge : ¬ IsZero (P.X (-d))) :
    signedProjectiveDimension Z = ((d : WithTop ℤ) : WithBot (WithTop ℤ)) := by
  have hcriterion (c : ℤ) : HasSignedProjectiveBound Z c ↔ d ≤ c := by
    rw [bound_iff_minimal_terms_zero k P lo hi hP hbound hminimal Z eP c]
    constructor
    · intro hc
      by_contra hdc
      have hcd : c < d := lt_of_not_ge hdc
      exact hedge (hc (-d) (neg_lt_neg hcd))
    · intro hdc n hn
      exact hlower n (lt_of_lt_of_le hn (neg_le_neg hdc))
  apply le_antisymm
  · exact signedProjectiveDimension_le_of_bound ((hcriterion d).mpr le_rfl)
  · unfold signedProjectiveDimension
    apply le_sInf
    rintro x ⟨c, hc, rfl⟩
    exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ((hcriterion c).mp hc))

/-- A positive cochain shift changes the representative bound by +s,
in the precise convention of the manuscript: (P[s])^n=P^(n+s). -/
theorem bound_shift {Z : DerivedCategory (ModuleCat.{u} A)} {d : ℤ}
    (h : HasSignedProjectiveBound Z d) (s : ℤ) :
    HasSignedProjectiveBound (Z⟦s⟧) (d+s) := by
  obtain ⟨P, hp, ⟨lo, hi, hb⟩, hl, ⟨eP⟩⟩ := h
  refine ⟨P⟦s⟧, ?_, ⟨lo-s, hi-s, ?_⟩, ?_, ?_⟩
  · intro n
    exact hp (n+s)
  · intro n hn
    exact hb (n+s) (by omega)
  · intro n hn
    exact hl (n+s) (by omega)
  · exact ⟨(DerivedCategory.Q.commShiftIso s).app P ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) s).mapIso eP⟩
/-- The converse uses the actual inverse shift, so the sign is a proved
representative equivalence rather than a numerical convention. -/
theorem bound_shift_iff (Z : DerivedCategory (ModuleCat.{u} A)) (d s : ℤ) :
    HasSignedProjectiveBound (Z⟦s⟧) (d+s) ↔ HasSignedProjectiveBound Z d := by
  constructor
  · intro h
    have hback : HasSignedProjectiveBound ((Z⟦s⟧)⟦-s⟧) d := by
      simpa only [add_neg_cancel_right] using bound_shift h (-s)
    exact (bound_iso_iff
      ((shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{u} A)) s (-s)
        (add_neg_cancel s)).app Z) d).mp hback
  · intro h
    exact bound_shift h s

/-- Integer translation extended to both infinities. It fixes bottom and top. -/
def signedTranslation (s : ℤ) :
    WithBot (WithTop ℤ) ≃o WithBot (WithTop ℤ) :=
  (OrderIso.addRight s).withTopCongr.withBotCongr

@[simp] theorem signedTranslation_coe (s d : ℤ) :
    signedTranslation s ((d : WithTop ℤ) : WithBot (WithTop ℤ)) =
      (((d+s : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := rfl

/-- The extended order translation is ordinary addition by a finite integer,
including the manuscript's negative-infinity convention for zero objects. -/
theorem signedTranslation_eq_add (s : ℤ) (x : WithBot (WithTop ℤ)) :
    signedTranslation s x = x + ((s : WithTop ℤ) : WithBot (WithTop ℤ)) := by
  induction x using WithBot.recBotCoe with
  | bot => simp [signedTranslation]
  | coe x =>
    induction x using WithTop.recTopCoe with
    | top =>
      change (↑(⊤ : WithTop ℤ) : WithBot (WithTop ℤ)) =
        (↑(⊤ : WithTop ℤ) : WithBot (WithTop ℤ)) + ↑(s : WithTop ℤ)
      rw [← WithBot.coe_add, WithTop.top_add]
    | coe d => simp [signedTranslation]

/-- Actual shifted projective representatives translate the infimum of
bounds, with both infinities preserved; no residue formula is assumed. -/
theorem signedProjectiveDimension_shift
    (Z : DerivedCategory (ModuleCat.{u} A)) (s : ℤ) :
    signedProjectiveDimension (Z⟦s⟧) =
      signedProjectiveDimension Z + ((s : WithTop ℤ) : WithBot (WithTop ℤ)) := by
  let c : ℤ → WithBot (WithTop ℤ) := fun d => ((d : WithTop ℤ) : WithBot (WithTop ℤ))
  have himage : c '' {d | HasSignedProjectiveBound (Z⟦s⟧) d} =
      signedTranslation s '' (c '' {d | HasSignedProjectiveBound Z d}) := by
    ext x
    constructor
    · rintro ⟨d,hd,rfl⟩
      change HasSignedProjectiveBound (Z⟦s⟧) d at hd
      have hback : HasSignedProjectiveBound Z (d-s) :=
        (bound_shift_iff Z (d-s) s).mp (by simpa only [sub_add_cancel] using hd)
      refine ⟨c (d-s),⟨d-s,hback,rfl⟩,?_⟩
      change signedTranslation s (((d-s : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) =
        ((d : WithTop ℤ) : WithBot (WithTop ℤ))
      rw [signedTranslation_coe,sub_add_cancel]
    · rintro ⟨y,⟨d,hd,rfl⟩,rfl⟩
      refine ⟨d+s,(bound_shift_iff Z d s).mpr hd,?_⟩
      simp [c]
  change sInf (c '' {d | HasSignedProjectiveBound (Z⟦s⟧) d}) = _
  rw [himage, sInf_image, ← (signedTranslation s).map_sInf]
  exact signedTranslation_eq_add s (signedProjectiveDimension Z)
end SignedExtrema
end
end Note198.ComplexProjectiveDimension



