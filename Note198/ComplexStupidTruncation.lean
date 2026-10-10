import Note198.ComplexProjectiveModels
import Mathlib.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Order.ConditionallyCompleteLattice.Finset

namespace Note198.ComplexStupidTruncation
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
open scoped ModuleCat.Algebra
universe u
section Truncation
variable {A : Type u} [Ring A]
variable (K : CochainComplex (ModuleCat.{u} A) ℤ) (lo : ℤ)

abbrev tailEmbedding := ComplexShape.embeddingUpIntGE (lo+1)
abbrev tail : CochainComplex (ModuleCat.{u} A) ℤ := K.stupidTrunc (tailEmbedding lo)

/-- The retained degrees are exactly the integers at least lo+1. -/
theorem tail_image_iff (n : ℤ) :
    (∃ i : ℕ, (tailEmbedding lo).f i = n) ↔ lo+1 ≤ n := by
  constructor
  · rintro ⟨i,hi⟩
    change (lo+1)+(i:ℤ)=n at hi
    omega
  · intro hn
    refine ⟨(n-(lo+1)).toNat,?_⟩
    change (lo+1)+((n-(lo+1)).toNat:ℤ)=n
    rw [Int.toNat_of_nonneg (by omega)]
    omega

def tailComponent (n : ℤ) : (tail K lo).X n ⟶ K.X n := by
  classical
  exact if h : ∃ i : ℕ, (tailEmbedding lo).f i=n then
    (K.stupidTruncXIso (tailEmbedding lo) h.choose_spec).hom else 0

theorem tailComponent_image (i : ℕ) (n : ℤ) (hi : (tailEmbedding lo).f i=n) :
    tailComponent K lo n = (K.stupidTruncXIso (tailEmbedding lo) hi).hom := by
  classical
  unfold tailComponent
  split_ifs with h
  · have hh : h.choose=i := (tailEmbedding lo).injective_f (h.choose_spec.trans hi.symm)
    subst i
    simp only [dif_pos h]
  · exact (h ⟨i,hi⟩).elim

/-- The stupid truncation inclusion is an actual complex map, including the
boundary from lo to lo+1. -/
def tailInclusion : tail K lo ⟶ K where
  f := tailComponent K lo
  comm' i' j' hij := by
    classical
    by_cases hi : ∃ i : ℕ, (tailEmbedding lo).f i=i'
    · obtain ⟨i,hi⟩ := hi
      have hj : ∃ j : ℕ, (tailEmbedding lo).f j=j' := by
        apply (tail_image_iff lo j').mpr
        have hh := (tail_image_iff lo i').mp ⟨i,hi⟩
        change i'+1=j' at hij
        omega
      obtain ⟨j,hj⟩ := hj
      rw [tailComponent_image K lo i i' hi,tailComponent_image K lo j j' hj]
      dsimp [tail,stupidTruncXIso,stupidTrunc]
      rw [extend_d_eq _ (tailEmbedding lo) hi hj,restriction_d_eq _ (tailEmbedding lo) hi hj]
      simp only [Iso.trans_hom,Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id]
      simp [restrictionXIso]
    · exact ((K.restriction (tailEmbedding lo)).isZero_extend_X
        (tailEmbedding lo) i' (not_exists.mp hi)).eq_of_src _ _

theorem tail_lower (n : ℤ) (hn : n < lo+1) : IsZero ((tail K lo).X n) := by
  apply K.isZero_stupidTrunc_X (tailEmbedding lo) n
  intro i hi
  have hh := (tail_image_iff lo n).mp ⟨i,hi⟩
  omega

theorem tailInclusion_isIso (n : ℤ) (hn : lo+1 ≤ n) :
    IsIso ((tailInclusion K lo).f n) := by
  obtain ⟨i,hi⟩ := (tail_image_iff lo n).mpr hn
  change IsIso (tailComponent K lo n)
  rw [tailComponent_image K lo i n hi]
  exact (K.stupidTruncXIso (tailEmbedding lo) hi).isIso_hom

variable (hbelow : ∀ n, n < lo → IsZero (K.X n))

/-- Projection to the actual lowest term, placed in its original degree lo. -/
def lowestProjection : K ⟶ (single (ModuleCat.{u} A) (.up ℤ) lo).obj (K.X lo) :=
  mkHomToSingle (𝟙 _) (fun i hi => by
    change i+1=lo at hi
    exact (hbelow i (by omega)).eq_of_src _ _)

theorem lowestProjection_isIso : IsIso ((lowestProjection K lo hbelow).f lo) := by
  dsimp [lowestProjection]
  rw [mkHomToSingle_f]
  simp only [Category.id_comp]
  infer_instance

theorem tail_projection_zero : tailInclusion K lo ≫ lowestProjection K lo hbelow = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n=lo
  · subst n
    exact (tail_lower K lo lo (by omega)).eq_of_src _ _
  · exact (isZero_single_obj_X (.up ℤ) lo (K.X lo) n hn).eq_of_tgt _ _

def lowestShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ) :=
  ShortComplex.mk (tailInclusion K lo) (lowestProjection K lo hbelow)
    (tail_projection_zero K lo hbelow)

/-- The stupid truncation sequence is genuinely short exact in every degree,
not merely a triangle requested as an extra hypothesis. -/
theorem lowest_shortExact : (lowestShortComplex K lo hbelow).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let f := (tailInclusion K lo).f n
  let g := (lowestProjection K lo hbelow).f n
  have hf : Function.Injective f.hom := by
    by_cases hn : lo+1 ≤ n
    · letI := tailInclusion_isIso K lo n hn
      exact (ModuleCat.mono_iff_injective _).mp inferInstance
    · letI := ModuleCat.subsingleton_of_isZero (tail_lower K lo n (by omega))
      exact fun x y _ => Subsingleton.elim x y
  have hg : Function.Surjective g.hom := by
    by_cases hn : n=lo
    · subst n
      letI := lowestProjection_isIso K lo hbelow
      exact (ModuleCat.epi_iff_surjective _).mp inferInstance
    · letI := ModuleCat.subsingleton_of_isZero
        (isZero_single_obj_X (.up ℤ) lo (K.X lo) n hn)
      exact fun y => ⟨0,Subsingleton.elim _ _⟩
  refine ShortComplex.ShortExact.mk' ?_
    ((ModuleCat.mono_iff_injective _).mpr hf)
    ((ModuleCat.epi_iff_surjective _).mpr hg)
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  change LinearMap.range f.hom = LinearMap.ker g.hom
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    have hz := congrArg (fun t => t.f n) (tail_projection_zero K lo hbelow)
    have he : f ≫ g = 0 := hz
    have hy := congrArg (fun t : (tail K lo).X n ⟶
      ((single (ModuleCat.{u} A) (.up ℤ) lo).obj (K.X lo)).X n => t x) he
    exact hy
  · intro hy
    by_cases hn : n=lo
    · subst n
      letI := lowestProjection_isIso K lo hbelow
      have hgi : Function.Injective g.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
      have hy0 : y=0 := hgi (by simpa using hy)
      subst y
      exact ⟨0,map_zero _⟩
    · by_cases hln : lo+1 ≤ n
      · letI := tailInclusion_isIso K lo n hln
        exact (ModuleCat.epi_iff_surjective f).mp inferInstance y
      · letI := ModuleCat.subsingleton_of_isZero (hbelow n (by omega))
        exact ⟨0,Subsingleton.elim _ _⟩

theorem tail_term_finite (hK : ∀ n, Module.Finite A (K.X n)) (n : ℤ) :
    Module.Finite A ((tail K lo).X n) := by
  by_cases hn : ∃ i : ℕ, (tailEmbedding lo).f i=n
  · letI := hK n
    exact Module.Finite.equiv (K.stupidTruncXIso (tailEmbedding lo) hn.choose_spec).symm.toLinearEquiv
  · have hz : IsZero ((tail K lo).X n) :=
      K.isZero_stupidTrunc_X (tailEmbedding lo) n (not_exists.mp hn)
    letI : Subsingleton ((tail K lo).X n) := ModuleCat.subsingleton_of_isZero hz
    infer_instance

theorem tail_bounded (hi : ℤ)
    (hK : ∀ n, n < lo ∨ hi < n → IsZero (K.X n)) (n : ℤ)
    (hn : n < lo+1 ∨ hi < n) : IsZero ((tail K lo).X n) := by
  rcases hn with hn | hn
  · exact tail_lower K lo n hn
  · by_cases hh : ∃ i : ℕ, (tailEmbedding lo).f i=n
    · exact (hK n (Or.inr hn)).of_iso
        (K.stupidTruncXIso (tailEmbedding lo) hh.choose_spec)
    · exact K.isZero_stupidTrunc_X (tailEmbedding lo) n (not_exists.mp hh)

end Truncation
section FiniteGlobalDimension
open OAI.LittleFinitistic Note198.ComplexProjectiveModels
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} A)]
variable (g : ℕ) (hg : ∀ M : ModuleCat.{u} A, HasProjectiveDimensionLE M g)

include k g hg in
/-- Finite global dimension supplies every finite stalk model used in the
stupid truncation induction. -/
theorem finite_module_stalk_model (M : ModuleCat.{u} A) [Module.Finite A M] (n : ℤ) :
    HasFiniteProjectiveModel ((DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj M) := by
  letI : Module.Finite k M := Module.Finite.trans A M
  exact finite_stalk_model (PDMinimal.FiniteModule.of (k:=k) (A:=A) M) g (hg M) n

include k g hg in
/-- Every actual bounded finite-module complex acquires a bounded finite
projective model. The proof constructs the lowest-term short exact sequence
at each step and uses actual cone closure, not an assumed resolution of K. -/
theorem bounded_finite_complex_model_by_length (r : ℕ) :
    ∀ (K : CochainComplex (ModuleCat.{u} A) ℤ) (lo : ℤ),
      (∀ n, Module.Finite A (K.X n)) →
      (∀ n, n < lo ∨ lo+(r:ℤ) < n → IsZero (K.X n)) →
      HasFiniteProjectiveModel (DerivedCategory.Q.obj K) := by
  induction r with
  | zero =>
    intro K lo hfinite hbound
    letI : K.IsStrictlyGE lo := by
      rw [CochainComplex.isStrictlyGE_iff]
      intro n hn
      exact hbound n (Or.inl hn)
    letI : K.IsStrictlyLE lo := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro n hn
      exact hbound n (Or.inr (by simpa using hn))
    obtain ⟨M,⟨e⟩⟩ := CochainComplex.exists_iso_single (K:=K) lo
    let eM := (eval (ModuleCat.{u} A) (.up ℤ) lo).mapIso e ≪≫
      singleObjXSelf (.up ℤ) lo M
    letI := hfinite lo
    letI : Module.Finite A ((eval (ModuleCat.{u} A) (.up ℤ) lo).obj K) := by
      change Module.Finite A (K.X lo)
      exact hfinite lo
    letI : Module.Finite A M := Module.Finite.equiv eM.toLinearEquiv
    have hm := finite_module_stalk_model (k:=k) g hg M lo
    exact model_of_iso hm (DerivedCategory.Q.mapIso e).symm
  | succ r ih =>
    intro K lo hfinite hbound
    have htail := ih (tail K lo) (lo+1) (tail_term_finite K lo hfinite) (by
      intro n hn
      apply tail_bounded K lo (lo+((r+1:ℕ):ℤ)) hbound n
      rcases hn with hn | hn
      · exact Or.inl hn
      · exact Or.inr (by omega))
    letI := hfinite lo
    have hstalk := finite_module_stalk_model (k:=k) g hg (K.X lo) lo
    let hbelow := fun n hn => hbound n (Or.inl hn)
    have hs := lowest_shortExact K lo hbelow
    exact model_triangle_middle (DerivedCategory.triangleOfSES hs)
      (DerivedCategory.triangleOfSES_distinguished hs) htail hstalk

include k g hg in
/-- The finite-window form includes empty windows: in that case every term
is zero and the same induction applies to the one-degree containing window. -/
theorem bounded_finite_complex_model
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (lo hi : ℤ)
    (hfinite : ∀ n, Module.Finite A (K.X n))
    (hbound : ∀ n, n < lo ∨ hi < n → IsZero (K.X n)) :
    HasFiniteProjectiveModel (DerivedCategory.Q.obj K) := by
  apply bounded_finite_complex_model_by_length (k:=k) g hg (hi-lo).toNat K lo hfinite
  intro n hn
  apply hbound n
  rcases hn with hn | hn
  · exact Or.inl hn
  · exact Or.inr (by
      have hh : hi-lo ≤ ((hi-lo).toNat:ℤ) := by omega
      omega)

/-- The literal bounded derived category of finite modules is the essential
image of actual bounded finite-module complexes under the localization Q. -/
def InBoundedFiniteDerived (Z : DerivedCategory (ModuleCat.{u} A)) : Prop :=
  ∃ (K : CochainComplex (ModuleCat.{u} A) ℤ) (lo hi : ℤ),
    (∀ n, Module.Finite A (K.X n)) ∧
    (∀ n, n < lo ∨ hi < n → IsZero (K.X n)) ∧
    Nonempty (DerivedCategory.Q.obj K ≅ Z)

include k g hg in
/-- No finite projective representative is an input: every object of the
actual bounded finite-module essential image receives one from global dimension. -/
theorem bounded_derived_finite_projective_model
    (Z : DerivedCategory (ModuleCat.{u} A)) (hZ : InBoundedFiniteDerived Z) :
    HasFiniteProjectiveModel Z := by
  obtain ⟨K,lo,hi,hfinite,hbound,⟨e⟩⟩ := hZ
  exact model_of_iso (bounded_finite_complex_model (k:=k) g hg K lo hi hfinite hbound) e

include k g hg in
/-- Minimal bounded representatives are constructed for every actual bounded
finite-derived object; the final statement has no projective-model input. -/
theorem bounded_derived_minimal_model
    (Z : DerivedCategory (ModuleCat.{u} A)) (hZ : InBoundedFiniteDerived Z) :
    ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ) (lo hi : ℤ),
      (∀ n, Module.Finite A (P.X n) ∧ Module.Projective A (P.X n)) ∧
      (∀ n, n < lo ∨ hi < n → IsZero (P.X n)) ∧
      (∀ n, LinearMap.range (P.d n (n+1)).hom ≤
        Ring.jacobson A • (⊤ : Submodule A (P.X (n+1)))) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ Z) := by
  obtain ⟨P,lo,hi,hP,hb,⟨eP⟩⟩ := bounded_derived_finite_projective_model (k:=k) g hg Z hZ
  have hp : ∀ n, FiniteDimensional k (P.X n) ∧ Module.Projective A (P.X n) := by
    intro n
    letI := (hP n).1
    exact ⟨Module.Finite.trans A (P.X n),(hP n).2⟩
  obtain ⟨Q,hQ,hminimal⟩ :=
    Note198.ComplexProjectiveDimension.exists_minimal_bounded_representative k P lo hi hp hb
  obtain ⟨e⟩ := hQ.1
  letI := e.quasiIso_hom
  let eQ : DerivedCategory.Q.obj Q ≅ Z :=
    (asIso (DerivedCategory.Q.map e.hom)).symm ≪≫ eP
  refine ⟨Q,lo,hi,?_,hQ.2.2,hminimal,⟨eQ⟩⟩
  intro n
  letI := (hQ.2.1 n).1
  exact ⟨Module.Finite.of_restrictScalars_finite k A (Q.X n),(hQ.2.1 n).2⟩

include g hg in
/-- The residue criterion is now supplied for every object of Db of finite
modules, with its actual minimal projective model constructed from global dimension.
The residue complex is the genuine tensor of that K-projective representative. -/
theorem bounded_derived_residue_bound_detection
    (Z : DerivedCategory (ModuleCat.{u} A)) (hZ : InBoundedFiniteDerived Z) :
    ∃ P : CochainComplex (ModuleCat.{u} A) ℤ,
      Nonempty (DerivedCategory.Q.obj P ≅ Z) ∧
      ∀ d : ℤ, Note198.ComplexProjectiveDimension.HasSignedProjectiveBound Z d ↔
        ∀ n : ℤ, n < -d → IsZero
          ((Note198.ComplexProjectiveDimension.residueComplex k P).homology n) := by
  obtain ⟨P,lo,hi,hP,hb,hminimal,⟨e⟩⟩ := bounded_derived_minimal_model (k:=k) g hg Z hZ
  exact ⟨P,⟨e⟩,fun d =>
    Note198.ComplexProjectiveDimension.bound_iff_residueHomology_zero k P lo hi hP hb hminimal Z e d⟩

/-- Signed degrees detected by the actual residue tensor model. Degree d
means the cohomology in degree -d is nonzero. -/
def residueDegreeSet (P : CochainComplex (ModuleCat.{u} A) ℤ) : Set ℤ :=
  {d | ¬ IsZero ((Note198.ComplexProjectiveDimension.residueComplex k P).homology (-d))}

theorem residueDegreeSet_finite (P : CochainComplex (ModuleCat.{u} A) ℤ) (lo hi : ℤ)
    (hb : ∀ n, n < lo ∨ hi < n → IsZero (P.X n)) : (residueDegreeSet (k:=k) P).Finite := by
  apply (Set.finite_Icc (-hi) (-lo)).subset
  intro d hd
  constructor
  · by_contra hh
    exact hd (Note198.ComplexProjectiveDimension.residueHomology_isZero_of_term_zero k P (-d)
      (hb (-d) (Or.inr (by omega))))
  · by_contra hh
    exact hd (Note198.ComplexProjectiveDimension.residueHomology_isZero_of_term_zero k P (-d)
      (hb (-d) (Or.inl (by omega))))

/-- The infimum over actual projective representatives equals the supremum
of signed nonzero residue degrees; the empty degree set gives -∞. -/
theorem signed_pd_eq_residue_sup
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (lo hi : ℤ)
    (hP : ∀ n, Module.Finite A (P.X n) ∧ Module.Projective A (P.X n))
    (hb : ∀ n, n < lo ∨ hi < n → IsZero (P.X n))
    (hm : ∀ n, LinearMap.range (P.d n (n+1)).hom ≤
      Ring.jacobson A • (⊤ : Submodule A (P.X (n+1))))
    (Z : DerivedCategory (ModuleCat.{u} A)) (e : DerivedCategory.Q.obj P ≅ Z) :
    Note198.ComplexProjectiveDimension.signedProjectiveDimension Z =
      sSup ((fun d : ℤ => ((d : WithTop ℤ) : WithBot (WithTop ℤ))) ''
        residueDegreeSet (k:=k) P) := by
  let degrees := residueDegreeSet (k:=k) P
  have hc (c : ℤ) : Note198.ComplexProjectiveDimension.HasSignedProjectiveBound Z c ↔
      ∀ d ∈ degrees, d ≤ c := by
    rw [Note198.ComplexProjectiveDimension.bound_iff_residueHomology_zero k P lo hi hP hb hm Z e c]
    constructor
    · intro h d hd
      by_contra hdc
      exact hd (h (-d) (by omega))
    · intro h n hn
      by_contra hzero
      have hd : -n ∈ degrees := by simpa only [degrees,residueDegreeSet,Set.mem_setOf_eq,neg_neg] using hzero
      have hh := h (-n) hd
      omega
  by_cases hne : degrees.Nonempty
  · have hfin : degrees.Finite := residueDegreeSet_finite (k:=k) P lo hi hb
    let d : ℤ := sSup degrees
    have hgreatest : IsGreatest degrees d := hne.isGreatest_csSup hfin
    have hdim : Note198.ComplexProjectiveDimension.signedProjectiveDimension Z =
        ((d : WithTop ℤ) : WithBot (WithTop ℤ)) := by
      apply le_antisymm
      · exact Note198.ComplexProjectiveDimension.signedProjectiveDimension_le_of_bound
          ((hc d).mpr hgreatest.2)
      · unfold Note198.ComplexProjectiveDimension.signedProjectiveDimension
        apply le_sInf
        rintro x ⟨c,hc',rfl⟩
        exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ((hc c).mp hc' d hgreatest.1))
    rw [hdim]
    apply le_antisymm
    · exact le_sSup ⟨d,hgreatest.1,rfl⟩
    · apply sSup_le
      rintro x ⟨c,hc',rfl⟩
      exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (hgreatest.2 hc'))
  · have hemp : degrees=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hbot : Note198.ComplexProjectiveDimension.signedProjectiveDimension Z = ⊥ := by
      apply WithBot.eq_bot_iff_forall_le.mpr
      intro b
      induction b using WithTop.recTopCoe with
      | top => exact le_top
      | coe d =>
        apply Note198.ComplexProjectiveDimension.signedProjectiveDimension_le_of_bound
        exact (hc d).mpr (by simp [hemp])
    rw [hbot]
    change (⊥ : WithBot (WithTop ℤ)) = sSup ((fun d : ℤ =>
      ((d : WithTop ℤ) : WithBot (WithTop ℤ))) '' degrees)
    simp [hemp]

include g hg in
/-- The manuscript's signed residue-sup formula now covers every actual
Db object with no supplied projective representative or minimality witness. -/
theorem bounded_derived_exact_residue_sup
    (Z : DerivedCategory (ModuleCat.{u} A)) (hZ : InBoundedFiniteDerived Z) :
    ∃ P : CochainComplex (ModuleCat.{u} A) ℤ,
      Nonempty (DerivedCategory.Q.obj P ≅ Z) ∧
      Note198.ComplexProjectiveDimension.signedProjectiveDimension Z =
        sSup ((fun d : ℤ => ((d : WithTop ℤ) : WithBot (WithTop ℤ))) ''
          residueDegreeSet (k:=k) P) := by
  obtain ⟨P,lo,hi,hP,hb,hm,⟨e⟩⟩ := bounded_derived_minimal_model (k:=k) g hg Z hZ
  exact ⟨P,⟨e⟩,signed_pd_eq_residue_sup (k:=k) P lo hi hP hb hm Z e⟩
end FiniteGlobalDimension
end
end Note198.ComplexStupidTruncation