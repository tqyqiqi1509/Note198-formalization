import Note198.ComplexProjectiveDimension
import OAI.Algebra.Finitistic.Dimension.PDMinimalResolution
import OAI.Algebra.Finitistic.Dimension.PDDimension
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

namespace Note198.ComplexProjectiveModels
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open OAI.LittleFinitistic
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} A)]
variable (M : PDMinimal.FiniteModule k A)

/-- The actual successive-cover resolution in cohomological degrees -n. -/
def stalkProjectiveComplex : CochainComplex (ModuleCat.{u} A) ℤ :=
  (PDMinimal.complex M).extend ComplexShape.embeddingDownNat

/-- The augmentation is a genuine complex map to the degree-zero stalk. -/
def stalkAugmentation : stalkProjectiveComplex M ⟶
    (HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj M.cat :=
  HomologicalComplex.extendMap (PDMinimal.resolution M).π ComplexShape.embeddingDownNat ≫
    (HomologicalComplex.extendSingleIso (e := ComplexShape.embeddingDownNat)
      (X := M.cat) 0 0 (by simp)).hom

theorem stalkAugmentation_quasiIso : QuasiIso (stalkAugmentation M) := by
  let f := HomologicalComplex.extendMap (PDMinimal.resolution M).π
    ComplexShape.embeddingDownNat
  let e := HomologicalComplex.extendSingleIso (e := ComplexShape.embeddingDownNat)
    (X := M.cat) 0 0 (by simp)
  letI : QuasiIso f := (HomologicalComplex.quasiIso_extendMap_iff
    (PDMinimal.resolution M).π ComplexShape.embeddingDownNat).mpr
      (PDMinimal.resolution M).quasiIso
  change QuasiIso (f ≫ e.hom)
  exact quasiIso_comp f e.hom

def stalkDerivedIso : DerivedCategory.Q.obj (stalkProjectiveComplex M) ≅
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M.cat :=
  letI := stalkAugmentation_quasiIso M
  asIso (DerivedCategory.Q.map (stalkAugmentation M))

theorem stalk_term_projective (n : ℤ) :
    Module.Projective A ((stalkProjectiveComplex M).X n) := by
  have hcat : Projective ((stalkProjectiveComplex M).X n) := by
    dsimp [stalkProjectiveComplex]
    infer_instance
  exact (IsProjective.iff_projective _).mpr hcat

theorem stalk_term_finite (n : ℤ) :
    Module.Finite A ((stalkProjectiveComplex M).X n) := by
  by_cases hn : 0 < n
  · have hz : IsZero ((stalkProjectiveComplex M).X n) := by
      apply (PDMinimal.complex M).isZero_extend_X ComplexShape.embeddingDownNat n
      intro j hj
      simp only [ComplexShape.embeddingDownNat_f] at hj
      omega
    letI := ModuleCat.subsingleton_of_isZero hz
    infer_instance
  · let j := (-n).toNat
    have hj : ComplexShape.embeddingDownNat.f j = n := by
      simp only [ComplexShape.embeddingDownNat_f]
      dsimp [j]
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    let e := (PDMinimal.complex M).extendXIso ComplexShape.embeddingDownNat hj
    have hfinite : Module.Finite A ((PDMinimal.complex M).X j) := by
      change Module.Finite A (PDMinimal.term M j)
      infer_instance
    letI := hfinite
    exact Module.Finite.equiv e.symm.toLinearEquiv

/-- Finite numerical module projective dimension terminates the actual
successive-cover resolution; no bounded-resolution witness is assumed. -/
theorem stalk_term_bounded (g : ℕ) (hg : HasProjectiveDimensionLE M.cat g)
    (n : ℤ) (hn : n < -(g : ℤ) ∨ 0 < n) :
    IsZero ((stalkProjectiveComplex M).X n) := by
  letI : HasProjectiveDimensionLE M.cat g := hg
  rcases hn with hn | hn
  · let j := (-n).toNat
    have hj : ComplexShape.embeddingDownNat.f j = n := by
      simp only [ComplexShape.embeddingDownNat_f]
      dsimp [j]
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    have hjg : g < j := by
      have he : (j : ℤ) = -n := Int.toNat_of_nonneg (by omega)
      omega
    obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [hi] at hj hjg
    have hgi : HasProjectiveDimensionLE M.cat i :=
      hasProjectiveDimensionLT_of_ge M.cat (g+1) (i+1) (by omega)
    have hz : IsZero ((PDMinimal.complex M).X (i+1)) := by
      apply ModuleCat.isZero_iff_subsingleton.mpr
      change Subsingleton (PDMinimal.term M (i+1))
      exact PDMinimal.term_zero_of_pdLE M i hgi
    exact hz.of_iso ((PDMinimal.complex M).extendXIso ComplexShape.embeddingDownNat hj)
  · apply (PDMinimal.complex M).isZero_extend_X ComplexShape.embeddingDownNat n
    intro j hj
    simp only [ComplexShape.embeddingDownNat_f] at hj
    omega

/-- A finite-dimensional module with numerical pd ≤ g has a genuine
bounded finite projective stalk model, constructed from its actual covers. -/
theorem finite_stalk_projective_model (g : ℕ) (hg : HasProjectiveDimensionLE M.cat g) :
    ∃ P : CochainComplex (ModuleCat.{u} A) ℤ,
      (∀ n, Module.Finite A (P.X n) ∧ Module.Projective A (P.X n)) ∧
      (∀ n, n < -(g : ℤ) ∨ 0 < n → IsZero (P.X n)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M.cat) :=
  ⟨stalkProjectiveComplex M, fun n => ⟨stalk_term_finite M n, stalk_term_projective M n⟩,
    stalk_term_bounded M g hg, ⟨stalkDerivedIso M⟩⟩

/-- Existence of an actual bounded complex of finite projectives representing Z. -/
def HasFiniteProjectiveModel (Z : DerivedCategory (ModuleCat.{u} A)) : Prop :=
  ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ) (lo hi : ℤ),
    (∀ n, Module.Finite A (P.X n) ∧ Module.Projective A (P.X n)) ∧
    (∀ n, n < lo ∨ hi < n → IsZero (P.X n)) ∧
    Nonempty (DerivedCategory.Q.obj P ≅ Z)

theorem model_of_iso {Z W : DerivedCategory (ModuleCat.{u} A)}
    (h : HasFiniteProjectiveModel Z) (e : Z ≅ W) : HasFiniteProjectiveModel W := by
  obtain ⟨P,lo,hi,hP,hb,⟨i⟩⟩ := h
  exact ⟨P,lo,hi,hP,hb,⟨i ≪≫ e⟩⟩

theorem model_shift {Z : DerivedCategory (ModuleCat.{u} A)}
    (h : HasFiniteProjectiveModel Z) (s : ℤ) : HasFiniteProjectiveModel (Z⟦s⟧) := by
  obtain ⟨P,lo,hi,hP,hb,⟨i⟩⟩ := h
  refine ⟨P⟦s⟧,lo-s,hi-s,?_,?_,?_⟩
  · intro n
    exact hP (n+s)
  · intro n hn
    exact hb (n+s) (by omega)
  · exact ⟨(DerivedCategory.Q.commShiftIso s).app P ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) s).mapIso i⟩

/-- Cone terms are actual finite projectives via the native biproduct-to-product
isomorphism, rather than a finiteness or projectivity certificate assumed for the cone. -/
theorem cone_terms_finite_projective
    {P Q : CochainComplex (ModuleCat.{u} A) ℤ} (f : P ⟶ Q)
    (hP : ∀ n, Module.Finite A (P.X n) ∧ Module.Projective A (P.X n))
    (hQ : ∀ n, Module.Finite A (Q.X n) ∧ Module.Projective A (Q.X n)) (n : ℤ) :
    Module.Finite A ((CochainComplex.mappingCone f).X n) ∧
      Module.Projective A ((CochainComplex.mappingCone f).X n) := by
  letI := (hP (n+1)).1
  letI := (hP (n+1)).2
  letI := (hQ n).1
  letI := (hQ n).2
  let e : (CochainComplex.mappingCone f).X n ≅
      ModuleCat.of A ((P.X (n+1)) × (Q.X n)) :=
    HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n+1) (by rfl) ≪≫
      ModuleCat.biprodIsoProd (P.X (n+1)) (Q.X n)
  letI : Module.Finite A (ModuleCat.of A ((P.X (n+1)) × (Q.X n))) := by
    change Module.Finite A ((P.X (n+1)) × (Q.X n))
    infer_instance
  exact ⟨Module.Finite.equiv e.symm.toLinearEquiv,
    Module.Projective.of_equiv' e.symm.toLinearEquiv⟩

/-- The cochain cone has support in the union of the target support and
source support shifted by -1, with explicit endpoint conventions. -/
theorem cone_bounded
    {P Q : CochainComplex (ModuleCat.{u} A) ℤ} (f : P ⟶ Q)
    (plo phi qlo qhi : ℤ)
    (hP : ∀ n, n < plo ∨ phi < n → IsZero (P.X n))
    (hQ : ∀ n, n < qlo ∨ qhi < n → IsZero (Q.X n))
    (n : ℤ) (hn : n < min (plo-1) qlo ∨ max (phi-1) qhi < n) :
    IsZero ((CochainComplex.mappingCone f).X n) := by
  apply HomologicalComplex.homotopyCofiber.isZero_X f n
  · apply hQ
    rcases hn with hn | hn
    · exact Or.inl (lt_of_lt_of_le hn (min_le_right _ _))
    · exact Or.inr (lt_of_le_of_lt (le_max_right _ _) hn)
  · intro j hj
    change n+1=j at hj
    apply hP
    rcases hn with hn | hn
    · have hh := lt_of_lt_of_le hn (min_le_left (plo-1) qlo)
      exact Or.inl (by omega)
    · have hh := lt_of_le_of_lt (le_max_left (phi-1) qhi) hn
      exact Or.inr (by omega)

theorem cone_has_finite_projective_model
    {P Q : CochainComplex (ModuleCat.{u} A) ℤ} (f : P ⟶ Q)
    (plo phi qlo qhi : ℤ)
    (hP : ∀ n, Module.Finite A (P.X n) ∧ Module.Projective A (P.X n))
    (hQ : ∀ n, Module.Finite A (Q.X n) ∧ Module.Projective A (Q.X n))
    (hbP : ∀ n, n < plo ∨ phi < n → IsZero (P.X n))
    (hbQ : ∀ n, n < qlo ∨ qhi < n → IsZero (Q.X n)) :
    HasFiniteProjectiveModel (DerivedCategory.Q.obj (CochainComplex.mappingCone f)) :=
  ⟨CochainComplex.mappingCone f,min (plo-1) qlo,max (phi-1) qhi,
    cone_terms_finite_projective f hP hQ,
    cone_bounded f plo phi qlo qhi hbP hbQ,⟨Iso.refl _⟩⟩

/-- Morphisms between represented derived objects lift to genuine complex
maps when the source is an actual bounded projective complex. -/
theorem derived_morphism_lift
    (P Q : CochainComplex (ModuleCat.{u} A) ℤ) (hi : ℤ)
    (hP : ∀ n, Module.Projective A (P.X n))
    (hb : ∀ n, hi < n → IsZero (P.X n))
    (f : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj Q) :
    ∃ g : P ⟶ Q, DerivedCategory.Q.map g = f := by
  letI := Note198.ComplexProjectiveDimension.bounded_projective_isKProjective P hi hP hb
  let π := HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)
  let aP := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app P
  let aQ := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app Q
  obtain ⟨φ,hφ⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P (π.obj Q)).surjective
    (aP.hom ≫ f ≫ aQ.inv)
  let g := π.preimage φ
  refine ⟨g,?_⟩
  apply (cancel_epi aP.hom).mp
  have hnat := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.naturality g
  change DerivedCategory.Qh.map (π.map g) ≫ aQ.hom =
    aP.hom ≫ DerivedCategory.Q.map g at hnat
  rw [← hnat]
  have hπ : π.map g = φ := π.map_preimage φ
  rw [hπ,hφ]
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]

/-- Closure under actual distinguished triangles follows by lifting the first
morphism and comparing with its genuine finite projective mapping cone. -/
theorem model_triangle_third
    (T : Triangle (DerivedCategory (ModuleCat.{u} A)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat.{u} A)))
    (h₁ : HasFiniteProjectiveModel T.obj₁)
    (h₂ : HasFiniteProjectiveModel T.obj₂) : HasFiniteProjectiveModel T.obj₃ := by
  obtain ⟨P,plo,phi,hP,hbP,⟨eP⟩⟩ := h₁
  obtain ⟨Q,qlo,qhi,hQ,hbQ,⟨eQ⟩⟩ := h₂
  obtain ⟨f,hf⟩ := derived_morphism_lift P Q phi (fun n => (hP n).2)
    (fun n hn => hbP n (Or.inr hn)) (eP.hom ≫ T.mor₁ ≫ eQ.inv)
  let C := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)
  have hC : C ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) :=
    DerivedCategory.mappingCone_triangle_distinguished f
  let e : C ≅ T := CategoryTheory.Pretriangulated.isoTriangleOfIso₁₂ C T hC hT eP eQ (by
    change DerivedCategory.Q.map f ≫ eQ.hom = eP.hom ≫ T.mor₁
    rw [hf]
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id])
  exact model_of_iso (cone_has_finite_projective_model f plo phi qlo qhi hP hQ hbP hbQ)
    (Triangle.π₃.mapIso e)

theorem finite_stalk_model (g : ℕ) (hg : HasProjectiveDimensionLE M.cat g) (n : ℤ) :
    HasFiniteProjectiveModel
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj M.cat) := by
  obtain ⟨P,hP,hb,e⟩ := finite_stalk_projective_model M g hg
  have hzero : HasFiniteProjectiveModel
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M.cat) :=
    ⟨P,-(g:ℤ),0,hP,hb,e⟩
  exact model_of_iso (model_shift hzero (-n))
    (((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso (-n) n 0
      (neg_add_cancel n)).app M.cat)

theorem model_triangle_middle
    (T : Triangle (DerivedCategory (ModuleCat.{u} A)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat.{u} A)))
    (h₁ : HasFiniteProjectiveModel T.obj₁)
    (h₃ : HasFiniteProjectiveModel T.obj₃) : HasFiniteProjectiveModel T.obj₂ :=
  model_triangle_third T.invRotate (CategoryTheory.Pretriangulated.inv_rot_of_distTriang T hT)
    (model_shift h₃ (-1)) h₁
end
end Note198.ComplexProjectiveModels
