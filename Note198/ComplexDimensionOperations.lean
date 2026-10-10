import Note198.ComplexStupidTruncation
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Category.ModuleCat.Biproducts

namespace Note198.ComplexDimensionOperations
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
open ComplexProjectiveDimension ComplexProjectiveModels ComplexStupidTruncation
open scoped ModuleCat.Algebra ZeroObject
universe u
variable {A : Type u} [Ring A] [HasDerivedCategory.{u+1} (ModuleCat.{u} A)]

/-- The actual termwise biproduct remains finite projective. -/
theorem biprod_terms_finite_projective
    (P Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (hp : ∀ n, Module.Finite A (P.X n) ∧ Module.Projective A (P.X n))
    (hq : ∀ n, Module.Finite A (Q.X n) ∧ Module.Projective A (Q.X n)) (n : ℤ) :
    Module.Finite A ((P ⊞ Q).X n) ∧ Module.Projective A ((P ⊞ Q).X n) := by
  letI := (hp n).1
  letI := (hp n).2
  letI := (hq n).1
  letI := (hq n).2
  let e := HomologicalComplex.biprodXIso P Q n ≪≫ ModuleCat.biprodIsoProd (P.X n) (Q.X n)
  exact ⟨Module.Finite.equiv e.symm.toLinearEquiv,
    Module.Projective.of_equiv' e.symm.toLinearEquiv⟩

/-- Support of the actual biproduct is the union of the two support windows. -/
theorem biprod_bounded (P Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (pl ph ql qh : ℤ)
    (hp : ∀ n, n < pl ∨ ph < n → IsZero (P.X n))
    (hq : ∀ n, n < ql ∨ qh < n → IsZero (Q.X n))
    (n : ℤ) (hn : n < min pl ql ∨ max ph qh < n) : IsZero ((P ⊞ Q).X n) := by
  apply ((HomologicalComplex.biprodXIso P Q n).isZero_iff).mpr
  apply (biprod_isZero_iff _ _).mpr
  constructor
  · apply hp n
    rcases hn with hn | hn
    · exact Or.inl (lt_of_lt_of_le hn (min_le_left _ _))
    · exact Or.inr (lt_of_le_of_lt (le_max_left _ _) hn)
  · apply hq n
    rcases hn with hn | hn
    · exact Or.inl (lt_of_lt_of_le hn (min_le_right _ _))
    · exact Or.inr (lt_of_le_of_lt (le_max_right _ _) hn)

variable (k : Type u) [Field k] [Algebra k A]

/-- Additive residue tensor and homology preserve the actual binary biproduct. -/
def residueHomologyBiprodIso (P Q : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (residueComplex k (P ⊞ Q)).homology n ≅
      (residueComplex k P).homology n ⊞ (residueComplex k Q).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (.up ℤ) n).mapIso
    (((OAI.LittleFinitistic.PDTensor.tensorFunctor k A
      (OAI.LittleFinitistic.PDTensor.Residue (A := A))).mapHomologicalComplex
        (.up ℤ)).mapBiprod P Q) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (.up ℤ) n).mapBiprod _ _

/-- Nonzero residue degrees of a genuine biproduct are precisely the union. -/
theorem residueDegreeSet_biprod (P Q : CochainComplex (ModuleCat.{u} A) ℤ) :
    residueDegreeSet (k := k) (P ⊞ Q) =
      residueDegreeSet (k := k) P ∪ residueDegreeSet (k := k) Q := by
  ext d
  change (¬ IsZero ((residueComplex k (P ⊞ Q)).homology (-d))) ↔
    (¬ IsZero ((residueComplex k P).homology (-d))) ∨
      (¬ IsZero ((residueComplex k Q).homology (-d)))
  rw [(residueHomologyBiprodIso k P Q (-d)).isZero_iff, biprod_isZero_iff]
  exact not_and_or


/-- Actual finite-derived objects are closed under the native binary biproduct. -/
theorem boundedFinite_biprod
    (Z T : DerivedCategory (ModuleCat.{u} A))
    (hZ : InBoundedFiniteDerived Z) (hT : InBoundedFiniteDerived T) :
    InBoundedFiniteDerived (Z ⊞ T) := by
  obtain ⟨K,kl,kh,hk,hkb,⟨eK⟩⟩ := hZ
  obtain ⟨L,ll,lh,hl,hlb,⟨eL⟩⟩ := hT
  refine ⟨K ⊞ L,min kl ll,max kh lh,?_,
    biprod_bounded K L kl kh ll lh hkb hlb,?_⟩
  · intro n
    letI := hk n
    letI := hl n
    let e := HomologicalComplex.biprodXIso K L n ≪≫ ModuleCat.biprodIsoProd (K.X n) (L.X n)
    exact Module.Finite.equiv e.symm.toLinearEquiv
  · exact ⟨DerivedCategory.Q.mapBiprod K L ≪≫ biprod.mapIso eK eL⟩

/-- The native empty finite biproduct is a zero object. -/
theorem finZero_biproduct_isZero (f : Fin 0 → DerivedCategory (ModuleCat.{u} A)) :
    IsZero (⨁ f) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply biproduct.hom_ext
  intro i
  exact Fin.elim0 i

/-- Separate the zeroth component from the actual Fin(n+1)-indexed biproduct. -/
def finSuccBiproductIso {n : ℕ} (f : Fin (n+1) → DerivedCategory (ModuleCat.{u} A)) :
    (⨁ f) ≅ f 0 ⊞ (⨁ fun i : Fin n => f i.succ) := by
  have hzero : biproduct.ι f 0 ≫
      (biproduct.lift fun i : Fin n => biproduct.π f i.succ) = 0 := by
    apply biproduct.hom_ext
    intro j
    simp [Category.assoc, biproduct.ι_π]
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_succ] at hv
    omega
  have hsucc (i : Fin n) : biproduct.ι f i.succ ≫
      (biproduct.lift fun j : Fin n => biproduct.π f j.succ) =
        biproduct.ι (fun j : Fin n => f j.succ) i := by
    apply biproduct.hom_ext
    intro j
    simp [Category.assoc, biproduct.ι_π]
  refine {
    hom := biprod.lift (biproduct.π f 0)
      (biproduct.lift fun i : Fin n => biproduct.π f i.succ)
    inv := biprod.desc (biproduct.ι f 0)
      (biproduct.desc fun i : Fin n => biproduct.ι f i.succ)
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  · apply biproduct.hom_ext'
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [Category.assoc, hzero, hsucc, biproduct.ι_π]
    all_goals simp [← Category.assoc, hzero, hsucc]
  · apply biprod.hom_ext'
    · apply biprod.hom_ext <;> simp [Category.assoc, hzero]
    · apply biproduct.hom_ext'
      intro i
      apply biprod.hom_ext <;> simp [Category.assoc, hsucc, biproduct.ι_π]
/-- Fin-indexed native biproducts stay in the bounded finite derived category. -/
theorem boundedFinite_fin_biproduct (n : ℕ)
    (f : Fin n → DerivedCategory (ModuleCat.{u} A))
    (hf : ∀ i, InBoundedFiniteDerived (f i)) :
    InBoundedFiniteDerived (⨁ f) := by
  induction n with
  | zero =>
    refine ⟨0,0,0,?_,?_,?_⟩
    · intro j
      have hz : IsZero ((0 : CochainComplex (ModuleCat.{u} A) ℤ).X j) :=
        (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) j).map_isZero
          (isZero_zero (CochainComplex (ModuleCat.{u} A) ℤ))
      letI := ModuleCat.subsingleton_of_isZero hz
      infer_instance
    · intro j hj
      exact (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) j).map_isZero
        (isZero_zero (CochainComplex (ModuleCat.{u} A) ℤ))
    · exact ⟨DerivedCategory.Q.mapZeroObject ≪≫
        (finZero_biproduct_isZero f).isoZero.symm⟩
  | succ n ih =>
    have h := boundedFinite_biprod (f 0) (⨁ fun i : Fin n => f i.succ)
      (hf 0) (ih (fun i => f i.succ) (fun i => hf i.succ))
    obtain ⟨K,lo,hi,hk,hb,⟨e⟩⟩ := h
    exact ⟨K,lo,hi,hk,hb,⟨e ≪≫ (finSuccBiproductIso f).symm⟩⟩
section FiniteGlobalDimension
variable [FiniteDimensional k A] (g : ℕ)
    (hg : ∀ M : ModuleCat.{u} A, HasProjectiveDimensionLE M g)

include k g hg in
/-- The exact maximum formula holds for actual bounded finite-derived
objects, with no minimal representatives supplied by the caller. Bottom
values of zero summands are retained throughout the supremum proof. -/
theorem signedProjectiveDimension_biprod
    (Z T : DerivedCategory (ModuleCat.{u} A))
    (hZ : InBoundedFiniteDerived Z) (hT : InBoundedFiniteDerived T) :
    signedProjectiveDimension (Z ⊞ T) =
      max (signedProjectiveDimension Z) (signedProjectiveDimension T) := by
  obtain ⟨P,pl,ph,hp,hpb,hpm,⟨eP⟩⟩ :=
    bounded_derived_minimal_model (k:=k) g hg Z hZ
  obtain ⟨Q,ql,qh,hq,hqb,hqm,⟨eQ⟩⟩ :=
    bounded_derived_minimal_model (k:=k) g hg T hT
  have hPQ := biprod_terms_finite_projective P Q hp hq
  have hbPQ := biprod_bounded P Q pl ph ql qh hpb hqb
  let ePQ : DerivedCategory.Q.obj (P ⊞ Q) ≅ Z ⊞ T :=
    DerivedCategory.Q.mapBiprod P Q ≪≫ biprod.mapIso eP eQ
  have hZT : InBoundedFiniteDerived (Z ⊞ T) :=
    ⟨P ⊞ Q,min pl ql,max ph qh,fun n => (hPQ n).1,hbPQ,⟨ePQ⟩⟩
  obtain ⟨W,wl,wh,hw,hwb,hwm,⟨eW⟩⟩ :=
    bounded_derived_minimal_model (k:=k) g hg (Z ⊞ T) hZT
  letI : W.IsKProjective := bounded_projective_isKProjective W wh
    (fun n => (hw n).2) (fun n hn => hwb n (Or.inr hn))
  letI : (P ⊞ Q).IsKProjective := bounded_projective_isKProjective (P ⊞ Q) (max ph qh)
    (fun n => (hPQ n).2) (fun n hn => hbPQ n (Or.inr hn))
  have hd : residueDegreeSet (k:=k) W =
      residueDegreeSet (k:=k) P ∪ residueDegreeSet (k:=k) Q := by
    rw [← residueDegreeSet_biprod k P Q]
    ext d
    exact not_congr (residueHomologyIsoOfDerivedIso k W (P ⊞ Q)
      (eW ≪≫ ePQ.symm) (-d)).isZero_iff
  rw [signed_pd_eq_residue_sup (k:=k) W wl wh hw hwb hwm (Z ⊞ T) eW,
    signed_pd_eq_residue_sup (k:=k) P pl ph hp hpb hpm Z eP,
    signed_pd_eq_residue_sup (k:=k) Q ql qh hq hqb hqm T eQ,
    hd,Set.image_union,sSup_union]

include k g hg in
/-- The actual finite biproduct has the maximum signed dimension of its
components. For the empty family the supremum and dimension are both bottom. -/
theorem signedProjectiveDimension_fin_biproduct (n : ℕ)
    (f : Fin n → DerivedCategory (ModuleCat.{u} A))
    (hf : ∀ i, InBoundedFiniteDerived (f i)) :
    signedProjectiveDimension (⨁ f) = ⨆ i, signedProjectiveDimension (f i) := by
  induction n with
  | zero =>
    rw [signedProjectiveDimension_iso (finZero_biproduct_isZero f).isoZero,
      signedProjectiveDimension_zero]
    simp
  | succ n ih =>
    rw [signedProjectiveDimension_iso (finSuccBiproductIso f),
      signedProjectiveDimension_biprod k g hg _ _ (hf 0)
        (boundedFinite_fin_biproduct n (fun i => f i.succ) (fun i => hf i.succ)),
      ih (fun i => f i.succ) (fun i => hf i.succ)]
    apply le_antisymm
    · apply max_le
      · exact le_iSup (fun i : Fin (n+1) => signedProjectiveDimension (f i)) 0
      · apply iSup_le
        intro i
        exact le_iSup (fun j : Fin (n+1) => signedProjectiveDimension (f j)) i.succ
    · apply iSup_le
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact le_max_left _ _
      · exact (le_iSup (fun j : Fin n => signedProjectiveDimension (f j.succ)) j).trans
          (le_max_right _ _)
end FiniteGlobalDimension
end
end Note198.ComplexDimensionOperations


