import Note198.ComplexModuleDimension
import Note198.ComplexCohomologyModels
import OAI.Algebra.Finitistic.Dimension.PDResidueBaseBar

namespace Note198.ComplexResidueBaseChange
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open OAI.LittleFinitistic
open Note198.ComplexProjectiveDimension Note198.ComplexModuleDimension
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable [FiniteDimensional k A] [FiniteDimensional k D]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} D)]
variable (f : A →ₐ[k] D) (hf : Function.Surjective f)
variable (hsq : ∀ a ∈ RingHom.ker f.toRingHom, ∀ b ∈ RingHom.ker f.toRingHom, a*b=0)
variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N]
variable [IsScalarTower k A N] [FiniteDimensional k N]

abbrev bar : CochainComplex (ModuleCat.{u} D) ℤ :=
  (OAI.DerivedBar.twoSidedComplex k A D N f).extend ComplexShape.embeddingDownNat

theorem bar_projective (n : ℤ) : Module.Projective D ((bar f N).X n) := by
  have hp (i : ℕ) : Projective ((OAI.DerivedBar.twoSidedComplex k A D N f).X i) :=
    PDResidueAssociativity.twoSided_projective f N i
  letI : ∀ i : ℕ, Projective ((OAI.DerivedBar.twoSidedComplex k A D N f).X i) := hp
  have : Projective ((bar f N).X n) := by dsimp [bar]; infer_instance
  exact (IsProjective.iff_projective _).mpr this

theorem bar_upper_zero (n : ℤ) (hn : 0 < n) : IsZero ((bar f N).X n) := by
  apply (OAI.DerivedBar.twoSidedComplex k A D N f).isZero_extend_X
    ComplexShape.embeddingDownNat n
  intro j hj
  simp only [ComplexShape.embeddingDownNat_f] at hj
  omega

include hf hsq in
/-- The actual A-residue Tor group and the D-residue cohomology of any
bounded finite-projective representative of the actual D-bar agree. The
D-bar itself may have infinitely many nonzero projective terms below zero. -/
def actualResidueTorIso
    (P : CochainComplex (ModuleCat.{u} D) ℤ) (hi : ℤ)
    (hp : ∀ n, Module.Projective D (P.X n))
    (hb : ∀ n, hi < n → IsZero (P.X n))
    (e : DerivedCategory.Q.obj (bar f N) ≅ DerivedCategory.Q.obj P) (n : ℕ) :
    PDTensor.Tor (k:=k) (PDTensor.Residue (A:=A)) (ModuleCat.of A N) n ≅
      (residueComplex k P).homology (-(n:ℤ)) := by
  letI := bounded_projective_isKProjective (bar f N) 0 (bar_projective f N)
    (bar_upper_zero f N)
  letI := bounded_projective_isKProjective P hi hp hb
  exact PDResidueAssociativity.residueTorIso f N hf hsq n ≪≫
    (Note198.ComplexExtensionTensor.mappedExtensionHomologyIso
      (PDTensor.tensorFunctor k D (PDTensor.Residue (A:=D)))
      (OAI.DerivedBar.twoSidedComplex k A D N f) n).symm ≪≫
    residueHomologyIsoOfDerivedIso k (bar f N) P e (-(n:ℤ))

include hf hsq in
/-- Exact finite bounds across square-zero base change. This uses actual
signed projective representatives and the actual residue tensor; neither
projective dimension is redefined using Tor. -/
theorem module_pd_bound_iff_signed_base_bound
    (P : CochainComplex (ModuleCat.{u} D) ℤ) (lo hi : ℤ)
    (hp : ∀ n, Module.Finite D (P.X n) ∧ Module.Projective D (P.X n))
    (hb : ∀ n, n < lo ∨ hi < n → IsZero (P.X n))
    (e : DerivedCategory.Q.obj (bar f N) ≅ DerivedCategory.Q.obj P) (d : ℕ) :
    HasProjectiveDimensionLE (ModuleCat.of A N) d ↔
      HasSignedProjectiveBound (DerivedCategory.Q.obj (bar f N)) (d:ℤ) := by
  let M := PDMinimal.FiniteModule.of (k:=k) (A:=A) N
  rw [bound_iff_representative_residue_zero (k:=k) P lo hi hp hb _ e.symm]
  constructor
  · intro hd j hj
    letI : HasProjectiveDimensionLE M.cat d := by
      change HasProjectiveDimensionLE (ModuleCat.of A N) d
      exact hd
    let n : ℕ := (-j).toNat
    have hn : -(n:ℤ) = j := by
      dsimp [n]
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    have hdn : d < n := by
      have : (n:ℤ) = -j := by dsimp [n]; exact Int.toNat_of_nonneg (by omega)
      omega
    have hpd : HasProjectiveDimensionLE M.cat (n-1) :=
      hasProjectiveDimensionLT_of_ge M.cat (d+1) ((n-1)+1) (by omega)
    have hz := (PDTensor.pdLE_iff_residueTor_zero M (n-1)).mp hpd
    change IsZero (PDTensor.Tor (k:=k) (PDTensor.Residue (A:=A))
      (ModuleCat.of A N) ((n-1)+1)) at hz
    have hz' : IsZero (PDTensor.Tor (k:=k) (PDTensor.Residue (A:=A)) (ModuleCat.of A N) n) := by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hz
    have h := (actualResidueTorIso f hf hsq N P hi (fun i => (hp i).2)
      (fun i hi => hb i (Or.inr hi)) e n).isZero_iff.mp hz'
    simpa only [hn] using h
  · intro h
    apply (PDTensor.pdLE_iff_residueTor_zero M d).mpr
    exact (actualResidueTorIso f hf hsq N P hi (fun i => (hp i).2)
      (fun i hi => hb i (Or.inr hi)) e (d+1)).isZero_iff.mpr
      (h (-((d+1:ℕ):ℤ)) (by push_cast; omega))

include hf hsq in
/-- The exact signed base-change value follows from an actual module pd
bound and an actual nonzero residue Tor edge. Negative signed comparison
bounds are also ruled out by that edge. -/
theorem signed_base_eq_of_module_tor_edge
    (P : CochainComplex (ModuleCat.{u} D) ℤ) (lo hi : ℤ)
    (hp : ∀ n, Module.Finite D (P.X n) ∧ Module.Projective D (P.X n))
    (hb : ∀ n, n < lo ∨ hi < n → IsZero (P.X n))
    (e : DerivedCategory.Q.obj (bar f N) ≅ DerivedCategory.Q.obj P) (d : ℕ)
    (hd : HasProjectiveDimensionLE (ModuleCat.of A N) d)
    (hedge : ¬ IsZero (PDTensor.Tor (k:=k) (PDTensor.Residue (A:=A)) (ModuleCat.of A N) d)) :
    signedProjectiveDimension (DerivedCategory.Q.obj (bar f N)) =
      (((d:ℤ):WithTop ℤ):WithBot (WithTop ℤ)) := by
  have hbound := (module_pd_bound_iff_signed_base_bound f hf hsq N P lo hi hp hb e d).mp hd
  apply le_antisymm
  · exact signedProjectiveDimension_le_of_bound hbound
  · unfold signedProjectiveDimension
    apply le_sInf
    rintro x ⟨c,hc,rfl⟩
    have hdc : (d:ℤ) ≤ c := by
      by_contra h
      have hz := (bound_iff_representative_residue_zero (k:=k) P lo hi hp hb _ e.symm c).mp hc
        (-(d:ℤ)) (neg_lt_neg (lt_of_not_ge h))
      exact hedge ((actualResidueTorIso f hf hsq N P hi (fun i => (hp i).2)
        (fun i hi => hb i (Or.inr hi)) e d).isZero_iff.mpr hz)
    exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hdc)
include hf hsq in
/-- Finite numerical pd provides the residue edge internally, so the exact
base-change equality has no extra Tor witness in its statement. -/
theorem signed_base_eq_projectiveDimension
    (P : CochainComplex (ModuleCat.{u} D) ℤ) (lo hi : ℤ)
    (hp : ∀ n, Module.Finite D (P.X n) ∧ Module.Projective D (P.X n))
    (hb : ∀ n, n < lo ∨ hi < n → IsZero (P.X n))
    (e : DerivedCategory.Q.obj (bar f N) ≅ DerivedCategory.Q.obj P) (d : ℕ)
    (hpd : projectiveDimension (ModuleCat.of A N) = d) :
    signedProjectiveDimension (DerivedCategory.Q.obj (bar f N)) =
      (((d:ℤ):WithTop ℤ):WithBot (WithTop ℤ)) := by
  letI : HasDerivedCategory.{u+1} (ModuleCat.{u} A) :=
    HasDerivedCategory.standard (ModuleCat.{u} A)
  let M := PDMinimal.FiniteModule.of (k:=k) (A:=A) N
  exact signed_base_eq_of_module_tor_edge f hf hsq N P lo hi hp hb e d
    ((projectiveDimension_le_iff _ d).mp (le_of_eq hpd))
    (residueTor_nonzero_of_projectiveDimension_eq M d hpd)

include hf hsq in
/-- The original bounded finite-cohomology scope is used to construct the
D-model. Neither the model nor a minimality/residue certificate is an input. -/
theorem finite_cohomology_base_bound_iff
    (g : ℕ) (hg : ∀ M : ModuleCat.{u} D, HasProjectiveDimensionLE M g)
    (lo hi : ℤ)
    (hc : ∀ n, FiniteDimensional k
      ((ModuleCat.restrictScalars (algebraMap k D)).obj
        (Note198.ComplexCohomologyModels.H n (DerivedCategory.Q.obj (bar f N)))))
    (hb : ∀ n, n < lo ∨ hi < n → IsZero
      (Note198.ComplexCohomologyModels.H n (DerivedCategory.Q.obj (bar f N)))) (d : ℕ) :
    HasProjectiveDimensionLE (ModuleCat.of A N) d ↔
      HasSignedProjectiveBound (DerivedCategory.Q.obj (bar f N)) (d:ℤ) := by
  have hDb := Note198.ComplexCohomologyModels.finite_dimensional_cohomology_in_bounded_finite_derived
    (k:=k) g hg (DerivedCategory.Q.obj (bar f N)) lo hi hc hb
  obtain ⟨P,pl,ph,hp,hpb,⟨e⟩⟩ :=
    Note198.ComplexStupidTruncation.bounded_derived_finite_projective_model
      (k:=k) g hg _ hDb
  exact module_pd_bound_iff_signed_base_bound f hf hsq N P pl ph hp hpb e.symm d
include hf hsq in
/-- Conversely an exact finite signed base-change value gives the actual
numerical module pd for a nonzero module. Zero modules retain their separate
bottom convention; no nonzero Tor edge is assumed here. -/
theorem module_projectiveDimension_eq_of_signed_base
    (P : CochainComplex (ModuleCat.{u} D) ℤ) (lo hi : ℤ)
    (hp : ∀ n, Module.Finite D (P.X n) ∧ Module.Projective D (P.X n))
    (hb : ∀ n, n < lo ∨ hi < n → IsZero (P.X n))
    (e : DerivedCategory.Q.obj (bar f N) ≅ DerivedCategory.Q.obj P) (d : ℕ)
    (hN : ¬ IsZero (ModuleCat.of A N))
    (hsigned : signedProjectiveDimension (DerivedCategory.Q.obj (bar f N)) =
      (((d:ℤ):WithTop ℤ):WithBot (WithTop ℤ))) :
    projectiveDimension (ModuleCat.of A N) = d := by
  have hbound : HasSignedProjectiveBound (DerivedCategory.Q.obj (bar f N)) (d:ℤ) :=
    (signed_pd_le_iff_bound (k:=k) P lo hi hp hb _ e.symm d).mp (le_of_eq hsigned)
  have hpd := (module_pd_bound_iff_signed_base_bound f hf hsq N P lo hi hp hb e d).mpr hbound
  apply le_antisymm ((projectiveDimension_le_iff _ d).mpr hpd)
  cases d with
  | zero => exact (projectiveDimension_ge_zero_iff _).mpr hN
  | succ d =>
    apply (projectiveDimension_ge_iff _ (d+1)).mpr
    intro hd
    have hb' := (module_pd_bound_iff_signed_base_bound f hf hsq N P lo hi hp hb e d).mp hd
    have hle := signedProjectiveDimension_le_of_bound hb'
    rw [hsigned] at hle
    have hle' : ((d+1:ℕ):ℤ) ≤ (d:ℤ) :=
      WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hle)
    omega
/-- Embed actual categorical module pd into signed extended integers.
Zero maps to bottom, infinite pd to top, and a natural finite value to
that integer. This changes the value type, not the definition of module pd. -/
def signedModuleProjectiveDimension (M : ModuleCat.{u} A) : WithBot (WithTop ℤ) :=
  WithBot.map (WithTop.map (fun n : ℕ => (n:ℤ))) (projectiveDimension M)

/-- An actual zero module gives an actual zero bar object, not merely
vanishing in a finite set of inspected degrees. -/
theorem bar_isZero_of_input_isZero (hN : IsZero (ModuleCat.of A N)) :
    IsZero (DerivedCategory.Q.obj (bar f N)) := by
  letI : Subsingleton N := ModuleCat.isZero_iff_subsingleton.mp hN
  have hsub (i : ℕ) : Subsingleton (OAI.DerivedBar.term k A N i) := by
    induction i with
    | zero =>
      change Subsingleton N
      infer_instance
    | succ i ih =>
      letI := ih
      change Subsingleton (A ⊗[k] OAI.DerivedBar.term k A N i)
      infer_instance
  have hchain (i : ℕ) : IsZero ((OAI.DerivedBar.twoSidedComplex k A D N f).X i) := by
    change IsZero (ModuleCat.of D (D ⊗[k] OAI.DerivedBar.term k A N i))
    letI := hsub i
    apply ModuleCat.isZero_iff_subsingleton.mpr
    change Subsingleton (D ⊗[k] OAI.DerivedBar.term k A N i)
    infer_instance
  have hterm (n : ℤ) : IsZero ((bar f N).X n) := by
    by_cases hn : n ≤ 0
    · let i : ℕ := (-n).toNat
      have hi : ComplexShape.embeddingDownNat.f i = n :=
        Note198.ComplexExtensionTensor.downIndex_eq n hn
      exact (hchain i).of_iso
        ((OAI.DerivedBar.twoSidedComplex k A D N f).extendXIso ComplexShape.embeddingDownNat hi)
    · exact bar_upper_zero f N n (by omega)
  have hbar : IsZero (bar f N) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply HomologicalComplex.hom_ext
    intro n
    exact (hterm n).eq_of_src _ _
  exact DerivedCategory.Q.map_isZero hbar

include hf hsq in
/-- The complete finite-model comparison includes N=0 and both extended
value conventions. Actual A-module pd and actual signed D-base-change pd
are proved equal after the explicit natural-to-integer embedding. -/
theorem signed_module_pd_eq_signed_base
    (P : CochainComplex (ModuleCat.{u} D) ℤ) (lo hi : ℤ)
    (hp : ∀ n, Module.Finite D (P.X n) ∧ Module.Projective D (P.X n))
    (hb : ∀ n, n < lo ∨ hi < n → IsZero (P.X n))
    (e : DerivedCategory.Q.obj (bar f N) ≅ DerivedCategory.Q.obj P) :
    signedModuleProjectiveDimension (ModuleCat.of A N) =
      signedProjectiveDimension (DerivedCategory.Q.obj (bar f N)) := by
  let d : ℕ := (-lo).toNat
  have hbound : HasSignedProjectiveBound (DerivedCategory.Q.obj (bar f N)) (d:ℤ) := by
    refine ⟨P,fun n => (hp n).2,⟨lo,hi,hb⟩,?_,⟨e.symm⟩⟩
    intro n hn
    have hd := Int.self_le_toNat (-lo)
    exact hb n (Or.inl (by dsimp [d] at hn; omega))
  have hd := (module_pd_bound_iff_signed_base_bound f hf hsq N P lo hi hp hb e d).mpr hbound
  have hfinite : projectiveDimension (ModuleCat.of A N) ≠ ⊤ :=
    (projectiveDimension_ne_top_iff _).mpr ⟨d,hd⟩
  generalize hdim : projectiveDimension (ModuleCat.of A N) = value
  induction value using WithBot.recBotCoe with
  | bot =>
    have hzero := (projectiveDimension_eq_bot_iff _).mp hdim
    have hz := bar_isZero_of_input_isZero f N hzero
    rw [signedProjectiveDimension_iso hz.isoZero,signedProjectiveDimension_zero]
    simp only [signedModuleProjectiveDimension,hdim]
    rfl
  | coe value =>
    induction value using WithTop.recTopCoe with
    | top => exact (hfinite hdim).elim
    | coe n =>
      rw [signed_base_eq_projectiveDimension f hf hsq N P lo hi hp hb e n hdim]
      simp only [signedModuleProjectiveDimension,hdim]
      rfl

include hf hsq in
/-- Original bounded finite-cohomology data supplies the comparison model
internally, including the zero object. -/
theorem bounded_finite_signed_module_pd_eq_signed_base
    (g : ℕ) (hg : ∀ M : ModuleCat.{u} D, HasProjectiveDimensionLE M g)
    (hDb : Note198.ComplexStupidTruncation.InBoundedFiniteDerived
      (DerivedCategory.Q.obj (bar f N))) :
    signedModuleProjectiveDimension (ModuleCat.of A N) =
      signedProjectiveDimension (DerivedCategory.Q.obj (bar f N)) := by
  obtain ⟨P,lo,hi,hp,hb,⟨e⟩⟩ :=
    Note198.ComplexStupidTruncation.bounded_derived_finite_projective_model
      (k:=k) g hg _ hDb
  exact signed_module_pd_eq_signed_base f hf hsq N P lo hi hp hb e.symm

end
end Note198.ComplexResidueBaseChange






