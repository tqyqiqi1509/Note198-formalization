import Note198.ComplexStupidTruncation
import OAI.Algebra.Finitistic.Localization.DerivedTruncationCohomology

namespace Note198.ComplexCohomologyModels
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open ComplexProjectiveModels ComplexStupidTruncation OAI.LittleFinitistic
open scoped ModuleCat.Algebra
universe u
variable {A : Type u} [Ring A] [HasDerivedCategory.{u+1} (ModuleCat.{u} A)]
abbrev H (n : ℤ) (Z : DerivedCategory (ModuleCat.{u} A)) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj Z
abbrev t := (DerivedCategory.TStructure.t :
  CategoryTheory.Triangulated.TStructure (DerivedCategory (ModuleCat.{u} A)))
abbrev lower (b : ℤ) (Z : DerivedCategory (ModuleCat.{u} A)) := (t.truncLT b).obj Z
abbrev upper (b : ℤ) (Z : DerivedCategory (ModuleCat.{u} A)) := (t.truncGE b).obj Z
abbrev triangle (b : ℤ) (Z : DerivedCategory (ModuleCat.{u} A)) := (t.triangleLTGE b).obj Z

/-- Actual cohomology of the lower truncation agrees below the cutoff. -/
def lowerHomologyIso (b : ℤ) (Z : DerivedCategory (ModuleCat.{u} A))
    (n : ℤ) (hn : n < b) : H n (lower b Z) ≅ H n Z := by
  let f := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map ((t.truncLTι b).app Z)
  have h0 := DerivedCategory.isZero_of_isGE (upper b Z) b n hn
  have h1 := DerivedCategory.isZero_of_isGE (upper b Z) b (n-1) (by omega)
  haveI : Mono f :=
    (DerivedCategory.HomologySequence.exact₁ (triangle b Z)
      (t.triangleLTGE_distinguished b Z) (n-1) n (by omega)).mono_g (h1.eq_of_src _ _)
  haveI : Epi f :=
    (DerivedCategory.HomologySequence.exact₂ (triangle b Z)
      (t.triangleLTGE_distinguished b Z) n).epi_f (h0.eq_of_tgt _ _)
  letI : IsIso f := isIso_of_mono_of_epi f
  exact asIso f

/-- Actual cohomology of the upper truncation agrees above the cutoff. -/
def upperHomologyIso (b : ℤ) (Z : DerivedCategory (ModuleCat.{u} A))
    (n : ℤ) (hn : b ≤ n) : H n Z ≅ H n (upper b Z) := by
  let f := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map ((t.truncGEπ b).app Z)
  have h0 := DerivedCategory.isZero_of_isLE (lower b Z) (b-1) n (by omega)
  have h1 := DerivedCategory.isZero_of_isLE (lower b Z) (b-1) (n+1) (by omega)
  haveI : Mono f :=
    (DerivedCategory.HomologySequence.exact₂ (triangle b Z)
      (t.triangleLTGE_distinguished b Z) n).mono_g (h0.eq_of_src _ _)
  haveI : Epi f :=
    (DerivedCategory.HomologySequence.exact₃ (triangle b Z)
      (t.triangleLTGE_distinguished b Z) n (n+1) rfl).epi_f (h1.eq_of_tgt _ _)
  letI : IsIso f := isIso_of_mono_of_epi f
  exact asIso f

variable {k : Type u} [Field k] [Algebra k A] [FiniteDimensional k A]
variable (g : ℕ) (hg : ∀ M : ModuleCat.{u} A, HasProjectiveDimensionLE M g)

include k g hg in
/-- Postnikov induction on a genuine cohomology window constructs a finite
projective representative. Terms of an arbitrary input representative are
not assumed finite or projective. -/
theorem finite_cohomology_model_by_length (r : ℕ) :
    ∀ (Z : DerivedCategory (ModuleCat.{u} A)) (lo : ℤ),
      (∀ n, Module.Finite A (H n Z)) →
      (∀ n, n < lo ∨ lo + (r : ℤ) < n → IsZero (H n Z)) →
      HasFiniteProjectiveModel Z := by
  induction r with
  | zero =>
    intro Z lo hf hb
    letI : Z.IsGE lo := (DerivedCategory.isGE_iff Z lo).mpr (fun n hn => hb n (Or.inl hn))
    letI : Z.IsLE lo := (DerivedCategory.isLE_iff Z lo).mpr
      (fun n hn => hb n (Or.inr (by simpa using hn)))
    letI := hf lo
    have hmodel := finite_module_stalk_model (k:=k) g hg (H lo Z) lo
    exact model_of_iso hmodel (DerivedTruncation.singleIso Z lo).symm
  | succ r ih =>
    intro Z lo hf hb
    let b : ℤ := lo + ((r+1 : ℕ) : ℤ)
    letI : Z.IsLE b := (DerivedCategory.isLE_iff Z b).mpr
      (fun n hn => hb n (Or.inr hn))
    have hfiniteLower (n : ℤ) : Module.Finite A (H n (lower b Z)) := by
      by_cases hn : n < b
      · letI := hf n
        exact Module.Finite.equiv (lowerHomologyIso b Z n hn).symm.toLinearEquiv
      · have hz := DerivedCategory.isZero_of_isLE (lower b Z) (b-1) n (by omega)
        letI := ModuleCat.subsingleton_of_isZero hz
        infer_instance
    have hboundLower (n : ℤ) (hn : n < lo ∨ lo+(r:ℤ) < n) :
        IsZero (H n (lower b Z)) := by
      by_cases hnb : n < b
      · apply (lowerHomologyIso b Z n hnb).isZero_iff.mpr
        apply hb n
        rcases hn with hn | hn
        · exact Or.inl hn
        · dsimp [b] at hnb
          push_cast at hnb
          omega
      · exact DerivedCategory.isZero_of_isLE (lower b Z) (b-1) n (by omega)
    have hlower := ih (lower b Z) lo hfiniteLower hboundLower
    letI : (upper b Z).IsLE b := by infer_instance
    let eupper : upper b Z ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} A) b).obj (H b Z) :=
      DerivedTruncation.singleIso (upper b Z) b ≪≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) b).mapIso (upperHomologyIso b Z b le_rfl).symm
    letI := hf b
    have hupper := model_of_iso (finite_module_stalk_model (k:=k) g hg (H b Z) b) eupper.symm
    exact model_triangle_middle (triangle b Z) (t.triangleLTGE_distinguished b Z) hlower hupper

include k g hg in
/-- The full manuscript cohomology scope, including an empty window. -/
theorem finite_cohomology_projective_model
    (Z : DerivedCategory (ModuleCat.{u} A)) (lo hi : ℤ)
    (hf : ∀ n, Module.Finite A (H n Z))
    (hb : ∀ n, n < lo ∨ hi < n → IsZero (H n Z)) : HasFiniteProjectiveModel Z := by
  apply finite_cohomology_model_by_length (k:=k) g hg (hi-lo).toNat Z lo hf
  intro n hn
  apply hb n
  rcases hn with hn | hn
  · exact Or.inl hn
  · have h := Int.self_le_toNat (hi-lo)
    exact Or.inr (by omega)

include k g hg in
/-- In particular bounded finite cohomology has an actual bounded complex
of finite modules as representative: the claimed domain bridge is proved. -/
theorem finite_cohomology_in_bounded_finite_derived
    (Z : DerivedCategory (ModuleCat.{u} A)) (lo hi : ℤ)
    (hf : ∀ n, Module.Finite A (H n Z))
    (hb : ∀ n, n < lo ∨ hi < n → IsZero (H n Z)) : InBoundedFiniteDerived Z := by
  obtain ⟨P,pl,ph,hp,hpb,he⟩ := finite_cohomology_projective_model (k:=k) g hg Z lo hi hf hb
  exact ⟨P,pl,ph,fun n => (hp n).1,hpb,he⟩

include g hg in
/-- Input finite-dimensional cohomology is sufficient, through the actual
scalar restriction rather than a finite-term assumption. -/
theorem finite_dimensional_cohomology_in_bounded_finite_derived
    (Z : DerivedCategory (ModuleCat.{u} A)) (lo hi : ℤ)
    (hf : ∀ n, FiniteDimensional k
      ((ModuleCat.restrictScalars (algebraMap k A)).obj (H n Z)))
    (hb : ∀ n, n < lo ∨ hi < n → IsZero (H n Z)) : InBoundedFiniteDerived Z := by
  apply finite_cohomology_in_bounded_finite_derived (k:=k) g hg Z lo hi _ hb
  intro n
  letI : Module.Finite k (H n Z) := hf n
  exact Module.Finite.of_restrictScalars_finite k A (H n Z)

include g hg in
/-- Exact residue detection now covers the original bounded finite
cohomology scope and constructs its representative internally. -/
theorem finite_cohomology_exact_residue_sup
    (Z : DerivedCategory (ModuleCat.{u} A)) (lo hi : ℤ)
    (hf : ∀ n, FiniteDimensional k
      ((ModuleCat.restrictScalars (algebraMap k A)).obj (H n Z)))
    (hb : ∀ n, n < lo ∨ hi < n → IsZero (H n Z)) :
    ∃ P : CochainComplex (ModuleCat.{u} A) ℤ,
      Nonempty (DerivedCategory.Q.obj P ≅ Z) ∧
      ComplexProjectiveDimension.signedProjectiveDimension Z =
        sSup ((fun d : ℤ => ((d : WithTop ℤ) : WithBot (WithTop ℤ))) ''
          residueDegreeSet (k:=k) P) :=
  bounded_derived_exact_residue_sup (k:=k) g hg Z
    (finite_dimensional_cohomology_in_bounded_finite_derived (k:=k) g hg Z lo hi hf hb)
end
end Note198.ComplexCohomologyModels
