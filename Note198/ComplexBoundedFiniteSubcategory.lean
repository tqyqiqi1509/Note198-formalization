import Note198.ComplexCohomologyModels
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.Retract

namespace Note198.ComplexBoundedFiniteSubcategory
noncomputable section
open CategoryTheory CategoryTheory.Limits
open ComplexStupidTruncation ComplexProjectiveModels ComplexCohomologyModels
open scoped ModuleCat.Algebra ZeroObject
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} A)]
variable (g : ℕ) (hg : ∀ M : ModuleCat.{u} A, HasProjectiveDimensionLE M g)

/-- The finite-term representative definition has its genuine bounded
finite-dimensional cohomology meaning; cohomology is restricted along
the actual algebra map k -> A. -/
theorem bounded_finite_cohomology
    (Z : DerivedCategory (ModuleCat.{u} A)) (hZ : InBoundedFiniteDerived Z) :
    ∃ lo hi : ℤ,
      (∀ n, FiniteDimensional k
        ((ModuleCat.restrictScalars (algebraMap k A)).obj (H n Z))) ∧
      (∀ n, n < lo ∨ hi < n → IsZero (H n Z)) := by
  obtain ⟨K,lo,hi,hf,hb,⟨e⟩⟩ := hZ
  let F := ModuleCat.restrictScalars (algebraMap k A)
  let eH (n : ℤ) : H n Z ≅ K.homology n :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n).app K
  refine ⟨lo,hi,?_,?_⟩
  · intro n
    letI : Module.Finite A (K.X n) := hf n
    letI : IsScalarTower k A (K.X n) :=
      IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := K.X n)
        (fun _ _ => rfl)
    letI : FiniteDimensional k (K.X n) := Module.Finite.trans A (K.X n)
    let termScalarIdentity : K.X n →ₗ[k] F.obj (K.X n) :=
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    letI : FiniteDimensional k (F.obj (K.X n)) :=
      Module.Finite.of_surjective termScalarIdentity (fun x => ⟨x,rfl⟩)
    letI : FiniteDimensional k (F.obj (K.sc n).X₂) := by
      change FiniteDimensional k (F.obj (K.X n))
      infer_instance
    letI : FiniteDimensional k (F.obj (K.sc n).cycles) :=
      FiniteDimensional.of_injective (F.map (K.sc n).iCycles).hom
        ((ModuleCat.mono_iff_injective _).mp inferInstance)
    letI : FiniteDimensional k (F.obj (K.homology n)) :=
      FiniteDimensional.of_surjective (F.map (K.sc n).homologyπ).hom
        ((ModuleCat.epi_iff_surjective _).mp inferInstance)
    exact FiniteDimensional.of_injective (F.map (eH n).hom).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  · intro n hn
    exact ((eH n).isZero_iff).mpr
      ((K.sc n).isZero_homology_of_isZero_X₂ (hb n hn))

include g hg in
/-- The original cohomological scope and the actual bounded finite-module
essential image agree, under the proved global module bound. -/
theorem bounded_finite_iff_cohomology (Z : DerivedCategory (ModuleCat.{u} A)) :
    InBoundedFiniteDerived Z ↔
      ∃ lo hi : ℤ,
        (∀ n, FiniteDimensional k
          ((ModuleCat.restrictScalars (algebraMap k A)).obj (H n Z))) ∧
        (∀ n, n < lo ∨ hi < n → IsZero (H n Z)) := by
  constructor
  · exact bounded_finite_cohomology (k:=k) Z
  · rintro ⟨lo,hi,hf,hb⟩
    exact finite_dimensional_cohomology_in_bounded_finite_derived
      (k:=k) g hg Z lo hi hf hb

theorem bounded_finite_of_projective_model
    (Z : DerivedCategory (ModuleCat.{u} A)) (hZ : HasFiniteProjectiveModel Z) :
    InBoundedFiniteDerived Z := by
  obtain ⟨P,lo,hi,hp,hb,e⟩ := hZ
  exact ⟨P,lo,hi,fun n => (hp n).1,hb,e⟩

include k g hg in
/-- Retracts are checked on actual cohomology, then represented internally. -/
theorem bounded_finite_retract
    {Z W : DerivedCategory (ModuleCat.{u} A)} (r : Retract Z W)
    (hW : InBoundedFiniteDerived W) : InBoundedFiniteDerived Z := by
  obtain ⟨lo,hi,hf,hb⟩ := bounded_finite_cohomology (k:=k) W hW
  let F := ModuleCat.restrictScalars (algebraMap k A)
  apply finite_dimensional_cohomology_in_bounded_finite_derived
    (k:=k) g hg Z lo hi
  · intro n
    let rH := r.map (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n)
    letI : FiniteDimensional k (F.obj (H n W)) := hf n
    exact FiniteDimensional.of_injective (F.map rH.i).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  · intro n hn
    let rH := r.map (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n)
    apply (IsZero.iff_id_eq_zero _).mpr
    rw [← rH.retract, (hb n hn).eq_of_tgt rH.i 0, zero_comp]

include k g hg in
theorem bounded_finite_stable_retracts :
    ObjectProperty.IsStableUnderRetracts (InBoundedFiniteDerived (A:=A) :
      ObjectProperty (DerivedCategory (ModuleCat.{u} A))) :=
  ⟨fun r h => bounded_finite_retract (k:=k) g hg r h⟩

include k g hg in
/-- Actual bounded finite projective models supply the distinguished-triangle
and shift closure of Db of finite modules. -/
theorem bounded_finite_triangulated :
    ObjectProperty.IsTriangulated (InBoundedFiniteDerived (A:=A) :
      ObjectProperty (DerivedCategory (ModuleCat.{u} A))) := by
  let Db : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) := InBoundedFiniteDerived
  letI : Db.IsStableUnderRetracts := bounded_finite_stable_retracts (k:=k) g hg
  have hz : Db 0 := by
    refine ⟨0,0,0,?_,?_,?_⟩
    · intro n
      have hn : IsZero ((0 : CochainComplex (ModuleCat.{u} A) ℤ).X n) :=
        (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n).map_isZero
          (isZero_zero (CochainComplex (ModuleCat.{u} A) ℤ))
      letI := ModuleCat.subsingleton_of_isZero hn
      infer_instance
    · intro n _
      exact (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n).map_isZero
        (isZero_zero (CochainComplex (ModuleCat.{u} A) ℤ))
    · exact ⟨(DerivedCategory.Q.map_isZero (isZero_zero _)).isoZero⟩
  letI : Db.ContainsZero := ⟨⟨0,isZero_zero _,hz⟩⟩
  letI : Db.IsStableUnderShift ℤ :=
    { isStableUnderShiftBy := fun s =>
        { le_shift := fun Z hZ => bounded_finite_of_projective_model _
            (model_shift (bounded_derived_finite_projective_model (k:=k) g hg Z hZ) s) } }
  letI : Db.IsTriangulatedClosed₂ :=
    ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ =>
      bounded_finite_of_projective_model _ (model_triangle_middle T hT
        (bounded_derived_finite_projective_model (k:=k) g hg _ h₁)
        (bounded_derived_finite_projective_model (k:=k) g hg _ h₃)))
  exact {
    toContainsZero := inferInstance
    toIsStableUnderShift := inferInstance
    toIsTriangulatedClosed₂ := inferInstance }

end
end Note198.ComplexBoundedFiniteSubcategory


