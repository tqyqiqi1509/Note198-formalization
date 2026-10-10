import Note198.GenericExactDimension
import OAI.Algebra.Finitistic.Bar.CountRetracts

namespace Note198.GenericPDDetection
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
open Note198.ComplexProjectiveDimension Note198.ComplexStupidTruncation
attribute [local instance] HasDerivedCategory.standard
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable [FiniteDimensional k D] [FiniteDimensional k X]
local instance (N : ModuleCat.{u} D) : Module k N :=
  DerivedBar.BimoduleTensor.scalarModule k D N
local instance (N : ModuleCat.{u} D) : IsScalarTower k D N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance (N : ModuleCat.{u} D) : Module (TrivSqZeroExt D X) N :=
  DerivedBar.ParityBridge.inflatedModule D X N
local instance (N : ModuleCat.{u} D) : IsScalarTower k (TrivSqZeroExt D X) N :=
  IsScalarTower.of_algebraMap_smul (fun a v => IsScalarTower.algebraMap_smul D a v)

/-- Every nonzero actual derived iterate gives the general lower bound,
even when A-module projective dimension is infinite. The actual count
summand is retained as a retract of the native base change. -/
theorem lower_bound_of_survival (N : ModuleCat.{u} D) [FiniteDimensional k N]
    (r : ℕ) (h : ¬ IsZero (GenericFiniteBar.iterate k D X N r)) :
    (r:ℕ) ≤ projectiveDimension (ModuleCat.of (TrivSqZeroExt D X) N) := by
  letI : FiniteDimensional k (TrivSqZeroExt D X) :=
    inferInstanceAs (FiniteDimensional k (D × X))
  obtain ⟨n,hn⟩ := DerivedBar.IterateSupport.nonzero_homology k D X N r h
  let T := (DerivedBar.ParityBridge.shiftedIterateDiagram k D X N).obj ⟨r⟩
  have hT : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} D)
      (-((n+r:ℕ):ℤ))).obj T) := by
    intro hz
    let e := ((DerivedCategory.homologyFunctor (ModuleCat.{u} D) 0).shiftIso
      (r:ℤ) (-((n+r:ℕ):ℤ)) (-(n:ℤ)) (by push_cast; omega)).app
        (GenericFiniteBar.iterate k D X N r)
    exact hn (e.isZero_iff.mp hz)
  exact NativeBaseChangeDetection.lower_bound_of_native_retract
    (TrivSqZeroExt.fstHom k D X) N
    ((DerivedBar.derivedBaseChange D (TrivSqZeroExt.fstHom k D X)).obj
      (ModuleCat.of (TrivSqZeroExt D X) N)) T (Iso.refl _)
    (DerivedBar.ParityBridge.shiftedIterateInclusion k D X N r)
    (DerivedBar.ParityBridge.shiftedIterateProjection k D X N r)
    (DerivedBar.ParityBridge.shiftedIterate_retract k D X N r)
    r (n+r) (by omega) hT

variable (g : ℕ) (hg : ∀ M : ModuleCat.{u} D, HasProjectiveDimensionLE M g)

include g hg in
/-- Actual tensor extinction gives finite pd over the actual square-zero
extension, for every finite module N. X is not assumed projective. -/
theorem finite_pd_of_extinction (N : ModuleCat.{u} D) [FiniteDimensional k N]
    (t : ℕ) (ht : IsZero (GenericFiniteBar.iterate k D X N t)) :
    projectiveDimension (ModuleCat.of (TrivSqZeroExt D X) N) < ⊤ := by
  letI : FiniteDimensional k (TrivSqZeroExt D X) :=
    inferInstanceAs (FiniteDimensional k (D × X))
  have hfinite (r : Fin t) : InBoundedFiniteDerived (GenericFiniteBar.count k D X N r) :=
    ComplexFiniteBarDimension.boundedFinite_shift _
      (GenericFiniteBar.iterate_boundedFinite k D X g hg N r) (r.val:ℤ)
  have hsum := ComplexDimensionOperations.boundedFinite_fin_biproduct t
    (fun r => GenericFiniteBar.count k D X N r) hfinite
  let e := Classical.choice (GenericFiniteBar.finite_bar k D X N t ht)
  obtain ⟨P,lo,hi,hp,hb,⟨eP⟩⟩ :=
    bounded_derived_finite_projective_model (k:=k) g hg _ hsum
  let ebar : DerivedCategory.Q.obj (ComplexResidueBaseChange.bar
      (TrivSqZeroExt.fstHom k D X) N) ≅ DerivedCategory.Q.obj P := e ≪≫ eP.symm
  let d : ℕ := (-lo).toNat
  have hbound : HasSignedProjectiveBound (DerivedCategory.Q.obj
      (ComplexResidueBaseChange.bar (TrivSqZeroExt.fstHom k D X) N)) (d:ℤ) := by
    refine ⟨P,fun n => (hp n).2,⟨lo,hi,hb⟩,?_,⟨ebar.symm⟩⟩
    intro n hn
    have hd := Int.self_le_toNat (-lo)
    exact hb n (Or.inl (by dsimp [d] at hn; omega))
  have hpd := (ComplexResidueBaseChange.module_pd_bound_iff_signed_base_bound
    (TrivSqZeroExt.fstHom k D X) (fun d => ⟨TrivSqZeroExt.inl d,rfl⟩)
    (fun a ha b hb => PDSquareZero.kernel_square_zero X a b ha hb)
    N P lo hi hp hb ebar d).mpr hbound
  exact lt_of_le_of_lt ((projectiveDimension_le_iff _ d).mpr hpd)
    (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top d))

/-- The entire general Corollary 6.2, with literal finite global
dimension and no chosen g/hg or derived-resolution certificate. The
manuscript's two-sided finite global dimension implies the left-sided
hypothesis here. The lower bound allows infinite A-module pd. -/
theorem detection_of_finite_global_dimension
    (hD : (⨆ M : ModuleCat.{u} D, projectiveDimension M) < ⊤)
    (N : ModuleCat.{u} D) [FiniteDimensional k N] :
    (∀ t : ℕ, IsZero (GenericFiniteBar.iterate k D X N t) →
      projectiveDimension (ModuleCat.of (TrivSqZeroExt D X) N) < ⊤) ∧
    (∀ r : ℕ, ¬ IsZero (GenericFiniteBar.iterate k D X N r) →
      (r:ℕ) ≤ projectiveDimension (ModuleCat.of (TrivSqZeroExt D X) N)) := by
  obtain ⟨g,hg⟩ := (Note198.finite_global_dimension_iff_uniform_bound.{u,u} D).mp hD
  exact ⟨fun t ht => finite_pd_of_extinction k D X g hg N t ht,
    fun r hr => lower_bound_of_survival k D X N r hr⟩
end
end Note198.GenericPDDetection

