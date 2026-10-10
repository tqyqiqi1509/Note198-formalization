import Note198.ComplexResidueBaseChange
import Note198.ComplexDimensionOperations

namespace Note198.ComplexFiniteBarDimension
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
open Note198.ComplexProjectiveDimension Note198.ComplexStupidTruncation
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable [FiniteDimensional k A] [FiniteDimensional k D]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} D)]
variable (g : ℕ) (hg : ∀ M : ModuleCat.{u} D, HasProjectiveDimensionLE M g)

theorem boundedFinite_shift (Z : DerivedCategory (ModuleCat.{u} D))
    (hZ : InBoundedFiniteDerived Z) (s : ℤ) : InBoundedFiniteDerived (Z⟦s⟧) := by
  obtain ⟨K,lo,hi,hf,hb,⟨e⟩⟩ := hZ
  refine ⟨K⟦s⟧,lo-s,hi-s,?_,?_,?_⟩
  · intro n
    exact hf (n+s)
  · intro n hn
    exact hb (n+s) (by omega)
  · exact ⟨(DerivedCategory.Q.commShiftIso s).app K ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} D)) s).mapIso e⟩

include g hg in
/-- Actual finite bar decompositions give the manuscript's precise maximum,
including bottom dimensions of zero summands. The decomposition is an actual
derived isomorphism, not a cohomology dimension or numerical certificate. -/
theorem signed_base_finite_max
    (f : A →ₐ[k] D) (N : Type u) [AddCommGroup N] [Module k N] [Module A N]
    [IsScalarTower k A N] (r : ℕ)
    (Z : Fin r → DerivedCategory (ModuleCat.{u} D)) (s : Fin r → ℤ)
    (hZ : ∀ i, InBoundedFiniteDerived (Z i))
    (e : DerivedCategory.Q.obj (ComplexResidueBaseChange.bar f N) ≅
      ⨁ fun i => (Z i)⟦s i⟧) :
    signedProjectiveDimension (DerivedCategory.Q.obj (ComplexResidueBaseChange.bar f N)) =
      ⨆ i, signedProjectiveDimension (Z i) + (((s i):WithTop ℤ):WithBot (WithTop ℤ)) := by
  rw [signedProjectiveDimension_iso e,
    ComplexDimensionOperations.signedProjectiveDimension_fin_biproduct k g hg r
      (fun i => (Z i)⟦s i⟧) (fun i => boundedFinite_shift (Z i) (hZ i) (s i))]
  simp only [signedProjectiveDimension_shift]

include g hg in
/-- The actual finite maximum determines the numerical A-module pd. Its
projective D-model is constructed internally; no minimality or Tor edge is
supplied. The nonzero input has finite integer maximum d. -/
theorem module_pd_eq_finite_max
    (f : A →ₐ[k] D) (hf : Function.Surjective f)
    (hsq : ∀ a ∈ RingHom.ker f.toRingHom, ∀ b ∈ RingHom.ker f.toRingHom, a*b=0)
    (N : Type u) [AddCommGroup N] [Module k N] [Module A N]
    [IsScalarTower k A N] [FiniteDimensional k N]
    (hN : ¬ IsZero (ModuleCat.of A N)) (r : ℕ)
    (Z : Fin r → DerivedCategory (ModuleCat.{u} D)) (s : Fin r → ℤ)
    (hZ : ∀ i, InBoundedFiniteDerived (Z i))
    (e : DerivedCategory.Q.obj (ComplexResidueBaseChange.bar f N) ≅
      ⨁ fun i => (Z i)⟦s i⟧) (d : ℕ)
    (hmax : (⨆ i, signedProjectiveDimension (Z i) +
      (((s i):WithTop ℤ):WithBot (WithTop ℤ))) =
        (((d:ℤ):WithTop ℤ):WithBot (WithTop ℤ))) :
    projectiveDimension (ModuleCat.of A N) = d := by
  have hDb := ComplexDimensionOperations.boundedFinite_fin_biproduct r
    (fun i => (Z i)⟦s i⟧) (fun i => boundedFinite_shift (Z i) (hZ i) (s i))
  obtain ⟨P,lo,hi,hp,hb,⟨eP⟩⟩ :=
    bounded_derived_finite_projective_model (k:=k) g hg _ hDb
  exact ComplexResidueBaseChange.module_projectiveDimension_eq_of_signed_base
    f hf hsq N P lo hi hp hb (e ≪≫ eP.symm) d hN
    ((signed_base_finite_max g hg f N r Z s hZ e).trans hmax)
end
end Note198.ComplexFiniteBarDimension
