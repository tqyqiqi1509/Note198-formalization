import Note198.SafeResidueBaseBar
import OAI.Algebra.Finitistic.Bar.DerivedTensorBarSplitting

namespace Note198.NativeBaseChangeDetection
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
attribute [local instance] HasDerivedCategory.standard
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A]
  [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)
variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N]
  [IsScalarTower k A N]

/-- The native derived base change and its concrete two-sided bar model
are compared on their actual complex representatives. -/
def barComparison :
    (DerivedBar.derivedBaseChange D f).obj (ModuleCat.of A N) ≅
      PDBarQuotient.baseDerived f N :=
  DerivedBar.derivedBaseChangeBarIso D f N ≪≫
    (DerivedBar.integerQ D).mapIso (DerivedBar.tensorBarIso k A D N f)

/-- The finite-pd detection consumer uses the native derived functor,
the actual residue-module associativity and all D-modules in its global bound. -/
theorem finite_pd_of_native_bounded
    [FiniteDimensional k A] [FiniteDimensional k N]
    (hf : Function.Surjective f)
    (hsq : ∀ a ∈ RingHom.ker f.toRingHom,
      ∀ b ∈ RingHom.ker f.toRingHom, a*b=0)
    (g : ℕ) (hg : ∀ M : ModuleCat.{u} D, HasProjectiveDimensionLE M g)
    (h : ∃ b : ℕ, ∀ n, b < n → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))).obj
        ((DerivedBar.derivedBaseChange D f).obj (ModuleCat.of A N)))) :
    projectiveDimension (ModuleCat.of A N) < ⊤ :=
  SafeResidueAssociativity.finite_pd_of_base_derived_iso f N hf hsq g hg _
    (barComparison f N).symm h

/-- A genuine nonzero cohomology group of a retract of native base change
gives the lower bound, retaining its inclusion and projection. -/
theorem lower_bound_of_native_retract
    [FiniteDimensional k A] [FiniteDimensional k N]
    (Z T : DerivedCategory (ModuleCat.{u} D))
    (e : (DerivedBar.derivedBaseChange D f).obj (ModuleCat.of A N) ≅ Z)
    (i : T ⟶ Z) (p : Z ⟶ T) (hip : i ≫ p = 𝟙 T)
    (r n : ℕ) (hrn : r ≤ n)
    (h : ¬ IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat D) (-(n : ℤ))).obj T)) :
    r ≤ projectiveDimension (ModuleCat.of A N) :=
  PDBarQuotient.lower_bound_of_base_derived_retract f N Z T
    ((barComparison f N).symm ≪≫ e) i p hip r n hrn h

end
end Note198.NativeBaseChangeDetection
