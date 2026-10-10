import Note198.SelectingOrdinaryOdd
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

namespace Note198.SelectingOrdinaryQ
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI.LittleFinitistic
attribute [local instance] HasDerivedCategory.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)

instance exact_limits : PreservesFiniteLimits (functor E S) := by
  letI := preserves_homology E S
  exact Functor.preservesFiniteLimits_of_preservesHomology _
instance exact_colimits : PreservesFiniteColimits (functor E S) := by
  letI := preserves_homology E S
  exact Functor.preservesFiniteColimits_of_preservesHomology _
instance derived_lifting : Localization.Lifting DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} (QuadraticEncoding.B E.relations)) (.up ℤ))
    (complexFunctor E S ⋙ DerivedCategory.Q) (derived E S) := ⟨comparison E S⟩

def exactIso : derived E S ≅ (functor E S).mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} (QuadraticEncoding.B E.relations)) (.up ℤ))
    (complexFunctor E S ⋙ DerivedCategory.Q) (complexFunctor E S ⋙ DerivedCategory.Q)
    (derived E S) (functor E S).mapDerivedCategory (Iso.refl _)

instance derived_additive : (derived E S).Additive :=
  Functor.additive_of_iso (exactIso E S).symm
instance derived_commShift : (derived E S).CommShift ℤ :=
  Functor.CommShift.ofIso (exactIso E S).symm ℤ

def stalkIso (M : ModuleCat.{u} (QuadraticEncoding.B E.relations)) (n : ℤ) :
    (derived E S).obj ((DerivedCategory.singleFunctor _ n).obj M) ≅
      (DerivedCategory.singleFunctor _ n).obj ((functor E S).obj M) :=
  (exactIso E S).app _ ≪≫ ((functor E S).mapDerivedCategorySingleFunctor n).app M

theorem stalk_isomorphism (M : ModuleCat.{u} (QuadraticEncoding.B E.relations)) (n : ℤ) :
    Nonempty ((derived E S).obj ((DerivedCategory.singleFunctor _ n).obj M) ≅
      (DerivedCategory.singleFunctor _ n).obj ((functor E S).obj M)) := ⟨stalkIso E S M n⟩
end
end Note198.SelectingOrdinaryQ

namespace Note198.SelectingOrdinaryOdd
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI.LittleFinitistic
attribute [local instance] HasDerivedCategory.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
abbrev secondFunctor : ModuleCat.{u} (SelectingOrdinaryQ.Eblock E S) ⥤
    ModuleCat.{u} (SelectingOrdinaryAlgebra.D E S) :=
  ProductModules.secondInflation.{u,u} (QuadraticEncoding.B E.relations)
    (SelectingOrdinaryQ.Eblock E S)
instance second_exact_limits : PreservesFiniteLimits (secondFunctor E S) := by
  letI : (secondFunctor E S).PreservesHomology := RestrictionHomology.preservesHomology.{u}
    (RingHom.snd (QuadraticEncoding.B E.relations) (SelectingOrdinaryQ.Eblock E S))
  exact Functor.preservesFiniteLimits_of_preservesHomology _
instance second_exact_colimits : PreservesFiniteColimits (secondFunctor E S) := by
  letI : (secondFunctor E S).PreservesHomology := RestrictionHomology.preservesHomology.{u}
    (RingHom.snd (QuadraticEncoding.B E.relations) (SelectingOrdinaryQ.Eblock E S))
  exact Functor.preservesFiniteColimits_of_preservesHomology _
instance second_lifting : Localization.Lifting DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} (SelectingOrdinaryQ.Eblock E S)) (.up ℤ))
    (secondComplex E S ⋙ DerivedCategory.Q) (second E S) := ⟨secondComparison E S⟩
def secondExactIso : second E S ≅ (secondFunctor E S).mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} (SelectingOrdinaryQ.Eblock E S)) (.up ℤ))
    (secondComplex E S ⋙ DerivedCategory.Q) (secondComplex E S ⋙ DerivedCategory.Q)
    (second E S) (secondFunctor E S).mapDerivedCategory (Iso.refl _)
instance second_additive : (second E S).Additive := Functor.additive_of_iso (secondExactIso E S).symm
instance second_commShift : (second E S).CommShift ℤ :=
  Functor.CommShift.ofIso (secondExactIso E S).symm ℤ
def secondStalkIso (M : ModuleCat.{u} (SelectingOrdinaryQ.Eblock E S)) (n : ℤ) :
    (second E S).obj ((DerivedCategory.singleFunctor _ n).obj M) ≅
      (DerivedCategory.singleFunctor _ n).obj ((secondFunctor E S).obj M) :=
  (secondExactIso E S).app _ ≪≫ ((secondFunctor E S).mapDerivedCategorySingleFunctor n).app M
theorem second_stalk_isomorphism (M : ModuleCat.{u} (SelectingOrdinaryQ.Eblock E S)) (n : ℤ) :
    Nonempty ((second E S).obj ((DerivedCategory.singleFunctor _ n).obj M) ≅
      (DerivedCategory.singleFunctor _ n).obj ((secondFunctor E S).obj M)) := ⟨secondStalkIso E S M n⟩
end
end Note198.SelectingOrdinaryOdd
