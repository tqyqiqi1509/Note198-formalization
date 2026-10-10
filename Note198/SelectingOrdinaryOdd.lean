import Note198.SelectingOrdinaryQ
import Note198.SelectingOrdinaryIteration
import OAI.Algebra.Finitistic.Ordinary.OrdinaryXBlockComparison

namespace Note198.SelectingOrdinaryOdd
noncomputable section
open CategoryTheory OAI OAI.LittleFinitistic
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
open SelectingOrdinaryAlgebra SelectingOrdinarySimulation

abbrev secondComplex := (ProductModules.secondInflation (QuadraticEncoding.B E.relations)
  (SelectingOrdinaryQ.Eblock E S)).mapHomologicalComplex (.up ℤ)

theorem second_inverts : (HomologicalComplex.quasiIso
    (ModuleCat.{u} (SelectingOrdinaryQ.Eblock E S)) (.up ℤ)).IsInvertedBy
    (secondComplex E S ⋙ DerivedCategory.Q) := by
  intro C C' f hf
  letI : QuasiIso f := hf
  haveI : QuasiIso ((secondComplex E S).map f) :=
    (RestrictionHomology.quasiIso_iff (RingHom.snd (QuadraticEncoding.B E.relations)
      (SelectingOrdinaryQ.Eblock E S)) f).mpr inferInstance
  exact (inferInstance : IsIso (DerivedCategory.Q.map ((secondComplex E S).map f)))

def second : DerivedCategory (ModuleCat.{u} (SelectingOrdinaryQ.Eblock E S)) ⥤
    DerivedCategory (ModuleCat.{u} (D E S)) :=
  Localization.lift (secondComplex E S ⋙ DerivedCategory.Q) (second_inverts E S) DerivedCategory.Q

def secondComparison : DerivedCategory.Q ⋙ second E S ≅ secondComplex E S ⋙ DerivedCategory.Q :=
  Localization.fac (secondComplex E S ⋙ DerivedCategory.Q) (second_inverts E S) DerivedCategory.Q

def firstTensorComparison (Z : CochainComplex (ModuleCat.{u} (QuadraticEncoding.B E.relations)) ℤ) :
    (ordinary E S).obj ((first E S).obj (DerivedCategory.Q.obj Z)) ≅
      (second E S).obj ((SelectingOrdinaryQ.derived E S).obj (DerivedCategory.Q.obj Z)) :=
  (ordinary E S).mapIso ((BlockModule.derivedFirstComparison _ _).app Z) ≪≫
  (OrdinarySimulation.XResolution.derivedTensorComparison
    (SelectingRectification.bimodule E S) (a E S) (length E S)).app
      (BlockModule.firstComplex _ _ Z) ≪≫
  DerivedCategory.Q.mapIso (OrdinarySimulation.XResolution.firstBlockComparison
    (SelectingRectification.bimodule E S) (a E S) (length E S) Z) ≪≫
  ((secondComparison E S).app ((SelectingOrdinaryQ.complexFunctor E S).obj Z)).symm ≪≫
  (second E S).mapIso ((SelectingOrdinaryQ.comparison E S).app Z).symm

def firstTensorObject (Y : DerivedCategory (ModuleCat.{u} (QuadraticEncoding.B E.relations))) :
    (ordinary E S).obj ((first E S).obj Y) ≅
      (second E S).obj ((SelectingOrdinaryQ.derived E S).obj Y) :=
  let e := DerivedCategory.Q.objObjPreimageIso Y
  (ordinary E S).mapIso ((first E S).mapIso e.symm) ≪≫
  firstTensorComparison E S (DerivedCategory.Q.objPreimage Y) ≪≫
  (second E S).mapIso ((SelectingOrdinaryQ.derived E S).mapIso e)

theorem first_tensor_isomorphism (Y : DerivedCategory (ModuleCat.{u} (QuadraticEncoding.B E.relations))) :
    Nonempty ((ordinary E S).obj ((first E S).obj Y) ≅
      (second E S).obj ((SelectingOrdinaryQ.derived E S).obj Y)) :=
  ⟨firstTensorObject E S Y⟩

/-- The actual odd iterate is second-block inflation of actual degree-zero
projective tensor applied to the same full binomial object as the even iterate. -/
theorem odd_binomial (j : ℕ) (Y : SelectingIteration.Family (k := k) (R := R)) :
    Nonempty (((ordinary E S).obj^[2*j+1]) (SelectingOrdinaryIteration.evaluated E S Y) ≅
      (second E S).obj ((SelectingOrdinaryQ.derived E S).obj
        (ExternalTensor.Binomial.binomialObject (b E S) 3 j
          (SelectingIteration.evaluation E (((SelectingIteration.selected S)^[j]) Y))))) := by
  rw [Function.iterate_succ_apply']
  exact ⟨(ordinary E S).mapIso (Classical.choice
    (SelectingOrdinaryIteration.even_binomial E S j Y)) ≪≫ firstTensorObject E S _⟩
end
end Note198.SelectingOrdinaryOdd
