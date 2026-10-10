import Note198.SelectingOrdinaryOddSplit
import OAI.Algebra.Finitistic.Ordinary.OrdinaryFirstDerivedCompatibility

namespace Note198.SelectingOrdinaryEvenSplit
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
open SelectingIteration SelectingOrdinarySimulation

abbrev firstFunctor := ProductModules.firstInflation (QuadraticEncoding.B E.relations)
  (SelectingOrdinaryQ.Eblock E S)
abbrev firstModule (Y : Family (k := k) (R := R)) :=
  (firstFunctor E S).obj (SelectingOrdinaryOddSplit.input E Y)

def firstStalkIso (M : ModuleCat.{u} (QuadraticEncoding.B E.relations)) (n : ℤ) :
    (first E S).obj ((DerivedCategory.singleFunctor _ n).obj M) ≅
      (DerivedCategory.singleFunctor _ n).obj ((firstFunctor E S).obj M) :=
  (BlockModule.derivedFirstIso _ _).app _ ≪≫
    ((firstFunctor E S).mapDerivedCategorySingleFunctor n).app M

def evaluatedStalkIso (Y : Family (k := k) (R := R)) :
    SelectingOrdinaryIteration.evaluated E S Y ≅
      (DerivedCategory.singleFunctor _ 0).obj (firstModule E S Y) :=
  firstStalkIso E S (SelectingOrdinaryOddSplit.input E Y) 0

/-- The even iterate retains every binomial multiplicity and is expressed
as shifts of actual first-block inflated modules. -/
theorem even_shifted_modules (j : ℕ) (Y : Family (k := k) (R := R)) :
    Nonempty (((ordinary E S).obj^[2*j]) (SelectingOrdinaryIteration.evaluated E S Y) ≅
      ExternalTensor.Binomial.binomialObject (SelectingOrdinaryAlgebra.b E S) 3 j
        ((DerivedCategory.singleFunctor _ 0).obj
          (firstModule E S (((selected S)^[j]) Y)))) := by
  let Z := ((selected S)^[j]) Y
  exact ⟨Classical.choice (SelectingOrdinaryIteration.even_binomial E S j Y) ≪≫
    Note198.mapBinomial (first E S) (SelectingOrdinaryAlgebra.b E S) 3 j
      (evaluation E Z) ≪≫
    Note198.binomialMapIso (SelectingOrdinaryAlgebra.b E S) 3 j
      (evaluatedStalkIso E S Z)⟩

/-- The original first-block tensor input is an actual stalk module. -/
theorem first_stalk_isomorphism (Y : Family (k := k) (R := R)) :
    Nonempty (SelectingOrdinaryIteration.evaluated E S Y ≅
      (DerivedCategory.singleFunctor _ 0).obj (firstModule E S Y)) :=
  ⟨evaluatedStalkIso E S Y⟩

theorem first_module_dimension (Y : Family (k := k) (R := R)) :
    projectiveDimension (firstModule E S Y) =
      projectiveDimension (SelectingOrdinaryOddSplit.input E Y) :=
  ProductProjectiveDimension.firstInflation_dimension_eq _ _ _

end
end Note198.SelectingOrdinaryEvenSplit
