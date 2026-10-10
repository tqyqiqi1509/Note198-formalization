import Note198.SelectingOrdinaryQStructures

namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
attribute [local instance] HasDerivedCategory.standard HasExt.standard

section BinomialFunctor
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
    [HasShift C ℤ] {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteBiproducts D]
    [HasShift D ℤ]
variable [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive]

def mapBinomial (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
    (b d : ℤ) (j : ℕ) (X : C) :
    F.obj (ExternalTensor.Binomial.binomialObject b d j X) ≅
      ExternalTensor.Binomial.binomialObject b d j (F.obj X) :=
  F.mapBiproduct _ ≪≫ biproduct.mapIso (fun q : Fin (j+1) =>
    F.mapBiproduct _ ≪≫ biproduct.mapIso (fun _ : Fin (Nat.choose j q.val) =>
      (F.commShiftIso ((j : ℤ)*b+d*(q.val : ℤ))).app X))

def binomialMapIso (b d : ℤ) (j : ℕ) {X Y : C} (e : X ≅ Y) :
    ExternalTensor.Binomial.binomialObject b d j X ≅
      ExternalTensor.Binomial.binomialObject b d j Y :=
  biproduct.mapIso (fun q : Fin (j+1) => biproduct.mapIso
    (fun _ : Fin (Nat.choose j q.val) => (shiftFunctor C ((j : ℤ)*b+d*(q.val : ℤ))).mapIso e))
end BinomialFunctor

namespace SelectingOrdinaryOddSplit
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
open SelectingIteration SelectingOrdinarySimulation SelectingOrdinaryOdd

def input (Y : Family (k := k) (R := R)) : ModuleCat.{u} (QuadraticEncoding.B E.relations) :=
  letI : Module k Y.val := Module.compHom Y.val (algebraMap k R)
  letI : IsScalarTower k R Y.val := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  ModuleCat.of (QuadraticEncoding.B E.relations) (SelectingRealization.input (E := E) (Y := Y.val))
abbrev Qmodule (Y : Family (k := k) (R := R)) := (SelectingOrdinaryQ.functor E S).obj (input E Y)
abbrev inflatedQmodule (Y : Family (k := k) (R := R)) :=
  (secondFunctor E S).obj (Qmodule E S Y)

def evaluationQIso (Y : Family (k := k) (R := R)) :
    (SelectingOrdinaryQ.derived E S).obj (evaluation E Y) ≅
      (DerivedCategory.singleFunctor _ 0).obj (Qmodule E S Y) :=
  SelectingOrdinaryQ.stalkIso E S (input E Y) 0

/-- Every multiplicity is still indexed by Fin(choose j q), including the
empty multiplicities at the boundary. Both tensor and inflation act on the
actual modules, and the displayed degree is exactly j*b+3*q. -/
theorem odd_shifted_modules (j : ℕ) (Y : Family (k := k) (R := R)) :
    Nonempty (((ordinary E S).obj^[2*j+1]) (SelectingOrdinaryIteration.evaluated E S Y) ≅
      ExternalTensor.Binomial.binomialObject (SelectingOrdinaryAlgebra.b E S) 3 j
        ((DerivedCategory.singleFunctor _ 0).obj
          (inflatedQmodule E S (((selected S)^[j]) Y)))) := by
  let Z := ((selected S)^[j]) Y
  exact ⟨Classical.choice (odd_binomial E S j Y) ≪≫
    (second E S).mapIso (mapBinomial (SelectingOrdinaryQ.derived E S)
      (SelectingOrdinaryAlgebra.b E S) 3 j (evaluation E Z)) ≪≫
    mapBinomial (second E S) (SelectingOrdinaryAlgebra.b E S) 3 j
      ((SelectingOrdinaryQ.derived E S).obj (evaluation E Z)) ≪≫
    binomialMapIso (SelectingOrdinaryAlgebra.b E S) 3 j
      ((second E S).mapIso (evaluationQIso E S Z) ≪≫ secondStalkIso E S (Qmodule E S Z) 0)⟩

theorem inflated_Q_dimension_eq (Y : Family (k := k) (R := R)) :
    projectiveDimension (inflatedQmodule E S Y) = projectiveDimension (Qmodule E S Y) :=
  ProductProjectiveDimension.secondInflation_dimension_eq _ _ _

theorem Q_dimension_le (Y : Family (k := k) (R := R)) :
    projectiveDimension (inflatedQmodule E S Y) ≤ (SelectingOrdinaryAlgebra.length E S+2 : ℕ) := by
  rw [inflated_Q_dimension_eq E S Y]
  exact SelectingOrdinaryQ.module_dimension_le E S _
end SelectingOrdinaryOddSplit
end
end Note198
