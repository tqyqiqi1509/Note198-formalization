import Note198.OrdinaryProductDimensionExact
import OAI.Algebra.Finitistic.Ordinary.OrdinaryMiddleTensorFunctors
import OAI.Algebra.Finitistic.Ordinary.OrdinaryProjectiveTensor
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.RingTheory.TensorProduct.Finite

namespace Note198.SelectingOrdinaryQ
noncomputable section
open CategoryTheory OAI.LittleFinitistic OrdinarySimulation
open scoped TensorProduct
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)

abbrev Eblock := QuadraticEncoding.B E.relations ⊗[k]
  ChainAlgebra k (SelectingOrdinaryAlgebra.length E S)

/-- The actual functor Q=O tensor_B -, with its E-block action retained. -/
abbrev functor : ModuleCat.{u} (QuadraticEncoding.B E.relations) ⥤ ModuleCat.{u} (Eblock E S) :=
  middleLeftFunctor k (Eblock E S) (QuadraticEncoding.B E.relations)
    (SelectingOrdinaryAlgebra.O E S)

theorem maps_exact (C : ShortComplex (ModuleCat.{u} (QuadraticEncoding.B E.relations)))
    (hC : C.Exact) : (C.map (functor E S)).Exact := by
  have ht := BalancedTensor.projectiveTensor_mapsExact k (QuadraticEncoding.B E.relations)
    (SelectingOrdinaryAlgebra.O E S) C hC
  rw [ShortComplex.moduleCat_exact_iff] at ht ⊢
  exact ht

theorem preserves_homology : (functor E S).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (maps_exact E S)

abbrev complexFunctor := (functor E S).mapHomologicalComplex (.up ℤ)

theorem maps_quasiIso {C C' : CochainComplex
    (ModuleCat.{u} (QuadraticEncoding.B E.relations)) ℤ} (f : C ⟶ C') [QuasiIso f] :
    QuasiIso ((complexFunctor E S).map f) := by
  letI := preserves_homology E S
  infer_instance

theorem module_dimension_le (M : ModuleCat.{u} (QuadraticEncoding.B E.relations)) :
    projectiveDimension ((functor E S).obj M) ≤ (SelectingOrdinaryAlgebra.length E S+2 : ℕ) :=
  tensor_chain_module_projectiveDimension_le
    (ThreeVertexAlgebra.directedSystem (QuadraticEncoding.composition E.relations)) _ _

theorem finite (M : ModuleCat.{u} (QuadraticEncoding.B E.relations))
    [FiniteDimensional k (BalancedTensor.ScalarLeftModule k (QuadraticEncoding.B E.relations) M)] :
    FiniteDimensional k (BalancedTensor.ScalarLeftModule k (Eblock E S)
      ((functor E S).obj M)) := by
  let T := LeftTensor k (QuadraticEncoding.B E.relations) (Eblock E S)
    (SelectingOrdinaryAlgebra.O E S)
    (BalancedTensor.ScalarLeftModule k (QuadraticEncoding.B E.relations) M)
  letI : FiniteDimensional k (SelectingOrdinaryAlgebra.O E S) :=
    SelectingOrdinaryAlgebra.O_finite E S
  letI : FiniteDimensional k ((SelectingOrdinaryAlgebra.O E S) ⊗[k]
      (BalancedTensor.ScalarLeftModule k (QuadraticEncoding.B E.relations) M)) :=
    Module.Finite.tensorProduct _ _ _
  letI : FiniteDimensional k T := by
    let K := BalancedTensor.relations k (QuadraticEncoding.B E.relations)
      (SelectingOrdinaryAlgebra.O E S)
      (BalancedTensor.ScalarLeftModule k (QuadraticEncoding.B E.relations) M)
    exact Module.Finite.of_surjective K.mkQ K.mkQ_surjective
  let f : T →ₗ[k] BalancedTensor.ScalarLeftModule k (Eblock E S) ((functor E S).obj M) :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => (IsScalarTower.algebraMap_smul (Eblock E S) c x).symm }
  exact Module.Finite.of_surjective f (fun x => ⟨x,rfl⟩)

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} (QuadraticEncoding.B E.relations))]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} (Eblock E S))]

theorem inverts : (HomologicalComplex.quasiIso
    (ModuleCat.{u} (QuadraticEncoding.B E.relations)) (.up ℤ)).IsInvertedBy
      (complexFunctor E S ⋙ DerivedCategory.Q) := by
  intro C C' f hf
  letI : QuasiIso f := hf
  letI := maps_quasiIso E S f
  exact (inferInstance : IsIso (DerivedCategory.Q.map ((complexFunctor E S).map f)))

/-- Since the actual O is right projective, its derived functor is the
localization of ordinary degree-zero tensor, on all input complexes. -/
def derived : DerivedCategory (ModuleCat.{u} (QuadraticEncoding.B E.relations)) ⥤
    DerivedCategory (ModuleCat.{u} (Eblock E S)) :=
  Localization.lift (complexFunctor E S ⋙ DerivedCategory.Q) (inverts E S) DerivedCategory.Q

def comparison : DerivedCategory.Q ⋙ derived E S ≅ complexFunctor E S ⋙ DerivedCategory.Q :=
  Localization.fac (complexFunctor E S ⋙ DerivedCategory.Q) (inverts E S) DerivedCategory.Q

theorem comparison_exists : Nonempty
    (DerivedCategory.Q ⋙ derived E S ≅ complexFunctor E S ⋙ DerivedCategory.Q) :=
  ⟨comparison E S⟩
end
end Note198.SelectingOrdinaryQ
