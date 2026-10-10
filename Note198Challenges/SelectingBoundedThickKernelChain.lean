import Note198.SelectingBoundedScope
import Note198.ComplexBoundedFiniteSubcategory

namespace Note198.SelectingBoundedThickKernelChain
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
open ComplexStupidTruncation
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)

def boundedProperty : ObjectProperty
    (DerivedCategory (ModuleCat.{u} (QuadraticEncoding.B E.relations))) :=
  InBoundedFiniteDerived

abbrev Db := (boundedProperty E).FullSubcategory

theorem base_global_bound (N : ModuleCat.{u} (QuadraticEncoding.B E.relations)) :
    HasProjectiveDimensionLE N 2 :=
  (projectiveDimension_le_iff N 2).mp
    ((DirectedBound.DirectedSystem.both_sides_projectiveDimension_le
      (ThreeVertexAlgebra.directedSystem (QuadraticEncoding.composition E.relations))).1 N)

/-- The restricted category has precisely the original bounded finite
cohomology scope, with the actual canonical field restriction. -/
theorem original_scope_iff
    (Z : DerivedCategory (ModuleCat.{u} (QuadraticEncoding.B E.relations))) :
    boundedProperty E Z ↔ ∃ lo hi : ℤ,
      (∀ n, FiniteDimensional k ((ModuleCat.restrictScalars
        (algebraMap k (QuadraticEncoding.B E.relations))).obj
          (ComplexCohomologyModels.H n Z))) ∧
      (∀ n, n < lo ∨ hi < n → IsZero (ComplexCohomologyModels.H n Z)) :=
  ComplexBoundedFiniteSubcategory.bounded_finite_iff_cohomology
    (k:=k) 2 (base_global_bound E) Z

instance bounded_retracts : (boundedProperty E).IsStableUnderRetracts :=
  ComplexBoundedFiniteSubcategory.bounded_finite_stable_retracts
    (k:=k) 2 (base_global_bound E)

instance bounded_triangulated : (boundedProperty E).IsTriangulated :=
  ComplexBoundedFiniteSubcategory.bounded_finite_triangulated
    (k:=k) 2 (base_global_bound E)

/-- Restriction of the same actual selecting tensor functor to Db of finite
modules. Its object and arrow actions are those of the native functor. -/
def phi : Db E ⥤ Db E :=
  (boundedProperty E).lift ((boundedProperty E).ι ⋙ SelectingDerivedFunctor.Phi E S)
    (fun Z => SelectingBoundedScope.phi_preserves_bounded_finite E S Z.obj Z.property)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance phi_additive : (phi E S).Additive := by
  unfold phi
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance phi_commShift : (phi E S).CommShift ℤ := by
  letI : (SelectingDerivedFunctor.Phi E S).CommShift ℤ := inferInstance
  letI : (boundedProperty E).ι.CommShift ℤ := inferInstance
  letI : ((boundedProperty E).ι ⋙ SelectingDerivedFunctor.Phi E S).CommShift ℤ :=
    inferInstance
  unfold phi
  exact ObjectProperty.commShiftLift (boundedProperty E)
    ((boundedProperty E).ι ⋙ SelectingDerivedFunctor.Phi E S)
    (fun Z => SelectingBoundedScope.phi_preserves_bounded_finite E S Z.obj Z.property)

/-- The inclusion intertwines every actual restricted iterate with the full
native derived iterate, with equality of the underlying objects. -/
theorem iterate_inclusion (j : ℕ) (Z : Db E) :
    (boundedProperty E).ι.obj (((phi E S).obj^[j]) Z) =
      (((SelectingDerivedFunctor.Phi E S).obj^[j]) ((boundedProperty E).ι.obj Z)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (SelectingDerivedFunctor.Phi E S).obj
      ((boundedProperty E).ι.obj (((phi E S).obj^[j]) Z)) = _
    rw [ih]

def kernel (j : ℕ) : ObjectProperty (Db E) :=
  ObjectProperty.inverseImage
    (fun Z => IsZero (((SelectingDerivedFunctor.Phi E S).obj^[j]) Z) :
      ObjectProperty (DerivedCategory (ModuleCat.{u} (QuadraticEncoding.B E.relations))))
    (boundedProperty E).ι

/-- This is the literal kernel of the actual restricted endofunctor. -/
theorem kernel_iff (j : ℕ) (Z : Db E) :
    kernel E S j Z ↔ IsZero (((phi E S).obj^[j]) Z) := by
  change IsZero (((SelectingDerivedFunctor.Phi E S).obj^[j])
    ((boundedProperty E).ι.obj Z)) ↔ _
  rw [← iterate_inclusion]
  constructor
  · exact IsZero.of_full_of_faithful_of_isZero (boundedProperty E).ι _
  · exact (boundedProperty E).ι.map_isZero

theorem restricted_kernel_thick (j : ℕ) :
    (kernel E S j).IsTriangulated ∧ (kernel E S j).IsStableUnderRetracts := by
  let P : ObjectProperty
      (DerivedCategory (ModuleCat.{u} (QuadraticEncoding.B E.relations))) :=
    fun Z => IsZero (((SelectingDerivedFunctor.Phi E S).obj^[j]) Z)
  letI : P.IsTriangulated := (SelectingThickKernelChain.actual_kernel_thick E S j).1
  letI : P.IsStableUnderRetracts := (SelectingThickKernelChain.actual_kernel_thick E S j).2
  refine ⟨?_, TriangleObjectInverseImage.inverse_retracts (boundedProperty E).ι P⟩
  change ObjectProperty.IsTriangulated (P.inverseImage (boundedProperty E).ι)
  infer_instance

/-- Thick closure for the literal intrinsic zero-object predicate in Db. -/
theorem literal_restricted_kernel_thick (j : ℕ) :
    ObjectProperty.IsTriangulated
      (fun Z => IsZero (((phi E S).obj^[j]) Z) : ObjectProperty (Db E)) ∧
    ObjectProperty.IsStableUnderRetracts
      (fun Z => IsZero (((phi E S).obj^[j]) Z) : ObjectProperty (Db E)) := by
  sorry

theorem bounded_successive_witness
    (F : SelectingBrickFamily.SourceFamily k R S) (j : ℕ) :
    ∃ Z : Db E, ¬ kernel E S j Z ∧ kernel E S (j+1) Z := by
  let m : ℕ+ := ⟨j+1,Nat.succ_pos j⟩
  let Y : SelectingIteration.Family (k:=k) (R:=R) := ⟨F.V m,F.finite m⟩
  let Z : Db E := ⟨SelectingIteration.evaluation E Y,
    SelectingBoundedScope.evaluation_bounded_finite E Y⟩
  refine ⟨Z,?_,?_⟩
  · intro hz
    have hs := (SelectingKernelChain.iterate_zero_iff E S j Y).mp hz
    rw [SelectingIteration.iterate_val] at hs
    obtain ⟨x,y,hxy⟩ := (F.alive m j (Nat.lt_succ_self j)).exists_pair_ne
    exact hxy (hs.elim x y)
  · apply (SelectingKernelChain.iterate_zero_iff E S (j+1) Y).mpr
    rw [SelectingIteration.iterate_val]
    exact F.extinct m

/-- The strictly increasing thick chain inside the manuscript's actual
bounded finite-dimensional derived category. -/
theorem restricted_strict_thick_chain
    (F : SelectingBrickFamily.SourceFamily k R S) (j : ℕ) :
    (kernel E S j).IsTriangulated ∧ (kernel E S j).IsStableUnderRetracts ∧
      {Z : Db E | kernel E S j Z} ⊂ {Z : Db E | kernel E S (j+1) Z} := by
  refine ⟨(restricted_kernel_thick E S j).1,(restricted_kernel_thick E S j).2,?_⟩
  apply Set.ssubset_iff_subset_ne.mpr
  constructor
  · intro Z hz
    change IsZero (((SelectingDerivedFunctor.Phi E S).obj^[j+1]) Z.obj)
    rw [Function.iterate_succ_apply']
    exact (SelectingDerivedFunctor.Phi E S).map_isZero hz
  · intro heq
    obtain ⟨Z,hnot,hyes⟩ := bounded_successive_witness E S F j
    apply hnot
    change Z ∈ {Z : Db E | kernel E S j Z}
    rw [heq]
    exact hyes

/-- Literal strict kernel inclusions of the genuinely restricted native
functor, inside the bounded finite-dimensional derived category. -/
theorem literal_restricted_strict_chain
    (F : SelectingBrickFamily.SourceFamily k R S) (j : ℕ) :
    {Z : Db E | IsZero (((phi E S).obj^[j]) Z)} ⊂
      {Z : Db E | IsZero (((phi E S).obj^[j+1]) Z)} := by
  sorry

end
end Note198.SelectingBoundedThickKernelChain
