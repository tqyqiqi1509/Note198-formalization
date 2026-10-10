import Note198.SelectingIteration
import Note198.SelectingBrickFamily
import OAI.Algebra.Finitistic.Iteration.BinomialVanishing

namespace Note198.SelectingKernelChain
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
open SelectingIteration

theorem iterate_zero_iff (j : ℕ) (Y : Family (k := k) (R := R)) :
    IsZero (((SelectingDerivedFunctor.Phi E S).obj^[j]) (evaluation E Y)) ↔
      Subsingleton ((((selected S)^[j]) Y).val) := by
  let e : (((SelectingDerivedFunctor.Phi E S).obj^[j]) (evaluation E Y)) ≅
      ExternalTensor.Binomial.binomialObject 0 3 j
        (evaluation E (((selected S)^[j]) Y)) := by
    simpa only [ExternalTensor.Binomial.binomialObject,mul_zero,zero_add] using
      Classical.choice (binomial_iteration E S j Y)
  exact e.isZero_iff.trans
    ((ExternalTensor.Binomial.binomialObject_isZero_iff 0 3 j _).trans
      (evaluation_zero E (((selected S)^[j]) Y)))

/-- The actual constructed source family provides a new object in every
successive kernel of the fixed selecting derived tensor functor. -/
theorem successive_kernel_witness
    (F : SelectingBrickFamily.SourceFamily k R S) (j : ℕ) :
    ∃ Z : DerivedCategory (ModuleCat.{u} (QuadraticEncoding.B E.relations)),
      ¬ IsZero (((SelectingDerivedFunctor.Phi E S).obj^[j]) Z) ∧
      IsZero (((SelectingDerivedFunctor.Phi E S).obj^[j+1]) Z) := by
  let m : ℕ+ := ⟨j+1,Nat.succ_pos j⟩
  let Y : Family (k := k) (R := R) := ⟨F.V m,F.finite m⟩
  refine ⟨evaluation E Y,?_,?_⟩
  · intro hz
    have hs := (iterate_zero_iff E S j Y).mp hz
    rw [iterate_val] at hs
    obtain ⟨x,y,hxy⟩ := (F.alive m j (Nat.lt_succ_self j)).exists_pair_ne
    exact hxy (hs.elim x y)
  · apply (iterate_zero_iff E S (j+1) Y).mpr
    rw [iterate_val]
    exact F.extinct m

/-- The object sets of the actual kernels form a strictly increasing chain.
Closure under triangles and summands is proved for these same kernels in
SelectingThickKernelChain, using actual mapping-cone objects. -/
theorem strict_kernel_chain (F : SelectingBrickFamily.SourceFamily k R S) (j : ℕ) :
    {Z | IsZero (((SelectingDerivedFunctor.Phi E S).obj^[j]) Z)} ⊂
      {Z | IsZero (((SelectingDerivedFunctor.Phi E S).obj^[j+1]) Z)} := by
  apply Set.ssubset_iff_subset_ne.mpr
  constructor
  · intro Z hz
    change IsZero (((SelectingDerivedFunctor.Phi E S).obj^[j+1]) Z)
    change IsZero (((SelectingDerivedFunctor.Phi E S).obj^[j]) Z) at hz
    rw [Function.iterate_succ_apply']
    exact (SelectingDerivedFunctor.Phi E S).map_isZero hz
  · intro heq
    obtain ⟨Z,hnot,hyes⟩ := successive_kernel_witness E S F j
    apply hnot
    change Z ∈ {Z | IsZero (((SelectingDerivedFunctor.Phi E S).obj^[j]) Z)}
    rw [heq]
    exact hyes

end
end Note198.SelectingKernelChain
