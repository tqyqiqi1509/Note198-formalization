import Note198.SelectingThickKernelChain
import Note198.SelectingOrdinaryAlgebra
import Note198.ComplexStupidTruncation
import Note198.SelectingFamilyQDimension

namespace Note198.SelectingBoundedScope
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
open ExternalTensor.Section4 BimoduleTotal ComplexStupidTruncation
open scoped ModuleCat.Algebra
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u

section Total
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] [FiniteDimensional k B]
variable (P : BiComplex k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable (hP : ∀ i, FiniteDimensional k (BimoduleBalancedTensor.Input k B (P.X (p i))))
variable (K : CochainComplex (ModuleCat.{u} B) ℤ)

include hP in
theorem total_terms_finite (hK : ∀ n, Module.Finite B (K.X n)) (n : ℤ) :
    Module.Finite B ((total k B P p hp K).X n) := by
  letI : ∀ i, FiniteDimensional k (BimoduleBalancedTensor.Input k B (P.X (p i))) := hP
  letI : ∀ q, FiniteDimensional k (ComplexTensor.leftTerm k B K q) := fun q => by
    letI : Module.Finite B (ComplexTensor.leftTerm k B K q) := by
      change Module.Finite B (K.X q)
      exact hK q
    exact Module.Finite.trans B (ComplexTensor.leftTerm k B K q)
  letI : FiniteDimensional k ((vectorTotal k B P p hp K).X n) := by
    change FiniteDimensional k (∀ i : Fin l, Term k B P K (p i) (n + -(p i)))
    infer_instance
  letI : FiniteDimensional k
      (BalancedTensor.ScalarLeftModule k B ((total k B P p hp K).X n)) :=
    Module.Finite.equiv (underlyingTerm k B P p hp K n).symm
  let f : BalancedTensor.ScalarLeftModule k B ((total k B P p hp K).X n) →ₗ[k]
      ((total k B P p hp K).X n) :=
    { toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  letI : Module.Finite k ((total k B P p hp K).X n) :=
    Module.Finite.of_surjective f (fun x => ⟨x,rfl⟩)
  exact Module.Finite.of_restrictScalars_finite k B ((total k B P p hp K).X n)

/-- Actual support bounds for the finite total, including empty input windows. -/
theorem total_terms_bounded (loP hiP lo hi : ℤ)
    (hdeg : ∀ i, loP ≤ p i ∧ p i ≤ hiP)
    (hK : ∀ n, n < lo ∨ hi < n → IsZero (K.X n))
    (n : ℤ) (hn : n < lo+loP ∨ hi+hiP < n) :
    IsZero ((total k B P p hp K).X n) := by
  letI : ∀ i : Fin l, Subsingleton (Term k B P K (p i) (n + -(p i))) := fun i => by
    have hq : n + -(p i) < lo ∨ hi < n + -(p i) := by
      have hd := hdeg i
      omega
    letI : Subsingleton (ComplexTensor.leftTerm k B K (n + -(p i))) := by
      change Subsingleton (K.X (n + -(p i)))
      exact ModuleCat.subsingleton_of_isZero (hK (n + -(p i)) hq)
    dsimp [Term, BimoduleBalancedTensor.Tensor, BalancedTensor.Tensor]
    infer_instance
  letI : Subsingleton ((total k B P p hp K).X n) := by
    change Subsingleton (∀ i : Fin l, Term k B P K (p i) (n + -(p i)))
    infer_instance
  exact ModuleCat.isZero_of_subsingleton _
end Total

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)

theorem bimodule_input_finite (n : ℤ) :
    FiniteDimensional k (BimoduleBalancedTensor.Input k (QuadraticEncoding.B E.relations)
      ((SelectingRectification.bimodule E S).X n)) := by
  let f : ((OrdinarySimulation.underlyingComplex (k:=k)
      (SelectingRectification.bimodule E S)).X n) →ₗ[k]
      BimoduleBalancedTensor.Input k (QuadraticEncoding.B E.relations)
        ((SelectingRectification.bimodule E S).X n) :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => by
        have hc := (Algebra.TensorProduct.includeRight :
          (QuadraticEncoding.B E.relations)ᵐᵒᵖ →ₐ[k]
            Enveloping k (QuadraticEncoding.B E.relations)).commutes c
        exact congrArg (fun a : Enveloping k (QuadraticEncoding.B E.relations) =>
          a • (show ((SelectingRectification.bimodule E S).X n) from x)) hc.symm }
  exact Module.Finite.of_surjective f (fun x => ⟨x,rfl⟩)

/-- The actual native selecting tensor preserves the manuscript's bounded
 derived category of finite-dimensional modules. -/
theorem phi_preserves_bounded_finite
    (Z : DerivedCategory (ModuleCat.{u} (QuadraticEncoding.B E.relations)))
    (hZ : InBoundedFiniteDerived Z) :
    InBoundedFiniteDerived ((SelectingDerivedFunctor.Phi E S).obj Z) := by
  obtain ⟨K,lo,hi,hK,hb,⟨e⟩⟩ := hZ
  let d := SelectingDerivedFunctor.model E S
  letI : ∀ i, Module.Projective (QuadraticEncoding.B E.relations)ᵐᵒᵖ
      (ComplexTensor.rightTerm k _ (BimoduleTotal.right k _ (SelectingRectification.bimodule E S))
        (d.degrees i)) := fun i => d.projective (d.degrees i)
  let T := total k (QuadraticEncoding.B E.relations) (SelectingRectification.bimodule E S)
    d.degrees (intervalDegrees_strictMono d.lower d.upper) K
  refine ⟨T,lo+d.lower,hi+d.lower+((d.upper-d.lower).toNat:ℤ),?_,?_,?_⟩
  · exact total_terms_finite k _ _ d.degrees _
      (fun i => bimodule_input_finite E S (d.degrees i)) K hK
  · intro n hn
    apply total_terms_bounded k _ _ d.degrees _ K d.lower
      (d.lower+((d.upper-d.lower).toNat:ℤ)) lo hi _ hb n (by omega)
    intro i
    dsimp [BimoduleTotal.BoundedProjective.degrees,intervalDegrees]
    have hlt := i.isLt
    omega
  · exact ⟨(d.comparison.app K).symm ≪≫ (SelectingDerivedFunctor.Phi E S).mapIso e⟩

/-- Every strict-kernel witness is already a finite degree-zero stalk. -/
theorem evaluation_bounded_finite (Y : SelectingIteration.Family (k:=k) (R:=R)) :
    InBoundedFiniteDerived (SelectingIteration.evaluation E Y) := by
  let N := SelectingOrdinaryOddSplit.input E Y
  letI : FiniteDimensional k (BalancedTensor.ScalarLeftModule k _ N) :=
    SelectingFamilyQDimension.input_finite E Y
  let f : BalancedTensor.ScalarLeftModule k (QuadraticEncoding.B E.relations) N →ₗ[k] N :=
    { toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  letI : FiniteDimensional k N := Module.Finite.of_surjective f (fun x => ⟨x,rfl⟩)
  letI : Module.Finite (QuadraticEncoding.B E.relations) N :=
    Module.Finite.of_restrictScalars_finite k (QuadraticEncoding.B E.relations) N
  let K := (HomologicalComplex.single (ModuleCat (QuadraticEncoding.B E.relations)) (.up ℤ) 0).obj N
  refine ⟨K,0,0,?_,?_,⟨Iso.refl _⟩⟩
  · intro n
    by_cases hn : n=0
    · subst n
      exact Module.Finite.equiv (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).symm.toLinearEquiv
    · letI := ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 N n hn)
      infer_instance
  · intro n hn
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 N n (by omega)
end
end Note198.SelectingBoundedScope
