import Note198.SelectingOrdinaryOddSplit
import Note198.ComplexModuleDimension
import Note198.ComplexDimensionOperations

namespace Note198.ComplexBinomialModuleDimension
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI.LittleFinitistic
open ComplexProjectiveDimension ComplexProjectiveModels ComplexStupidTruncation
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (g : ℕ) (hg : ∀ M : ModuleCat.{u} A, HasProjectiveDimensionLE M g)

include g hg in
theorem binomial_bounded_finite (M : PDMinimal.FiniteModule k A) (j : ℕ) (b : ℤ) :
    InBoundedFiniteDerived (OAI.ExternalTensor.Binomial.binomialObject b 3 j
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M.cat)) := by
  let Z := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M.cat
  have hshift (q : Fin (j+1)) : InBoundedFiniteDerived (Z⟦(j:ℤ)*b+3*(q.val:ℤ)⟧) := by
    obtain ⟨P,lo,hi,hP,hb,he⟩ := model_shift (finite_stalk_model M g (hg M.cat) 0)
      ((j:ℤ)*b+3*(q.val:ℤ))
    exact ⟨P,lo,hi,fun a => (hP a).1,hb,he⟩
  exact ComplexDimensionOperations.boundedFinite_fin_biproduct _ _ (fun q =>
    ComplexDimensionOperations.boundedFinite_fin_biproduct _ _ (fun _ => hshift q))

include g hg in
/-- Exact signed dimension of the full actual repeated biproduct. The top
weight q=j has multiplicity choose j j=1 and supplies the nonzero edge. -/
theorem binomial_signed_dimension (M : PDMinimal.FiniteModule k A) (n j : ℕ) (b : ℤ)
    (hpd : projectiveDimension M.cat = n) :
    signedProjectiveDimension (OAI.ExternalTensor.Binomial.binomialObject b 3 j
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M.cat)) =
      ((((n:ℤ)+(j:ℤ)*b+3*(j:ℤ)):WithTop ℤ):WithBot (WithTop ℤ)) := by
  let Z := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M.cat
  let t : Fin (j+1) → ℤ := fun q => (j:ℤ)*b+3*(q.val:ℤ)
  have hshift (q : Fin (j+1)) : InBoundedFiniteDerived (Z⟦t q⟧) := by
    obtain ⟨P,lo,hi,hP,hb,he⟩ := model_shift (finite_stalk_model M g (hg M.cat) 0) (t q)
    exact ⟨P,lo,hi,fun a => (hP a).1,hb,he⟩
  have hin (q : Fin (j+1)) : InBoundedFiniteDerived
      (⨁ fun _ : Fin (Nat.choose j q.val) => Z⟦t q⟧) :=
    ComplexDimensionOperations.boundedFinite_fin_biproduct _ _ (fun _ => hshift q)
  have hval (q : Fin (j+1)) : signedProjectiveDimension (Z⟦t q⟧) =
      ((((n:ℤ)+t q):WithTop ℤ):WithBot (WithTop ℤ)) := by
    rw [signedProjectiveDimension_shift, ComplexModuleDimension.signed_stalk_eq_projectiveDimension M n hpd]
    rfl
  change signedProjectiveDimension (⨁ fun q : Fin (j+1) =>
    ⨁ fun _ : Fin (Nat.choose j q.val) => Z⟦t q⟧) = _
  rw [ComplexDimensionOperations.signedProjectiveDimension_fin_biproduct k g hg _ _ hin]
  have hinner (q : Fin (j+1)) : signedProjectiveDimension
      (⨁ fun _ : Fin (Nat.choose j q.val) => Z⟦t q⟧) =
      ⨆ _ : Fin (Nat.choose j q.val), ((((n:ℤ)+t q):WithTop ℤ):WithBot (WithTop ℤ)) := by
    rw [ComplexDimensionOperations.signedProjectiveDimension_fin_biproduct k g hg _ _ (fun _ => hshift q)]
    simp only [hval]
  simp_rw [hinner]
  apply le_antisymm
  · apply iSup_le
    intro q
    apply iSup_le
    intro r
    apply WithBot.coe_le_coe.mpr
    apply WithTop.coe_le_coe.mpr
    dsimp [t]
    have hq := q.isLt
    omega
  · apply le_iSup_of_le
      (f := fun q : Fin (j+1) => ⨆ _ : Fin (Nat.choose j q.val),
        ((((n:ℤ)+t q):WithTop ℤ):WithBot (WithTop ℤ))) (Fin.last j)
    apply le_iSup_of_le
      (f := fun _ : Fin (Nat.choose j (Fin.last j).val) =>
        ((((n:ℤ)+t (Fin.last j)):WithTop ℤ):WithBot (WithTop ℤ)))
      (show Fin (Nat.choose j (Fin.last j).val) from ⟨0, by simp⟩)
    exact (show
      ((((n:ℤ)+(j:ℤ)*b+3*(j:ℤ)):WithTop ℤ):WithBot (WithTop ℤ)) ≤
        ((((n:ℤ)+t (Fin.last j)):WithTop ℤ):WithBot (WithTop ℤ)) from by
      apply WithBot.coe_le_coe.mpr
      apply WithTop.coe_le_coe.mpr
      dsimp [t]
      omega)
end
end Note198.ComplexBinomialModuleDimension
