import Note198.SelectingFamilyQDimension
import Note198.ComplexBinomialModuleDimension

namespace Note198.SelectingFamilyOddSigned
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
open SelectingIteration SelectingOrdinaryOddSplit SelectingFamilyQDimension
open ComplexProjectiveDimension
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)

theorem inflated_Q_finite (Y : Family (k := k) (R := R)) :
    FiniteDimensional k (BalancedTensor.ScalarLeftModule k (SelectingOrdinaryAlgebra.D E S)
      (inflatedQmodule E S Y)) := by
  letI := Q_finite E S Y
  let f : BalancedTensor.ScalarLeftModule k (SelectingOrdinaryQ.Eblock E S) (Qmodule E S Y) →ₗ[k]
      BalancedTensor.ScalarLeftModule k (SelectingOrdinaryAlgebra.D E S) (inflatedQmodule E S Y) :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_surjective f (fun x => ⟨x,rfl⟩)

def finiteQ (Y : Family (k := k) (R := R)) : PDMinimal.FiniteModule k (SelectingOrdinaryAlgebra.D E S) := by
  letI := inflated_Q_finite E S Y
  letI := BalancedTensor.scalarLeftTower k (SelectingOrdinaryAlgebra.D E S) (inflatedQmodule E S Y)
  exact PDMinimal.FiniteModule.of
    (BalancedTensor.ScalarLeftModule k (SelectingOrdinaryAlgebra.D E S) (inflatedQmodule E S Y))

/-- The signed value of the actual odd iterate is determined by the
actual numerical projective dimension of Q, preserving the original shifts. -/
theorem odd_signed_dimension (Y : Family (k := k) (R := R)) (j n : ℕ)
    (hpd : projectiveDimension (inflatedQmodule E S (((selected S)^[j]) Y)) = n) :
    signedProjectiveDimension (((SelectingOrdinarySimulation.ordinary E S).obj^[2*j+1])
      (SelectingOrdinaryIteration.evaluated E S Y)) =
      ((((n:ℤ)+(j:ℤ)*SelectingOrdinaryAlgebra.b E S+3*(j:ℤ)):WithTop ℤ):WithBot (WithTop ℤ)) := by
  let g := SelectingOrdinaryAlgebra.length E S+2
  have hg (N : ModuleCat.{u} (SelectingOrdinaryAlgebra.D E S)) : HasProjectiveDimensionLE N g :=
    (projectiveDimension_le_iff N g).mp (SelectingOrdinaryDimension.module_dimension_le E S N)
  rw [signedProjectiveDimension_iso (Classical.choice (odd_shifted_modules E S j Y))]
  exact ComplexBinomialModuleDimension.binomial_signed_dimension g hg
    (finiteQ E S (((selected S)^[j]) Y)) n j (SelectingOrdinaryAlgebra.b E S) hpd

variable (F : SelectingBrickFamily.SourceFamily k R S)

/-- The coefficient δ_j and the odd signed formula are proved from the
actual surviving family module; the caller supplies no numerical pd certificate. -/
theorem odd_signed_dimension_exists (m : ℕ+) (j : ℕ) (hj : j < m.val) :
    ∃ n : ℕ, n ≤ SelectingOrdinaryAlgebra.length E S+2 ∧
      projectiveDimension (inflatedQmodule E S
        (((selected S)^[j]) (SelectingFamilyFiniteBar.source F m))) = n ∧
      signedProjectiveDimension (((SelectingOrdinarySimulation.ordinary E S).obj^[2*j+1])
        (SelectingOrdinaryIteration.evaluated E S (SelectingFamilyFiniteBar.source F m))) =
        ((((n:ℤ)+(j:ℤ)*SelectingOrdinaryAlgebra.b E S+3*(j:ℤ)):WithTop ℤ):WithBot (WithTop ℤ)) := by
  obtain ⟨n,hn,hpd⟩ := odd_dimension_exists E S F m j hj
  exact ⟨n,hn,hpd,odd_signed_dimension E S (SelectingFamilyFiniteBar.source F m) j n hpd⟩
end
end Note198.SelectingFamilyOddSigned
