import Note198.SelectingFamilyOddSigned

namespace Note198.SelectingFamilyEvenSigned
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
open SelectingIteration SelectingOrdinaryEvenSplit SelectingFamilyQDimension
open ComplexProjectiveDimension
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)

theorem inflated_first_finite (Y : Family (k := k) (R := R)) :
    FiniteDimensional k (BalancedTensor.ScalarLeftModule k (SelectingOrdinaryAlgebra.D E S)
      (firstModule E S Y)) := by
  letI := input_finite E Y
  let f : BalancedTensor.ScalarLeftModule k (QuadraticEncoding.B E.relations)
      (SelectingOrdinaryOddSplit.input E Y) →ₗ[k]
      BalancedTensor.ScalarLeftModule k (SelectingOrdinaryAlgebra.D E S) (firstModule E S Y) :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_surjective f (fun x => ⟨x,rfl⟩)

def finiteFirst (Y : Family (k := k) (R := R)) : PDMinimal.FiniteModule k (SelectingOrdinaryAlgebra.D E S) := by
  letI := inflated_first_finite E S Y
  letI := BalancedTensor.scalarLeftTower k (SelectingOrdinaryAlgebra.D E S) (firstModule E S Y)
  exact PDMinimal.FiniteModule.of
    (BalancedTensor.ScalarLeftModule k (SelectingOrdinaryAlgebra.D E S) (firstModule E S Y))

theorem first_dimension_le_two (Y : Family (k := k) (R := R)) :
    projectiveDimension (firstModule E S Y) ≤ (2 : ℕ) := by
  rw [first_module_dimension E S Y]
  exact (DirectedBound.DirectedSystem.both_sides_projectiveDimension_le
    (ThreeVertexAlgebra.directedSystem (QuadraticEncoding.composition E.relations))).1 _

theorem even_signed_dimension (Y : Family (k := k) (R := R)) (j n : ℕ)
    (hpd : projectiveDimension (firstModule E S (((selected S)^[j]) Y)) = n) :
    signedProjectiveDimension (((SelectingOrdinarySimulation.ordinary E S).obj^[2*j])
      (SelectingOrdinaryIteration.evaluated E S Y)) =
      ((((n:ℤ)+(j:ℤ)*SelectingOrdinaryAlgebra.b E S+3*(j:ℤ)):WithTop ℤ):WithBot (WithTop ℤ)) := by
  let g := SelectingOrdinaryAlgebra.length E S+2
  have hg (N : ModuleCat.{u} (SelectingOrdinaryAlgebra.D E S)) : HasProjectiveDimensionLE N g :=
    (projectiveDimension_le_iff N g).mp (SelectingOrdinaryDimension.module_dimension_le E S N)
  rw [signedProjectiveDimension_iso (Classical.choice (even_shifted_modules E S j Y))]
  exact ComplexBinomialModuleDimension.binomial_signed_dimension g hg
    (finiteFirst E S (((selected S)^[j]) Y)) n j (SelectingOrdinaryAlgebra.b E S) hpd

variable (F : SelectingBrickFamily.SourceFamily k R S)

/-- The actual even coefficients ε_j lie in [0,2]; their signed iterate
values are exact, with no supplied dimension or nonzero certificate. -/
theorem even_signed_dimension_exists (m : ℕ+) (j : ℕ) (hj : j < m.val) :
    ∃ n : ℕ, n ≤ 2 ∧
      projectiveDimension (firstModule E S
        (((selected S)^[j]) (SelectingFamilyFiniteBar.source F m))) = n ∧
      signedProjectiveDimension (((SelectingOrdinarySimulation.ordinary E S).obj^[2*j])
        (SelectingOrdinaryIteration.evaluated E S (SelectingFamilyFiniteBar.source F m))) =
        ((((n:ℤ)+(j:ℤ)*SelectingOrdinaryAlgebra.b E S+3*(j:ℤ)):WithTop ℤ):WithBot (WithTop ℤ)) := by
  let Y := ((selected S)^[j]) (SelectingFamilyFiniteBar.source F m)
  have hY : Nontrivial Y.val := by
    dsimp [Y]
    rw [SelectingIteration.iterate_val]
    exact F.alive m j hj
  letI := hY
  letI : Nontrivial (firstModule E S Y) :=
    inferInstanceAs (Nontrivial (Y.val × Y.val × Y.val))
  obtain ⟨n,hn,hpd⟩ := finite_numeric_dimension (firstModule E S Y) 2 (first_dimension_le_two E S Y)
  exact ⟨n,hn,hpd,even_signed_dimension E S (SelectingFamilyFiniteBar.source F m) j n hpd⟩
end
end Note198.SelectingFamilyEvenSigned
