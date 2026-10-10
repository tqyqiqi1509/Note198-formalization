import Note198.SelectingFamilyEvenSigned

namespace Note198.SelectingFamilyCountDimensions
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
open SelectingIteration ComplexProjectiveDimension
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
variable (F : SelectingBrickFamily.SourceFamily k R S)

/-- The coefficients are the actual projective dimensions of the two
surviving modules, chosen once from proved finite numerical values. -/
def epsilon (m : ℕ+) (j : Fin m.val) : ℕ := Classical.choose
  (SelectingFamilyEvenSigned.even_signed_dimension_exists E S F m j.val j.isLt)
def delta (m : ℕ+) (j : Fin m.val) : ℕ := Classical.choose
  (SelectingFamilyOddSigned.odd_signed_dimension_exists E S F m j.val j.isLt)

theorem epsilon_bound (m : ℕ+) (j : Fin m.val) : epsilon E S F m j ≤ 2 :=
  (Classical.choose_spec (SelectingFamilyEvenSigned.even_signed_dimension_exists E S F m j.val j.isLt)).1
theorem delta_bound (m : ℕ+) (j : Fin m.val) :
    delta E S F m j ≤ SelectingOrdinaryAlgebra.length E S+2 :=
  (Classical.choose_spec (SelectingFamilyOddSigned.odd_signed_dimension_exists E S F m j.val j.isLt)).1

theorem count_signed (m : ℕ+) (r : ℕ) :
    signedProjectiveDimension (SelectingFiniteBar.count E S (SelectingFamilyFiniteBar.firstModule E S F m) r) =
      signedProjectiveDimension (((SelectingOrdinarySimulation.ordinary E S).obj^[r])
        (SelectingOrdinaryIteration.evaluated E S (SelectingFamilyFiniteBar.source F m))) +
        (((r:ℤ):WithTop ℤ):WithBot (WithTop ℤ)) := by
  let e := mapObjectIteration (SelectingOrdinarySimulation.ordinary E S)
    (SelectingOrdinaryEvenSplit.evaluatedStalkIso E S (SelectingFamilyFiniteBar.source F m)) r ≪≫
    Classical.choice (SelectingOrdinaryBarComparison.ordinary_stalk_bar E S
      (SelectingFamilyFiniteBar.firstModule E S F m) r)
  rw [signedProjectiveDimension_shift, ← signedProjectiveDimension_iso e]

theorem even_count_dimension (m : ℕ+) (j : Fin m.val) :
    signedProjectiveDimension (SelectingFiniteBar.count E S
      (SelectingFamilyFiniteBar.firstModule E S F m) (2*j.val)) =
      ((((epsilon E S F m j:ℤ)+(j.val:ℤ)*(SelectingOrdinaryAlgebra.b E S+5)):WithTop ℤ):
        WithBot (WithTop ℤ)) := by
  have h := (Classical.choose_spec
    (SelectingFamilyEvenSigned.even_signed_dimension_exists E S F m j.val j.isLt)).2.2
  rw [count_signed E S F m (2*j.val), h]
  change ((((epsilon E S F m j:ℤ)+(j.val:ℤ)*SelectingOrdinaryAlgebra.b E S+
    3*(j.val:ℤ)+(2*j.val:ℕ)):WithTop ℤ):WithBot (WithTop ℤ)) = _
  have hn : (epsilon E S F m j : ℤ) + (j.val : ℤ) * SelectingOrdinaryAlgebra.b E S +
      3 * (j.val : ℤ) + ((2*j.val : ℕ) : ℤ) =
        (epsilon E S F m j : ℤ) + (j.val : ℤ) * (SelectingOrdinaryAlgebra.b E S+5) := by
    push_cast
    ring
  exact congrArg (fun x : ℤ => ((x : WithTop ℤ) : WithBot (WithTop ℤ))) hn

theorem odd_count_dimension (m : ℕ+) (j : Fin m.val) :
    signedProjectiveDimension (SelectingFiniteBar.count E S
      (SelectingFamilyFiniteBar.firstModule E S F m) (2*j.val+1)) =
      ((((delta E S F m j:ℤ)+(j.val:ℤ)*(SelectingOrdinaryAlgebra.b E S+5)+1):WithTop ℤ):
        WithBot (WithTop ℤ)) := by
  have h := (Classical.choose_spec
    (SelectingFamilyOddSigned.odd_signed_dimension_exists E S F m j.val j.isLt)).2.2
  rw [count_signed E S F m (2*j.val+1), h]
  change ((((delta E S F m j:ℤ)+(j.val:ℤ)*SelectingOrdinaryAlgebra.b E S+
    3*(j.val:ℤ)+(2*j.val+1:ℕ)):WithTop ℤ):WithBot (WithTop ℤ)) = _
  have hn : (delta E S F m j : ℤ) + (j.val : ℤ) * SelectingOrdinaryAlgebra.b E S +
      3 * (j.val : ℤ) + ((2*j.val+1 : ℕ) : ℤ) =
        (delta E S F m j : ℤ) + (j.val : ℤ) * (SelectingOrdinaryAlgebra.b E S+5)+1 := by
    push_cast
    ring
  exact congrArg (fun x : ℤ => ((x : WithTop ℤ) : WithBot (WithTop ℤ))) hn
end
end Note198.SelectingFamilyCountDimensions
