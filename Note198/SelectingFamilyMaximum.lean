import Note198.SelectingFamilyCountDimensions
import Note198.FiniteMaximum

namespace Note198.SelectingFamilyMaximum
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
open SelectingFamilyCountDimensions ComplexProjectiveDimension
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
variable (F : SelectingBrickFamily.SourceFamily k R S)

abbrev coefficient := (SelectingOrdinaryAlgebra.b E S).toNat
def maximum (m : ℕ+) : ℕ := FiniteMaximum.maximum (coefficient E S) m.val
  (epsilon E S F m) (delta E S F m)

theorem even_value (m : ℕ+) (j : Fin m.val) :
    signedProjectiveDimension (SelectingFiniteBar.count E S
      (SelectingFamilyFiniteBar.firstModule E S F m) (2*j.val)) =
      ((((FiniteMaximum.value (coefficient E S) m.val
        (epsilon E S F m) (delta E S F m) (Sum.inl j):ℕ):ℤ):WithTop ℤ):
        WithBot (WithTop ℤ)) := by
  rw [even_count_dimension E S F m j]
  have hv : (epsilon E S F m j : ℤ) + (j.val : ℤ) *
      (SelectingOrdinaryAlgebra.b E S+5) =
      ((FiniteMaximum.value (coefficient E S) m.val
        (epsilon E S F m) (delta E S F m)
        (Sum.inl j) : ℕ) : ℤ) := by
    dsimp [FiniteMaximum.value,coefficient]
    push_cast
    rw [Int.toNat_of_nonneg (SelectingOrdinaryAlgebra.b_nonneg E S)]
    ring
  exact congrArg (fun x : ℤ => ((x : WithTop ℤ) : WithBot (WithTop ℤ))) hv

theorem odd_value (m : ℕ+) (j : Fin m.val) :
    signedProjectiveDimension (SelectingFiniteBar.count E S
      (SelectingFamilyFiniteBar.firstModule E S F m) (2*j.val+1)) =
      ((((FiniteMaximum.value (coefficient E S) m.val
        (epsilon E S F m) (delta E S F m) (Sum.inr j):ℕ):ℤ):WithTop ℤ):
        WithBot (WithTop ℤ)) := by
  rw [odd_count_dimension E S F m j]
  have hv : (delta E S F m j : ℤ) + (j.val : ℤ) *
      (SelectingOrdinaryAlgebra.b E S+5)+1 =
      ((FiniteMaximum.value (coefficient E S) m.val
        (epsilon E S F m) (delta E S F m)
        (Sum.inr j) : ℕ) : ℤ) := by
    dsimp [FiniteMaximum.value,coefficient]
    push_cast
    rw [Int.toNat_of_nonneg (SelectingOrdinaryAlgebra.b_nonneg E S)]
    ring
  exact congrArg (fun x : ℤ => ((x : WithTop ℤ) : WithBot (WithTop ℤ))) hv

/-- Reindex the actual surviving counts by their even and odd contributions.
Every count and every contribution occurs, including the final odd term. -/
theorem count_maximum (m : ℕ+) :
    (⨆ r : Fin (2*m.val), signedProjectiveDimension
      (SelectingFiniteBar.count E S (SelectingFamilyFiniteBar.firstModule E S F m) r.val)) =
      ((((maximum E S F m:ℕ):ℤ):WithTop ℤ):WithBot (WithTop ℤ)) := by
  rw [maximum, ← FiniteMaximum.signed_maximum _ _ _ _ m.pos]
  apply le_antisymm
  · apply iSup_le
    intro r
    let j : Fin m.val := ⟨r.val/2,by omega⟩
    by_cases h : r.val % 2 = 0
    · have hr : r.val = 2*j.val := by dsimp [j]; omega
      rw [hr,even_value E S F m j]
      exact le_iSup (fun i : Sum (Fin m.val) (Fin m.val) =>
        ((((FiniteMaximum.value (coefficient E S) m.val
          (epsilon E S F m) (delta E S F m) i : ℕ) : ℤ) : WithTop ℤ) :
            WithBot (WithTop ℤ))) (Sum.inl j)
    · have hr : r.val = 2*j.val+1 := by dsimp [j]; omega
      rw [hr,odd_value E S F m j]
      exact le_iSup (fun i : Sum (Fin m.val) (Fin m.val) =>
        ((((FiniteMaximum.value (coefficient E S) m.val
          (epsilon E S F m) (delta E S F m) i : ℕ) : ℤ) : WithTop ℤ) :
            WithBot (WithTop ℤ))) (Sum.inr j)
  · apply iSup_le
    intro i
    rcases i with j | j
    · have h := le_iSup (fun r : Fin (2*m.val) =>
        signedProjectiveDimension (SelectingFiniteBar.count E S
          (SelectingFamilyFiniteBar.firstModule E S F m) r.val))
        (⟨2*j.val,by omega⟩ : Fin (2*m.val))
      simpa only [even_value E S F m j] using h
    · have h := le_iSup (fun r : Fin (2*m.val) =>
        signedProjectiveDimension (SelectingFiniteBar.count E S
          (SelectingFamilyFiniteBar.firstModule E S F m) r.val))
        (⟨2*j.val+1,by omega⟩ : Fin (2*m.val))
      simpa only [odd_value E S F m j] using h

theorem maximum_bounds (m : ℕ+) :
    (coefficient E S+5)*(m.val-1)+1 ≤ maximum E S F m ∧
      maximum E S F m ≤ (coefficient E S+5)*(m.val-1)+
        SelectingOrdinaryAlgebra.length E S+3 :=
  FiniteMaximum.bounds _ _ _ _ _ m.pos
    (epsilon_bound E S F m) (delta_bound E S F m)

end
end Note198.SelectingFamilyMaximum
