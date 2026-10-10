import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.CompleteLattice.Lemmas
import Mathlib.Order.TypeTags
import Mathlib.Tactic
import Note198.Arithmetic

namespace Note198.FiniteMaximum
noncomputable section
variable (b l m : ℕ) (epsilon delta : Fin m → ℕ)

/-- The two actual finite-pd contributions in the manuscript's maximum.
The inputs epsilon and delta are supplied by the B- and E-module proofs. -/
def value : Sum (Fin m) (Fin m) → ℕ
  | .inl j => (b+5)*j.val + epsilon j
  | .inr j => (b+5)*j.val + 1 + delta j

def maximum : ℕ := Finset.univ.sup (value b m epsilon delta)

theorem term_le_maximum (i : Sum (Fin m) (Fin m)) :
    value b m epsilon delta i ≤ maximum b m epsilon delta :=
  Finset.le_sup (Finset.mem_univ i)

theorem bounds (hm : 0 < m) (he : ∀ j, epsilon j ≤ 2)
    (hd : ∀ j, delta j ≤ l+2) :
    (b+5)*(m-1)+1 ≤ maximum b m epsilon delta ∧
      maximum b m epsilon delta ≤ (b+5)*(m-1)+l+3 := by
  constructor
  · let j : Fin m := ⟨m-1,by omega⟩
    have hj := term_le_maximum b m epsilon delta (Sum.inr j)
    change (b+5)*(m-1)+1+delta j ≤ maximum b m epsilon delta at hj
    omega
  · apply Finset.sup_le
    intro i _
    rcases i with j | j
    · exact (Note198.final_term_upper_bounds b l m j.val
        (epsilon j) (delta j) j.isLt (he j) (hd j)).1
    · exact (Note198.final_term_upper_bounds b l m j.val
        (epsilon j) (delta j) j.isLt (he j) (hd j)).2

theorem signed_maximum (hm : 0 < m) :
    (⨆ i : Sum (Fin m) (Fin m),
      ((((value b m epsilon delta i : ℕ):ℤ):WithTop ℤ):WithBot (WithTop ℤ))) =
      ((((maximum b m epsilon delta : ℕ):ℤ):WithTop ℤ):WithBot (WithTop ℤ)) := by
  apply le_antisymm
  · apply iSup_le
    intro i
    exact_mod_cast term_le_maximum b m epsilon delta i
  · have hne : (Finset.univ : Finset (Sum (Fin m) (Fin m))).Nonempty :=
      ⟨Sum.inl ⟨0,hm⟩,Finset.mem_univ _⟩
    obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup Finset.univ hne
      (value b m epsilon delta)
    change maximum b m epsilon delta = value b m epsilon delta i at hi
    rw [hi]
    exact le_iSup (fun j : Sum (Fin m) (Fin m) =>
      ((((value b m epsilon delta j : ℕ) : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))) i

theorem natural_maximum (hm : 0 < m) :
    (⨆ i : Sum (Fin m) (Fin m),
      (value b m epsilon delta i : WithBot ℕ∞)) =
      (maximum b m epsilon delta : WithBot ℕ∞) := by
  apply le_antisymm
  · apply iSup_le
    intro i
    exact_mod_cast term_le_maximum b m epsilon delta i
  · have hne : (Finset.univ : Finset (Sum (Fin m) (Fin m))).Nonempty :=
      ⟨Sum.inl ⟨0,hm⟩,Finset.mem_univ _⟩
    obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup Finset.univ hne
      (value b m epsilon delta)
    change maximum b m epsilon delta = value b m epsilon delta i at hi
    rw [hi]
    exact le_iSup (fun j : Sum (Fin m) (Fin m) =>
      (value b m epsilon delta j : WithBot ℕ∞)) i

end
end Note198.FiniteMaximum
