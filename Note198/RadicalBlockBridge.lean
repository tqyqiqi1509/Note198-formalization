import Note198.Radical
import Note198.RadicalWordPowers
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBlockBimodule

namespace Note198
noncomputable section
open OAI.LittleFinitistic.OrdinarySimulation
universe u

section Blocks
variable {k L R O T : Type u} [Field k] [Ring L] [Ring R]
  [Algebra k L] [Algebra k R]
  [AddCommGroup O] [AddCommGroup T] [Module k O] [Module k T]
  [Module R O] [Module L T] [Module Lᵐᵒᵖ O] [Module Rᵐᵒᵖ T]
  [SMulCommClass R Lᵐᵒᵖ O] [SMulCommClass L Rᵐᵒᵖ T]
  [IsScalarTower k R O] [IsScalarTower k L T]
  [IsScalarTower k Lᵐᵒᵖ O] [IsScalarTower k Rᵐᵒᵖ T]

/-- Projection from the radical of a product to the radical of the first ring. -/
theorem product_radical_fst {d : L × R} (hd : d ∈ Ring.jacobson (L × R)) :
    d.1 ∈ Ring.jacobson L := by
  let f : L × R →+* L := RingHom.fst L R
  letI : RingHomSurjective f := ⟨fun x => ⟨(x, 0), rfl⟩⟩
  exact Ring.le_comap_jacobson f hd

/-- Projection from the radical of a product to the radical of the second ring. -/
theorem product_radical_snd {d : L × R} (hd : d ∈ Ring.jacobson (L × R)) :
    d.2 ∈ Ring.jacobson R := by
  let f : L × R →+* R := RingHom.snd L R
  letI : RingHomSurjective f := ⟨fun x => ⟨(0, x), rfl⟩⟩
  exact Ring.le_comap_jacobson f hd

include k

/-- Proposition 7.1's seven-word bound for the actual off-diagonal
square-zero extension. Here L is B and R is E in the manuscript.
Only nilpotence of words in the two base radicals remains as a hypothesis;
the decomposition and both bimodule annihilation conditions are proved
from the actual upstream OffDiagonal actions. -/
theorem off_diagonal_radical_seven_word
    (left_three : ∀ ds : List L, (∀ d ∈ ds, d ∈ Ring.jacobson L) →
      3 ≤ ds.length → ds.prod = 0)
    (right_four : ∀ ds : List R, (∀ d ∈ ds, d ∈ Ring.jacobson R) →
      4 ≤ ds.length → ds.prod = 0)
    (xs : List (TrivSqZeroExt (L × R) (OffDiagonal O T)))
    (length_seven : xs.length = 7)
    (radical_factors : ∀ a ∈ xs,
      a ∈ Ring.jacobson (TrivSqZeroExt (L × R) (OffDiagonal O T))) :
    xs.prod = 0 := by
  have fst_zero (ds : List (L × R))
      (hall : ∀ d ∈ ds, d ∈ Ring.jacobson (L × R)) (hlen : 3 ≤ ds.length) :
      ds.prod.1 = 0 := by
    change (RingHom.fst L R) ds.prod = 0
    rw [map_list_prod]
    apply left_three
    · intro d hd
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
      exact product_radical_fst (hall a ha)
    · simpa only [List.length_map] using hlen
  have snd_zero (ds : List (L × R))
      (hall : ∀ d ∈ ds, d ∈ Ring.jacobson (L × R)) (hlen : 4 ≤ ds.length) :
      ds.prod.2 = 0 := by
    change (RingHom.snd L R) ds.prod = 0
    rw [map_list_prod]
    apply right_four
    · intro d hd
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
      exact product_radical_snd (hall a ha)
    · simpa only [List.length_map] using hlen
  apply radical_seven_word (k := k)
    (fun x : OffDiagonal O T => x.2 = 0)
    (fun x : OffDiagonal O T => x.1 = 0)
    _ _ _ _ xs length_seven radical_factors
  · intro ds hall hlen
    exact Prod.ext (fst_zero ds hall (by omega)) (snd_zero ds hall hlen)
  · intro x
    refine ⟨(x.1, 0), (0, x.2), rfl, rfl, ?_⟩
    apply Prod.ext
    · change x.1 = x.1 + 0
      exact (add_zero x.1).symm
    · change x.2 = 0 + x.2
      exact (zero_add x.2).symm
  · intro x hx ds hall hlen
    have hz := fst_zero ds hall hlen
    apply Prod.ext
    · change MulOpposite.op ds.prod.1 • x.1 = 0
      simp [hz]
    · change MulOpposite.op ds.prod.2 • x.2 = 0
      simp [hx]
  · intro x hx ds hall hlen
    have hz := fst_zero ds hall hlen
    apply Prod.ext
    · change ds.prod.2 • x.1 = 0
      simp [hx]
    · change ds.prod.1 • x.2 = 0
      simp [hz]

/-- The actual seventh Jacobson-radical power vanishes, under the two
base-radical bounds. This is an ideal equality, not only a word calculation. -/
theorem off_diagonal_radical_pow_seven_zero
    (left_three : ∀ ds : List L, (∀ d ∈ ds, d ∈ Ring.jacobson L) →
      3 ≤ ds.length → ds.prod = 0)
    (right_four : ∀ ds : List R, (∀ d ∈ ds, d ∈ Ring.jacobson R) →
      4 ≤ ds.length → ds.prod = 0) :
    Ring.jacobson (TrivSqZeroExt (L × R) (OffDiagonal O T)) ^ 7 = ⊥ := by
  apply ideal_power_zero_of_words _ 7
  intro ds hlen hall
  exact off_diagonal_radical_seven_word (k := k) left_three right_four ds hlen hall

end Blocks
end
end Note198
