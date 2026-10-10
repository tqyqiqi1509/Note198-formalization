import OAI.Algebra.Finitistic.Dimension.PDSquareZero
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Data.List.Enum
import Lean.Elab.Tactic.Omega

namespace Note198
noncomputable section
universe u

section SquareZero
variable {k D X : Type u} [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [Module k X]
  [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

/-- The actual radical identity used in Proposition 7.1, valid over any field.
The inverse image places no restriction on the square-zero coordinate. -/
theorem square_zero_radical :
    Ring.jacobson (TrivSqZeroExt D X) =
      Ideal.comap (TrivSqZeroExt.fstHom k D X).toRingHom (Ring.jacobson D) :=
  OAI.LittleFinitistic.PDSquareZero.radical_eq_comap X

end SquareZero

section SevenWords
variable {D X : Type u} [Ring D] [AddCommGroup X]
  [Module D X] [Module Dᵐᵒᵖ X] [SMulCommClass D Dᵐᵒᵖ X]

/-- The seven-factor word calculation in Proposition 7.1.
`S` represents the radical of D. `O` and `T` represent the two summands of X.
The hypotheses encode D-radical words of length four, right annihilation
of O by length-three words, and left annihilation of T by length-three words.
This proves the noncommutative calculation in the actual square-zero ring;
it does not identify these predicates with the manuscript's constructed
bimodules or prove their annihilation hypotheses. -/
theorem square_zero_seven_word
    (S : Set D) (O T : X → Prop)
    (base_zero : ∀ ds : List D, (∀ d ∈ ds, d ∈ S) → 4 ≤ ds.length → ds.prod = 0)
    (decompose : ∀ x : X, ∃ o t, O o ∧ T t ∧ x = o + t)
    (right_O : ∀ o, O o → ∀ ds : List D,
      (∀ d ∈ ds, d ∈ S) → 3 ≤ ds.length → MulOpposite.op ds.prod • o = 0)
    (left_T : ∀ t, T t → ∀ ds : List D,
      (∀ d ∈ ds, d ∈ S) → 3 ≤ ds.length → ds.prod • t = 0)
    (xs : List (TrivSqZeroExt D X)) (length_seven : xs.length = 7)
    (coordinates : ∀ a ∈ xs, a.fst ∈ S) : xs.prod = 0 := by
  have allS : ∀ d ∈ xs.map TrivSqZeroExt.fst, d ∈ S := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
    exact coordinates a ha
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_list_prod]
    exact base_zero _ allS (by simpa [length_seven])
  · rw [TrivSqZeroExt.snd_list_prod]
    apply List.sum_eq_zero
    intro y hy
    obtain ⟨⟨a, i⟩, hi, rfl⟩ := List.mem_map.mp hy
    have hi_lt : i < xs.length := List.snd_lt_of_mem_zipIdx hi
    have hpre : ∀ d ∈ (xs.map TrivSqZeroExt.fst).take i, d ∈ S :=
      fun d hd => allS d (List.mem_of_mem_take hd)
    have hsuf : ∀ d ∈ (xs.map TrivSqZeroExt.fst).drop (i + 1), d ∈ S :=
      fun d hd => allS d (List.mem_of_mem_drop hd)
    by_cases hp : 4 ≤ i
    · have hz := base_zero _ hpre (by simp only [List.length_take, List.length_map]; omega)
      simp [hz]
    · by_cases hs : 4 ≤ 7 - (i + 1)
      · have hz := base_zero _ hsuf (by simpa only [List.length_drop, List.length_map,
          length_seven] using hs)
        simp [hz]
      · obtain ⟨o, t, ho, ht, hat⟩ := decompose a.snd
        have hlenpre : 3 ≤ ((xs.map TrivSqZeroExt.fst).take i).length := by
          simp only [List.length_take, List.length_map]
          omega
        have hlensuf : 3 ≤ ((xs.map TrivSqZeroExt.fst).drop (i + 1)).length := by
          simp only [List.length_drop, List.length_map]
          omega
        have hozero := right_O o ho _ hsuf hlensuf
        have htzero := left_T t ht _ hpre hlenpre
        simp only [hat, smul_add]
        rw [← smul_comm ((xs.map TrivSqZeroExt.fst).take i).prod
          (MulOpposite.op ((xs.map TrivSqZeroExt.fst).drop (i + 1)).prod) o]
        simp [hozero, htzero]

end SevenWords

section RadicalWords
variable {k D X : Type u} [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [Module k X]
  [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

include k

/-- Every seven-factor word in the actual Jacobson radical vanishes,
provided the base and bimodule annihilation conditions have been established.
The concrete construction of those conditions remains a separate task. -/
theorem radical_seven_word (O T : X → Prop)
    (base_zero : ∀ ds : List D, (∀ d ∈ ds, d ∈ Ring.jacobson D) →
      4 ≤ ds.length → ds.prod = 0)
    (decompose : ∀ x : X, ∃ o t, O o ∧ T t ∧ x = o + t)
    (right_O : ∀ o, O o → ∀ ds : List D,
      (∀ d ∈ ds, d ∈ Ring.jacobson D) →
      3 ≤ ds.length → MulOpposite.op ds.prod • o = 0)
    (left_T : ∀ t, T t → ∀ ds : List D,
      (∀ d ∈ ds, d ∈ Ring.jacobson D) → 3 ≤ ds.length → ds.prod • t = 0)
    (xs : List (TrivSqZeroExt D X)) (length_seven : xs.length = 7)
    (radical_factors : ∀ a ∈ xs, a ∈ Ring.jacobson (TrivSqZeroExt D X)) :
    xs.prod = 0 := by
  apply square_zero_seven_word (Ring.jacobson D : Set D) O T
    base_zero decompose right_O left_T xs length_seven
  intro a ha
  have hr := radical_factors a ha
  rw [square_zero_radical (k := k)] at hr
  exact hr

end RadicalWords
end
end Note198
