import Note198.EvaluationLoewy
import Note198.InflationHom
import Note198.Radical
import Mathlib.RingTheory.Ideal.Prod

namespace Note198
noncomputable section
open OAI.LittleFinitistic OAI.LittleFinitistic.QuadraticEncoding
universe u v

/-- Ideal powers respect a ring map in the required direction also for
noncommutative rings. -/
theorem ideal_power_le_comap {A B : Type u} [Ring A] [Ring B]
    (f : A →+* B) (I : Ideal A) (J : Ideal B) (h : I ≤ Ideal.comap f J) (n : ℕ) :
    I^n ≤ Ideal.comap f (J^n) := by
  induction n with
  | zero =>
    simp only [Submodule.pow_zero,Ideal.one_eq_top,Ideal.comap_top]
    exact le_top
  | succ n ih =>
    rw [Submodule.pow_succ,Submodule.pow_succ]
    apply Ideal.mul_le.mpr
    intro a ha b hb
    change f (a*b) ∈ J^n * J
    rw [map_mul]
    exact Ideal.mul_mem_mul (ih ha) (h hb)

variable {k S Q : Type u} [Field k] [Ring S] [Algebra k S]
  [AddCommGroup Q] [Module k Q]
variable {d t : ℕ} (P : Relations k d t)

/-- A radical element in B remains radical in the first product block.
The proof uses the actual nilpotent product ideal, not a radical certificate. -/
theorem encoding_product_radical_left (b : B P) (hb : b ∈ Ring.jacobson (B P)) :
    (b,0) ∈ Ring.jacobson (B P × S) := by
  let I := (Ring.jacobson (B P)).prod (⊥ : Ideal S)
  have hi : I^3 = ⊥ := by
    apply ideal_power_zero_of_words _ 3
    intro ds hlen hall
    apply Prod.ext
    · change (RingHom.fst (B P) S) ds.prod = 0
      rw [map_list_prod]
      apply three_vertex_radical_words_zero (composition P)
      · intro a ha
        obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ha
        exact ((Ideal.mem_prod (Ring.jacobson (B P)) (⊥ : Ideal S)).mp (hall z hz)).1
      · simpa only [List.length_map] using hlen.ge
    · cases ds with
      | nil => simp at hlen
      | cons a ds =>
        have ha : a.2 = 0 := ((Ideal.mem_prod (Ring.jacobson (B P)) (⊥ : Ideal S)).mp (hall a (by simp))).2
        simp only [List.prod_cons]
        change a.2 * ds.prod.2 = 0
        rw [ha,zero_mul]
  exact nilpotent_ideal_le_jacobson I 3 hi ((Ideal.mem_prod (Ring.jacobson (B P)) (⊥ : Ideal S)).mpr ⟨hb,by simp⟩)

variable [Module (B P × S) Q] [Module (B P × S)ᵐᵒᵖ Q]
  [IsScalarTower k (B P × S) Q] [IsScalarTower k (B P × S)ᵐᵒᵖ Q]
  [SMulCommClass (B P × S) (B P × S)ᵐᵒᵖ Q]

theorem selecting_lift_encoding_radical (b : B P) (hb : b ∈ Ring.jacobson (B P)) :
    (TrivSqZeroExt.inl (b,0) : TrivSqZeroExt (B P × S) Q) ∈
      Ring.jacobson (TrivSqZeroExt (B P × S) Q) := by
  rw [square_zero_radical (k := k)]
  exact encoding_product_radical_left P b hb

variable {Y : Type v} [AddCommGroup Y] [Module k Y] (W : Representation P Y)

/-- J_A^3 annihilates the actual inflated evaluation module even though
J_A^3 need not itself vanish. -/
theorem inflated_evaluation_cube_annihilates
    (a : TrivSqZeroExt (B P × S) Q)
    (ha : a ∈ Ring.jacobson (TrivSqZeroExt (B P × S) Q)^3)
    (y : RingInflation (selecting_first_projection (k := k) (L := B P) (R := S) (X := Q))
      W.Evaluation) : a • y = 0 := by
  let f := selecting_first_projection (k := k) (L := B P) (R := S) (X := Q)
  letI : RingHomSurjective f := ⟨selecting_first_projection_surjective⟩
  have h := ideal_power_le_comap f (Ring.jacobson _) (Ring.jacobson _) (Ring.le_comap_jacobson f) 3 ha
  change f a ∈ Ring.jacobson (B P)^3 at h
  exact evaluation_radical_cube_annihilates P W (f a) h y

/-- Both distinguished arrows lift into J_A, and their product carries
the first copy of a nonzero vector into the third copy. -/
theorem inflated_evaluation_square_nonzero [Nontrivial Y] :
    ∃ a ∈ Ring.jacobson (TrivSqZeroExt (B P × S) Q)^2,
      ∃ y : RingInflation (selecting_first_projection (k := k) (L := B P) (R := S) (X := Q))
        W.Evaluation, a • y ≠ 0 := by
  obtain ⟨y,hy⟩ := exists_ne (0 : Y)
  let a01 : TrivSqZeroExt (B P × S) Q := TrivSqZeroExt.inl (arrow01 P 0,0)
  let a12 : TrivSqZeroExt (B P × S) Q := TrivSqZeroExt.inl (arrow12 P 0,0)
  refine ⟨a12*a01,?_,(y,0,0),?_⟩
  · rw [Submodule.pow_succ,Submodule.pow_one]
    exact Ideal.mul_mem_mul
      (selecting_lift_encoding_radical (S := S) (Q := Q) P _ (encoding_arrow12_mem_radical P 0))
      (selecting_lift_encoding_radical (S := S) (Q := Q) P _ (encoding_arrow01_mem_radical P 0))
  · change (arrow12 P 0 * arrow01 P 0) • (show W.Evaluation from (y,0,0)) ≠ 0
    have h01 : arrow01 P 0 • (show W.Evaluation from (y,0,0)) =
        (show W.Evaluation from (0,y,0)) := W.s_smul _
    have h12 : arrow12 P 0 • (show W.Evaluation from (0,y,0)) =
        (show W.Evaluation from (0,0,y)) := W.s'_smul _
    have hact : (arrow12 P 0 * arrow01 P 0) • (show W.Evaluation from (y,0,0)) =
        (show W.Evaluation from (0,0,y)) :=
      (mul_smul (arrow12 P 0) (arrow01 P 0) (show W.Evaluation from (y,0,0))).trans
        ((congrArg (fun z : W.Evaluation => arrow12 P 0 • z) h01).trans h12)
    intro h
    exact hy (congrArg (fun z : W.Evaluation => z.2.2) (hact.symm.trans h))

theorem inflated_evaluation_loewy_exact_three [Nontrivial Y] :
    (∀ a ∈ Ring.jacobson (TrivSqZeroExt (B P × S) Q)^3,
      ∀ y : RingInflation (selecting_first_projection (k := k) (L := B P) (R := S) (X := Q))
        W.Evaluation, a • y = 0) ∧
    (∃ a ∈ Ring.jacobson (TrivSqZeroExt (B P × S) Q)^2,
      ∃ y : RingInflation (selecting_first_projection (k := k) (L := B P) (R := S) (X := Q))
        W.Evaluation, a • y ≠ 0) :=
  ⟨inflated_evaluation_cube_annihilates P W,inflated_evaluation_square_nonzero P W⟩

end
end Note198
