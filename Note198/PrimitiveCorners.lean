import Note198.RadicalBlockBridge
import Note198.DirectedRadical

namespace Note198
noncomputable section
open OAI.LittleFinitistic.OrdinarySimulation
universe u

/-- The algebraic definition of a primitive idempotent: a nonzero idempotent
has no decomposition as a sum of two nonzero orthogonal idempotents. -/
def IsPrimitiveIdempotent {A : Type u} [Ring A] (e : A) : Prop :=
  e ≠ 0 ∧ e * e = e ∧ ∀ f g : A,
    f * f = f → g * g = g → f * g = 0 → g * f = 0 → f + g = e → f = 0 ∨ g = 0

theorem primitive_of_scalar_corner {k A : Type u} [Field k] [Ring A] [Algebra k A]
    (e : A) (hne : e ≠ 0) (hid : e * e = e)
    (hcorner : ∀ a : A, ∃ c : k, e * a * e = c • e) : IsPrimitiveIdempotent e := by
  refine ⟨hne, hid, ?_⟩
  intro f g hf _hg hfg hgf hsum
  have hef : e * f = f := by rw [← hsum, add_mul, hf, hgf, add_zero]
  have hfe : f * e = f := by rw [← hsum, mul_add, hf, hfg, add_zero]
  have hefe : e * f * e = f := by rw [hef, hfe]
  obtain ⟨c, hc⟩ := hcorner f
  have hscale : f = c • e := by simpa only [hefe] using hc
  have hcidem : c * c = c := by
    apply smul_left_injective k hne
    calc
      (c * c) • e = (c • e) * (c • e) := by rw [smul_mul_smul_comm, hid]
      _ = f * f := by rw [← hscale]
      _ = f := hf
      _ = c • e := hscale
  have hczero : c * (c - 1) = 0 := by rw [mul_sub, mul_one, hcidem, sub_self]
  rcases mul_eq_zero.mp hczero with hzero | hone
  · left; simpa [hzero] using hscale
  · right
    have hc1 : c = 1 := sub_eq_zero.mp hone
    have hfeq : f = e := by simpa [hc1] using hscale
    have hh : e + g = e + 0 := by simpa [hfeq] using hsum
    exact add_left_cancel hh

section OffDiagonal
variable {k L R O T : Type u} [Field k] [Ring L] [Ring R]
  [Algebra k L] [Algebra k R]
  [AddCommGroup O] [AddCommGroup T] [Module k O] [Module k T]
  [Module R O] [Module L T] [Module Lᵐᵒᵖ O] [Module Rᵐᵒᵖ T]
  [SMulCommClass R Lᵐᵒᵖ O] [SMulCommClass L Rᵐᵒᵖ T]
  [IsScalarTower k R O] [IsScalarTower k L T]
  [IsScalarTower k Lᵐᵒᵖ O] [IsScalarTower k Rᵐᵒᵖ T]

theorem off_diagonal_first_corner (e : L)
    (a : TrivSqZeroExt (L × R) (OffDiagonal O T)) :
    TrivSqZeroExt.inl (e, (0 : R)) * a * TrivSqZeroExt.inl (e, (0 : R)) =
      TrivSqZeroExt.inl (e * a.fst.1 * e, (0 : R)) := by
  apply TrivSqZeroExt.ext
  · apply Prod.ext <;> simp [TrivSqZeroExt.fst_mul]
  · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.fst_inl, smul_zero, zero_add, add_zero]
    apply Prod.ext
    · change MulOpposite.op e • ((0 : R) • a.snd.1) = 0
      simp
    · change MulOpposite.op (0 : R) • (e • a.snd.2) = 0
      simp

theorem off_diagonal_second_corner (e : R)
    (a : TrivSqZeroExt (L × R) (OffDiagonal O T)) :
    TrivSqZeroExt.inl ((0 : L), e) * a * TrivSqZeroExt.inl ((0 : L), e) =
      TrivSqZeroExt.inl ((0 : L), e * a.fst.2 * e) := by
  apply TrivSqZeroExt.ext
  · apply Prod.ext <;> simp [TrivSqZeroExt.fst_mul]
  · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.fst_inl, smul_zero, zero_add, add_zero]
    apply Prod.ext
    · change MulOpposite.op (0 : L) • (e • a.snd.1) = 0
      simp
    · change MulOpposite.op e • ((0 : L) • a.snd.2) = 0
      simp

theorem off_diagonal_first_scalar_corner (e : L)
    (hcorner : ∀ d : L, ∃ c : k, e * d * e = c • e)
    (a : TrivSqZeroExt (L × R) (OffDiagonal O T)) :
    ∃ c : k, TrivSqZeroExt.inl (e, (0 : R)) * a * TrivSqZeroExt.inl (e, (0 : R)) =
      c • TrivSqZeroExt.inl (e, (0 : R)) := by
  obtain ⟨c, hc⟩ := hcorner a.fst.1
  refine ⟨c, ?_⟩
  rw [off_diagonal_first_corner, hc]
  apply TrivSqZeroExt.ext
  · apply Prod.ext <;> simp
  · simp

theorem off_diagonal_second_scalar_corner (e : R)
    (hcorner : ∀ d : R, ∃ c : k, e * d * e = c • e)
    (a : TrivSqZeroExt (L × R) (OffDiagonal O T)) :
    ∃ c : k, TrivSqZeroExt.inl ((0 : L), e) * a * TrivSqZeroExt.inl ((0 : L), e) =
      c • TrivSqZeroExt.inl ((0 : L), e) := by
  obtain ⟨c, hc⟩ := hcorner a.fst.2
  refine ⟨c, ?_⟩
  rw [off_diagonal_second_corner, hc]
  apply TrivSqZeroExt.ext
  · apply Prod.ext <;> simp
  · simp

theorem off_diagonal_first_primitive (e : L) (hne : e ≠ 0) (hid : e * e = e)
    (hcorner : ∀ d : L, ∃ c : k, e * d * e = c • e) :
    IsPrimitiveIdempotent (TrivSqZeroExt.inl (e, (0 : R)) :
      TrivSqZeroExt (L × R) (OffDiagonal O T)) := by
  apply primitive_of_scalar_corner (k := k)
  · intro h
    exact hne (congrArg (fun a : TrivSqZeroExt (L × R) (OffDiagonal O T) => a.fst.1) h)
  · apply TrivSqZeroExt.ext
    · apply Prod.ext <;> simp [TrivSqZeroExt.fst_mul, hid]
    · simp [TrivSqZeroExt.snd_mul]
  · exact off_diagonal_first_scalar_corner e hcorner

theorem off_diagonal_second_primitive (e : R) (hne : e ≠ 0) (hid : e * e = e)
    (hcorner : ∀ d : R, ∃ c : k, e * d * e = c • e) :
    IsPrimitiveIdempotent (TrivSqZeroExt.inl ((0 : L), e) :
      TrivSqZeroExt (L × R) (OffDiagonal O T)) := by
  apply primitive_of_scalar_corner (k := k)
  · intro h
    exact hne (congrArg (fun a : TrivSqZeroExt (L × R) (OffDiagonal O T) => a.fst.2) h)
  · apply TrivSqZeroExt.ext
    · apply Prod.ext <;> simp [TrivSqZeroExt.fst_mul, hid]
    · simp [TrivSqZeroExt.snd_mul]
  · exact off_diagonal_second_scalar_corner e hcorner

end OffDiagonal
end
end Note198
