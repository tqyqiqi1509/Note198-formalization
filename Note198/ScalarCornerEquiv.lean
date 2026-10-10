import Note198.PrimitiveCorners
import Mathlib.RingTheory.Idempotents

namespace Note198
noncomputable section
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- The scalar embedding into the actual corner ring, whose identity is e. -/
def scalar_corner_embedding (e : A) (he : IsIdempotentElem e) : k →+* he.Corner where
  toFun c := ⟨c • e, c • e, by simp [mul_smul_comm, smul_mul_assoc, he.eq]⟩
  map_zero' := by apply Subtype.ext; change (0 : k) • e = (0 : A); simp
  map_one' := by apply Subtype.ext; change (1 : k) • e = e; simp
  map_add' c d := by apply Subtype.ext; change (c+d) • e = c • e + d • e; exact add_smul c d e
  map_mul' c d := by
    apply Subtype.ext
    change (c*d) • e = (c • e) * (d • e)
    simp [smul_mul_smul_comm,he.eq,smul_smul,mul_comm]

theorem scalar_corner_embedding_injective (e : A) (he : IsIdempotentElem e) (hne : e ≠ 0) :
    Function.Injective (scalar_corner_embedding (k := k) e he) := by
  intro c d h
  exact smul_left_injective k hne (congrArg Subtype.val h)

theorem scalar_corner_embedding_surjective (e : A) (he : IsIdempotentElem e)
    (hcorner : ∀ a : A, ∃ c : k, e * a * e = c • e) :
    Function.Surjective (scalar_corner_embedding (k := k) e he) := by
  intro y
  obtain ⟨a, ha⟩ := y.property
  obtain ⟨c, hc⟩ := hcorner a
  refine ⟨c, Subtype.ext ?_⟩
  change c • e = y.val
  exact hc.symm.trans ha

/-- The actual corner ring is the ground field; the inverse equivalence
sends c to c times the vertex idempotent. -/
def scalar_corner_ring_equiv (e : A) (he : IsIdempotentElem e) (hne : e ≠ 0)
    (hcorner : ∀ a : A, ∃ c : k, e * a * e = c • e) : he.Corner ≃+* k :=
  (RingEquiv.ofBijective (scalar_corner_embedding e he)
    ⟨scalar_corner_embedding_injective e he hne,
      scalar_corner_embedding_surjective e he hcorner⟩).symm

end
end Note198
