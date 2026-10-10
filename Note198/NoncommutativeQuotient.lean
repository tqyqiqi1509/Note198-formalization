import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Congruence.Hom

namespace Note198
noncomputable section
universe u v
variable {A : Type u} [Ring A]

/-- The congruence modulo a two-sided ideal of a possibly noncommutative ring.
Its relation is exactly x−y∈I. -/
def ideal_ring_con (I : Ideal A) [I.IsTwoSided] : RingCon A :=
  (TwoSidedIdeal.mk' (I : Set A) I.zero_mem
    (fun ha hb => I.add_mem ha hb) (fun ha => I.neg_mem ha)
    (fun {_ _} hb => I.mul_mem_left _ hb)
    (fun {_ _} ha => Ideal.mul_mem_right _ I ha)).ringCon

abbrev NoncommutativeQuotient (I : Ideal A) [I.IsTwoSided] := (ideal_ring_con I).Quotient

theorem ideal_ring_con_rel (I : Ideal A) [I.IsTwoSided] (a b : A) :
    ideal_ring_con I a b ↔ a-b ∈ I := Iff.rfl

variable {k : Type u} [Field k] [Algebra k A]
variable {B : Type v} [Ring B] [Algebra k B]

def noncommutative_quotient_equiv (I : Ideal A) [I.IsTwoSided]
    (f : A →ₐ[k] B) (h : I = RingHom.ker f.toRingHom) (hf : Function.Surjective f) :
    NoncommutativeQuotient I ≃ₐ[k] B := by
  have hc : ideal_ring_con I = RingCon.ker f.toRingHom := by
    apply RingCon.ext
    intro a b
    change a-b ∈ I ↔ f a = f b
    rw [h]
    change f (a-b) = 0 ↔ f a = f b
    rw [map_sub,sub_eq_zero]
  have hg : Function.Surjective (RingCon.kerLiftₐ f) := by
    intro b
    obtain ⟨a,rfl⟩ := hf b
    exact ⟨(RingCon.ker f.toRingHom).mk' a,rfl⟩
  have hc' : ideal_ring_con I = (RingCon.ker f.toRingHom).comap
      (AlgEquiv.refl : A ≃ₐ[k] A) := by
    apply RingCon.ext
    intro a b
    change ideal_ring_con I a b ↔ RingCon.ker f.toRingHom a b
    rw [hc]
  exact (RingCon.congrₐ k (AlgEquiv.refl : A ≃ₐ[k] A) hc').trans
    (AlgEquiv.ofBijective (RingCon.kerLiftₐ f) ⟨RingCon.kerLiftₐ_injective f,hg⟩)

end
end Note198
