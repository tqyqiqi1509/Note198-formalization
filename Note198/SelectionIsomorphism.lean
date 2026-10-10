import Note198.EndomorphismSelection

set_option maxHeartbeats 0

namespace Note198.EndomorphismSelection
noncomputable section
open CategoryTheory
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (S : Data k R)

/-- The selection operation carries actual R-linear isomorphisms to
R-linear isomorphisms, including the restriction along the endomorphism. -/
def HEquiv {M N : ModuleCat.{u} R} (f : M ≃ₗ[R] N) : H S M ≃ₗ[R] H S N where
  toFun x := ⟨f x.val, by
    change S.e • f x.val = f x.val
    rw [← f.map_smul, x.property]⟩
  invFun y := ⟨f.symm y.val, by
    change S.e • f.symm y.val = f.symm y.val
    rw [← f.symm.map_smul, y.property]⟩
  left_inv x := Subtype.ext (f.symm_apply_apply x.val)
  right_inv y := Subtype.ext (f.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (f.map_add x.val y.val)
  map_smul' r x := by
    apply Subtype.ext
    change f (S.α r • x.val) = S.α r • f x.val
    exact f.map_smul (S.α r) x.val

def iterateEquiv {M N : ModuleCat.{u} R} (f : M ≃ₗ[R] N) :
    ∀ j, iterate S M j ≃ₗ[R] iterate S N j
  | 0 => f
  | j+1 => HEquiv S (iterateEquiv f j)

/-- Different exact extinction times force nonisomorphic source modules.
This uses the actual selection operation, rather than assuming orthogonality. -/
theorem nonisomorphic_of_extinction_times (M N : ModuleCat.{u} R)
    (m n : ℕ) (hmn : m ≠ n)
    (hM : (∀ j < m, Nontrivial (iterate S M j)) ∧ Subsingleton (iterate S M m))
    (hN : (∀ j < n, Nontrivial (iterate S N j)) ∧ Subsingleton (iterate S N n)) :
    ¬ Nonempty (M ≃ₗ[R] N) := by
  rintro ⟨f⟩
  rcases lt_or_gt_of_ne hmn with h | h
  · letI := hM.2
    letI := hN.1 m h
    have hz : Subsingleton (iterate S N m) := (iterateEquiv S f m).symm.injective.subsingleton
    exact @not_subsingleton _ inferInstance hz
  · letI := hN.2
    letI := hM.1 n h
    have hz : Subsingleton (iterate S M n) := (iterateEquiv S f n).injective.subsingleton
    exact @not_subsingleton _ inferInstance hz

end
end Note198.EndomorphismSelection
