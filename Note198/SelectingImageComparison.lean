import Note198.EndomorphismSelection
import OAI.Algebra.Finitistic.Localization.SourceCornerEvaluation

namespace Note198.SelectingImageComparison
noncomputable section
open CategoryTheory OAI.LittleFinitistic OAI.LittleFinitistic.SourceImageEvaluation
open OAI.LittleFinitistic.QuadraticEncoding
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (S : EndomorphismSelection.Data k R)
variable {Y : Type u} [AddCommGroup Y] [Module k Y]
  [Module R Y] [IsScalarTower k R Y]

/-- Evaluation's image and the actual selected vector space, with the alpha
restriction of scalars used in the definition of H. -/
def equiv : imageSpace (k := k) (Y := Y) S.e ≃ₗ[k]
    EndomorphismSelection.vectorObject (k := k) (EndomorphismSelection.H S (ModuleCat.of R Y)) where
  toFun x := ⟨x.val.down, by
    obtain ⟨z, hz⟩ := x.property
    have hz' : S.e • z.down = x.val.down := congrArg ULift.down hz
    change S.e • x.val.down = x.val.down
    rw [← hz', ← mul_smul, S.idempotent]⟩
  invFun x := ⟨ULift.up x.val, ⟨ULift.up x.val, by
    change ULift.up (S.e • x.val) = ULift.up x.val
    exact congrArg ULift.up x.property⟩⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    apply Subtype.ext
    change c • x.val.down = S.α (algebraMap k R c) • x.val.down
    rw [AlgHom.commutes, algebraMap_smul]

abbrev moduleAction (r : R) (x : EndomorphismSelection.H S (ModuleCat.of R Y)) :
    EndomorphismSelection.H S (ModuleCat.of R Y) := r • x

/-- The compressed alpha action equals the defining R-action on H(Y). -/
theorem equiv_action (r : R) (x : imageSpace (k := k) (Y := Y) S.e) :
    equiv S ((imageCornerEnd (action (k := k) (Y := Y) S.e).hom
      (action (k := k) (Y := Y) (S.α r)).hom) x) =
      moduleAction S r (equiv S x) := by
  apply Subtype.ext
  have h := imageCorner_restriction (k := k) (Y := Y) S.e (S.α r)
    S.idempotent (S.central (S.α r)).eq x
  exact congrArg ULift.down h

theorem image_nontrivial_of (h : Nontrivial (EndomorphismSelection.H S (ModuleCat.of R Y))) :
    Nontrivial (imageSpace (k := k) (Y := Y) S.e) := by
  let i := equiv S (Y := Y)
  obtain ⟨x, y, hxy⟩ := h.exists_pair_ne
  exact ⟨⟨i.symm x, i.symm y, fun he => hxy (i.symm.injective he)⟩⟩

theorem image_subsingleton_of (h : Subsingleton (EndomorphismSelection.H S (ModuleCat.of R Y))) :
    Subsingleton (imageSpace (k := k) (Y := Y) S.e) :=
  ⟨fun x y => (equiv S).injective (h.elim (equiv S x) (equiv S y))⟩

end
end Note198.SelectingImageComparison
