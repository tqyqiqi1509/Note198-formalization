import Note198.GenericOddAction
import OAI.Algebra.Finitistic.Localization.SourceOddDoubleEvaluation

namespace Note198.GenericOddEvaluation
noncomputable section
open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Limits
open OAI.LittleFinitistic OAI.LittleFinitistic.QuadraticEncoding
open OAI.LittleFinitistic.SourceImageEvaluation
attribute [local instance] HasDerivedCategory.standard
universe u v w
variable {k : Type u} [Field k] {R : Type w} [Ring R] [Algebra k R]
variable (E : OAI.LittleFinitistic.SelectionEncoding.Encoding k R)
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]
local instance : HasFiniteBiproducts (Karoubi (SourceVerdier.Q E.relations)) :=
  Karoubi.karoubi_hasFiniteBiproducts
local instance : HasBinaryBiproducts (Karoubi (SourceVerdier.Q E.relations)) :=
  hasBinaryBiproducts_of_finite_biproducts _
local instance : PreservesBinaryBiproducts (completed (Y := Y) E) :=
  preservesBinaryBiproducts_of_preservesBiproducts _
def oddDoubleImageIso (e : R) (he : e*e=e) (s : ℤ) :
    (completed (Y := Y) E).obj (U E e he ⊞ OddDouble.formalShift (U E e he) s) ≅
      imageDerived (k := k) (Y := Y) e ⊞ (imageDerived (k := k) (Y := Y) e)⟦(s : ℤ)⟧ :=
  (completed (Y := Y) E).mapBiprod _ _ ≪≫
    biprod.mapIso (summandImageIso (Y := Y) E e he) (shiftedImageIso (Y := Y) E e he s)

theorem oddDouble_corner_square (e a : R) (he : e*e=e) (s : ℤ) :
    (completed (Y := Y) E).map
      (biprod.map (corner E e a he) ((OddDouble.formalShiftFunctor s).map (corner E e a he))) ≫
      (oddDoubleImageIso (Y := Y) E e he s).hom =
    (oddDoubleImageIso (Y := Y) E e he s).hom ≫
      biprod.map (imageCorner (k := k) (Y := Y) e a) ((imageCorner (k := k) (Y := Y) e a)⟦(s : ℤ)⟧') := by
  exact BiprodEvaluationSquare.square (completed (Y := Y) E)
    (corner E e a he) ((OddDouble.formalShiftFunctor s).map (corner E e a he))
    (summandImageIso (Y := Y) E e he) (shiftedImageIso (Y := Y) E e he s)
    (imageCorner (k := k) (Y := Y) e a) ((imageCorner (k := k) (Y := Y) e a)⟦(s : ℤ)⟧')
    (completed_corner_square E e a he) (shifted_corner_square E e a he s)

set_option maxHeartbeats 800000 in
theorem oddDouble_selecting_square (e : R) (he : e*e=e) (hc : ∀ r : R,e*r=r*e)
    (alpha : R →ₐ[k] R) (r : R) (s : ℤ) :
    (completed (Y := Y) E).map
      (GenericOddAction.oddDoubleAction (SourceQuotientAction.theta E) e he hc alpha s r) ≫
      (oddDoubleImageIso (Y := Y) E e he s).hom =
    (oddDoubleImageIso (Y := Y) E e he s).hom ≫
      biprod.map (imageCorner (k := k) (Y := Y) e (alpha r)) ((imageCorner (k := k) (Y := Y) e (alpha r))⟦(s : ℤ)⟧') := by
  have hc' := selecting_action_eq_corner E e he hc alpha r
  have hd := (GenericOddAction.oddDoubleAction_apply
    (SourceQuotientAction.theta E) e he hc alpha s r).trans
      (congrArg₂ (fun f g => biprod.map f g) hc'
        (congrArg (OddDouble.formalShiftFunctor s).map hc'))
  exact (congrArg (fun f => (completed (Y := Y) E).map f ≫
    (oddDoubleImageIso (Y := Y) E e he s).hom) hd).trans
      (oddDouble_corner_square E e (alpha r) he s)

end
end Note198.GenericOddEvaluation
