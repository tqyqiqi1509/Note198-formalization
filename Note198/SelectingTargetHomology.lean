import Note198.SelectingNativeAction
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace SelectingTargetHomology
open OAI.LittleFinitistic
open QuadraticEncoding SelectingNativeEvaluation FiniteProjectiveHomotopy
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {S : EndomorphismSelection.Data k R}
variable {Y : Type u} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]
abbrev C := ModuleCat.{u} k
abbrev I := derivedTargetInclusion.{u,u} (k := k)
abbrev cohomology (n : ℤ) := (I (k := k)) ⋙ DerivedCategory.homologyFunctor (C (k := k)) n
instance (n : ℤ) : ((cohomology (k := k)) n).Additive := by dsimp [cohomology]; infer_instance
instance (n : ℤ) : PreservesBinaryBiproducts ((cohomology (k := k)) n) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

def stalkIso : (I (k := k)).obj (HDerived (S := S) (Y := Y)) ≅
    (DerivedCategory.singleFunctor (C (k := k)) 0).obj (H (S := S) (Y := Y)) := Iso.refl _
def shiftedIso : (I (k := k)).obj ((HDerived (S := S) (Y := Y))⟦(3 : ℤ)⟧) ≅
    (DerivedCategory.singleFunctor (C (k := k)) (-3)).obj (H (S := S) (Y := Y)) :=
  ((I (k := k)).commShiftIso (3 : ℤ)).app _ ≪≫
    (shiftFunctor _ (3 : ℤ)).mapIso (stalkIso (S := S) (Y := Y)) ≪≫
      ((DerivedCategory.singleFunctors (C (k := k))).shiftIso 3 (-3) 0 (by norm_num)).app _

def stalkHomologyIso : ((cohomology (k := k)) 0).obj (HDerived (S := S) (Y := Y)) ≅ H (S := S) (Y := Y) :=
  (DerivedCategory.homologyFunctor (C (k := k)) 0).mapIso (stalkIso (S := S)) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (C (k := k)) 0).app _
def shiftedHomologyIso : ((cohomology (k := k)) (-3)).obj ((HDerived (S := S) (Y := Y))⟦(3 : ℤ)⟧) ≅ H (S := S) (Y := Y) :=
  (DerivedCategory.homologyFunctor (C (k := k)) (-3)).mapIso (shiftedIso (S := S)) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (C (k := k)) (-3)).app _

theorem single_zero (M : (C (k := k))) (i n : ℤ) (hn : n ≠ i) :
    IsZero ((DerivedCategory.homologyFunctor (C (k := k)) n).obj
      ((DerivedCategory.singleFunctor (C (k := k)) i).obj M)) := by
  rcases lt_or_gt_of_ne hn with h | h
  · exact DerivedCategory.isZero_of_isGE _ i n h
  · exact DerivedCategory.isZero_of_isLE _ i n h
theorem stalk_zero (n : ℤ) (hn : n ≠ 0) :
    IsZero (((cohomology (k := k)) n).obj (HDerived (S := S) (Y := Y))) :=
  ((DerivedCategory.homologyFunctor (C (k := k)) n).mapIso (stalkIso (S := S) (Y := Y))).isZero_iff.mpr
    ((single_zero (k := k)) _ _ _ hn)
theorem shifted_zero (n : ℤ) (hn : n ≠ -3) :
    IsZero (((cohomology (k := k)) n).obj ((HDerived (S := S) (Y := Y))⟦(3 : ℤ)⟧)) :=
  ((DerivedCategory.homologyFunctor (C (k := k)) n).mapIso (shiftedIso (S := S) (Y := Y))).isZero_iff.mpr
    ((single_zero (k := k)) _ _ _ hn)

def targetH0 : ((cohomology (k := k)) 0).obj (target (S := S) (Y := Y)) ≅ H (S := S) (Y := Y) :=
  ((cohomology (k := k)) 0).mapBiprod _ _ ≪≫
    (isoBiprodZero (shifted_zero (S := S) (Y := Y) 0 (by norm_num))).symm ≪≫ (stalkHomologyIso (S := S))

def targetHm3 : ((cohomology (k := k)) (-3)).obj (target (S := S) (Y := Y)) ≅ H (S := S) (Y := Y) :=
  ((cohomology (k := k)) (-3)).mapBiprod _ _ ≪≫
    (isoZeroBiprod (stalk_zero (S := S) (Y := Y) (-3) (by norm_num))).symm ≪≫ (shiftedHomologyIso (S := S))

theorem target_zero (n : ℤ) (h0 : n ≠ 0) (hm : n ≠ -3) :
    IsZero (((cohomology (k := k)) n).obj (target (S := S) (Y := Y))) :=
  (((cohomology (k := k)) n).mapBiprod _ _).isZero_iff.mpr
    ((biprod_isZero_iff _ _).mpr ⟨(stalk_zero (S := S)) n h0,(shifted_zero (S := S)) n hm⟩)

theorem stalkHomologyIso_hom : (stalkHomologyIso (S := S) (Y := Y)).hom =
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (C (k := k)) 0).app (H (S := S) (Y := Y))).hom := by
  change (DerivedCategory.homologyFunctor (C (k := k)) 0).map
    (𝟙 ((DerivedCategory.singleFunctor (C (k := k)) 0).obj (H (S := S) (Y := Y)))) ≫ _ = _
  rw [CategoryTheory.Functor.map_id,Category.id_comp]

theorem stalk_action (r : R) :
    ((cohomology (k := k)) 0).map (HDerivedAction (S := S) (Y := Y) r) ≫ (stalkHomologyIso (S := S) (Y := Y)).hom =
      (stalkHomologyIso (S := S) (Y := Y)).hom ≫ HAction (S := S) (Y := Y) r := by
  rw [(stalkHomologyIso_hom (S := S))]
  change (DerivedCategory.homologyFunctor (C (k := k)) 0).map
    (DerivedCategory.Qh.map ((inclusion k).map (HKAction (Y := Y) r))) ≫ _ = _
  dsimp only [HKAction]
  erw [Functor.map_preimage]
  change (DerivedCategory.homologyFunctor (C (k := k)) 0).map
    ((DerivedCategory.singleFunctor (C (k := k)) 0).map (HAction (S := S) (Y := Y) r)) ≫ _ = _
  exact (DerivedCategory.singleFunctorCompHomologyFunctorIso (C (k := k)) 0).hom.naturality
    (HAction (S := S) (Y := Y) r)

theorem shifted_action (r : R) :
    ((cohomology (k := k)) (-3)).map ((HDerivedAction (S := S) (Y := Y) r)⟦(3 : ℤ)⟧') ≫
      (shiftedHomologyIso (S := S) (Y := Y)).hom =
        (shiftedHomologyIso (S := S) (Y := Y)).hom ≫ HAction (S := S) (Y := Y) r := by
  have hst : (I (k := k)).map (HDerivedAction (S := S) (Y := Y) r) =
      (DerivedCategory.singleFunctor (C (k := k)) 0).map (HAction (S := S) (Y := Y) r) := by
    change DerivedCategory.Qh.map ((inclusion k).map (HKAction (Y := Y) r)) = _
    dsimp only [HKAction]
    erw [Functor.map_preimage]
    rfl
  have hshift : (I (k := k)).map ((HDerivedAction (S := S) (Y := Y) r)⟦(3 : ℤ)⟧') ≫ (shiftedIso (S := S) (Y := Y)).hom =
      (shiftedIso (S := S) (Y := Y)).hom ≫
        (DerivedCategory.singleFunctor (C (k := k)) (-3)).map (HAction (S := S) (Y := Y) r) := by
    have h1 := ((I (k := k)).commShiftIso (3 : ℤ)).hom.naturality (HDerivedAction (S := S) (Y := Y) r)
    have h2 := ((DerivedCategory.singleFunctors (C (k := k))).shiftIso 3 (-3) 0 (by norm_num)).hom.naturality
      (HAction (S := S) (Y := Y) r)
    dsimp only [Functor.comp_map] at h1 h2
    rw [hst] at h1
    have hh := (congrArg (fun f => f ≫
      (((DerivedCategory.singleFunctors (C (k := k))).shiftIso 3 (-3) 0 (by norm_num)).app
        (H (S := S) (Y := Y))).hom) h1).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun g => ((I (k := k)).commShiftIso (3 : ℤ)).hom.app (HDerived (S := S) (Y := Y)) ≫ g) h2))
    dsimp only [shiftedIso, stalkIso, Iso.trans_hom, Functor.mapIso_hom, Iso.refl_hom]
    erw [CategoryTheory.Functor.mapIso_hom, Iso.refl_hom,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact (Category.assoc _ _ _).symm.trans (hh.trans (Category.assoc _ _ _).symm)

  have h := congrArg (DerivedCategory.homologyFunctor (C (k := k)) (-3)).map hshift
  simp only [Functor.map_comp] at h
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso (C (k := k)) (-3)).hom.naturality
    (HAction (S := S) (Y := Y) r)
  dsimp only [Functor.comp_map,Functor.id_map] at hn
  dsimp only [shiftedHomologyIso,Iso.trans_hom,Functor.mapIso_hom,cohomology,Functor.comp_map]
  rw [← Category.assoc,h,Category.assoc]
  exact (congrArg (fun g => (DerivedCategory.homologyFunctor (C (k := k)) (-3)).map
    (shiftedIso (S := S) (Y := Y)).hom ≫ g) hn).trans (Category.assoc _ _ _).symm

theorem targetH0_hom : (targetH0 (S := S) (Y := Y)).hom =
    ((cohomology (k := k)) 0).map biprod.fst ≫ (stalkHomologyIso (S := S) (Y := Y)).hom := by
  simp [targetH0,isoBiprodZero]
  erw [biprod.lift_fst_assoc]
theorem targetHm3_hom : (targetHm3 (S := S) (Y := Y)).hom =
    ((cohomology (k := k)) (-3)).map biprod.snd ≫ (shiftedHomologyIso (S := S) (Y := Y)).hom := by
  simp [targetHm3,isoZeroBiprod]
  erw [biprod.lift_snd_assoc]

theorem targetH0_action (r : R) :
    ((cohomology (k := k)) 0).map (targetAction (S := S) (Y := Y) r) ≫ (targetH0 (S := S) (Y := Y)).hom =
      (targetH0 (S := S) (Y := Y)).hom ≫ HAction (S := S) (Y := Y) r := by
  rw [(targetH0_hom (S := S)),← Category.assoc,← Functor.map_comp]
  simp only [targetAction,biprod.map_fst,Functor.map_comp,Category.assoc,(stalk_action (S := S))]
theorem targetHm3_action (r : R) :
    ((cohomology (k := k)) (-3)).map (targetAction (S := S) (Y := Y) r) ≫ (targetHm3 (S := S) (Y := Y)).hom =
      (targetHm3 (S := S) (Y := Y)).hom ≫ HAction (S := S) (Y := Y) r := by
  rw [(targetHm3_hom (S := S)),← Category.assoc,← Functor.map_comp]
  simp only [targetAction,biprod.map_snd,Functor.map_comp,Category.assoc,(shifted_action (S := S))]
end SelectingTargetHomology

end

end Note198
