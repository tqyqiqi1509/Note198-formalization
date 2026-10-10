import Note198.BimoduleTotalConnecting
import Note198.CochainSplitConnectingShift

namespace Note198.BimoduleTotalTriangleCompatibility
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI.LittleFinitistic
open CategoryTheory.Pretriangulated
open OAI.ExternalTensor.Section4 BimoduleTotal CochainComplex
open BimoduleTotalDegreewiseSplit
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} B) ℤ))
variable (σ : ∀ n : ℤ, (S.map (HomologicalComplex.eval (ModuleCat B) (.up ℤ) n)).Splitting)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem column_connecting_compatibility (i : Fin l) :
    homOfDegreewiseSplit (S.map (BimoduleTotal.columnFunctor k B P (p i)))
      (fun n => columnSplitting k B P p S σ i n) =
    (BimoduleTotal.columnFunctor k B P (p i)).map (homOfDegreewiseSplit S σ) ≫
      ((BimoduleTotal.columnFunctor k B P (p i)).commShiftIso (1 : ℤ)).hom.app S.X₁ := by
  exact CochainSplitConnectingShift.connecting_map_shift
    (inputFunctor k B (P.X (p i))) (-(p i)) S σ

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Compatibility of the actual total connecting morphism with its frozen
coherent shift structure, including the horizontal bimodule differentials. -/
theorem total_connecting_compatibility :
    homOfDegreewiseSplit (S.map (functor k B P p hp))
      (totalSplitting k B P p hp S σ) =
    (functor k B P p hp).map (homOfDegreewiseSplit S σ) ≫
      ((functor k B P p hp).commShiftIso (1 : ℤ)).hom.app S.X₁ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  erw [BimoduleTotalConnecting.connecting_component]
  have hc := congrArg (fun f => (f.f n).hom (x i))
    (column_connecting_compatibility k B P p S σ i)
  change _ = (((shiftIso k B P p hp 1).hom.app S.X₁).f n).hom
    ((((functor k B P p hp).map (homOfDegreewiseSplit S σ)).f n).hom x) i
  erw [shiftIso_apply,functor_map_component]
  simp only [HomologicalComplex.comp_f,ModuleCat.hom_comp,LinearMap.comp_apply,
    ← Iso.app_hom,column_commShiftIso_eq] at hc
  change (show Term k B P S.X₁ (p i) (n+1 + -(p i)) from
      ((homOfDegreewiseSplit (S.map (BimoduleTotal.columnFunctor k B P (p i)))
        (fun n => columnSplitting k B P p S σ i n)).f n).hom (x i)) =
    (show Term k B P S.X₁ (p i) (n+1 + -(p i)) from
      (((shiftColumnIso k B P S.X₁ 1 (p i)).hom).f n).hom
        ((((BimoduleTotal.columnFunctor k B P (p i)).map
          (homOfDegreewiseSplit S σ)).f n).hom (x i))) at hc
  exact hc

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- This is a genuine isomorphism of triangles, including their third arrows. -/
def total_split_triangle_iso :
    (functor k B P p hp).mapTriangle.obj (triangleOfDegreewiseSplit S σ) ≅
      triangleOfDegreewiseSplit (S.map (functor k B P p hp))
        (totalSplitting k B P p hp S σ) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      change (functor k B P p hp).map S.f ≫ 𝟙 _ =
        𝟙 _ ≫ (functor k B P p hp).map S.f
      simp only [Category.comp_id, Category.id_comp])
    (by
      change (functor k B P p hp).map S.g ≫ 𝟙 _ =
        𝟙 _ ≫ (functor k B P p hp).map S.g
      simp only [Category.comp_id, Category.id_comp])
    (by
      change ((functor k B P p hp).map (homOfDegreewiseSplit S σ) ≫
          ((functor k B P p hp).commShiftIso (1 : ℤ)).hom.app S.X₁) ≫
          (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} B) ℤ) (1 : ℤ)).map
            (𝟙 ((functor k B P p hp).obj S.X₁)) =
        𝟙 ((functor k B P p hp).obj S.X₃) ≫
          homOfDegreewiseSplit (S.map (functor k B P p hp))
            (totalSplitting k B P p hp S σ)
      simp only [Functor.map_id, Category.comp_id, Category.id_comp]
      exact (total_connecting_compatibility k B P p hp S σ).symm)

theorem total_split_triangle_isomorphism : Nonempty (
    (functor k B P p hp).mapTriangle.obj (triangleOfDegreewiseSplit S σ) ≅
      triangleOfDegreewiseSplit (S.map (functor k B P p hp))
        (totalSplitting k B P p hp S σ)) :=
  ⟨total_split_triangle_iso k B P p hp S σ⟩
end
end Note198.BimoduleTotalTriangleCompatibility
