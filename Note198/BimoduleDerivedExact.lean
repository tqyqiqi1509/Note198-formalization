import Note198.BimoduleTotalTriangleCompatibility
import OAI.Algebra.Finitistic.Bimodule.BimoduleDerivedShift

namespace Note198.BimoduleDerivedExact
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI.LittleFinitistic
open CategoryTheory.Pretriangulated
open OAI.ExternalTensor.Section4 BimoduleTotal CochainComplex
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
variable [∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) (p i))]

instance comparison_commShift :
    NatTrans.CommShift (derivedComparison k B P p hp).hom ℤ := by
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ))
      (functor k B P p hp ⋙ DerivedCategory.Q) (derived k B P p hp) :=
    ⟨derivedComparison k B P p hp⟩
  exact NatTrans.commShift_iso_hom_of_localization DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ)) ℤ
    (functor k B P p hp ⋙ DerivedCategory.Q) (derived k B P p hp)

variable (S : ShortComplex (CochainComplex (ModuleCat.{u} B) ℤ))
variable (σ : ∀ n : ℤ, (S.map (HomologicalComplex.eval (ModuleCat B) (.up ℤ) n)).Splitting)

/-- The actual localization of every degreewise split triangle is distinguished. -/
theorem derived_split_distinguished :
    DerivedCategory.Q.mapTriangle.obj (triangleOfDegreewiseSplit S σ) ∈
      distTriang (DerivedCategory (ModuleCat.{u} B)) := by
  let q := HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ)
  exact isomorphic_distinguished _
    (DerivedCategory.Qh.map_distinguished _ (trianglehOfDegreewiseSplit_distinguished S σ)) _
    ((Functor.mapTriangleIso (DerivedCategory.quotientCompQhIso (ModuleCat.{u} B))).symm.app _ ≪≫
      (Functor.mapTriangleCompIso q DerivedCategory.Qh).app _)

/-- The derived total preserves the actual three arrows of every split triangle. -/
def splitTriangleIso :
    (derived k B P p hp).mapTriangle.obj
      (DerivedCategory.Q.mapTriangle.obj (triangleOfDegreewiseSplit S σ)) ≅
    DerivedCategory.Q.mapTriangle.obj
      (triangleOfDegreewiseSplit (S.map (functor k B P p hp))
        (BimoduleTotalDegreewiseSplit.totalSplitting k B P p hp S σ)) :=
  (Functor.mapTriangleCompIso DerivedCategory.Q (derived k B P p hp)).symm.app _ ≪≫
    (Functor.mapTriangleIso (derivedComparison k B P p hp)).app _ ≪≫
    (Functor.mapTriangleCompIso (functor k B P p hp) DerivedCategory.Q).app _ ≪≫
    DerivedCategory.Q.mapTriangle.mapIso
      (BimoduleTotalTriangleCompatibility.total_split_triangle_iso k B P p hp S σ)

theorem image_split_distinguished :
    (derived k B P p hp).mapTriangle.obj
      (DerivedCategory.Q.mapTriangle.obj (triangleOfDegreewiseSplit S σ)) ∈ distTriang _ :=
  isomorphic_distinguished _ (derived_split_distinguished B
    (S.map (functor k B P p hp))
    (BimoduleTotalDegreewiseSplit.totalSplitting k B P p hp S σ)) _
      (splitTriangleIso k B P p hp S σ)

/-- Genuine exactness of the fixed signed tensor total on the native derived
category, with its existing coherent shift structure. -/
theorem derived_isTriangulated : (derived k B P p hp).IsTriangulated := by
  constructor
  intro T hT
  obtain ⟨K,L,f,⟨e⟩⟩ := (DerivedCategory.mem_distTriang_iff T).mp hT
  have hc : (derived k B P p hp).mapTriangle.obj
      (DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle f)) ∈ distTriang _ := by
    rw [rotate_distinguished_triangle]
    exact isomorphic_distinguished _
      (image_split_distinguished k B P p hp
        (mappingCone.triangleRotateShortComplex f)
        (mappingCone.triangleRotateShortComplexSplitting f)) _
      (((derived k B P p hp).mapTriangleRotateIso.app _) ≪≫
        (derived k B P p hp).mapTriangle.mapIso
          (DerivedCategory.Q.mapTriangleRotateIso.app _) ≪≫
        (derived k B P p hp).mapTriangle.mapIso
          (DerivedCategory.Q.mapTriangle.mapIso
            (mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit f)))
  exact isomorphic_distinguished _ hc _ ((derived k B P p hp).mapTriangle.mapIso e)
end
end Note198.BimoduleDerivedExact
