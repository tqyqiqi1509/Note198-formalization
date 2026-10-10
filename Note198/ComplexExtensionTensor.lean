import Note198.ComplexProjectiveDimension
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

namespace Note198.ComplexExtensionTensor
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {A B : Type u} [Ring A] [Ring B]
variable (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.Additive]
abbrev downIndex (n : ℤ) : ℕ := (-n).toNat
lemma downIndex_eq (n : ℤ) (hn : n ≤ 0) :
    ComplexShape.embeddingDownNat.f (downIndex n) = n := by
  simp only [ComplexShape.embeddingDownNat_f,downIndex]
  rw [Int.toNat_of_nonneg (by omega)]
  omega

/-- Map an actual down-N chain complex and then extend, or extend first
and map: the two genuine complexes are canonically isomorphic. -/
def component (K : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℤ) :
    (((F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingDownNat)).X n) ≅
      (((F.mapHomologicalComplex (.down ℕ)).obj K).extend ComplexShape.embeddingDownNat).X n := by
  by_cases hn : n ≤ 0
  · exact F.mapIso (K.extendXIso ComplexShape.embeddingDownNat (downIndex_eq n hn)) ≪≫
      (((F.mapHomologicalComplex (.down ℕ)).obj K).extendXIso
        ComplexShape.embeddingDownNat (downIndex_eq n hn)).symm
  · have hout : ∀ j, ComplexShape.embeddingDownNat.f j ≠ n := by
      intro j hj
      simp only [ComplexShape.embeddingDownNat_f] at hj
      omega
    exact (F.map_isZero (K.isZero_extend_X ComplexShape.embeddingDownNat n hout)).isoZero ≪≫
      (((F.mapHomologicalComplex (.down ℕ)).obj K).isZero_extend_X
        ComplexShape.embeddingDownNat n hout).isoZero.symm

lemma component_of_nonpos (K : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℤ) (hn : n ≤ 0) :
    component F K n =
      F.mapIso (K.extendXIso ComplexShape.embeddingDownNat (downIndex_eq n hn)) ≪≫
        (((F.mapHomologicalComplex (.down ℕ)).obj K).extendXIso
          ComplexShape.embeddingDownNat (downIndex_eq n hn)).symm := by
  simp only [component,dif_pos hn]

def mapExtendIso (K : ChainComplex (ModuleCat.{u} A) ℕ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingDownNat) ≅
      ((F.mapHomologicalComplex (.down ℕ)).obj K).extend ComplexShape.embeddingDownNat :=
  HomologicalComplex.Hom.isoOfComponents (component F K) (by
    intro i j hij
    by_cases hi : i ≤ 0
    · by_cases hj : j ≤ 0
      · rw [component_of_nonpos F K i hi,component_of_nonpos F K j hj]
        dsimp only [Functor.mapHomologicalComplex_obj_d,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom]
        rw [K.extend_d_eq ComplexShape.embeddingDownNat (downIndex_eq i hi) (downIndex_eq j hj)]
        rw [((F.mapHomologicalComplex (.down ℕ)).obj K).extend_d_eq
          ComplexShape.embeddingDownNat (downIndex_eq i hi) (downIndex_eq j hj)]
        simp only [Functor.map_comp,Functor.mapHomologicalComplex_obj_d,Category.assoc,
          Iso.map_inv_hom_id_assoc, Iso.inv_hom_id_assoc]
      · have hout : ∀ m, ComplexShape.embeddingDownNat.f m ≠ j := by
          intro m hm
          simp only [ComplexShape.embeddingDownNat_f] at hm
          omega
        have hz := ((F.mapHomologicalComplex (.down ℕ)).obj K).isZero_extend_X
          ComplexShape.embeddingDownNat j hout
        exact hz.eq_of_tgt _ _
    · have hout : ∀ m, ComplexShape.embeddingDownNat.f m ≠ i := by
        intro m hm
        simp only [ComplexShape.embeddingDownNat_f] at hm
        omega
      have hz := F.map_isZero (K.isZero_extend_X ComplexShape.embeddingDownNat i hout)
      exact hz.eq_of_src _ _)

/-- The actual mapped cochain extension computes mapped chain homology
in the sign convention H^(-n)=H_n. -/
def mappedExtensionHomologyIso (K : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj
      (K.extend ComplexShape.embeddingDownNat)).homology (-(n : ℤ)) ≅
      ((F.mapHomologicalComplex (.down ℕ)).obj K).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) (-(n:ℤ))).mapIso
    (mapExtendIso F K) ≪≫
    ((F.mapHomologicalComplex (.down ℕ)).obj K).extendHomologyIso ComplexShape.embeddingDownNat rfl
end
end Note198.ComplexExtensionTensor

