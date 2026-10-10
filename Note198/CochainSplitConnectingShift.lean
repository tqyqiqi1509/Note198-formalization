import OAI.Algebra.Finitistic.Localization.SignedCochainShift
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

namespace Note198.CochainSplitConnectingShift
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open OAI.LittleFinitistic.BimoduleTotal
universe v v' u u'
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
variable [Preadditive C] [Preadditive D]
variable (G : C ⥤ D) [G.Additive] (a : ℤ)
local instance signedShift : (CategoryTheory.shiftFunctor (CochainComplex D ℤ) a).CommShift ℤ :=
  signedShiftComm D a

abbrev F : CochainComplex C ℤ ⥤ CochainComplex D ℤ :=
  G.mapHomologicalComplex (.up ℤ) ⋙ CategoryTheory.shiftFunctor (CochainComplex D ℤ) a

variable (S : ShortComplex (CochainComplex C ℤ))
variable (σ : ∀ n : ℤ, (S.map (eval C (.up ℤ) n)).Splitting)

set_option backward.isDefEq.respectTransparency false in
def shiftedSplitting (n : ℤ) :
    ((S.map (F G a)).map (eval D (.up ℤ) n)).Splitting :=
  (σ (n+a)).map G

/-- The connecting map of a degreewise-split sequence commutes with an
additive functor followed by a cochain shift, with the actual signed
shift-commutation structure. The shift sign appears both in the shifted
differential and in the commutation with the degree-one target shift. -/
theorem connecting_map_shift :
    homOfDegreewiseSplit (S.map (F G a)) (shiftedSplitting G a S σ) =
      (F G a).map (homOfDegreewiseSplit S σ) ≫
        ((F G a).commShiftIso (1 : ℤ)).hom.app S.X₁ := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [homOfDegreewiseSplit_f, cocycleOfDegreewiseSplit,
    HomComplex.Cochain.mk_v, shiftedSplitting, F,
    Functor.comp_map, HomologicalComplex.comp_f,
    CochainComplex.shiftFunctor_map_f',
    CochainComplex.shiftFunctor_obj_d',
    Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplex_obj_d,
    Functor.commShiftIso_comp_hom_app,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    signedShiftIso_hom_f]
  dsimp only [HomComplex.Cocycle.mk]
  simp only [HomComplex.Cochain.mk_v, Category.comp_id, ShortComplex.map_X₂,
    Functor.comp_obj, CochainComplex.shiftFunctor_obj_d',
    Functor.mapHomologicalComplex_obj_d, Functor.map_comp]
  simp only [ShortComplex.Splitting.map, Category.id_comp, Category.assoc,
    Linear.comp_units_smul, Linear.units_smul_comp]
  erw [Category.id_comp]
  change a.negOnePow • G.map (σ (n + a)).s ≫
      G.map (S.X₂.d (n + a) (n + 1 + a)) ≫ G.map (σ (n + 1 + a)).r =
    G.map (σ (n + a)).s ≫ G.map (S.X₂.d (n + a) (n + a + 1)) ≫
      G.map (σ (n + a + 1)).r ≫
        ((signedShiftIso D a 1).hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj S.X₁)).f n
  rw [signedShiftIso_hom_f]
  simp [Functor.map_comp, Linear.units_smul_comp, Linear.comp_units_smul,
    Category.assoc, HomologicalComplex.XIsoOfEq, add_assoc, add_left_comm, add_comm]
  have transport_connecting (z q q' : ℤ) (h : q = q') :
      G.map (σ z).s ≫ G.map (S.X₂.d z q) ≫ G.map (σ q).r =
        G.map (σ z).s ≫ G.map (S.X₂.d z q') ≫ G.map (σ q').r ≫
          eqToHom (congrArg (fun t => G.obj (S.X₁.X t)) h.symm) := by
    subst q'
    simp only [eqToHom_refl, Category.comp_id]
  exact transport_connecting (n+a) (n+1+a) (n+a+1) (by omega)

end
end Note198.CochainSplitConnectingShift
