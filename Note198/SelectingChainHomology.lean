import Note198.SelectingTargetHomology
import Note198.SelectingTensorComparison

namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace SelectingChainHomology
open OAI.LittleFinitistic
open QuadraticEncoding SelectingRectification SelectingNativeEvaluation Note198TensorComparison
open SelectingTargetHomology
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {E : SelectionEncoding.Encoding k R} {S : EndomorphismSelection.Data k R}
variable {Y : Type u} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]
abbrev representation := SourceActionEvaluation.representation (Y := Y) E
abbrev complex (D : SourceVerdier.K E.relations) := tensor (representation (E := E) (Y := Y)) D
abbrev source := Note198DiagramEvaluation.sourceEvaluation (E := E) (Y := Y)

def derivedIso (D : SourceVerdier.K E.relations) :
    DerivedCategory.Q.obj (complex (E := E) (Y := Y) D) ≅ (I (k := k)).obj ((source (E := E) (Y := Y)).obj D) :=
  (DerivedCategory.quotientCompQhIso (C (k := k))).symm.app _ ≪≫
    DerivedCategory.Qh.mapIso (finiteIso (representation (E := E) (Y := Y)) D)

def comparison (D : SourceVerdier.K E.relations) (n : ℤ) :
    (complex (E := E) (Y := Y) D).homology n ≅ ((cohomology (k := k)) n).obj ((source (E := E) (Y := Y)).obj D) :=
  (DerivedCategory.homologyFunctorFactors (C (k := k)) n).symm.app _ ≪≫
    (DerivedCategory.homologyFunctor (C (k := k)) n).mapIso (derivedIso (E := E) (Y := Y) D)

theorem derived_map {D D' : SourceVerdier.K E.relations}
    (f : ConcreteChainRepresentatives.representative E.relations D ⟶
      ConcreteChainRepresentatives.representative E.relations D') (a : D ⟶ D')
    (ha : (HomotopyCategory.quotient _ _).map f = a.hom) :
    DerivedCategory.Q.map (tensorMap (representation (E := E) (Y := Y)) f) ≫
      (derivedIso (E := E) (Y := Y) D').hom =
        (derivedIso (E := E) (Y := Y) D).hom ≫ (I (k := k)).map ((source (E := E) (Y := Y)).map a) := by
  have h := congrArg DerivedCategory.Qh.map (map_comparison (representation (E := E) (Y := Y)) f a ha)
  simp only [Functor.map_comp] at h
  have hn := (DerivedCategory.quotientCompQhIso (C (k := k))).inv.naturality
    (tensorMap (representation (E := E) (Y := Y)) f)
  exact DiagramEvaluationSquares.compose _ _ _
    ((DerivedCategory.quotientCompQhIso (C (k := k))).symm.app (complex (E := E) (Y := Y) D))
    ((DerivedCategory.quotientCompQhIso (C (k := k))).symm.app (complex (E := E) (Y := Y) D'))
    (DerivedCategory.Qh.mapIso (finiteIso (representation (E := E) (Y := Y)) D))
    (DerivedCategory.Qh.mapIso (finiteIso (representation (E := E) (Y := Y)) D')) hn h

theorem comparison_map {D D' : SourceVerdier.K E.relations}
    (f : ConcreteChainRepresentatives.representative E.relations D ⟶
      ConcreteChainRepresentatives.representative E.relations D') (a : D ⟶ D')
    (ha : (HomotopyCategory.quotient _ _).map f = a.hom) (n : ℤ) :
    HomologicalComplex.homologyMap (tensorMap (representation (E := E) (Y := Y)) f) n ≫
      (comparison (E := E) (Y := Y) D' n).hom =
        (comparison (E := E) (Y := Y) D n).hom ≫ ((cohomology (k := k)) n).map ((source (E := E) (Y := Y)).map a) := by
  have h := congrArg (DerivedCategory.homologyFunctor (C (k := k)) n).map (derived_map (E := E) (Y := Y) f a ha)
  simp only [Functor.map_comp] at h
  have hn := (DerivedCategory.homologyFunctorFactors (C (k := k)) n).inv.naturality
    (tensorMap (representation (E := E) (Y := Y)) f)
  exact DiagramEvaluationSquares.compose _ _ _
    ((DerivedCategory.homologyFunctorFactors (C (k := k)) n).symm.app (complex (E := E) (Y := Y) D))
    ((DerivedCategory.homologyFunctorFactors (C (k := k)) n).symm.app (complex (E := E) (Y := Y) D'))
    ((DerivedCategory.homologyFunctor (C (k := k)) n).mapIso (derivedIso (E := E) (Y := Y) D))
    ((DerivedCategory.homologyFunctor (C (k := k)) n).mapIso (derivedIso (E := E) (Y := Y) D')) hn h

def modelIso (n : ℤ) (hn : n = 0 ∨ n = -3) :
    ((cohomology (k := k)) n).obj (target (S := S) (Y := Y)) ≅ H (S := S) (Y := Y) := by
  by_cases h : n = 0
  · subst n; exact (targetH0 (S := S))
  · have hm : n = -3 := hn.resolve_left h
    subst n; exact (targetHm3 (S := S))

theorem model_action (n : ℤ) (hn : n = 0 ∨ n = -3) (r : R) :
    ((cohomology (k := k)) n).map (targetAction (S := S) (Y := Y) r) ≫ (modelIso (S := S) (Y := Y) n hn).hom =
      (modelIso (S := S) (Y := Y) n hn).hom ≫ HAction (S := S) (Y := Y) r := by
  rcases hn with rfl | rfl
  · exact (targetH0_action (S := S)) r
  · exact (targetHm3_action (S := S)) r

/-- Actual homology of a selected chain tensor, with its chosen (target (S := S)) identification. -/
def homologyIso (D : SourceVerdier.K E.relations)
    (e : (source (E := E) (Y := Y)).obj D ≅ target (S := S) (Y := Y))
    (n : ℤ) (hn : n = 0 ∨ n = -3) : (complex (E := E) (Y := Y) D).homology n ≅ H (S := S) (Y := Y) :=
  (comparison (E := E)) D n ≪≫ ((cohomology (k := k)) n).mapIso e ≪≫ (modelIso (S := S)) n hn

theorem homology_zero (D : SourceVerdier.K E.relations)
    (e : (source (E := E) (Y := Y)).obj D ≅ target (S := S) (Y := Y))
    (n : ℤ) (h0 : n ≠ 0) (hm : n ≠ -3) : IsZero ((complex (E := E) (Y := Y) D).homology n) :=
  ((comparison (E := E)) D n ≪≫ ((cohomology (k := k)) n).mapIso e).isZero_iff.mpr ((target_zero (S := S)) n h0 hm)

theorem homology_arrow {D D' : SourceVerdier.K E.relations}
    (f : ConcreteChainRepresentatives.representative E.relations D ⟶
      ConcreteChainRepresentatives.representative E.relations D') (a : D ⟶ D')
    (ha : (HomotopyCategory.quotient _ _).map f = a.hom)
    (eD : (source (E := E) (Y := Y)).obj D ≅ target (S := S) (Y := Y))
    (eE : (source (E := E) (Y := Y)).obj D' ≅ target (S := S) (Y := Y)) (r : R)
    (hs : (source (E := E) (Y := Y)).map a ≫ eE.hom = eD.hom ≫ targetAction (S := S) (Y := Y) r)
    (n : ℤ) (hn : n = 0 ∨ n = -3) :
    HomologicalComplex.homologyMap (tensorMap (representation (E := E) (Y := Y)) f) n ≫
      ((homologyIso (E := E) (S := S)) D' eE n hn).hom =
        ((homologyIso (E := E) (S := S)) D eD n hn).hom ≫ HAction (S := S) (Y := Y) r := by
  have h := congrArg ((cohomology (k := k)) n).map hs
  simp only [Functor.map_comp] at h
  exact DiagramEvaluationSquares.compose _ _ _
    ((comparison (E := E)) D n) ((comparison (E := E)) D' n)
    (((cohomology (k := k)) n).mapIso eD ≪≫ (modelIso (S := S)) n hn)
    (((cohomology (k := k)) n).mapIso eE ≪≫ (modelIso (S := S)) n hn)
    ((comparison_map (E := E)) f a ha n)
    (DiagramEvaluationSquares.compose _ _ _ (((cohomology (k := k)) n).mapIso eD)
      (((cohomology (k := k)) n).mapIso eE) ((modelIso (S := S)) n hn) ((modelIso (S := S)) n hn) h ((model_action (S := S)) n hn r))

/-- All three actual tensors have the primary (H (S := S))(Y) as homology in both selected degrees. -/
def D0Iso (n : ℤ) (hn : n = 0 ∨ n = -3) :
    (complex (E := E) (Y := Y) (fixedData E S).D₀).homology n ≅ H (S := S) (Y := Y) :=
  (homologyIso (E := E) (S := S)) _ (SelectingNativeEvaluation.D0Iso (E := E) (S := S)) n hn
def D1Iso (n : ℤ) (hn : n = 0 ∨ n = -3) :
    (complex (E := E) (Y := Y) (fixedData E S).D₁).homology n ≅ H (S := S) (Y := Y) :=
  (homologyIso (E := E) (S := S)) _ (SelectingNativeEvaluation.D1Iso (E := E) (S := S)) n hn
def D2Iso (n : ℤ) (hn : n = 0 ∨ n = -3) :
    (complex (E := E) (Y := Y) (fixedData E S).D₂).homology n ≅ H (S := S) (Y := Y) :=
  (homologyIso (E := E) (S := S)) _ (SelectingNativeEvaluation.D2Iso (E := E) (S := S)) n hn

theorem D0_zero (n : ℤ) (h0 : n ≠ 0) (hm : n ≠ -3) :
    IsZero ((complex (E := E) (Y := Y) (fixedData E S).D₀).homology n) :=
  (homology_zero (E := E) (S := S)) _ (SelectingNativeEvaluation.D0Iso (E := E) (S := S)) n h0 hm
theorem D1_zero (n : ℤ) (h0 : n ≠ 0) (hm : n ≠ -3) :
    IsZero ((complex (E := E) (Y := Y) (fixedData E S).D₁).homology n) :=
  (homology_zero (E := E) (S := S)) _ (SelectingNativeEvaluation.D1Iso (E := E) (S := S)) n h0 hm
theorem D2_zero (n : ℤ) (h0 : n ≠ 0) (hm : n ≠ -3) :
    IsZero ((complex (E := E) (Y := Y) (fixedData E S).D₂).homology n) :=
  (homology_zero (E := E) (S := S)) _ (SelectingNativeEvaluation.D2Iso (E := E) (S := S)) n h0 hm

/-- This applies to any chain representative of the same fixed first arrow. -/
theorem arrow01 (a : Fin (E.generators+1))
    (f : (ConcreteChainRepresentatives.representative E.relations (fixedData E S).D₀) ⟶ (ConcreteChainRepresentatives.representative E.relations (fixedData E S).D₁))
    (hf : (HomotopyCategory.quotient _ _).map f = ((fixedData E S).f a).hom)
    (n : ℤ) (hn : n = 0 ∨ n = -3) :
    HomologicalComplex.homologyMap (tensorMap (representation (E := E) (Y := Y)) f) n ≫ ((D1Iso (E := E) (S := S)) n hn).hom =
      ((D0Iso (E := E) (S := S)) n hn).hom ≫ HAction (S := S) (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator E) a) :=
  (homology_arrow (E := E) (S := S)) f ((fixedData E S).f a) hf (SelectingNativeEvaluation.D0Iso (E := E) (S := S)) (SelectingNativeEvaluation.D1Iso (E := E) (S := S)) _
    ((SelectingNativeEvaluation.D_arrow01 (E := E) (S := S)) a) n hn

theorem arrow12 (a : Fin (E.generators+1))
    (g : (ConcreteChainRepresentatives.representative E.relations (fixedData E S).D₁) ⟶ (ConcreteChainRepresentatives.representative E.relations (fixedData E S).D₂))
    (hg : (HomotopyCategory.quotient _ _).map g = ((fixedData E S).g a).hom)
    (n : ℤ) (hn : n = 0 ∨ n = -3) :
    HomologicalComplex.homologyMap (tensorMap (representation (E := E) (Y := Y)) g) n ≫ ((D2Iso (E := E) (S := S)) n hn).hom =
      ((D1Iso (E := E) (S := S)) n hn).hom ≫ HAction (S := S) (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator E) a) :=
  (homology_arrow (E := E) (S := S)) g ((fixedData E S).g a) hg (SelectingNativeEvaluation.D1Iso (E := E) (S := S)) (SelectingNativeEvaluation.D2Iso (E := E) (S := S)) _
    ((SelectingNativeEvaluation.D_arrow12 (E := E) (S := S)) a) n hn

theorem fixed_arrow01 (a : Fin (E.generators+1)) (n : ℤ) (hn : n = 0 ∨ n = -3) :
    HomologicalComplex.homologyMap
      (tensorMap (representation (E := E) (Y := Y)) ((SelectingRectification.fixedChain E S).f a)) n ≫ ((D1Iso (E := E) (S := S)) n hn).hom =
      ((D0Iso (E := E) (S := S)) n hn).hom ≫ HAction (S := S) (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator E) a) :=
  (arrow01 (E := E) (S := S)) a _ ((SelectingRectification.fixedChain E S).f_quotient a) n hn
theorem fixed_arrow12 (a : Fin (E.generators+1)) (n : ℤ) (hn : n = 0 ∨ n = -3) :
    HomologicalComplex.homologyMap
      (tensorMap (representation (E := E) (Y := Y)) ((SelectingRectification.fixedChain E S).g a)) n ≫ ((D2Iso (E := E) (S := S)) n hn).hom =
      ((D1Iso (E := E) (S := S)) n hn).hom ≫ HAction (S := S) (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator E) a) :=
  (arrow12 (E := E) (S := S)) a _ ((SelectingRectification.fixedChain E S).g_quotient a) n hn
end SelectingChainHomology

end

end Note198
