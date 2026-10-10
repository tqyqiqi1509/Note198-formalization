import Note198.SelectingNativeAction
import Note198.SelectingTensorComparison

namespace Note198.RemainingLiftedDiagram
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open OAI OAI.LittleFinitistic OAI.LittleFinitistic.FiniteProjectiveHomotopy
open SelectionEncoding RelationBasisCoefficients QuadraticEncoding
attribute [local instance] HasDerivedCategory.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : Encoding k R) (S : EndomorphismSelection.Data k R)
open SelectingRectification

/-- Proposition 3.4's fixed chain-level data. `relations` is an actual
Homotopy of the chain relation map to zero; its `hom n (n-1)` is the
right-B-linear degree -1 component, and its `comm n` is exactly the
chain-level d h + h d = relation equation. These objects and homotopies
are constructed from E,S, before any evaluation module is introduced. -/
theorem fixed_chain_data :
    (∃ lo hi : ℤ, ∀ n, n < lo ∨ hi < n →
      IsZero ((D₀ E S).X n) ∧ IsZero ((D₁ E S).X n) ∧
        IsZero ((D₂ E S).X n)) ∧
    (∀ n, Module.Projective (QuadraticEncoding.B E.relations)ᵐᵒᵖ ((D₀ E S).X n) ∧
      Module.Projective (QuadraticEncoding.B E.relations)ᵐᵒᵖ ((D₁ E S).X n) ∧
      Module.Projective (QuadraticEncoding.B E.relations)ᵐᵒᵖ ((D₂ E S).X n)) ∧
    (∀ n, Module.Finite (QuadraticEncoding.B E.relations)ᵐᵒᵖ ((D₀ E S).X n) ∧
      Module.Finite (QuadraticEncoding.B E.relations)ᵐᵒᵖ ((D₁ E S).X n) ∧
      Module.Finite (QuadraticEncoding.B E.relations)ᵐᵒᵖ ((D₂ E S).X n)) ∧
    (∀ r : RelationIndex E.relations, Nonempty (Homotopy
      (ExternalTensor.Section4.relationMap (ConcreteQuadraticDiagram.quadratic E.relations)
        (D₀ E S) (D₁ E S) (D₂ E S) (f E S) (g E S) r) 0)) := by
  sorry

variable {Y : Type u} [AddCommGroup Y] [Module k Y] [Module R Y]
  [IsScalarTower k R Y] [FiniteDimensional k Y]

abbrev representation := SourceActionEvaluation.representation (Y := Y) E

/-- This is the genuine tensor of the underlying fixed right-B complex;
no abstract evaluation object is substituted for its chain terms. -/
abbrev tensor (D : SourceVerdier.K E.relations) :=
  Note198TensorComparison.tensor (representation E (Y := Y)) D

abbrev tensorMap {D D' : SourceVerdier.K E.relations}
    (a : ConcreteChainRepresentatives.representative E.relations D ⟶
      ConcreteChainRepresentatives.representative E.relations D') :=
  Note198TensorComparison.tensorMap (representation E (Y := Y)) a

abbrev target := (derivedTargetInclusion (k := k)).obj
  (SelectingNativeEvaluation.target (S := S) (Y := Y))

abbrev targetAction (r : R) := (derivedTargetInclusion (k := k)).map
  (SelectingNativeEvaluation.targetAction (S := S) (Y := Y) r)

/-- The finite-vector essImage is included in the actual derived category;
its source evaluation is definitionally the localization of the genuine
representative tensor. -/
def tensorIso (D : SourceVerdier.K E.relations) :
    DerivedCategory.Q.obj (tensor E (Y := Y) D) ≅
      (derivedTargetInclusion (k := k)).obj
        ((Note198DiagramEvaluation.sourceEvaluation (E := E) (Y := Y)).obj D) :=
  Iso.refl _

def vertexIso0 : DerivedCategory.Q.obj (tensor E (Y := Y) (fixedData E S).D₀) ≅
    target (S := S) (Y := Y) :=
  (derivedTargetInclusion (k := k)).mapIso
    (SelectingNativeEvaluation.D0Iso (E := E) (S := S) (Y := Y))
def vertexIso1 : DerivedCategory.Q.obj (tensor E (Y := Y) (fixedData E S).D₁) ≅
    target (S := S) (Y := Y) :=
  (derivedTargetInclusion (k := k)).mapIso
    (SelectingNativeEvaluation.D1Iso (E := E) (S := S) (Y := Y))
def vertexIso2 : DerivedCategory.Q.obj (tensor E (Y := Y) (fixedData E S).D₂) ≅
    target (S := S) (Y := Y) :=
  (derivedTargetInclusion (k := k)).mapIso
    (SelectingNativeEvaluation.D2Iso (E := E) (S := S) (Y := Y))

private theorem tensor_arrow {D D' : SourceVerdier.K E.relations}
    (a : ConcreteChainRepresentatives.representative E.relations D ⟶
      ConcreteChainRepresentatives.representative E.relations D')
    (b : D ⟶ D')
    (hb : (HomotopyCategory.quotient _ _).map a = b.hom) :
    DerivedCategory.Q.map (tensorMap E (Y := Y) a) =
      (derivedTargetInclusion (k := k)).map
        ((Note198DiagramEvaluation.sourceEvaluation (E := E) (Y := Y)).map b) := by
  have h := Note198TensorComparison.map_comparison
    (representation E (Y := Y)) a b hb
  dsimp only [Note198TensorComparison.finiteIso,Iso.refl_hom] at h
  erw [Category.comp_id,Category.id_comp] at h
  change DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (ModuleCat k) (.up ℤ)).map
        (Note198TensorComparison.tensorMap (representation E (Y := Y)) a)) =
    DerivedCategory.Qh.map ((inclusion k).map
      ((SourceEvaluation.finite (representation E (Y := Y))).map b))
  exact congrArg DerivedCategory.Qh.map h

/-- Proposition 3.4's complete evaluated diagram, using the same fixed
chain maps for every finite-dimensional Y. The target is H(Y) plus H(Y)[3]
in Db(k); its R-action is the actual restricted α-action on eY, twice.
Index zero represents s/s', hence the action of 1 is the identity; every
other index represents x_h and gives α(x_h) on both summands. -/
theorem tensor_diagram :
    ∃ (i₀ : DerivedCategory.Q.obj (tensor E (Y := Y) (fixedData E S).D₀) ≅
        target (S := S) (Y := Y))
      (i₁ : DerivedCategory.Q.obj (tensor E (Y := Y) (fixedData E S).D₁) ≅
        target (S := S) (Y := Y))
      (i₂ : DerivedCategory.Q.obj (tensor E (Y := Y) (fixedData E S).D₂) ≅
        target (S := S) (Y := Y)),
      (∀ a, DerivedCategory.Q.map (tensorMap E (Y := Y) ((fixedChain E S).f a)) ≫ i₁.hom =
        i₀.hom ≫ targetAction (S := S) (Y := Y) (RelationBasisAction.arrow (generator E) a)) ∧
      (∀ a, DerivedCategory.Q.map (tensorMap E (Y := Y) ((fixedChain E S).g a)) ≫ i₂.hom =
        i₁.hom ≫ targetAction (S := S) (Y := Y) (RelationBasisAction.arrow (generator E) a)) := by
  sorry

end
end Note198.RemainingLiftedDiagram

