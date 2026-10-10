import Note198.GeneralFixedDiagram
import OAI.Algebra.Finitistic.Localization.UnderlyingRepresentatives
import OAI.Algebra.Finitistic.Rectification.RectificationLemma

set_option maxHeartbeats 500000
set_option profiler true

namespace Note198.SelectingRectification
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CategoryTheory.Idempotents
open OAI.LittleFinitistic
open OAI
open SelectionEncoding RelationBasisCoefficients RelationBasisAction FormalSummandAction
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : Encoding k R) (S : EndomorphismSelection.Data k R)

local instance : HasFiniteBiproducts (Karoubi (SourceVerdier.Q E.relations)) :=
  Karoubi.karoubi_hasFiniteBiproducts
local instance : HasBinaryBiproducts (Karoubi (SourceVerdier.Q E.relations)) :=
  hasBinaryBiproducts_of_finite_biproducts _

abbrev selectedSummand : Karoubi (SourceVerdier.Q E.relations) :=
  summand (SourceQuotientAction.theta E) S.e S.idempotent
abbrev selectedDouble : Karoubi (SourceVerdier.Q E.relations) :=
  selectedSummand E S ⊞ OddDouble.formalShift (selectedSummand E S) 3
abbrev selectedAction : R →ₐ[k] End (selectedDouble E S) :=
  oddDoubleAction (SourceQuotientAction.theta E) S.e S.idempotent
    (fun r => (S.central r).eq) S.α

structure FixedData : Type (u+1) where
  V₀ : SourceVerdier.Q E.relations
  ρ₀ : R →ₐ[k] End V₀
  iso : (toKaroubi (SourceVerdier.Q E.relations)).obj V₀ ≅
    selectedDouble E S
  D₀ : SourceVerdier.K E.relations
  D₁ : SourceVerdier.K E.relations
  D₂ : SourceVerdier.K E.relations
  φ₀ : (SourceVerdier.q E.relations).obj D₀ ≅ V₀
  φ₁ : (SourceVerdier.q E.relations).obj D₁ ≅ V₀
  φ₂ : (SourceVerdier.q E.relations).obj D₂ ≅ V₀
  f : Fin (E.generators + 1) → (D₀ ⟶ D₁)
  g : Fin (E.generators + 1) → (D₁ ⟶ D₂)
  equivariant : ∀ r : R,
    (toKaroubi (SourceVerdier.Q E.relations)).map (ρ₀ r) ≫ iso.hom = iso.hom ≫
      selectedAction E S r
  arrow01 : ∀ a : Fin (E.generators + 1), (SourceVerdier.q E.relations).map (f a) ≫ φ₁.hom =
    φ₀.hom ≫ ρ₀ (arrow (generator E) a)
  arrow12 : ∀ b : Fin (E.generators + 1), (SourceVerdier.q E.relations).map (g b) ≫ φ₂.hom =
    φ₁.hom ≫ ρ₀ (arrow (generator E) b)
  relations : ∀ r : RelationIndex E.relations,
    ∑ a, ∑ b, basisCoefficient E.relations r a b • (f a ≫ g b) = 0

def fixedData : FixedData E S := Classical.choice (by
  obtain ⟨V, ρ, i, D₀, D₁, D₂, φ₀, φ₁, φ₂, f, g, he, hf, hg, hr⟩ :=
    Note198.selecting_fixed_diagram_endomorphism E S
  exact ⟨⟨V, ρ, i, D₀, D₁, D₂, φ₀, φ₁, φ₂, f, g, he, hf, hg, hr⟩⟩)

structure ChainData : Type (u+1) where
  f : Fin (E.generators + 1) →
    (ConcreteChainRepresentatives.representative E.relations (fixedData E S).D₀ ⟶
      ConcreteChainRepresentatives.representative E.relations (fixedData E S).D₁)
  g : Fin (E.generators + 1) →
    (ConcreteChainRepresentatives.representative E.relations (fixedData E S).D₁ ⟶
      ConcreteChainRepresentatives.representative E.relations (fixedData E S).D₂)
  f_quotient : ∀ a,
    (HomotopyCategory.quotient (SourceVerdier.Proj E.relations) (.up ℤ)).map (f a) =
      ((fixedData E S).f a).hom
  g_quotient : ∀ b,
    (HomotopyCategory.quotient (SourceVerdier.Proj E.relations) (.up ℤ)).map (g b) =
      ((fixedData E S).g b).hom
  homotopy : ∀ r : RelationIndex E.relations,
    Homotopy (∑ a, ∑ b, basisCoefficient E.relations r a b • (f a ≫ g b)) 0

def fixedChain : ChainData E S := Classical.choice (by
  obtain ⟨f, g, hf, hg, ⟨h⟩⟩ := ConcreteChainRepresentatives.quadratic_representatives
    E.relations _ _ _ (fixedData E S).D₀ (fixedData E S).D₁ (fixedData E S).D₂
      (fixedData E S).f (fixedData E S).g (basisCoefficient E.relations)
        (fixedData E S).relations
  exact ⟨⟨f, g, hf, hg, h⟩⟩)

abbrev D₀ := UnderlyingRepresentatives.complex E.relations (fixedData E S).D₀
abbrev D₁ := UnderlyingRepresentatives.complex E.relations (fixedData E S).D₁
abbrev D₂ := UnderlyingRepresentatives.complex E.relations (fixedData E S).D₂

def f (a : Fin (E.generators + 1)) : D₀ E S ⟶ D₁ E S :=
  ((UnderlyingRepresentatives.forget E.relations).mapHomologicalComplex (.up ℤ)).map
    ((fixedChain E S).f a)
def g (b : Fin (E.generators + 1)) : D₁ E S ⟶ D₂ E S :=
  ((UnderlyingRepresentatives.forget E.relations).mapHomologicalComplex (.up ℤ)).map
    ((fixedChain E S).g b)

def relations (r : RelationIndex E.relations) : Homotopy
    (ExternalTensor.Section4.relationMap (ConcreteQuadraticDiagram.quadratic E.relations)
      (D₀ E S) (D₁ E S) (D₂ E S) (f E S) (g E S) r) 0 :=
  UnderlyingRepresentatives.relationHomotopy E.relations (E.generators + 1)
    (E.generators + 1) (Module.finrank k (QuadraticEncoding.relationSpace E.relations))
    (fixedData E S).D₀ (fixedData E S).D₁ (fixedData E S).D₂
    (fixedChain E S).f (fixedChain E S).g (basisCoefficient E.relations)
    (fixedChain E S).homotopy r

/-- The constructed selecting bimodule complex is fixed independently of Y. -/
def bimodule : ExternalTensor.Section4.BiComplex k (QuadraticEncoding.B E.relations) :=
  InducedRectification.total (ConcreteQuadraticDiagram.quadratic E.relations)
    (D₀ E S) (D₁ E S) (D₂ E S) (f E S) (g E S) (relations E S)

end
end Note198.SelectingRectification
