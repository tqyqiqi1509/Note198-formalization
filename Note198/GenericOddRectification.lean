import Note198.EndomorphismSelection
import Note198.EnvelopingProjective
import Note198.GenericOddAction
import OAI.Algebra.Finitistic.Localization.SourceQuotientAction
import OAI.Algebra.Finitistic.Localization.SourceShiftLinear
import OAI.Algebra.Finitistic.Encoding.RelationBasisAction
import OAI.Algebra.Finitistic.Localization.UnderlyingRepresentatives
import OAI.Algebra.Finitistic.Rectification.RectificationLemma

set_option maxHeartbeats 500000


namespace Note198.GenericOddRectification
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CategoryTheory.Idempotents
open OAI.LittleFinitistic
open OAI
open SelectionEncoding RelationBasisCoefficients RelationBasisAction FormalSummandAction
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : Encoding k R) (S : EndomorphismSelection.Data k R)
variable (s : ℤ) (hs : 3 ≤ s) (hodd : Odd s)

local instance : HasFiniteBiproducts (Karoubi (SourceVerdier.Q E.relations)) :=
  Karoubi.karoubi_hasFiniteBiproducts
local instance : HasBinaryBiproducts (Karoubi (SourceVerdier.Q E.relations)) :=
  hasBinaryBiproducts_of_finite_biproducts _

abbrev selectedSummand : Karoubi (SourceVerdier.Q E.relations) :=
  summand (SourceQuotientAction.theta E) S.e S.idempotent
abbrev selectedDouble : Karoubi (SourceVerdier.Q E.relations) :=
  selectedSummand E S ⊞ OddDouble.formalShift (selectedSummand E S) s
abbrev selectedAction : R →ₐ[k] End (selectedDouble E S s) :=
  GenericOddAction.oddDoubleAction (SourceQuotientAction.theta E) S.e S.idempotent
    (fun r => (S.central r).eq) S.α s

structure FixedData : Type (u+1) where
  V₀ : SourceVerdier.Q E.relations
  ρ₀ : R →ₐ[k] End V₀
  iso : (toKaroubi (SourceVerdier.Q E.relations)).obj V₀ ≅
    selectedDouble E S s
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
      selectedAction E S s r
  arrow01 : ∀ a : Fin (E.generators + 1), (SourceVerdier.q E.relations).map (f a) ≫ φ₁.hom =
    φ₀.hom ≫ ρ₀ (arrow (generator E) a)
  arrow12 : ∀ b : Fin (E.generators + 1), (SourceVerdier.q E.relations).map (g b) ≫ φ₂.hom =
    φ₁.hom ≫ ρ₀ (arrow (generator E) b)
  relations : ∀ r : RelationIndex E.relations,
    ∑ a, ∑ b, basisCoefficient E.relations r a b • (f a ≫ g b) = 0

def fixedData : FixedData E S s := Classical.choice (by
  obtain ⟨V, ρ, i, D₀, D₁, D₂, φ₀, φ₁, φ₂, f, g, he, hf, hg, hr⟩ :=
    GenericOddFixedDiagram.fixed_diagram (SourceVerdier.q E.relations)
      (SourceVerdier.Sigma E.relations) (SourceQuotientAction.theta E)
      S.e S.idempotent (fun r => (S.central r).eq) S.α s hs hodd
      (E.generators + 1) (E.generators + 1)
      (Module.finrank k (QuadraticEncoding.relationSpace E.relations))
      (arrow (generator E)) (arrow (generator E)) (basisCoefficient E.relations)
      (encoding_basis_action E)
  exact ⟨⟨V, ρ, i, D₀, D₁, D₂, φ₀, φ₁, φ₂, f, g, he, hf, hg, hr⟩⟩)

structure ChainData : Type (u+1) where
  f : Fin (E.generators + 1) →
    (ConcreteChainRepresentatives.representative E.relations (fixedData E S s hs hodd).D₀ ⟶
      ConcreteChainRepresentatives.representative E.relations (fixedData E S s hs hodd).D₁)
  g : Fin (E.generators + 1) →
    (ConcreteChainRepresentatives.representative E.relations (fixedData E S s hs hodd).D₁ ⟶
      ConcreteChainRepresentatives.representative E.relations (fixedData E S s hs hodd).D₂)
  f_quotient : ∀ a,
    (HomotopyCategory.quotient (SourceVerdier.Proj E.relations) (.up ℤ)).map (f a) =
      ((fixedData E S s hs hodd).f a).hom
  g_quotient : ∀ b,
    (HomotopyCategory.quotient (SourceVerdier.Proj E.relations) (.up ℤ)).map (g b) =
      ((fixedData E S s hs hodd).g b).hom
  homotopy : ∀ r : RelationIndex E.relations,
    Homotopy (∑ a, ∑ b, basisCoefficient E.relations r a b • (f a ≫ g b)) 0

def fixedChain : ChainData E S s hs hodd := Classical.choice (by
  obtain ⟨f, g, hf, hg, ⟨h⟩⟩ := ConcreteChainRepresentatives.quadratic_representatives
    E.relations _ _ _ (fixedData E S s hs hodd).D₀ (fixedData E S s hs hodd).D₁ (fixedData E S s hs hodd).D₂
      (fixedData E S s hs hodd).f (fixedData E S s hs hodd).g (basisCoefficient E.relations)
        (fixedData E S s hs hodd).relations
  exact ⟨⟨f, g, hf, hg, h⟩⟩)

abbrev D₀ := UnderlyingRepresentatives.complex E.relations (fixedData E S s hs hodd).D₀
abbrev D₁ := UnderlyingRepresentatives.complex E.relations (fixedData E S s hs hodd).D₁
abbrev D₂ := UnderlyingRepresentatives.complex E.relations (fixedData E S s hs hodd).D₂

def f (a : Fin (E.generators + 1)) : D₀ E S s hs hodd ⟶ D₁ E S s hs hodd :=
  ((UnderlyingRepresentatives.forget E.relations).mapHomologicalComplex (.up ℤ)).map
    ((fixedChain E S s hs hodd).f a)
def g (b : Fin (E.generators + 1)) : D₁ E S s hs hodd ⟶ D₂ E S s hs hodd :=
  ((UnderlyingRepresentatives.forget E.relations).mapHomologicalComplex (.up ℤ)).map
    ((fixedChain E S s hs hodd).g b)

def relations (r : RelationIndex E.relations) : Homotopy
    (ExternalTensor.Section4.relationMap (ConcreteQuadraticDiagram.quadratic E.relations)
      (D₀ E S s hs hodd) (D₁ E S s hs hodd) (D₂ E S s hs hodd) (f E S s hs hodd) (g E S s hs hodd) r) 0 :=
  UnderlyingRepresentatives.relationHomotopy E.relations (E.generators + 1)
    (E.generators + 1) (Module.finrank k (QuadraticEncoding.relationSpace E.relations))
    (fixedData E S s hs hodd).D₀ (fixedData E S s hs hodd).D₁ (fixedData E S s hs hodd).D₂
    (fixedChain E S s hs hodd).f (fixedChain E S s hs hodd).g (basisCoefficient E.relations)
    (fixedChain E S s hs hodd).homotopy r

/-- The constructed selecting bimodule complex is fixed independently of Y. -/
def bimodule : ExternalTensor.Section4.BiComplex k (QuadraticEncoding.B E.relations) :=
  InducedRectification.total (ConcreteQuadraticDiagram.quadratic E.relations)
    (D₀ E S s hs hodd) (D₁ E S s hs hodd) (D₂ E S s hs hodd) (f E S s hs hodd) (g E S s hs hodd) (relations E S s hs hodd)

/-- All original vertex inverses and arrow homotopies, boundedness,
finiteness and right projectivity of the actual selecting complex.
Enveloping-algebra projectivity is provided by a separate stronger bridge. -/
theorem verified : ∃ lo hi : ℤ,
    RectificationLemma.Verified E.relations (D₀ E S s hs hodd) (D₁ E S s hs hodd) (D₂ E S s hs hodd)
      (f E S s hs hodd) (g E S s hs hodd) (relations E S s hs hodd) lo hi := by
  obtain ⟨l₀, h₀, b₀⟩ := UnderlyingRepresentatives.bounded E.relations (fixedData E S s hs hodd).D₀
  obtain ⟨l₁, h₁, b₁⟩ := UnderlyingRepresentatives.bounded E.relations (fixedData E S s hs hodd).D₁
  obtain ⟨l₂, h₂, b₂⟩ := UnderlyingRepresentatives.bounded E.relations (fixedData E S s hs hodd).D₂
  let lo := min l₀ (min l₁ l₂)
  let hi := max h₀ (max h₁ h₂)
  refine ⟨lo, hi, RectificationLemma.rectification E.relations
    (D₀ E S s hs hodd) (D₁ E S s hs hodd) (D₂ E S s hs hodd) (f E S s hs hodd) (g E S s hs hodd) (relations E S s hs hodd) lo hi
    (fun n hn => b₀ n ?_) (fun n hn => b₁ n ?_) (fun n hn => b₂ n ?_)
    (UnderlyingRepresentatives.projective E.relations (fixedData E S s hs hodd).D₀)
    (UnderlyingRepresentatives.projective E.relations (fixedData E S s hs hodd).D₁)
    (UnderlyingRepresentatives.projective E.relations (fixedData E S s hs hodd).D₂)
    (UnderlyingRepresentatives.finite E.relations (fixedData E S s hs hodd).D₀)
    (UnderlyingRepresentatives.finite E.relations (fixedData E S s hs hodd).D₁)
    (UnderlyingRepresentatives.finite E.relations (fixedData E S s hs hodd).D₂)⟩
  all_goals dsimp [lo, hi] at hn; omega

/-- The actual fixed selecting complex is projective over the enveloping
algebra in each degree. Its source is chosen before any Y. -/
theorem bimodule_enveloping_projective : ∀ n, Projective ((bimodule E S s hs hodd).X n) := by
  exact EnvelopingProjective.total_enveloping_projective
    (ConcreteQuadraticDiagram.quadratic E.relations)
    (D₀ E S s hs hodd) (D₁ E S s hs hodd) (D₂ E S s hs hodd) (f E S s hs hodd) (g E S s hs hodd) (relations E S s hs hodd)
    (SourceVerdier.vertex_idem E.relations 0)
    (SourceVerdier.vertex_idem E.relations 1)
    (SourceVerdier.vertex_idem E.relations 2)
    (UnderlyingRepresentatives.projective E.relations (fixedData E S s hs hodd).D₀)
    (UnderlyingRepresentatives.projective E.relations (fixedData E S s hs hodd).D₁)
    (UnderlyingRepresentatives.projective E.relations (fixedData E S s hs hodd).D₂)

end
end Note198.GenericOddRectification
