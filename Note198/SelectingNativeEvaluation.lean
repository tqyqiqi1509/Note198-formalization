import Note198.SelectingEvaluation
import Note198.SelectingImageComparison

namespace Note198.SelectingNativeEvaluation
noncomputable section
open CategoryTheory CategoryTheory.Limits
open OAI.LittleFinitistic OAI.LittleFinitistic.SourceImageEvaluation
open OAI.LittleFinitistic.FiniteProjectiveHomotopy
open OAI.LittleFinitistic.QuadraticEncoding
attribute [local instance] HasDerivedCategory.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {E : SelectionEncoding.Encoding k R} {S : EndomorphismSelection.Data k R}
variable {Y : Type u} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]

abbrev H := EndomorphismSelection.vectorObject (k := k) (EndomorphismSelection.H S (ModuleCat.of R Y))
instance : FiniteDimensional k (H (S := S) (Y := Y)) :=
  Module.Finite.of_surjective (SelectingImageComparison.equiv S (Y := Y)).toLinearMap
    (SelectingImageComparison.equiv S (Y := Y)).surjective

def HK : K.{u,u} k := ⟨(vectorStalk (k := k)).obj (H (S := S) (Y := Y)), single_property _ 0⟩
def HDerived : FiniteVectorDerived.{u,u} (k := k) :=
  (derivedEmbedding k).toEssImage.obj (HK (S := S) (Y := Y))
def imageIsoK : imageK (k := k) (Y := Y) S.e ≅ HK (S := S) (Y := Y) :=
  (inclusion k).preimageIso ((vectorStalk (k := k)).mapIso
    (SelectingImageComparison.equiv S (Y := Y)).toModuleIso)
def imageIso : imageDerived (k := k) (Y := Y) S.e ≅ HDerived (S := S) (Y := Y) :=
  (derivedEmbedding k).toEssImage.mapIso (imageIsoK (S := S) (Y := Y))

abbrev target := HDerived (S := S) (Y := Y) ⊞ (HDerived (S := S) (Y := Y))⟦(3 : ℤ)⟧
def targetIso : Note198DiagramEvaluation.target (S := S) (Y := Y) ≅
    target (S := S) (Y := Y) :=
  biprod.mapIso (imageIso (S := S) (Y := Y))
    ((shiftFunctor (FiniteVectorDerived.{u,u} (k := k)) (3 : ℤ)).mapIso
      (imageIso (S := S) (Y := Y)))

def V0Iso : (Note198DiagramEvaluation.F (E := E) (Y := Y)).obj
    (SelectingRectification.fixedData E S).V₀ ≅ target (S := S) (Y := Y) :=
  Note198DiagramEvaluation.V0Iso (E := E) (S := S) ≪≫ targetIso
def D0Iso : (Note198DiagramEvaluation.sourceEvaluation (E := E) (Y := Y)).obj
    (SelectingRectification.fixedData E S).D₀ ≅ target (S := S) (Y := Y) :=
  Note198DiagramEvaluation.D0Iso (E := E) (S := S) ≪≫ targetIso
def D1Iso : (Note198DiagramEvaluation.sourceEvaluation (E := E) (Y := Y)).obj
    (SelectingRectification.fixedData E S).D₁ ≅ target (S := S) (Y := Y) :=
  Note198DiagramEvaluation.D1Iso (E := E) (S := S) ≪≫ targetIso
def D2Iso : (Note198DiagramEvaluation.sourceEvaluation (E := E) (Y := Y)).obj
    (SelectingRectification.fixedData E S).D₂ ≅ target (S := S) (Y := Y) :=
  Note198DiagramEvaluation.D2Iso (E := E) (S := S) ≪≫ targetIso

/-- All three vertices of the fixed source diagram evaluate to the actual
selected module H(Y), in degrees zero and minus three. -/
theorem fixed_vertices :
    Nonempty ((Note198DiagramEvaluation.sourceEvaluation (E := E) (Y := Y)).obj
      (SelectingRectification.fixedData E S).D₀ ≅ target (S := S) (Y := Y)) ∧
    Nonempty ((Note198DiagramEvaluation.sourceEvaluation (E := E) (Y := Y)).obj
      (SelectingRectification.fixedData E S).D₁ ≅ target (S := S) (Y := Y)) ∧
    Nonempty ((Note198DiagramEvaluation.sourceEvaluation (E := E) (Y := Y)).obj
      (SelectingRectification.fixedData E S).D₂ ≅ target (S := S) (Y := Y)) :=
  ⟨⟨Note198DiagramEvaluation.D0Iso (E := E) (S := S) ≪≫ targetIso⟩,
    ⟨Note198DiagramEvaluation.D1Iso (E := E) (S := S) ≪≫ targetIso⟩,
    ⟨Note198DiagramEvaluation.D2Iso (E := E) (S := S) ≪≫ targetIso⟩⟩

end
end Note198.SelectingNativeEvaluation
