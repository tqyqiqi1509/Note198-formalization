import Note198.EvaluationSourceHom
import Note198.InflationHom

namespace Note198
noncomputable section
open OAI.LittleFinitistic OAI.LittleFinitistic.QuadraticEncoding
open OAI.LittleFinitistic.SelectionEncoding
universe u v w z
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable (E : Encoding k R)
variable {S X : Type u} [Ring S] [Algebra k S] [AddCommGroup X] [Module k X]
  [Module (B E.relations × S) X] [Module (B E.relations × S)ᵐᵒᵖ X]
  [IsScalarTower k (B E.relations × S) X]
  [IsScalarTower k (B E.relations × S)ᵐᵒᵖ X]
  [SMulCommClass (B E.relations × S) (B E.relations × S)ᵐᵒᵖ X]
variable {Y : Type w} {Z : Type z} [AddCommGroup Y] [Module k Y]
  [AddCommGroup Z] [Module k Z] [Module R Y] [Module R Z]
  [IsScalarTower k R Y] [IsScalarTower k R Z]

/-- Full Hom correspondence from the source algebra to the actual inflated
selecting modules. Taking S=B⊗C and X=O⊕T gives Proposition 7.1's modules. -/
def source_selecting_hom_equiv : (Y →ₗ[R] Z) ≃
    (RingInflation
      (selecting_first_projection (k := k) (L := B E.relations) (R := S) (X := X))
      (sourceRepresentation (Y := Y) E).Evaluation →ₗ[
        TrivSqZeroExt (B E.relations × S) X]
    RingInflation
      (selecting_first_projection (k := k) (L := B E.relations) (R := S) (X := X))
      (sourceRepresentation (Y := Z) E).Evaluation) :=
  (source_evaluation_hom_equiv E).symm.trans
    (selecting_inflation_hom_equiv (k := k) (L := B E.relations) (R := S) (X := X))

theorem source_selecting_hom_bijective :
    Function.Bijective (source_selecting_hom_equiv (S := S) (X := X) (Y := Y) (Z := Z) E) :=
  (source_selecting_hom_equiv (S := S) (X := X) (Y := Y) (Z := Z) E).bijective

end
end Note198
