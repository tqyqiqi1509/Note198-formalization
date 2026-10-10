import Note198.EvaluationHom
import OAI.Algebra.Finitistic.Localization.EvaluationFromAlgebra
import OAI.Algebra.Finitistic.Selection.SelectionEncoding

namespace Note198
noncomputable section
open OAI.LittleFinitistic OAI.LittleFinitistic.QuadraticEncoding
open OAI.LittleFinitistic.SelectionEncoding OAI.LittleFinitistic.QuadraticPresentation
universe u v w z
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable (E : Encoding k R)
variable {Y : Type w} {Z : Type z} [AddCommGroup Y] [Module k Y]
  [AddCommGroup Z] [Module k Z] [Module R Y] [Module R Z]
  [IsScalarTower k R Y] [IsScalarTower k R Z]

abbrev sourceRepresentation : Representation E.relations Y :=
  Representation.ofModule (Y := Y) (generator E) (generator_relations E)

/-- Commuting with the displayed presentation generators implies commuting
with every element of the actual source algebra, by free-algebra induction
and the surjective presentation quotient. -/
theorem source_intertwiner_all (f : RepresentationIntertwiner
    (sourceRepresentation (Y := Y) E) (sourceRepresentation (Y := Z) E))
    (r : R) (y : Y) : f.val (r • y) = r • f.val y := by
  let q := originalMap k (Fin E.generators) (QuotientAction.polynomial E.relations)
  obtain ⟨p,hp⟩ := (original k (Fin E.generators) (QuotientAction.polynomial E.relations)).mkₐ_surjective
    (α := k) (E.equiv.symm r)
  have hr : E.equiv (q p) = r := by
    rw [show q p = E.equiv.symm r from hp]
    exact E.equiv.apply_symm_apply r
  have hh : ∀ x : Y, f.val (E.equiv (q p) • x) = E.equiv (q p) • f.val x := by
    apply FreeAlgebra.induction
      (motive := fun a => ∀ x : Y, f.val (E.equiv (q a) • x) = E.equiv (q a) • f.val x)
    · intro c x
      have hc : E.equiv (q (algebraMap k (FreeAlgebra k (Fin E.generators)) c)) =
          algebraMap k R c :=
        (congrArg E.equiv (q.commutes c)).trans (E.equiv.commutes c)
      have hY : E.equiv (q (algebraMap k (FreeAlgebra k (Fin E.generators)) c)) • x =
          c • x :=
        (congrArg (fun r : R => r • x) hc).trans
          (IsScalarTower.algebraMap_smul R c x)
      have hZ : E.equiv (q (algebraMap k (FreeAlgebra k (Fin E.generators)) c)) • f.val x =
          c • f.val x :=
        (congrArg (fun r : R => r • f.val x) hc).trans
          (IsScalarTower.algebraMap_smul R c (f.val x))
      exact (congrArg f.val hY).trans ((f.val.map_smul c x).trans hZ.symm)
    · intro h x
      exact f.property h x
    · intro a b ha hb x
      simp only [map_mul,mul_smul]
      rw [ha,hb]
    · intro a b ha hb x
      simp only [map_add,add_smul,LinearMap.map_add]
      rw [ha,hb]
  simpa only [hr] using hh y

def source_intertwiner_linearMap (f : RepresentationIntertwiner
    (sourceRepresentation (Y := Y) E) (sourceRepresentation (Y := Z) E)) : Y →ₗ[R] Z where
  toFun := f.val
  map_add' := f.val.map_add
  map_smul' := source_intertwiner_all E f

/-- A genuine bijection between R-linear maps and the concrete generator
intertwiners. No linearity of the inverse is assumed. -/
def source_intertwiner_equiv : (Y →ₗ[R] Z) ≃ RepresentationIntertwiner
    (sourceRepresentation (Y := Y) E) (sourceRepresentation (Y := Z) E) where
  toFun f := ⟨f.restrictScalars k,fun h y => f.map_smul (generator E h) y⟩
  invFun := source_intertwiner_linearMap E
  left_inv f := by ext y; rfl
  right_inv f := by apply Subtype.ext; ext y; rfl

/-- The full faithful Hom correspondence for the actual three-copy module
M(V): projection at vertex zero and the diagonal lift are inverse. -/
def source_evaluation_hom_equiv :
    ((sourceRepresentation (Y := Y) E).Evaluation →ₗ[B E.relations]
      (sourceRepresentation (Y := Z) E).Evaluation) ≃ (Y →ₗ[R] Z) :=
  (evaluation_hom_equiv (sourceRepresentation (Y := Y) E)
    (sourceRepresentation (Y := Z) E)).trans (source_intertwiner_equiv E).symm

end
end Note198
