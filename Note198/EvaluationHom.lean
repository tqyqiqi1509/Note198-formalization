import OAI.Algebra.Finitistic.Localization.EvaluationModule
import OAI.Algebra.Finitistic.Encoding.EncodingLinearity

namespace Note198
noncomputable section
open OAI.LittleFinitistic OAI.LittleFinitistic.QuadraticEncoding
universe u v w
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} {Z : Type w} [AddCommGroup Y] [Module k Y]
  [AddCommGroup Z] [Module k Z]
variable (X : Representation P Y) (W : Representation P Z)

@[simp] lemma evaluation_inclusion_zero (y : Y) :
    X.inclusion 0 y = (show X.Evaluation from (y,0,0)) := rfl
@[simp] lemma evaluation_inclusion_one (y : Y) :
    X.inclusion 1 y = (show X.Evaluation from (0,y,0)) := rfl
@[simp] lemma evaluation_inclusion_two (y : Y) :
    X.inclusion 2 y = (show X.Evaluation from (0,0,y)) := rfl

/-- The actual component of a B-module map at vertex zero. -/
def evaluation_hom_component (F : X.Evaluation →ₗ[B P] W.Evaluation) : Y →ₗ[k] Z :=
  (W.projection 0).comp ((F.restrictScalars k).comp (X.inclusion 0))

theorem evaluation_hom_inclusion (F : X.Evaluation →ₗ[B P] W.Evaluation)
    (i : Fin 3) (y : Y) :
    F (X.inclusion i y) = W.inclusion i (evaluation_hom_component X W F y) := by
  have h0 : F (X.inclusion 0 y) = W.inclusion 0 (evaluation_hom_component X W F y) := by
    have h := F.map_smul (ThreeVertexAlgebra.vertex (composition P) 0) (X.inclusion 0 y)
    simpa only [X.vertex_smul,W.vertex_smul,X.projection_inclusion,
      evaluation_hom_component,LinearMap.comp_apply,LinearMap.restrictScalars_apply] using h
  have h1 : F (X.inclusion 1 y) = W.inclusion 1 (evaluation_hom_component X W F y) := by
    have hX : arrow01 P 0 • X.inclusion 0 y = X.inclusion 1 y := X.s_smul _
    have hW : arrow01 P 0 • W.inclusion 0 (evaluation_hom_component X W F y) =
        W.inclusion 1 (evaluation_hom_component X W F y) := W.s_smul _
    exact (congrArg F hX.symm).trans ((F.map_smul (arrow01 P 0) (X.inclusion 0 y)).trans
      ((congrArg (fun z : W.Evaluation => arrow01 P 0 • z) h0).trans hW))
  have h2 : F (X.inclusion 2 y) = W.inclusion 2 (evaluation_hom_component X W F y) := by
    have hX : arrow12 P 0 • X.inclusion 1 y = X.inclusion 2 y := X.s'_smul _
    have hW : arrow12 P 0 • W.inclusion 1 (evaluation_hom_component X W F y) =
        W.inclusion 2 (evaluation_hom_component X W F y) := W.s'_smul _
    exact (congrArg F hX.symm).trans ((F.map_smul (arrow12 P 0) (X.inclusion 1 y)).trans
      ((congrArg (fun z : W.Evaluation => arrow12 P 0 • z) h1).trans hW))
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem evaluation_hom_coordinates (F : X.Evaluation →ₗ[B P] W.Evaluation)
    (y : X.Evaluation) :
    F y = (evaluation_hom_component X W F y.1,
      evaluation_hom_component X W F y.2.1,evaluation_hom_component X W F y.2.2) := by
  have h : y = X.inclusion 0 y.1 + X.inclusion 1 y.2.1 + X.inclusion 2 y.2.2 := by
    rcases y with ⟨a,b,c⟩
    change (a,b,c) = (a+0+0,0+b+0,0+0+c)
    simp only [add_zero,zero_add]
  calc
    F y = F (X.inclusion 0 y.1 + X.inclusion 1 y.2.1 + X.inclusion 2 y.2.2) :=
      congrArg F h
    _ = W.inclusion 0 (evaluation_hom_component X W F y.1) +
        W.inclusion 1 (evaluation_hom_component X W F y.2.1) +
        W.inclusion 2 (evaluation_hom_component X W F y.2.2) := by
      rw [F.map_add,F.map_add,evaluation_hom_inclusion,evaluation_hom_inclusion,
        evaluation_hom_inclusion]
    _ = _ := by
      change (evaluation_hom_component X W F y.1+0+0,
        0+evaluation_hom_component X W F y.2.1+0,
        0+0+evaluation_hom_component X W F y.2.2) = _
      simp only [add_zero,zero_add]

theorem evaluation_hom_generator (F : X.Evaluation →ₗ[B P] W.Evaluation)
    (h : Fin d) (y : Y) :
    evaluation_hom_component X W F (X.generator h y) =
      W.generator h (evaluation_hom_component X W F y) := by
  have hX : arrow01 P h.succ • X.inclusion 0 y = X.inclusion 1 (X.generator h y) :=
    X.generator01_smul h _
  have hW : arrow01 P h.succ • W.inclusion 0 (evaluation_hom_component X W F y) =
      W.inclusion 1 (W.generator h (evaluation_hom_component X W F y)) :=
    W.generator01_smul h _
  have he : W.inclusion 1 (evaluation_hom_component X W F (X.generator h y)) =
      W.inclusion 1 (W.generator h (evaluation_hom_component X W F y)) :=
    (evaluation_hom_inclusion X W F 1 (X.generator h y)).symm.trans
      ((congrArg F hX.symm).trans
        ((F.map_smul (arrow01 P h.succ) (X.inclusion 0 y)).trans
          ((congrArg (fun z : W.Evaluation => arrow01 P h.succ • z)
            (evaluation_hom_inclusion X W F 0 y)).trans hW)))
  exact congrArg (fun z : W.Evaluation => z.2.1) he

/-- Maps of the underlying spaces commuting with the actual generator actions. -/
def RepresentationIntertwiner :=
  {f : Y →ₗ[k] Z // ∀ h y, f (X.generator h y) = W.generator h (f y)}

def evaluation_diagonal (f : Y →ₗ[k] Z) : X.Evaluation →ₗ[k] W.Evaluation where
  toFun y := (f y.1,f y.2.1,f y.2.2)
  map_add' a b := by
    change (f (a.1+b.1),f (a.2.1+b.2.1),f (a.2.2+b.2.2)) =
      (f a.1+f b.1,f a.2.1+f b.2.1,f a.2.2+f b.2.2)
    simp only [map_add]
  map_smul' c a := by
    change (f (c • a.1),f (c • a.2.1),f (c • a.2.2)) =
      (c • f a.1,c • f a.2.1,c • f a.2.2)
    simp only [map_smul]

@[simp] lemma evaluation_diagonal_apply (f : Y →ₗ[k] Z) (y : X.Evaluation) :
    evaluation_diagonal X W f y = (show W.Evaluation from (f y.1,f y.2.1,f y.2.2)) := rfl

/-- A generator intertwiner induces an actual B-linear map, including every
length-two path and the whole relation quotient, via the proved generators. -/
def evaluation_hom_lift (f : RepresentationIntertwiner X W) :
    X.Evaluation →ₗ[B P] W.Evaluation :=
  EncodingLinearity.linearMap P (evaluation_diagonal X W f.val)
    (by
      intro i y
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [W.vertex0_smul (evaluation_diagonal X W f.val y),X.vertex0_smul y]
        change (f.val y.1,f.val 0,f.val 0) = (f.val y.1,0,0)
        simp only [map_zero]
      · refine Fin.cases ?_ (fun j => ?_) i
        · change evaluation_diagonal X W f.val
            (ThreeVertexAlgebra.vertex (composition P) 1 • y) =
              ThreeVertexAlgebra.vertex (composition P) 1 • evaluation_diagonal X W f.val y
          rw [W.vertex1_smul (evaluation_diagonal X W f.val y),X.vertex1_smul y]
          change (f.val 0,f.val y.2.1,f.val 0) = (0,f.val y.2.1,0)
          simp only [map_zero]
        · have hj : j = 0 := Subsingleton.elim j 0
          subst j
          change evaluation_diagonal X W f.val
            (ThreeVertexAlgebra.vertex (composition P) 2 • y) =
              ThreeVertexAlgebra.vertex (composition P) 2 • evaluation_diagonal X W f.val y
          rw [W.vertex2_smul (evaluation_diagonal X W f.val y),X.vertex2_smul y]
          change (f.val 0,f.val 0,f.val y.2.2) = (0,0,f.val y.2.2)
          simp only [map_zero])
    (by
      intro a y
      cases a using Fin.cases with
      | zero =>
        rw [W.s_smul (evaluation_diagonal X W f.val y),X.s_smul y]
        change (f.val 0,f.val y.1,f.val 0) = (0,f.val y.1,0)
        simp only [map_zero]
      | succ h =>
        rw [W.generator01_smul h (evaluation_diagonal X W f.val y),X.generator01_smul h y]
        change (f.val 0,f.val (X.generator h y.1),f.val 0) =
          (0,W.generator h (f.val y.1),0)
        simp only [map_zero,f.property])
    (by
      intro a y
      cases a using Fin.cases with
      | zero =>
        rw [W.s'_smul (evaluation_diagonal X W f.val y),X.s'_smul y]
        change (f.val 0,f.val 0,f.val y.2.1) = (0,0,f.val y.2.1)
        simp only [map_zero]
      | succ h =>
        rw [W.generator12_smul h (evaluation_diagonal X W f.val y),X.generator12_smul h y]
        change (f.val 0,f.val 0,f.val (X.generator h y.2.1)) =
          (0,0,W.generator h (f.val y.2.1))
        simp only [map_zero,f.property])

/-- A genuine bijection of the actual Hom set with generator intertwiners;
the two identity arrows force all three components to be the same map. -/
def evaluation_hom_equiv : (X.Evaluation →ₗ[B P] W.Evaluation) ≃
    RepresentationIntertwiner X W where
  toFun F := ⟨evaluation_hom_component X W F,evaluation_hom_generator X W F⟩
  invFun := evaluation_hom_lift X W
  left_inv F := by
    apply LinearMap.ext
    intro y
    exact (evaluation_hom_coordinates X W F y).symm
  right_inv f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro y
    rfl

end
end Note198
