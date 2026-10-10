import OAI.Algebra.Finitistic.Rectification.InducedRectification
import Mathlib.LinearAlgebra.DirectSum.Finsupp

namespace Note198.EnvelopingProjective
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
open OAI OAI.ExternalTensor OAI.ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

/-- The regular enveloping module, with its regular action fixed before
installing the external tensor action. -/
def regularObject : ModuleCat.{u} (Enveloping k B) :=
  ModuleCat.of (Enveloping k B) (ULift.{u} (Enveloping k B))

theorem regular_projective : Module.Projective (Enveloping k B) (regularObject k B) := by
  change Module.Projective (Enveloping k B) (ULift.{u} (Enveloping k B))
  infer_instance

attribute [local instance] OAI.ExternalTensor.bimodule OAI.ExternalTensor.rightModule

/-- The external action on the two regular factors is the enveloping
regular action. In the right factor op(d) acts by op(d)*op(c)=op(c*d). -/
def regularEquiv :
    @LinearEquiv (Enveloping k B) (Enveloping k B) _ _
      (RingHom.id _) (RingHom.id _) inferInstance inferInstance
      (B ⊗[k] Bᵐᵒᵖ) (regularObject k B) _ _
      (OAI.ExternalTensor.bimodule k B B Bᵐᵒᵖ) (regularObject k B).isModule := by
  letI : Module (Enveloping k B) (B ⊗[k] Bᵐᵒᵖ) :=
    OAI.ExternalTensor.bimodule k B B Bᵐᵒᵖ
  exact {
    toFun := ULift.up
    invFun := ULift.down
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun a x => by
      apply ULift.ext
      change OAI.ExternalTensor.action k B B Bᵐᵒᵖ a x = a * x
      induction a using TensorProduct.inductionOn with
      | tmul b c =>
        induction x using TensorProduct.inductionOn with
        | tmul v w =>
          simp only [OAI.ExternalTensor.action, Algebra.TensorProduct.lift_tmul,
            Module.End.mul_apply, OAI.ExternalTensor.leftAction_tmul,
            OAI.ExternalTensor.rightAction_tmul,
            Algebra.TensorProduct.tmul_mul_tmul, smul_eq_mul]
        | add x y hx hy => simp_all only [map_add, mul_add]
      | add a b ha hb => simp_all only [map_add, LinearMap.add_apply, add_mul] }

def idealProjection (e : B) : B →ₗ[B] leftIdeal B e :=
  (LinearMap.mulRight B e).rangeRestrict

theorem idealProjection_subtype (e : B) (he : e * e = e) :
    (idealProjection B e).comp (leftIdeal B e).subtype = LinearMap.id := by
  ext x
  obtain ⟨b, hb⟩ := x.property
  change x.val * e = x.val
  rw [← hb]
  change b * e * e = b * e
  rw [mul_assoc, he]

/-- The principal left ideal tensored with a regular right module is
an actual retract of the regular enveloping module. -/
theorem regular_column_projective (e : B) (he : e * e = e) :
    Module.Projective (Enveloping k B) (Column k B Bᵐᵒᵖ e) := by
  letI := regular_projective k B
  letI : Module (Enveloping k B) (B ⊗[k] Bᵐᵒᵖ) :=
    OAI.ExternalTensor.bimodule k B B Bᵐᵒᵖ
  let i := (regularEquiv k B).toLinearMap.comp
    (OAI.ExternalTensor.map (k := k) (leftIdeal B e).subtype (LinearMap.id : Bᵐᵒᵖ →ₗ[Bᵐᵒᵖ] Bᵐᵒᵖ))
  let p := (OAI.ExternalTensor.map (k := k) (idealProjection B e)
    (LinearMap.id : Bᵐᵒᵖ →ₗ[Bᵐᵒᵖ] Bᵐᵒᵖ)).comp (regularEquiv k B).symm.toLinearMap
  apply Module.Projective.of_split i p
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul v c =>
    change idealProjection B e v.val ⊗ₜ[k] c = v ⊗ₜ[k] c
    have h := LinearMap.congr_fun (idealProjection_subtype B e he) v
    simpa using congrArg (fun z => z ⊗ₜ[k] c) h
  | add x y hx hy => simp_all [map_add]

/-- Distributing the external tensor over a free right module preserves
both the left and right actions, hence is enveloping-linear. -/
def columnFinsuppEquiv (e : B) (ι : Type u) [DecidableEq ι] :
    Column k B (ι →₀ Bᵐᵒᵖ) e ≃ₗ[Enveloping k B]
      (ι →₀ Column k B Bᵐᵒᵖ e) where
  __ := (TensorProduct.finsuppRight k k (leftIdeal B e) Bᵐᵒᵖ ι).toAddEquiv
  map_smul' a x := by
    induction a using TensorProduct.inductionOn with
    | tmul b c =>
      induction x using TensorProduct.inductionOn with
      | tmul v w =>
        ext j
        change (TensorProduct.finsuppRight k k (leftIdeal B e) Bᵐᵒᵖ ι)
          ((b • v) ⊗ₜ[k] (c • w)) j =
          (b ⊗ₜ[k] c : Enveloping k B) •
            ((TensorProduct.finsuppRight k k (leftIdeal B e) Bᵐᵒᵖ ι)
              (v ⊗ₜ[k] w) j)
        simp only [TensorProduct.finsuppRight_apply_tmul_apply,
          Finsupp.smul_apply, OAI.ExternalTensor.smul_tmul]
      | add x y hx hy => simp_all [smul_add]
    | add a b ha hb => simp_all [add_smul]

/-- No finite-dimensionality assumption is needed for this projectivity:
the given right-projective input splits off a genuine free right module. -/
theorem column_enveloping_projective (e : B) (he : e * e = e)
    (N : Type u) [AddCommGroup N] [Module k N] [Module Bᵐᵒᵖ N]
    [IsScalarTower k Bᵐᵒᵖ N] [Module.Projective Bᵐᵒᵖ N] :
    Module.Projective (Enveloping k B) (Column k B N e) := by
  classical
  obtain ⟨i, hi⟩ := (Module.projective_def' (R := Bᵐᵒᵖ) (P := N)).mp inferInstance
  letI := regular_column_projective k B e he
  letI : Module.Projective (Enveloping k B) (N →₀ Column k B Bᵐᵒᵖ e) :=
    Module.Projective.of_equiv (finsuppLequivDFinsupp (Enveloping k B)).symm
  letI : Module.Projective (Enveloping k B) (Column k B (N →₀ Bᵐᵒᵖ) e) :=
    Module.Projective.of_equiv (columnFinsuppEquiv k B e N).symm
  apply Module.Projective.of_split
    (OAI.ExternalTensor.map (k := k) (LinearMap.id : leftIdeal B e →ₗ[B] leftIdeal B e) i)
    (OAI.ExternalTensor.map (k := k) (LinearMap.id : leftIdeal B e →ₗ[B] leftIdeal B e)
      (Finsupp.linearCombination Bᵐᵒᵖ id))
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul v n =>
    simpa using congrArg (fun z => v ⊗ₜ[k] z) (LinearMap.congr_fun hi n)
  | add x y hx hy => simp_all [map_add]

theorem column_category_projective (e : B) (he : e * e = e)
    (N : ModuleCat.{u} Bᵐᵒᵖ) [Module.Projective Bᵐᵒᵖ N] :
    Projective ((columnFunctor k B e).obj N) := by
  change Projective (ModuleCat.of (Enveloping k B) (Column k B N e))
  letI : Module.Projective (Enveloping k B) (Column k B N e) :=
    column_enveloping_projective k B e he N
  exact ModuleCat.projective_of_categoryTheory_projective _

theorem sum_term_projective {I : Type} [Fintype I] (K : I → BiComplex k B)
    (n : ℤ) (hK : ∀ i, Projective ((K i).X n)) :
    Projective ((⨁ K).X n) := by
  letI (i : I) : Projective ((K i).X n) := hK i
  apply Projective.of_iso ((eval _ _ n).mapBiproduct K).symm
  refine ⟨fun f e _ => ⟨biproduct.desc (fun i => by
    letI : Projective (((eval _ _ n).obj ∘ K) i) := hK i
    exact Projective.factorThru (biproduct.ι ((eval _ _ n).obj ∘ K) i ≫ f) e), ?_⟩⟩
  apply biproduct.hom_ext'
  intro i
  letI : Projective (((eval _ _ n).obj ∘ K) i) := hK i
  simp only [biproduct.ι_desc_assoc, Projective.factorThru_comp]

theorem biprod_term_projective (K L : BiComplex k B) (n : ℤ)
    (hK : Projective (K.X n)) (hL : Projective (L.X n)) :
    Projective ((K ⊞ L).X n) := by
  letI : Projective ((eval (ModuleCat.{u} (Enveloping k B)) (.up ℤ) n).obj K) := hK
  letI : Projective ((eval (ModuleCat.{u} (Enveloping k B)) (.up ℤ) n).obj L) := hL
  letI := preservesBinaryBiproducts_of_preservesBiproducts
    (eval (ModuleCat.{u} (Enveloping k B)) (.up ℤ) n)
  apply Projective.of_iso ((eval _ _ n).mapBiprod K L).symm
  refine ⟨fun f e _ => ⟨biprod.desc
    (Projective.factorThru (biprod.inl ≫ f) e)
    (Projective.factorThru (biprod.inr ≫ f) e), ?_⟩⟩
  apply biprod.hom_ext'
  · simp only [biprod.inl_desc_assoc, Projective.factorThru_comp]
  · simp only [biprod.inr_desc_assoc, Projective.factorThru_comp]

variable {k B}
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

theorem columns_enveloping_projective
    (e₀ : s.e₀ * s.e₀ = s.e₀) (e₁ : s.e₁ * s.e₁ = s.e₁)
    (e₂ : s.e₂ * s.e₂ = s.e₂)
    (h₀ : ∀ n, Module.Projective Bᵐᵒᵖ (D₀.X n))
    (h₁ : ∀ n, Module.Projective Bᵐᵒᵖ (D₁.X n))
    (h₂ : ∀ n, Module.Projective Bᵐᵒᵖ (D₂.X n)) (n : ℤ) :
    Projective ((L0Prime s D₀ D₁ D₂ f g).X n) ∧
    Projective ((L1Prime s D₀ D₁ D₂ f g).X n) ∧
    Projective ((L2Prime s D₀ D₁ D₂ f g).X n) := by
  letI := h₀ n
  letI := h₁ n
  letI := h₂ n
  letI := column_category_projective k B s.e₀ e₀ (D₀.X n)
  letI := column_category_projective k B s.e₁ e₁ (D₀.X n)
  letI := column_category_projective k B s.e₂ e₂ (D₀.X n)
  letI := column_category_projective k B s.e₁ e₁ (D₁.X n)
  letI := column_category_projective k B s.e₂ e₂ (D₁.X n)
  letI := column_category_projective k B s.e₂ e₂ (D₂.X n)
  refine ⟨?_, ?_, ?_⟩
  · apply biprod_term_projective
    · exact column_category_projective k B s.e₀ e₀ (D₀.X n)
    · apply biprod_term_projective
      · exact column_category_projective k B s.e₁ e₁ (D₁.X n)
      · exact column_category_projective k B s.e₂ e₂ (D₂.X n)
  · apply biprod_term_projective
    · apply sum_term_projective
      intro a
      exact column_category_projective k B s.e₁ e₁ (D₀.X n)
    · apply sum_term_projective
      intro b
      exact column_category_projective k B s.e₂ e₂ (D₁.X n)
  · apply sum_term_projective
    intro r
    exact column_category_projective k B s.e₂ e₂ (D₀.X n)

/-- The actual three-column total is termwise projective as a bimodule,
not merely after restriction to right modules. -/
theorem total_enveloping_projective
    (e₀ : s.e₀ * s.e₀ = s.e₀) (e₁ : s.e₁ * s.e₁ = s.e₁)
    (e₂ : s.e₂ * s.e₂ = s.e₂)
    (h₀ : ∀ n, Module.Projective Bᵐᵒᵖ (D₀.X n))
    (h₁ : ∀ n, Module.Projective Bᵐᵒᵖ (D₁.X n))
    (h₂ : ∀ n, Module.Projective Bᵐᵒᵖ (D₂.X n)) :
    ∀ n, Projective ((OAI.LittleFinitistic.InducedRectification.total s D₀ D₁ D₂ f g H).X n) := by
  have hc := columns_enveloping_projective s D₀ D₁ D₂ f g e₀ e₁ e₂ h₀ h₁ h₂
  exact OAI.LittleFinitistic.RectificationTotal.total_projective _ _ _
    (fun n => (hc n).1) (fun n => (hc n).2.1) (fun n => (hc n).2.2)

end
end Note198.EnvelopingProjective
