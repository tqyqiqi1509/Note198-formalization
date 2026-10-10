import Note198.GenericOddDouble
import OAI.Algebra.Finitistic.Localization.FormalSummandAction
import OAI.Algebra.Finitistic.Localization.DiagramLifting

namespace Note198.GenericOddAction
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Idempotents
open OAI.LittleFinitistic OAI.LittleFinitistic.FormalSummandAction
variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]
variable {C : Type*} [Category C] [Preadditive C] [Linear k C]
variable [HasShift C ℤ] [HasZeroObject C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [∀ n : ℤ, (shiftFunctor C n).Linear k]
local instance : HasFiniteBiproducts (Karoubi C) := Karoubi.karoubi_hasFiniteBiproducts
local instance : HasBinaryBiproducts (Karoubi C) := hasBinaryBiproducts_of_finite_biproducts _
variable {L : C} (θ : R →ₐ[k] End L) (e : R) (he : e * e = e)
variable (hc : ∀ r : R, e * r = r * e) (α : R →ₐ[k] R) (s : ℤ)

/-- The selecting algebra acts on both summands, with the chosen shift s. -/
def oddDoubleAction :
    R →ₐ[k] End (summand θ e he ⊞ OddDouble.formalShift (summand θ e he) s) :=
  biprodAction (action θ e he hc α)
    (mapAction (OddDouble.formalShiftFunctor s) (action θ e he hc α))

/-- Application of the actual two-summand action. -/
theorem oddDoubleAction_apply (r : R) :
    oddDoubleAction θ e he hc α s r =
      biprod.map (action θ e he hc α r)
        ((OddDouble.formalShiftFunctor s).map (action θ e he hc α r)) := rfl
/-- The actual object and its action are chosen before the evaluation module. -/
theorem fixed_old_object_with_action (hs : 3 ≤ s) (hodd : Odd s) :
    ∃ (V₀ : C) (ρ₀ : R →ₐ[k] End V₀)
      (i : (toKaroubi C).obj V₀ ≅
        summand θ e he ⊞ OddDouble.formalShift (summand θ e he) s),
      ∀ r : R, (toKaroubi C).map (ρ₀ r) ≫ i.hom =
        i.hom ≫ oddDoubleAction θ e he hc α s r := by
  obtain ⟨V₀, ⟨i⟩⟩ := OddDoubleGeneral.manuscript_all_odd (summand θ e he) s hs hodd
  let σ := oddDoubleAction θ e he hc α s
  let τ := transportAction i σ
  refine ⟨V₀, oldAction τ, i, ?_⟩
  intro r
  rw [oldAction_lift]
  change (i.hom ≫ σ r ≫ i.inv) ≫ i.hom = i.hom ≫ σ r
  simp
end
end Note198.GenericOddAction
namespace Note198.GenericOddFixedDiagram
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Idempotents
open OAI.LittleFinitistic OAI.LittleFinitistic.FormalSummandAction
variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]
variable {C Q : Type*} [Category C] [Category Q] [Preadditive C] [Preadditive Q]
  [Linear k C] [Linear k Q]

/-- Algebra relations are the homogeneous quadratic diagram relations under any action. -/
theorem action_relations {X : Q} (ρ : R →ₐ[k] End X) (na nb nr : ℕ)
    (x : Fin na → R) (y : Fin nb → R) (c : Fin nr → Fin na → Fin nb → k)
    (hc : ∀ t, ∑ a, ∑ b, c t a b • (y b * x a) = 0) :
    ∀ t, ∑ a, ∑ b, c t a b • ((ρ (x a) : X ⟶ X) ≫ ρ (y b)) = 0 := by
  intro t
  have h := congrArg ρ (hc t)
  simpa only [map_sum,map_smul,map_mul,map_zero,End.mul_def] using h

variable (q : C ⥤ Q) (W : MorphismProperty C) [q.IsLocalization W]
  [W.HasRightCalculusOfFractions] [q.Additive] [q.Linear k]
variable [HasShift Q ℤ] [HasZeroObject Q]
  [∀ n : ℤ, (shiftFunctor Q n).Additive] [Pretriangulated Q]
  [∀ n : ℤ, (shiftFunctor Q n).Linear k]
local instance : HasFiniteBiproducts (Karoubi Q) := Karoubi.karoubi_hasFiniteBiproducts
local instance : HasBinaryBiproducts (Karoubi Q) :=
  hasBinaryBiproducts_of_finite_biproducts (Karoubi Q)

include W in
/-- Fixed source-category objects and arrows, with every quadratic relation exact,
represent the odd double of the selecting action in the localization. -/
theorem fixed_diagram {L : Q} (θ : R →ₐ[k] End L)
    (e : R) (he : e*e=e) (hec : ∀ r : R, e*r=r*e) (α : R →ₐ[k] R)
    (s : ℤ) (hs : 3 ≤ s) (hodd : Odd s)
    (na nb nr : ℕ) (x : Fin na → R) (y : Fin nb → R)
    (c : Fin nr → Fin na → Fin nb → k)
    (hc : ∀ t, ∑ a, ∑ b, c t a b • (y b * x a) = 0) :
    ∃ (V₀ : Q) (ρ₀ : R →ₐ[k] End V₀)
      (i : (toKaroubi Q).obj V₀ ≅
        summand θ e he ⊞ OddDouble.formalShift (summand θ e he) s)
      (D₀ D₁ D₂ : C) (φ₀ : q.obj D₀ ≅ V₀) (φ₁ : q.obj D₁ ≅ V₀)
      (φ₂ : q.obj D₂ ≅ V₀) (f : Fin na → (D₀ ⟶ D₁)) (g : Fin nb → (D₁ ⟶ D₂)),
      (∀ r : R, (toKaroubi Q).map (ρ₀ r) ≫ i.hom =
        i.hom ≫ GenericOddAction.oddDoubleAction θ e he hec α s r) ∧
      (∀ a, q.map (f a) ≫ φ₁.hom = φ₀.hom ≫ ρ₀ (x a)) ∧
      (∀ b, q.map (g b) ≫ φ₂.hom = φ₁.hom ≫ ρ₀ (y b)) ∧
      (∀ t, ∑ a, ∑ b, c t a b • (f a ≫ g b) = 0) := by
  obtain ⟨V₀,ρ₀,i,hi⟩ := GenericOddAction.fixed_old_object_with_action θ e he hec α s hs hodd
  obtain ⟨D₀,D₁,D₂,φ₀,φ₁,φ₂,f,g,hf,hg,hrel⟩ :=
    DiagramLifting.finite_quadratic_diagram_lifting q W na nb nr V₀ V₀ V₀
      (fun a => ρ₀ (x a)) (fun b => ρ₀ (y b)) c (action_relations ρ₀ na nb nr x y c hc)
  exact ⟨V₀,ρ₀,i,D₀,D₁,D₂,φ₀,φ₁,φ₂,f,g,hi,hf,hg,hrel⟩

end Note198.GenericOddFixedDiagram
