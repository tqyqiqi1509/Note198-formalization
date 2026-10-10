import Note198.BimoduleTotalDegreewiseSplit
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

namespace Note198.BimoduleTotalConeSequence
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
open ExternalTensor.Section4 BimoduleTotal CochainComplex
universe u
variable {B : Type u} [Ring B]
variable {K L : CochainComplex (ModuleCat.{u} B) ℤ} (f : K ⟶ L)

/-- The standard rotated cone sequence uses the negative projection to `K[1]`. -/
def sequence : ShortComplex (CochainComplex (ModuleCat.{u} B) ℤ) :=
  ShortComplex.mk (mappingCone.inr f) (mappingCone.triangle f).mor₃
    (mappingCone.inr_triangleδ f)

set_option backward.isDefEq.respectTransparency false in
def degreeSplitting (n : ℤ) :
    ((sequence f).map (HomologicalComplex.eval (ModuleCat B) (.up ℤ) n)).Splitting where
  r := (mappingCone.snd f).v n n (add_zero n)
  s := (-(K.shiftFunctorObjXIso 1 n (n+1) rfl).hom) ≫
    (mappingCone.inl f).v (n+1) n (by omega)
  f_r := by
    exact mappingCone.inr_f_snd_v f n
  s_g := by
    change ((-((K.shiftFunctorObjXIso 1 n (n+1) rfl).hom)) ≫
      (mappingCone.inl f).v (n+1) n (by omega)) ≫ (mappingCone.triangle f).mor₃.f n =
        𝟙 ((K⟦(1 : ℤ)⟧).X n)
    have ht := mappingCone.inl_v_triangle_mor₃_f f (n+1) n (by omega)
    calc
      _ = (-((K.shiftFunctorObjXIso 1 n (n+1) rfl).hom)) ≫
          ((mappingCone.inl f).v (n+1) n (by omega) ≫ (mappingCone.triangle f).mor₃.f n) :=
        by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
      _ = (-((K.shiftFunctorObjXIso 1 n (n+1) rfl).hom)) ≫
          (-((K.shiftFunctorObjXIso 1 n (n+1) rfl).inv)) :=
        congrArg (fun t : K.X (n+1) ⟶ (K⟦(1 : ℤ)⟧).X n =>
          (-((K.shiftFunctorObjXIso 1 n (n+1) rfl).hom)) ≫ t) ht
      _ = 𝟙 _ := by simp
  id := by
    apply mappingCone.ext_from f (n+1) n rfl
    · dsimp [sequence]
      simp [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
        mappingCone.inl_v_triangle_mor₃_f]
      exact Category.id_comp ((mappingCone.inl f).v (n+1) n (by omega))
    · dsimp [sequence]
      simp [Preadditive.comp_add, Preadditive.add_comp, Category.assoc]

variable (k : Type u) [Field k] [Algebra k B]
variable (P : BiComplex k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

theorem total_cone_sequence_shortExact :
    ((sequence f).map (functor k B P p hp)).ShortExact :=
  BimoduleTotalDegreewiseSplit.total_shortExact k B P p hp (sequence f)
    (degreeSplitting f)

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]

/-- The images of the three rotated cone objects are the objects of an actual
 distinguished triangle. No exactness certificate is an input. -/
theorem total_cone_distinguished :
    DerivedCategory.triangleOfSES (total_cone_sequence_shortExact f k P p hp) ∈
      distTriang (DerivedCategory (ModuleCat.{u} B)) :=
  DerivedCategory.triangleOfSES_distinguished _
end
end Note198.BimoduleTotalConeSequence
