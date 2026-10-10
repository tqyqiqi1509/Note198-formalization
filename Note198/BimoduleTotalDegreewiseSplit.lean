import OAI.Algebra.Finitistic.Bimodule.BimoduleShiftCoherence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

namespace Note198.BimoduleTotalDegreewiseSplit
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
open ExternalTensor.Section4 BimoduleTotal
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} B) ℤ))
variable (hS : ∀ n : ℤ, (S.map (HomologicalComplex.eval (ModuleCat B) (.up ℤ) n)).Splitting)

def columnSplitting (i : Fin l) (n : ℤ) :
    ((S.map (columnFunctor k B P (p i))).map
      (HomologicalComplex.eval (ModuleCat B) (.up ℤ) n)).Splitting :=
  (hS (n + -(p i))).map (inputFunctor k B (P.X (p i)))

def totalSplitting (n : ℤ) :
    ((S.map (functor k B P p hp)).map
      (HomologicalComplex.eval (ModuleCat B) (.up ℤ) n)).Splitting where
  r := ModuleCat.ofHom
    { toFun := fun x i => (columnSplitting k B P p S hS i n).r.hom (x i)
      map_add' := fun x y => funext (fun i =>
        (columnSplitting k B P p S hS i n).r.hom.map_add (x i) (y i))
      map_smul' := fun b x => funext (fun i =>
        (columnSplitting k B P p S hS i n).r.hom.map_smul b (x i)) }
  s := ModuleCat.ofHom
    { toFun := fun x i => (columnSplitting k B P p S hS i n).s.hom (x i)
      map_add' := fun x y => funext (fun i =>
        (columnSplitting k B P p S hS i n).s.hom.map_add (x i) (y i))
      map_smul' := fun b x => funext (fun i =>
        (columnSplitting k B P p S hS i n).s.hom.map_smul b (x i)) }
  f_r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    have h := congrArg (fun f => f.hom (x i)) (columnSplitting k B P p S hS i n).f_r
    change (columnSplitting k B P p S hS i n).r.hom
      ((((functor k B P p hp).map S.f).f n).hom x i) = x i
    erw [functor_map_component]
    exact h
  s_g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    have h := congrArg (fun f => f.hom (x i)) (columnSplitting k B P p S hS i n).s_g
    change (((functor k B P p hp).map S.g).f n).hom
      (fun i => (columnSplitting k B P p S hS i n).s.hom (x i)) i = x i
    erw [functor_map_component]
    exact h
  id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    let C := ((S.map (columnFunctor k B P (p i))).map
      (HomologicalComplex.eval (ModuleCat B) (.up ℤ) n))
    have h := congrArg (fun f : C.X₂ ⟶ C.X₂ => f.hom (show C.X₂ from x i))
      (columnSplitting k B P p S hS i n).id
    change (show C.X₂ from ((((functor k B P p hp).map S.f).f n).hom
        (fun i => (columnSplitting k B P p S hS i n).r.hom (x i)) i)) +
      (show C.X₂ from (columnSplitting k B P p S hS i n).s.hom
        ((((functor k B P p hp).map S.g).f n).hom x i)) = (show C.X₂ from x i)
    erw [functor_map_component, functor_map_component]
    exact h

include hS in
/-- Signed finite tensor total preserves actual degreewise-split short
exact sequences, without an exactness assumption on the bimodule. -/
theorem total_shortExact : (S.map (functor k B P p hp)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact (totalSplitting k B P p hp S hS n).shortExact
end
end Note198.BimoduleTotalDegreewiseSplit
