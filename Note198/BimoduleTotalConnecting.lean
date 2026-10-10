import Note198.BimoduleTotalDegreewiseSplit
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

namespace Note198.BimoduleTotalConnecting
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI.LittleFinitistic
open OAI.ExternalTensor.Section4 BimoduleTotal CochainComplex
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} B) ℤ))
variable (σ : ∀ n : ℤ, (S.map (HomologicalComplex.eval (ModuleCat B) (.up ℤ) n)).Splitting)
open BimoduleTotalDegreewiseSplit

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Horizontal bimodule differentials do not contribute to the connecting
cocycle: the section followed by the retraction is zero in every input degree. -/
theorem horizontal_connecting_zero (n : ℤ) (i j : Fin l)
    (x : Term k B P S.X₃ (p i) (n + -(p i))) :
    (columnSplitting k B P p S σ j (n+1)).r.hom
      (entryBetween k B P S.X₂ n (n+1) (p i) (p j) rfl
        ((columnSplitting k B P p S σ i n).s.hom x)) = 0 := by
  unfold entryBetween
  split_ifs with hij
  · have heq : n + -(p i) = (n+1) + -(p j) := by omega
    have transport_sr (q q' : ℤ) (h : q = q') :
        (σ q).s ≫ eqToHom (congrArg S.X₂.X h) ≫ (σ q').r = 0 := by
      subst q'
      simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using (σ q).s_r
    have hsr : (σ (n + -(p i))).s ≫
        eqToHom (congrArg S.X₂.X heq) ≫ (σ ((n+1) + -(p j))).r = 0 :=
      transport_sr _ _ heq
    induction x using BalancedTensor.induction_on with
    | hz => simp only [map_zero]
    | ht a y =>
      have hy := congrArg (fun f => f.hom y) hsr
      change (σ ((n+1) + -(p j))).r.hom
        ((eqToHom (congrArg S.X₂.X heq)).hom ((σ (n + -(p i))).s.hom y)) = 0 at hy
      change BalancedTensor.mk k B
        (ComplexTensor.rightTerm k B (right k B P) (p j))
        (ComplexTensor.leftTerm k B S.X₁ ((n+1) + -(p j)))
        (((forgetRight k B).map (P.d (p i) (p j))).hom a)
        ((σ ((n+1) + -(p j))).r.hom
          ((eqToHom (congrArg S.X₂.X heq)).hom ((σ (n + -(p i))).s.hom y))) = 0
      rw [hy]
      exact (BalancedTensor.mk k B
        (ComplexTensor.rightTerm k B (right k B P) (p j))
        (ComplexTensor.leftTerm k B S.X₁ ((n+1) + -(p j)))
        (((forgetRight k B).map (P.d (p i) (p j))).hom a)).map_zero
    | ha x y hx hy =>
      simp only [map_add]
      rw [hx,hy,add_zero]
  · simp only [LinearMap.zero_apply, map_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Each component of the true connecting arrow of the total is the
connecting arrow of its shifted column; the horizontal terms have vanished. -/
theorem connecting_component (n : ℤ)
    (x : TotalTerm k B P p S.X₃ n) (j : Fin l) :
    ((homOfDegreewiseSplit (S.map (functor k B P p hp))
      (totalSplitting k B P p hp S σ)).f n).hom x j =
    ((homOfDegreewiseSplit (S.map (columnFunctor k B P (p j)))
      (fun n => columnSplitting k B P p S σ j n)).f n).hom (x j) := by
  rw [homOfDegreewiseSplit_f,homOfDegreewiseSplit_f]
  change (columnSplitting k B P p S σ j (n+1)).r.hom
    (((total k B P p hp S.X₂).d n (n+1)).hom
      (fun i => (columnSplitting k B P p S σ i n).s.hom (x i)) j) = _
  erw [total_d_apply k B P S.X₂ p hp n (n+1) rfl]
  rw [map_add,map_sum]
  have hz : (∑ i : Fin l, (columnSplitting k B P p S σ j (n+1)).r.hom
      (entryBetween k B P S.X₂ n (n+1) (p i) (p j) rfl
        ((columnSplitting k B P p S σ i n).s.hom (x i)))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact horizontal_connecting_zero k B P p S σ n i j (x i)
  rw [hz,add_zero]
  rw [← fullColumn_d]
  rfl
end
end Note198.BimoduleTotalConnecting
