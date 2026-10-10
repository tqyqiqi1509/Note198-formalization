import Note198.ComplexExtensionTensor
import Note198.ComplexProjectiveModels
import Note198.ComplexStupidTruncation
import OAI.Algebra.Finitistic.Dimension.PDDetection

namespace Note198.ComplexModuleDimension
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
open OAI.LittleFinitistic
open Note198.ComplexProjectiveDimension Note198.ComplexProjectiveModels
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} A)]

/-- Residue detection applies to any genuine bounded finite projective
representative; its differentials need not be minimal. -/
theorem bound_iff_representative_residue_zero
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (lo hi : ℤ)
    (hP : ∀ n, Module.Finite A (P.X n) ∧ Module.Projective A (P.X n))
    (hb : ∀ n, n < lo ∨ hi < n → IsZero (P.X n))
    (Z : DerivedCategory (ModuleCat.{u} A)) (eP : DerivedCategory.Q.obj P ≅ Z) (d : ℤ) :
    HasSignedProjectiveBound Z d ↔
      ∀ n, n < -d → IsZero ((residueComplex k P).homology n) := by
  have hp : ∀ n, FiniteDimensional k (P.X n) ∧ Module.Projective A (P.X n) := by
    intro n
    letI := (hP n).1
    exact ⟨Module.Finite.trans A (P.X n),(hP n).2⟩
  obtain ⟨Q,hQ,hm⟩ := exists_minimal_bounded_representative k P lo hi hp hb
  obtain ⟨e⟩ := hQ.1
  letI := e.quasiIso_hom
  let eQ : DerivedCategory.Q.obj Q ≅ Z :=
    (asIso (DerivedCategory.Q.map e.hom)).symm ≪≫ eP
  have hQfinite : ∀ n, Module.Finite A (Q.X n) ∧ Module.Projective A (Q.X n) := by
    intro n
    letI := (hQ.2.1 n).1
    exact ⟨Module.Finite.of_restrictScalars_finite k A (Q.X n),(hQ.2.1 n).2⟩
  letI := bounded_projective_isKProjective P hi (fun n => (hP n).2)
    (fun n hn => hb n (Or.inr hn))
  letI := bounded_projective_isKProjective Q hi (fun n => (hQfinite n).2)
    (fun n hn => hQ.2.2 n (Or.inr hn))
  rw [bound_iff_residueHomology_zero k Q lo hi hQfinite hQ.2.2 hm Z eQ d]
  exact forall_congr' fun n => imp_congr_right fun _ =>
    (residueHomologyIsoOfDerivedIso k Q P (eQ ≪≫ eP.symm) n).isZero_iff
include k in
/-- For any actual bounded finite-projective representative, the infimum
of signed bounds is attained whenever it is at most a finite integer.
This is proved by actual residue detection and its finite-support supremum. -/
theorem signed_pd_le_iff_bound
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (lo hi : ℤ)
    (hP : ∀ n, Module.Finite A (P.X n) ∧ Module.Projective A (P.X n))
    (hb : ∀ n, n < lo ∨ hi < n → IsZero (P.X n))
    (Z : DerivedCategory (ModuleCat.{u} A)) (eP : DerivedCategory.Q.obj P ≅ Z) (d : ℤ) :
    signedProjectiveDimension Z ≤ ((d:WithTop ℤ):WithBot (WithTop ℤ)) ↔
      HasSignedProjectiveBound Z d := by
  constructor
  · intro hle
    have hp : ∀ n, FiniteDimensional k (P.X n) ∧ Module.Projective A (P.X n) := by
      intro n
      letI := (hP n).1
      exact ⟨Module.Finite.trans A (P.X n),(hP n).2⟩
    obtain ⟨Q,hQ,hm⟩ := exists_minimal_bounded_representative k P lo hi hp hb
    obtain ⟨e⟩ := hQ.1
    letI := e.quasiIso_hom
    let eQ : DerivedCategory.Q.obj Q ≅ Z :=
      (asIso (DerivedCategory.Q.map e.hom)).symm ≪≫ eP
    have hQfinite : ∀ n, Module.Finite A (Q.X n) ∧ Module.Projective A (Q.X n) := by
      intro n
      letI := (hQ.2.1 n).1
      exact ⟨Module.Finite.of_restrictScalars_finite k A (Q.X n),(hQ.2.1 n).2⟩
    rw [Note198.ComplexStupidTruncation.signed_pd_eq_residue_sup
      (k:=k) Q lo hi hQfinite hQ.2.2 hm Z eQ] at hle
    apply (bound_iff_residueHomology_zero k Q lo hi hQfinite hQ.2.2 hm Z eQ d).mpr
    intro n hn
    by_contra hzero
    have hmem : (((-n):WithTop ℤ):WithBot (WithTop ℤ)) ∈
        ((fun c:ℤ => ((c:WithTop ℤ):WithBot (WithTop ℤ))) ''
          Note198.ComplexStupidTruncation.residueDegreeSet (k:=k) Q) := by
      refine ⟨-n,?_,rfl⟩
      simpa only [Note198.ComplexStupidTruncation.residueDegreeSet, Set.mem_setOf_eq, neg_neg] using hzero
    have hnd := (le_sSup hmem).trans hle
    have hnd' : -n ≤ d := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hnd)
    omega
  · exact signedProjectiveDimension_le_of_bound

variable (M : PDMinimal.FiniteModule k A)

/-- This is actual derived tensor cohomology, in the manuscript's sign
convention H^(-n)=Tor_n, for the actual minimal cover resolution. -/
def stalkResidueTorIso (n : ℕ) :
    (residueComplex k (stalkProjectiveComplex M)).homology (-(n:ℤ)) ≅
      PDTensor.Tor (k:=k) (PDTensor.Residue (A:=A)) M.cat n :=
  Note198.ComplexExtensionTensor.mappedExtensionHomologyIso
    (PDTensor.tensorFunctor k A (PDTensor.Residue (A:=A))) (PDMinimal.complex M) n ≪≫
      (PDTensor.torIsoModel (PDTensor.Residue (A:=A)) M n).symm

/-- Numerical module pd and signed stalk pd have the same finite bounds.
Only the module's own finite pd is needed, not finite global dimension of A. -/
theorem stalk_signed_bound_iff (g : ℕ) (hg : HasProjectiveDimensionLE M.cat g) (d : ℕ) :
    HasSignedProjectiveBound ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M.cat)
      (d:ℤ) ↔ HasProjectiveDimensionLE M.cat d := by
  rw [bound_iff_representative_residue_zero (k:=k) (stalkProjectiveComplex M) (-(g:ℤ)) 0
    (fun n => ⟨stalk_term_finite M n,stalk_term_projective M n⟩)
    (stalk_term_bounded M g hg) _ (stalkDerivedIso M)]
  constructor
  · intro h
    apply (PDTensor.pdLE_iff_residueTor_zero M d).mpr
    exact (stalkResidueTorIso M (d+1)).isZero_iff.mp
      (h (-((d+1:ℕ):ℤ)) (by push_cast; omega))
  · intro hd n hn
    letI : HasProjectiveDimensionLE M.cat d := hd
    let j : ℕ := (-n).toNat
    have hnj : -(j:ℤ) = n := by
      dsimp [j]
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    have hdj : d < j := by
      have : (j:ℤ) = -n := by dsimp [j]; exact Int.toNat_of_nonneg (by omega)
      omega
    have hj : HasProjectiveDimensionLE M.cat (j-1) :=
      hasProjectiveDimensionLT_of_ge M.cat (d+1) ((j-1)+1) (by omega)
    have hz := (PDTensor.pdLE_iff_residueTor_zero M (j-1)).mp hj
    have hzj : IsZero (PDTensor.Tor (k:=k) (PDTensor.Residue (A:=A)) M.cat j) := by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j)] using hz
    have := (stalkResidueTorIso M j).isZero_iff.mpr hzj
    simpa only [hnj] using this
/-- A residue edge gives the exact signed stalk dimension; the edge is the
actual Tor group, not an assumed formula for signed dimension. -/
theorem signed_stalk_eq_of_tor_edge (g n : ℕ)
    (hg : HasProjectiveDimensionLE M.cat g)
    (hn : HasProjectiveDimensionLE M.cat n)
    (hedge : ¬ IsZero (PDTensor.Tor (k:=k) (PDTensor.Residue (A:=A)) M.cat n)) :
    signedProjectiveDimension
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M.cat) =
      (((n:ℤ):WithTop ℤ):WithBot (WithTop ℤ)) := by
  have hcriterion (c : ℤ) :
      HasSignedProjectiveBound
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M.cat) c ↔ (n:ℤ) ≤ c := by
    rw [bound_iff_representative_residue_zero (k:=k) (stalkProjectiveComplex M) (-(g:ℤ)) 0
      (fun i => ⟨stalk_term_finite M i,stalk_term_projective M i⟩)
      (stalk_term_bounded M g hg) _ (stalkDerivedIso M)]
    constructor
    · intro hc
      by_contra h
      exact hedge ((stalkResidueTorIso M n).isZero_iff.mp
        (hc (-(n:ℤ)) (neg_lt_neg (lt_of_not_ge h))))
    · intro h i hi
      exact residueHomology_isZero_of_term_zero k (stalkProjectiveComplex M) i
        (stalk_term_bounded M n hn i (Or.inl (by omega)))
  apply le_antisymm
  · exact signedProjectiveDimension_le_of_bound ((hcriterion n).mpr le_rfl)
  · unfold signedProjectiveDimension
    apply le_sInf
    rintro x ⟨c,hc,rfl⟩
    exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ((hcriterion c).mp hc))
/-- Exact numerical module pd supplies its own nonzero residue edge,
including pd zero. No minimal-term or Tor witness is required as input. -/
theorem residueTor_nonzero_of_projectiveDimension_eq (n : ℕ)
    (hpd : projectiveDimension M.cat = n) :
    ¬ IsZero (PDTensor.Tor (k:=k) (PDTensor.Residue (A:=A)) M.cat n) := by
  intro hz
  cases n with
  | zero =>
    have hterm := (PDTensor.residueTor_zero_iff_term M 0).mp hz
    letI := hterm
    haveI : Subsingleton M := Function.Surjective.subsingleton (PDMinimal.cover M).surjective
    have hzero : IsZero M.cat := by
      apply ModuleCat.isZero_iff_subsingleton.mpr
      change Subsingleton M
      infer_instance
    have hbot := (projectiveDimension_eq_bot_iff M.cat).mpr hzero
    rw [hpd] at hbot
    exact (by simp : (0 : WithBot ℕ∞) ≠ ⊥) hbot
  | succ n =>
    have hle := (projectiveDimension_le_iff M.cat n).mpr
      ((PDTensor.pdLE_iff_residueTor_zero M n).mpr hz)
    rw [hpd] at hle
    have hlt : (n : WithBot ℕ∞) < (n+1 : ℕ) := by exact_mod_cast Nat.lt_succ_self n
    exact (not_le_of_gt hlt) hle

/-- The manuscript's signed stalk value agrees with actual finite numerical
module projective dimension, with no detection edge assumed. -/
theorem signed_stalk_eq_projectiveDimension (n : ℕ)
    (hpd : projectiveDimension M.cat = n) :
    signedProjectiveDimension
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M.cat) =
      (((n:ℤ):WithTop ℤ):WithBot (WithTop ℤ)) := by
  have hn := (projectiveDimension_le_iff M.cat n).mp (le_of_eq hpd)
  exact signed_stalk_eq_of_tor_edge M n n hn hn
    (residueTor_nonzero_of_projectiveDimension_eq M n hpd)

end
end Note198.ComplexModuleDimension





