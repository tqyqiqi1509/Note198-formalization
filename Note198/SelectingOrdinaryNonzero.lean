import Note198.SelectingOrdinaryAlgebra
import Note198.EvaluationProjectiveNonzero

namespace Note198
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open OAI OAI.LittleFinitistic QuadraticEncoding OrdinarySimulation
universe u
namespace SelectingOrdinaryNonzero
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)

/-- Zero compression forces every actual term of the fixed complex to
vanish: the interval includes all its support. -/
theorem terms_zero_of_compression_zero
    [Subsingleton (SelectingOrdinaryAlgebra.O E S)] (n : ℤ) :
    IsZero ((SelectingRectification.bimodule E S).X n) := by
  classical
  by_cases hn : n < SelectingOrdinaryAlgebra.a E S ∨ SelectingOrdinaryAlgebra.b E S < n
  · exact SelectingOrdinaryAlgebra.support E S n hn
  · have hlow : SelectingOrdinaryAlgebra.a E S ≤ n := by omega
    have hhigh : n ≤ SelectingOrdinaryAlgebra.b E S := by omega
    let i : Fin (SelectingOrdinaryAlgebra.length E S + 1) :=
      ⟨(n - SelectingOrdinaryAlgebra.a E S).toNat, by
        have he := SelectingOrdinaryAlgebra.endpoints E S
        omega⟩
    have hi : SelectingOrdinaryAlgebra.a E S + (i.val : ℤ) = n := by
      dsimp [i]
      omega
    have hsub : Subsingleton ((SelectingRectification.bimodule E S).X
        (SelectingOrdinaryAlgebra.a E S + (i.val : ℤ))) := by
      have hz (x : (SelectingRectification.bimodule E S).X
          (SelectingOrdinaryAlgebra.a E S + (i.val : ℤ))) : x = 0 := by
        let w : SelectingOrdinaryAlgebra.O E S :=
          Function.update (fun j => 0) i x
        have hw : w = 0 := Subsingleton.elim _ _
        have hx := congrFun hw i
        have hx' : x = (0 : SelectingOrdinaryAlgebra.O E S) i := by
          simpa only [w, Function.update_self] using hx
        exact hx'.trans (show (0 : SelectingOrdinaryAlgebra.O E S) i = 0 from rfl)
      exact ⟨fun x y => (hz x).trans (hz y).symm⟩
    rw [← hi]
    letI := hsub
    exact ModuleCat.isZero_of_subsingleton _

variable {Y : Type u} [AddCommGroup Y] [Module k Y] [Module R Y]
  [IsScalarTower k R Y] [FiniteDimensional k Y]

/-- A genuinely nonzero value of H witnesses that the fixed ordinary
off-diagonal module O is nonzero. No property of O is assumed. -/
theorem ordinary_O_nontrivial
    [Nontrivial (SelectingNativeEvaluation.H (S := S) (Y := Y))] :
    Nontrivial (SelectingOrdinaryAlgebra.O E S) := by
  classical
  by_contra hn
  letI : Subsingleton (SelectingOrdinaryAlgebra.O E S) :=
    not_nontrivial_iff_subsingleton.mp hn
  have hterm (n : ℤ) : IsZero
      ((SelectingTensor.complex (enc := E) (S := S)
        (SelectingRealization.input (E := E) (Y := Y))).X n) :=
    (BimoduleBalancedTensor.functor k (B E.relations)
      (SelectingRealization.input (E := E) (Y := Y))).map_isZero
        (terms_zero_of_compression_zero E S n)
  have hcomplex : IsZero (SelectingTensor.complex (enc := E) (S := S)
      (SelectingRealization.input (E := E) (Y := Y))) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    ext n x
    letI := ModuleCat.isZero_iff_subsingleton.mp (hterm n)
    exact Subsingleton.elim _ _
  have hhom : IsZero ((SelectingTensor.complex (enc := E) (S := S)
      (SelectingRealization.input (E := E) (Y := Y))).homology 0) :=
    (homologyFunctor (ModuleCat (B E.relations)) (.up ℤ) 0).map_isZero hcomplex
  have href : IsZero (SelectingRealization.reference (E := E) (S := S) (Y := Y)) :=
    (SelectingRealization.cohomology (E := E) (S := S) (Y := Y) 0 (Or.inl rfl)).isZero_iff.mp hhom
  letI := ModuleCat.isZero_iff_subsingleton.mp href
  obtain ⟨y,hy⟩ := exists_ne (0 : SelectingNativeEvaluation.H (S := S) (Y := Y))
  have hz : (y,0,0) = (0 : SelectingRealization.reference (E := E) (S := S) (Y := Y)) :=
    Subsingleton.elim (α := SelectingRealization.reference (E := E) (S := S) (Y := Y))
      (show SelectingRealization.reference (E := E) (S := S) (Y := Y) from (y,0,0)) 0
  exact hy (congrArg (fun z : SelectingRealization.reference (E := E) (S := S) (Y := Y) => z.1) hz)

variable {V : Type u} [AddCommGroup V] [Module k V] (Z : Representation E.relations V)

/-- With one nonzero selected witness, Q(V)=O tensor_B M(V) is nonzero
for every nonzero input V. The right projectivity is that of the actual
compressed selecting complex. -/
theorem ordinary_Q_nontrivial
    [Nontrivial (SelectingNativeEvaluation.H (S := S) (Y := Y))] [Nontrivial V] :
    Nontrivial (BalancedTensor.Tensor k (B E.relations)
      (SelectingOrdinaryAlgebra.O E S) Z.Evaluation) := by
  letI := ordinary_O_nontrivial E S (Y := Y)
  exact projective_evaluation_tensor_nontrivial E.relations Z (SelectingOrdinaryAlgebra.O E S)

end SelectingOrdinaryNonzero
end
end Note198
