import Note198.SelectingOrdinaryAlgebra
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.Data.Int.Interval
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-! Actual dimensions of the coordinate algebras and the ordinary compression. -/
namespace Note198.ActualDimensionFormulas
noncomputable section
open CategoryTheory CategoryTheory.Limits OAI OAI.LittleFinitistic
open QuadraticEncoding OrdinarySimulation
open scoped TensorProduct
universe u
variable {k : Type u} [Field k]

/-- Each of the two actual arrow spaces has d+1 basis vectors. -/
theorem arrows_finrank (d : ℕ) : Module.finrank k (Arrows k d) = d + 1 := by
  simp [Arrows, Module.finrank_pi]

/-- The actual length-two path tensor space has dimension (d+1)^2. -/
theorem paths_finrank (d : ℕ) : Module.finrank k (QuadraticEncoding.Paths k d) = (d + 1)^2 := by
  simp [QuadraticEncoding.Paths, Module.finrank_tensorProduct, arrows_finrank, pow_two]

/-- No independence of the raw defining relations is assumed. -/
theorem encoding_dimension_add_relation {d t : ℕ} (P : Relations k d t) :
    Module.finrank k (B P) + Module.finrank k (relationSpace P) =
      3 + 2 * (d + 1) + (d + 1)^2 := by
  have hq := Submodule.finrank_quotient_add_finrank (relationSpace P)
  rw [paths_finrank] at hq
  change Module.finrank k
    (k × k × k × Arrows k d × Arrows k d × (QuadraticEncoding.Paths k d ⧸ relationSpace P)) +
      Module.finrank k (relationSpace P) = _
  simp only [Module.finrank_prod, Module.finrank_self, arrows_finrank]
  omega

/-- The formula for B subtracts the actual span dimension, not the raw relation count. -/
theorem encoding_dimension {d t : ℕ} (P : Relations k d t) :
    Module.finrank k (B P) =
      3 + 2 * (d + 1) + (d + 1)^2 - Module.finrank k (relationSpace P) := by
  exact Nat.eq_sub_of_add_eq (encoding_dimension_add_relation P)

/-- With an actual basis of the relation span, this is the manuscript's basis-cardinality formula. -/
theorem encoding_dimension_basis {d t : ℕ} (P : Relations k d t)
    {ι : Type*} [Fintype ι] (r : Module.Basis ι k (relationSpace P)) :
    Module.finrank k (B P) = 3 + 2 * (d+1) + (d+1)^2 - Fintype.card ι := by
  rw [encoding_dimension, Module.finrank_eq_card_basis r]

/-- The terminal character W has underlying vector space k. -/
theorem terminal_character_dimension : Module.finrank k k = 1 := Module.finrank_self k

/-- The actual chain algebra has l+1 vertices and l arrows. -/
theorem chain_dimension (l : ℕ) : Module.finrank k (ChainAlgebra k l) = 2*l + 1 := by
  change Module.finrank k ((Fin (l+1) → k) × (Fin l → k)) = _
  simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin]
  omega

/-- Indexing all integer degrees in the compression interval is equivalent to its Fin index. -/
theorem interval_sum (f : ℤ → ℕ) (a : ℤ) (l : ℕ) :
    (∑ i : Fin (l+1), f (a+(i.val:ℤ))) = ∑ n ∈ Finset.Icc a (a+(l:ℤ)), f n := by
  classical
  apply Finset.sum_bij (fun (i : Fin (l+1)) _ ↦ a+(i.val:ℤ))
  · intro i _
    simp only [Finset.mem_Icc]
    have hi := i.isLt
    constructor <;> omega
  · intro i _ j _ hij
    apply Fin.ext
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    let i : Fin (l+1) := ⟨(n-a).toNat, by omega⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    dsimp [i]
    omega
  · intro i _
    rfl

section Ordinary
variable {B₀ : Type u} [Ring B₀] [Algebra k B₀] [FiniteDimensional k B₀]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B₀)) ℤ)
variable [∀ n, FiniteDimensional k ((underlyingComplex (k := k) P).X n)]
variable (a : ℤ) (l : ℕ)

/-- Compression has exactly the dimensions of the actual terms on its interval. -/
theorem compression_dimension : Module.finrank k (BimoduleO P a l) =
    ∑ i : Fin (l+1), Module.finrank k ((underlyingComplex (k := k) P).X (a+(i.val:ℤ))) := by
  change Module.finrank k
    (∀ i : Fin (l+1), (underlyingComplex (k := k) P).X (a+(i.val:ℤ))) = _
  exact Module.finrank_pi_fintype k

/-- The actual opposite block is the specified one-dimensional terminal tensor. -/
theorem terminal_dimension : Module.finrank k (TerminalTensor B₀) = Module.finrank k B₀ := rfl

/-- D is B times the chain tensor, with its actual coordinate algebra structure. -/
theorem base_dimension : Module.finrank k (AlgebraD k l B₀) =
    (2*l+2) * Module.finrank k B₀ := by
  change Module.finrank k (B₀ × (B₀ ⊗[k] ChainAlgebra k l)) = _
  rw [Module.finrank_prod, Module.finrank_tensorProduct, chain_dimension]
  ring

/-- The dimension of the actual square-zero extension, before any specialization. -/
theorem ordinary_dimension :
    Module.finrank k (TrivSqZeroExt (AlgebraD k l B₀) (BimoduleX P a l)) =
      (2*l+3) * Module.finrank k B₀ +
        ∑ i : Fin (l+1), Module.finrank k ((underlyingComplex (k := k) P).X (a+(i.val:ℤ))) := by
  change Module.finrank k ((AlgebraD k l B₀) × (BimoduleO P a l × TerminalTensor B₀)) = _
  rw [Module.finrank_prod, base_dimension, Module.finrank_prod, compression_dimension,
    terminal_dimension]
  ring
end Ordinary

section Selecting
variable {R : Type u} [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)

/-- The formula applied to the actual globally constructed ordinary algebra A. -/
theorem selecting_ordinary_dimension :
    Module.finrank k (SelectingOrdinaryAlgebra.A E S) =
      (2 * SelectingOrdinaryAlgebra.length E S + 3) * Module.finrank k (B E.relations) +
      ∑ i : Fin (SelectingOrdinaryAlgebra.length E S + 1),
        Module.finrank k ((underlyingComplex (k := k) (SelectingRectification.bimodule E S)).X
          (SelectingOrdinaryAlgebra.a E S + (i.val : ℤ))) := by
  exact ordinary_dimension (SelectingRectification.bimodule E S)
    (SelectingOrdinaryAlgebra.a E S) (SelectingOrdinaryAlgebra.length E S)

/-- Every degree outside the actual selected interval has zero vector-space dimension. -/
theorem selecting_term_dimension_zero (n : ℤ)
    (hn : n < SelectingOrdinaryAlgebra.a E S ∨ SelectingOrdinaryAlgebra.b E S < n) :
    Module.finrank k ((underlyingComplex (k := k)
      (SelectingRectification.bimodule E S)).X n) = 0 := by
  letI : Subsingleton ((underlyingComplex (k := k)
      (SelectingRectification.bimodule E S)).X n) := by
    change Subsingleton ((SelectingRectification.bimodule E S).X n)
    exact ModuleCat.subsingleton_of_isZero (SelectingOrdinaryAlgebra.support E S n hn)
  exact Module.finrank_zero_of_subsingleton

/-- The manuscript's sum over all degrees is finite: all nonzero dimensions lie in [a,b]. -/
theorem selecting_dimension_support (n : ℤ)
    (hn : Module.finrank k ((underlyingComplex (k := k)
      (SelectingRectification.bimodule E S)).X n) ≠ 0) :
    n ∈ Finset.Icc (SelectingOrdinaryAlgebra.a E S) (SelectingOrdinaryAlgebra.b E S) := by
  by_contra h
  have hout : n < SelectingOrdinaryAlgebra.a E S ∨ SelectingOrdinaryAlgebra.b E S < n := by
    simp only [Finset.mem_Icc] at h
    omega
  exact hn (selecting_term_dimension_zero E S n hout)

/-- Actual A dimension, written as the finite sum over all degrees that can contribute. -/
theorem selecting_ordinary_dimension_integer_sum :
    Module.finrank k (SelectingOrdinaryAlgebra.A E S) =
      (2 * SelectingOrdinaryAlgebra.length E S + 3) * Module.finrank k (B E.relations) +
      ∑ n ∈ Finset.Icc (SelectingOrdinaryAlgebra.a E S) (SelectingOrdinaryAlgebra.b E S),
        Module.finrank k ((underlyingComplex (k := k) (SelectingRectification.bimodule E S)).X n) := by
  rw [selecting_ordinary_dimension]
  have h := interval_sum (fun n ↦ Module.finrank k
    ((underlyingComplex (k := k) (SelectingRectification.bimodule E S)).X n))
    (SelectingOrdinaryAlgebra.a E S) (SelectingOrdinaryAlgebra.length E S)
  rw [SelectingOrdinaryAlgebra.endpoints] at h
  exact congrArg (fun v : ℕ ↦
    (2 * SelectingOrdinaryAlgebra.length E S + 3) * Module.finrank k (B E.relations) + v) h

end Selecting
end
end Note198.ActualDimensionFormulas