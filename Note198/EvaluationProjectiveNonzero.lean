import Note198.EvaluationProjectiveDetection
import Note198.EvaluationLoewy
import OAI.Algebra.Finitistic.Ordinary.OrdinaryProjectiveTensor

namespace Note198
noncomputable section
open OAI.LittleFinitistic OAI.LittleFinitistic.QuadraticEncoding
universe u

section RowFinite
variable {R I : Type u} [Ring R]

/-- A free-module endomorphism with ideal coefficients raises the ideal
power of every coordinate. Every sum is the finite support of its input;
the index type need not be finite. -/
theorem finsupp_end_raises_ideal_power (K : Ideal R)
    (f : (I →₀ R) →ₗ[R] (I →₀ R))
    (hf : ∀ a b, f (Finsupp.single a 1) b ∈ K)
    (n : ℕ) (w : I →₀ R) (hw : ∀ a, w a ∈ K^n) :
    ∀ b, f w b ∈ K^(n+1) := by
  classical
  intro b
  have hexp : w = ∑ a ∈ w.support, Finsupp.single a (w a) := by
    simpa only [Finsupp.sum] using (Finsupp.sum_single w).symm
  rw [hexp]
  simp only [map_sum, Finsupp.finset_sum_apply]
  change (∑ a ∈ w.support, f (Finsupp.single a (w a)) b) ∈ K^(n+1)
  apply Submodule.sum_mem
  intro a ha
  have hs : f (Finsupp.single a (w a)) = (w a) • f (Finsupp.single a 1) := by
    rw [← f.map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hs]
  change w a * f (Finsupp.single a 1) b ∈ K^(n+1)
  rw [Submodule.pow_succ]
  exact Ideal.mul_mem_mul (hw a) (hf a b)

theorem finsupp_end_radical_cube_zero (K : Ideal R) (hK : K^3 = ⊥)
    (f : (I →₀ R) →ₗ[R] (I →₀ R))
    (hf : ∀ a b, f (Finsupp.single a 1) b ∈ K) :
    ∀ w, f (f (f w)) = 0 := by
  intro w
  have h0 : ∀ a, w a ∈ K^0 := by
    intro a
    rw [Submodule.pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  have h1 := finsupp_end_raises_ideal_power K f hf 0 w h0
  have h2 := finsupp_end_raises_ideal_power K f hf 1 (f w) h1
  have h3 := finsupp_end_raises_ideal_power K f hf 2 (f (f w)) h2
  apply Finsupp.ext
  intro b
  have hb := h3 b
  rw [hK] at hb
  exact hb
end RowFinite

variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

def encoding_op_diagonal_kernel : Ideal (B P)ᵐᵒᵖ :=
  RingHom.ker (three_vertex_diagonal (composition P)).op

theorem encoding_op_kernel_radical (c : (B P)ᵐᵒᵖ) :
    c ∈ encoding_op_diagonal_kernel P ↔ c.unop ∈ Ring.jacobson (B P) := by
  rw [encoding_radical_eq_diagonal_kernel]
  change (three_vertex_diagonal (composition P)).op c = 0 ↔
    three_vertex_diagonal (composition P) c.unop = 0
  constructor
  · intro h
    exact congrArg MulOpposite.unop h
  · intro h
    exact congrArg MulOpposite.op h

theorem encoding_op_kernel_cube_zero : (encoding_op_diagonal_kernel P)^3 = ⊥ := by
  apply ideal_power_zero_of_words _ 3
  intro ds hlen hall
  rcases ds with _ | ⟨a,ds⟩ <;> simp only [List.length_nil,List.length_cons] at hlen
  · omega
  rcases ds with _ | ⟨b,ds⟩ <;> simp only [List.length_nil,List.length_cons] at hlen
  · omega
  rcases ds with _ | ⟨c,ds⟩ <;> simp only [List.length_nil,List.length_cons] at hlen
  · omega
  have ha := (encoding_op_kernel_radical P a).mp (hall a (by simp))
  have hb := (encoding_op_kernel_radical P b).mp (hall b (by simp))
  have hc := (encoding_op_kernel_radical P c).mp (hall c (by simp))
  have hz := three_vertex_radical_triple_zero (composition P) c.unop b.unop a.unop hc hb ha
  apply MulOpposite.unop_injective
  simp only [List.prod_cons, MulOpposite.unop_mul, MulOpposite.unop_zero]
  calc
    ((ds.prod).unop * c.unop) * b.unop * a.unop =
        (ds.prod).unop * (c.unop * b.unop * a.unop) := by simp only [mul_assoc]
    _ = 0 := by rw [hz,mul_zero]

variable {Y : Type u} [AddCommGroup Y] [Module k Y] (X : Representation P Y)
variable (N : Type u) [AddCommGroup N] [Module k N] [Module (B P)ᵐᵒᵖ N]
  [IsScalarTower k (B P)ᵐᵒᵖ N]

/-- Every nonzero right projective module has nonzero tensor with the
actual three-vertex evaluation module. Projectivity supplies an actual
free retract, and the proof uses only its finite-support coordinates. -/
theorem projective_evaluation_tensor_nontrivial [Nontrivial Y] [Nontrivial N]
    [Module.Projective (B P)ᵐᵒᵖ N] :
    Nontrivial (BalancedTensor.Tensor k (B P) N X.Evaluation) := by
  classical
  by_contra hn
  letI : Subsingleton (BalancedTensor.Tensor k (B P) N X.Evaluation) :=
    not_nontrivial_iff_subsingleton.mp hn
  obtain ⟨i,hi⟩ := (Module.projective_def' (R := (B P)ᵐᵒᵖ) (P := N)).mp inferInstance
  let p := Finsupp.linearCombination (B P)ᵐᵒᵖ (id : N → N)
  let f := i.comp p
  have hcoeff : ∀ a b, f (Finsupp.single a 1) b ∈ encoding_op_diagonal_kernel P := by
    intro a b
    apply (encoding_op_kernel_radical P _).mpr
    apply evaluation_annihilating_element_mem_radical P X
    intro y
    exact retract_tensor_zero_projector_coefficient (k := k) N X.Evaluation i p a b y
  have hcube := finsupp_end_radical_cube_zero (encoding_op_diagonal_kernel P)
    (encoding_op_kernel_cube_zero P) f hcoeff
  have hid : ∀ w, f (f w) = f w := by
    intro w
    change i (p (i (p w))) = i (p w)
    have hh := congrArg (fun g : N →ₗ[(B P)ᵐᵒᵖ] N => g (p w)) hi
    exact congrArg i hh
  have hfzero : ∀ w, f w = 0 := by
    intro w
    have hh := hcube w
    rwa [hid,hid] at hh
  have hnzero : ∀ n : N, n = 0 := by
    intro n
    have hh := hfzero (i n)
    have hp := congrArg (fun g : N →ₗ[(B P)ᵐᵒᵖ] N => g n) hi
    change i (p (i n)) = 0 at hh
    change p (i n) = n at hp
    rw [hp] at hh
    have := congrArg p hh
    simpa only [hp,map_zero] using this
  obtain ⟨n,hn⟩ := exists_ne (0 : N)
  exact hn (hnzero n)

end
end Note198
