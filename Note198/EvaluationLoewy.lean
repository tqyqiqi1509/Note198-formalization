import Note198.RadicalBase
import Note198.DirectedResidue
import OAI.Algebra.Finitistic.Localization.EvaluationModule

namespace Note198
noncomputable section
open OAI.LittleFinitistic OAI.LittleFinitistic.QuadraticEncoding
universe u v
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- The actual radical consists of the elements with zero diagonal. -/
theorem encoding_radical_eq_diagonal_kernel :
    Ring.jacobson (B P) = RingHom.ker (three_vertex_diagonal (composition P)) := by
  apply le_antisymm
  · intro a ha
    obtain ⟨h0,h1,h2⟩ := three_vertex_radical_diagonal_zero (composition P) a ha
    change (a.1,a.2.1,a.2.2.1) = (0,0,0)
    simp [h0,h1,h2]
  · apply nilpotent_ideal_le_jacobson _ 3
    apply ideal_power_zero_of_words _ 3
    intro ds hlen hall
    rcases ds with _ | ⟨a,ds⟩ <;> simp only [List.length_nil,List.length_cons] at hlen
    · omega
    rcases ds with _ | ⟨b,ds⟩ <;> simp only [List.length_nil,List.length_cons] at hlen
    · omega
    rcases ds with _ | ⟨c,ds⟩ <;> simp only [List.length_nil,List.length_cons] at hlen
    · omega
    have ha := hall a (by simp)
    have hb := hall b (by simp)
    have hc := hall c (by simp)
    have hz (x : B P) (hx : x ∈ RingHom.ker (three_vertex_diagonal (composition P))) :
        x.1 = 0 ∧ x.2.1 = 0 ∧ x.2.2.1 = 0 :=
      ⟨congrArg Prod.fst hx, congrArg (fun z : k × k × k => z.2.1) hx,
        congrArg (fun z : k × k × k => z.2.2) hx⟩
    obtain ⟨ha0,ha1,ha2⟩ := hz a ha
    obtain ⟨hb0,hb1,hb2⟩ := hz b hb
    obtain ⟨hc0,hc1,hc2⟩ := hz c hc
    have habc : a*b*c = 0 := by
      apply ThreeVertexAlgebra.ext
      all_goals simp [ThreeVertexAlgebra.mul_eq,ThreeVertexAlgebra.mul,
        ha0,ha1,ha2,hb0,hb1,hb2,hc0,hc1,hc2]
    simp only [List.prod_cons]
    calc
      a * (b * (c * ds.prod)) = (a*b*c) * ds.prod := by simp only [mul_assoc]
      _ = 0 := by rw [habc,zero_mul]

theorem encoding_arrow01_mem_radical (a : Fin (d+1)) :
    arrow01 P a ∈ Ring.jacobson (B P) := by
  rw [encoding_radical_eq_diagonal_kernel]
  rfl

theorem encoding_arrow12_mem_radical (a : Fin (d+1)) :
    arrow12 P a ∈ Ring.jacobson (B P) := by
  rw [encoding_radical_eq_diagonal_kernel]
  rfl

variable {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

/-- Every element annihilating the evaluation module has zero diagonal,
because all three vertex copies contain the same nonzero vector space.
Thus the annihilator lies in the actual radical. -/
theorem evaluation_annihilating_element_mem_radical [Nontrivial Y] (a : B P)
    (ha : ∀ y : X.Evaluation, a • y = 0) : a ∈ Ring.jacobson (B P) := by
  obtain ⟨v,hv⟩ := exists_ne (0 : Y)
  have h0 : a.1 • v = 0 := congrArg (fun z : X.Evaluation => z.1) (ha (v,0,0))
  have h1 := congrArg (fun z : X.Evaluation => z.2.1) (ha (0,v,0))
  change X.arrowAction a.2.2.2.1 0 + a.2.1 • v = 0 at h1
  simp only [map_zero,zero_add] at h1
  have h2 := congrArg (fun z : X.Evaluation => z.2.2) (ha (0,0,v))
  change X.pathAction a.2.2.2.2.2 0 + X.arrowAction a.2.2.2.2.1 0 + a.2.2.1 • v = 0 at h2
  simp only [map_zero,zero_add] at h2
  have hd0 : a.1 = 0 := smul_left_injective k hv (h0.trans (zero_smul k v).symm)
  have hd1 : a.2.1 = 0 := smul_left_injective k hv (h1.trans (zero_smul k v).symm)
  have hd2 : a.2.2.1 = 0 := smul_left_injective k hv (h2.trans (zero_smul k v).symm)
  rw [encoding_radical_eq_diagonal_kernel]
  change (a.1,a.2.1,a.2.2.1) = (0,0,0)
  simp only [hd0,hd1,hd2]

/-- The radical cube annihilates the actual evaluation module. -/
theorem evaluation_radical_cube_annihilates (a : B P)
    (ha : a ∈ Ring.jacobson (B P)^3) (y : X.Evaluation) : a • y = 0 := by
  rw [three_vertex_radical_pow_three_zero (composition P)] at ha
  have hz : a = 0 := ha
  rw [hz,zero_smul]

/-- For a nonzero input module, the radical square acts nontrivially: the
two distinguished identity arrows carry vertex zero to vertex two. -/
theorem evaluation_radical_square_nonzero [Nontrivial Y] :
    ∃ a ∈ Ring.jacobson (B P)^2, ∃ y : X.Evaluation, a • y ≠ 0 := by
  obtain ⟨y,hy⟩ := exists_ne (0 : Y)
  refine ⟨arrow12 P 0 * arrow01 P 0, ?_, (y,0,0), ?_⟩
  · rw [Submodule.pow_succ,Submodule.pow_one]
    exact Ideal.mul_mem_mul
      (encoding_arrow12_mem_radical P 0) (encoding_arrow01_mem_radical P 0)
  · have h01 : arrow01 P 0 • (show X.Evaluation from (y,0,0)) =
        (show X.Evaluation from (0,y,0)) := X.s_smul _
    have h12 : arrow12 P 0 • (show X.Evaluation from (0,y,0)) =
        (show X.Evaluation from (0,0,y)) := X.s'_smul _
    have hact : (arrow12 P 0 * arrow01 P 0) • (show X.Evaluation from (y,0,0)) =
        (show X.Evaluation from (0,0,y)) :=
      (mul_smul (arrow12 P 0) (arrow01 P 0) (show X.Evaluation from (y,0,0))).trans
        ((congrArg (fun z : X.Evaluation => arrow12 P 0 • z) h01).trans h12)
    intro h
    exact hy (congrArg (fun z : X.Evaluation => z.2.2) (hact.symm.trans h))

/-- Loewy length exactly three, stated by the actual ideal actions without
introducing a certificate field or assuming the lower bound. -/
theorem evaluation_loewy_exact_three [Nontrivial Y] :
    (∀ a ∈ Ring.jacobson (B P)^3, ∀ y : X.Evaluation, a • y = 0) ∧
    (∃ a ∈ Ring.jacobson (B P)^2, ∃ y : X.Evaluation, a • y ≠ 0) :=
  ⟨evaluation_radical_cube_annihilates P X, evaluation_radical_square_nonzero P X⟩

end
end Note198

