import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

namespace Note198
/-! Note198 Lemma 2.3. General p version of the pulled group construction.
The actual infinite presentation and shift automorphism are constructed.
Finite presentation and independent central elements remain separate obligations. -/

open scoped commutatorElement

namespace PrimeGroup

section GroupTransfer

variable {G : Type*} [Group G]

/-- The commutator transfer identity establishing independence of the
internal index in the paper's central involutions. -/
theorem commutator_transfer (x y v u w : G)
    (hu : x*y = u*y*x) (hw : y*v = w*v*y)
    (hxv : Commute x v) (hwu : Commute w u) (hwv : Commute w v) :
    ⁅x,w⁆ = ⁅u,v⁆ := by
  have hconj : y*x*y⁻¹ = u⁻¹*x := by
    apply (mul_left_cancel_iff (a := u)).mp
    calc
      u*(y*x*y⁻¹) = (u*y*x)*y⁻¹ := by group
      _ = (x*y)*y⁻¹ := by rw [← hu]
      _ = u*(u⁻¹*x) := by group
  have hmove : x*w*v*y = u*w*v*y*x := by
    calc
      x*w*v*y = x*(y*v) := by rw [hw]; group
      _ = (x*y)*v := by group
      _ = (u*y*x)*v := by rw [hu]
      _ = u*y*(v*x) := by simp only [mul_assoc, hxv.eq]
      _ = u*(y*v)*x := by group
      _ = u*w*v*y*x := by rw [hw]; group
  have hxw : x*w = u*w*v*u⁻¹*v⁻¹*x := by
    calc
      x*w = (x*w*v*y)*y⁻¹*v⁻¹ := by group
      _ = (u*w*v*y*x)*y⁻¹*v⁻¹ := by rw [hmove]
      _ = u*w*v*(y*x*y⁻¹)*v⁻¹ := by group
      _ = u*w*v*(u⁻¹*x)*v⁻¹ := by rw [hconj]
      _ = u*w*v*u⁻¹*(v⁻¹*x) := by simp only [mul_assoc]; rw [hxv.inv_right.eq]
      _ = u*w*v*u⁻¹*v⁻¹*x := by group
  have hwc : Commute w (v*u⁻¹*v⁻¹) := by
    simpa only [mul_assoc] using hwv.mul_right (hwu.inv_right.mul_right hwv.inv_right)
  calc
    ⁅x,w⁆ = x*w*x⁻¹*w⁻¹ := rfl
    _ = u*w*v*u⁻¹*v⁻¹*w⁻¹ := by rw [hxw]; group
    _ = u*(w*(v*u⁻¹*v⁻¹))*w⁻¹ := by group
    _ = u*((v*u⁻¹*v⁻¹)*w)*w⁻¹ := by rw [hwc.eq]
    _ = ⁅u,v⁆ := by simp only [commutatorElement_def]; group

/-- A central commutator of an element whose order divides p has order dividing p. -/
theorem central_commutator_power (x y : G) (p : ℕ) (hx : x ^ p = 1)
    (hc : Commute x ⁅x,y⁆) : ⁅x,y⁆ ^ p = 1 := by
  rw [hc.commutatorElement_pow_left p, hx, commutatorElement_one_left]

end GroupTransfer

/-- The relators p used for the off-diagonal generators in Section 2. The
presentation and its finite-presentation reduction are separate obligations. -/
structure SelectionGroupData (p : ℕ) (G : Type*) [Group G] where
  T : Fin 3 → G
  U : Fin 3 → ℤ → G
  V : Fin 3 → ℤ → G
  W : Fin 3 → Fin 3 → ℤ → G
  power_U : ∀ i a, U i a ^ p = 1
  commute_UU : ∀ i j a b, i ≠ j → Commute (U i a) (U j b)
  commute_VV : ∀ i j a b, i ≠ j → Commute (V i a) (V j b)
  commute_UV : ∀ i j a b, i ≠ j → Commute (U i a) (V j b)
  commute_WU : ∀ i j h a b, h ≠ i → Commute (W i j a) (U h b)
  commute_WV : ∀ i j h a b, h ≠ j → Commute (W i j a) (V h b)
  commutator_UW : ∀ i j a b, i ≠ j → ⁅U i a, W i j b⁆ = U j (a+b)
  commutator_WV : ∀ i j a b, i ≠ j → ⁅W i j a, V j b⁆ = V i (a+b)
  commute_TT : ∀ i j, Commute (T i) (T j)
  conj_TU : ∀ l i a, T l * U i a * (T l)⁻¹ = U i (a - if l=i then 1 else 0)
  conj_TV : ∀ l i a, T l * V i a * (T l)⁻¹ = V i (a + if l=i then 1 else 0)
  conj_TW : ∀ l i j a, T l * W i j a * (T l)⁻¹ =
    W i j (a + (if l=i then 1 else 0) - if l=j then 1 else 0)
  diagonal_W : ∀ i a, W i i a = 1

namespace SelectionGroupData

variable {p : ℕ} {G : Type*} [Group G] (D : SelectionGroupData p G)

theorem split_transfer (i j : Fin 3) (a b c d : ℤ)
    (hij : i ≠ j) (hsum : a+b = c+d) :
    ⁅D.U i a, D.V i b⁆ = ⁅D.U j c, D.V j d⁆ := by
  have hU : D.U i a * D.W i j (c-a) =
      D.U j c * D.W i j (c-a) * D.U i a := by
    have h := D.commutator_UW i j a (c-a) hij
    have hc : a + (c-a) = c := by omega
    rw [hc] at h
    rw [← h]
    simp [commutatorElement_def, mul_assoc]
  have hV : D.W i j (c-a) * D.V j d =
      D.V i b * D.V j d * D.W i j (c-a) := by
    have h := D.commutator_WV i j (c-a) d hij
    have hb : c-a+d = b := by omega
    rw [hb] at h
    rw [← h]
    simp [commutatorElement_def, mul_assoc]
  exact commutator_transfer (D.U i a) (D.W i j (c-a)) (D.V j d)
    (D.U j c) (D.V i b) hU hV (D.commute_UV i j a d hij)
    (D.commute_UV j i c b hij.symm).symm (D.commute_VV i j b d hij)

theorem splitting_independent (i j : Fin 3) (a b c d : ℤ)
    (hsum : a+b = c+d) : ⁅D.U i a,D.V i b⁆ = ⁅D.U j c,D.V j d⁆ := by
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide)
  calc
    ⁅D.U i a,D.V i b⁆ = ⁅D.U k 0,D.V k (a+b)⁆ :=
      D.split_transfer i k a b 0 (a+b) hki.symm (by omega)
    _ = ⁅D.U j c,D.V j d⁆ :=
      D.split_transfer k j 0 (a+b) c d hkj (by omega)

def centralZ (N : ℤ) : G := ⁅D.U 0 0,D.V 0 N⁆

theorem centralZ_eq (N : ℤ) (i : Fin 3) (a b : ℤ) (h : a+b=N) :
    D.centralZ N = ⁅D.U i a,D.V i b⁆ := by
  exact D.splitting_independent 0 i 0 N a b (by omega)

theorem centralZ_commute_U (N : ℤ) (h : Fin 3) (a : ℤ) :
    Commute (D.centralZ N) (D.U h a) := by
  obtain ⟨i, hih, _⟩ := Fin.exists_ne_and_ne_of_two_lt h h (by decide)
  rw [D.centralZ_eq N i 0 N (by omega), commutatorElement_def]
  have hU := D.commute_UU i h 0 a hih
  have hV := (D.commute_UV h i a N hih.symm).symm
  exact ((hU.mul_left hV).mul_left hU.inv_left).mul_left hV.inv_left

theorem centralZ_commute_V (N : ℤ) (h : Fin 3) (a : ℤ) :
    Commute (D.centralZ N) (D.V h a) := by
  obtain ⟨i, hih, _⟩ := Fin.exists_ne_and_ne_of_two_lt h h (by decide)
  rw [D.centralZ_eq N i 0 N (by omega), commutatorElement_def]
  have hU := D.commute_UV i h 0 a hih
  have hV := D.commute_VV i h N a hih
  exact ((hU.mul_left hV).mul_left hU.inv_left).mul_left hV.inv_left

theorem centralZ_commute_W (N : ℤ) (i j : Fin 3) (a : ℤ) :
    Commute (D.centralZ N) (D.W i j a) := by
  obtain ⟨h, hhi, hhj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide)
  rw [D.centralZ_eq N h 0 N (by omega), commutatorElement_def]
  have hU := (D.commute_WU i j h a 0 hhi).symm
  have hV := (D.commute_WV i j h a N hhj).symm
  exact ((hU.mul_left hV).mul_left hU.inv_left).mul_left hV.inv_left

theorem centralZ_power (N : ℤ) : D.centralZ N ^ p = 1 := by
  apply central_commutator_power (D.U 0 0) (D.V 0 N) p (D.power_U 0 0)
  exact (D.centralZ_commute_U N 0 0).symm

theorem centralZ_commute_T (N : ℤ) (l : Fin 3) : Commute (D.centralZ N) (D.T l) := by
  have hconj : D.T l * D.centralZ N * (D.T l)⁻¹ = D.centralZ N := by
    rw [centralZ, conjugate_commutatorElement, D.conj_TU, D.conj_TV]
    exact (D.centralZ_eq N 0 _ _ (by omega)).symm
  show D.centralZ N * D.T l = D.T l * D.centralZ N
  calc
    D.centralZ N * D.T l = (D.T l * D.centralZ N * (D.T l)⁻¹) * D.T l := by rw [hconj]
    _ = D.T l * D.centralZ N := by group

end SelectionGroupData

namespace Presentation

variable (p : ℕ)

inductive Generator where
  | T : Fin 3 → Generator
  | U : Fin 3 → ℤ → Generator
  | V : Fin 3 → ℤ → Generator
  | W : Fin 3 → Fin 3 → ℤ → Generator

abbrev generatorT (i : Fin 3) := FreeGroup.of (Generator.T i)
abbrev generatorU (i : Fin 3) (a : ℤ) := FreeGroup.of (Generator.U i a)
abbrev generatorV (i : Fin 3) (a : ℤ) := FreeGroup.of (Generator.V i a)
abbrev generatorW (i j : Fin 3) (a : ℤ) := FreeGroup.of (Generator.W i j a)

/-- Explicit equation patterns of the paper's infinite presentation.
Diagonal W generators are set to one, so the total-index notation introduces
no additional group generators compared with the manuscript. -/
inductive Equation (p : ℕ) : FreeGroup Generator → FreeGroup Generator → Prop where
  | powerU (i a) : Equation p (generatorU i a ^ p) 1
  | commuteUU (i j a b) (h : i ≠ j) : Equation p (generatorU i a * generatorU j b) (generatorU j b * generatorU i a)
  | commuteVV (i j a b) (h : i ≠ j) : Equation p (generatorV i a * generatorV j b) (generatorV j b * generatorV i a)
  | commuteUV (i j a b) (h : i ≠ j) : Equation p (generatorU i a * generatorV j b) (generatorV j b * generatorU i a)
  | commuteWU (i j h a b) (hhi : h ≠ i) : Equation p (generatorW i j a * generatorU h b) (generatorU h b * generatorW i j a)
  | commuteWV (i j h a b) (hhj : h ≠ j) : Equation p (generatorW i j a * generatorV h b) (generatorV h b * generatorW i j a)
  | commutatorUW (i j a b) (h : i ≠ j) : Equation p ⁅generatorU i a,generatorW i j b⁆ (generatorU j (a+b))
  | commutatorWV (i j a b) (h : i ≠ j) : Equation p ⁅generatorW i j a,generatorV j b⁆ (generatorV i (a+b))
  | commuteTT (i j) : Equation p (generatorT i * generatorT j) (generatorT j * generatorT i)
  | conjTU (l i a) : Equation p (generatorT l * generatorU i a * (generatorT l)⁻¹) (generatorU i (a-if l=i then 1 else 0))
  | conjTV (l i a) : Equation p (generatorT l * generatorV i a * (generatorT l)⁻¹) (generatorV i (a+if l=i then 1 else 0))
  | conjTW (l i j a) : Equation p (generatorT l * generatorW i j a * (generatorT l)⁻¹)
      (generatorW i j (a+(if l=i then 1 else 0)-if l=j then 1 else 0))
  | diagonalW (i a) : Equation p (generatorW i i a) 1

def relators : Set (FreeGroup Generator) := {r | ∃ a b, Equation p a b ∧ r=a*b⁻¹}
abbrev AuxiliaryGroup := PresentedGroup (relators p)

theorem presented_equation_holds {a b : FreeGroup Generator} (h : Equation p a b) :
    PresentedGroup.mk (relators p) a = PresentedGroup.mk (relators p) b :=
  PresentedGroup.mk_eq_mk_of_mul_inv_mem ⟨a,b,h,rfl⟩

def data : SelectionGroupData p (AuxiliaryGroup p) where
  T i := PresentedGroup.of (.T i)
  U i a := PresentedGroup.of (.U i a)
  V i a := PresentedGroup.of (.V i a)
  W i j a := PresentedGroup.of (.W i j a)
  power_U i a := by simpa [generatorU, PresentedGroup.of] using presented_equation_holds p (.powerU i a)
  commute_UU i j a b h := by
    simpa [generatorU, PresentedGroup.of, Commute, SemiconjBy] using presented_equation_holds p (.commuteUU i j a b h)
  commute_VV i j a b h := by
    simpa [generatorV, PresentedGroup.of, Commute, SemiconjBy] using presented_equation_holds p (.commuteVV i j a b h)
  commute_UV i j a b h := by
    simpa [generatorU,generatorV, PresentedGroup.of, Commute, SemiconjBy] using presented_equation_holds p (.commuteUV i j a b h)
  commute_WU i j h a b hhi := by
    simpa [generatorW,generatorU, PresentedGroup.of, Commute, SemiconjBy] using presented_equation_holds p (.commuteWU i j h a b hhi)
  commute_WV i j h a b hhj := by
    simpa [generatorW,generatorV, PresentedGroup.of, Commute, SemiconjBy] using presented_equation_holds p (.commuteWV i j h a b hhj)
  commutator_UW i j a b h := by
    simpa [generatorU,generatorW, PresentedGroup.of] using presented_equation_holds p (.commutatorUW i j a b h)
  commutator_WV i j a b h := by
    simpa [generatorW,generatorV, PresentedGroup.of] using presented_equation_holds p (.commutatorWV i j a b h)
  commute_TT i j := by
    simpa [generatorT, PresentedGroup.of, Commute, SemiconjBy] using presented_equation_holds p (.commuteTT i j)
  conj_TU l i a := by simpa [generatorT,generatorU,PresentedGroup.of] using presented_equation_holds p (.conjTU l i a)
  conj_TV l i a := by simpa [generatorT,generatorV,PresentedGroup.of] using presented_equation_holds p (.conjTV l i a)
  conj_TW l i j a := by simpa [generatorT,generatorW,PresentedGroup.of] using presented_equation_holds p (.conjTW l i j a)
  diagonal_W i a := by simpa [generatorW,PresentedGroup.of] using presented_equation_holds p (.diagonalW i a)

def z (N : ℤ) : AuxiliaryGroup p := (data p).centralZ N

theorem z_power (N : ℤ) : z p N ^ p = 1 := (data p).centralZ_power N

theorem z_central (N : ℤ) (g : AuxiliaryGroup p) : Commute (z p N) g := by
  have hg : g ∈ Subgroup.closure (Set.range (PresentedGroup.of : Generator → (AuxiliaryGroup p))) := by
    rw [PresentedGroup.closure_range_of]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      obtain ⟨s,rfl⟩ := hg
      cases s with
      | T i => exact (data p).centralZ_commute_T N i
      | U i a => exact (data p).centralZ_commute_U N i a
      | V i a => exact (data p).centralZ_commute_V N i a
      | W i j a => exact (data p).centralZ_commute_W N i j a
  | one => exact Commute.one_right _
  | mul a b ha hb ia ib => exact ia.mul_right ib
  | inv a ha ia => exact ia.inv_right

def evaluate {G : Type*} [Group G] (D : SelectionGroupData p G) : Generator → G
  | .T i => D.T i
  | .U i a => D.U i a
  | .V i a => D.V i a
  | .W i j a => D.W i j a

theorem evaluate_equation {G : Type*} [Group G] (D : SelectionGroupData p G)
    {a b : FreeGroup Generator} (h : Equation p a b) :
    FreeGroup.lift (evaluate p D) a = FreeGroup.lift (evaluate p D) b := by
  cases h with
  | powerU i a => simpa [generatorU,evaluate] using D.power_U i a
  | commuteUU i j a b h => simpa [generatorU,evaluate] using (D.commute_UU i j a b h).eq
  | commuteVV i j a b h => simpa [generatorV,evaluate] using (D.commute_VV i j a b h).eq
  | commuteUV i j a b h => simpa [generatorU,generatorV,evaluate] using (D.commute_UV i j a b h).eq
  | commuteWU i j h a b hh => simpa [generatorW,generatorU,evaluate] using (D.commute_WU i j h a b hh).eq
  | commuteWV i j h a b hh => simpa [generatorW,generatorV,evaluate] using (D.commute_WV i j h a b hh).eq
  | commutatorUW i j a b h => simpa [generatorU,generatorW,evaluate] using D.commutator_UW i j a b h
  | commutatorWV i j a b h => simpa [generatorW,generatorV,evaluate] using D.commutator_WV i j a b h
  | commuteTT i j => simpa [generatorT,evaluate] using (D.commute_TT i j).eq
  | conjTU l i a => simpa [generatorT,generatorU,evaluate] using D.conj_TU l i a
  | conjTV l i a => simpa [generatorT,generatorV,evaluate] using D.conj_TV l i a
  | conjTW l i j a => simpa [generatorT,generatorW,evaluate] using D.conj_TW l i j a
  | diagonalW i a => simpa [generatorW,evaluate] using D.diagonal_W i a

def ofData {G : Type*} [Group G] (D : SelectionGroupData p G) : (AuxiliaryGroup p) →* G :=
  PresentedGroup.toGroup (f := evaluate p D) (by
    intro r hr
    obtain ⟨a,b,h,rfl⟩ := hr
    rw [map_mul,map_inv,evaluate_equation p D h,mul_inv_cancel])

@[simp] theorem ofData_of {G : Type*} [Group G] (D : SelectionGroupData p G) (s : Generator) :
    ofData p D (PresentedGroup.of s) = evaluate p D s := PresentedGroup.toGroup.of _

def shiftData {G : Type*} [Group G] (D : SelectionGroupData p G) (k : ℤ) :
    SelectionGroupData p G where
  T := D.T
  U i a := D.U i (a+k)
  V := D.V
  W := D.W
  power_U i a := D.power_U i (a+k)
  commute_UU i j a b h := D.commute_UU i j (a+k) (b+k) h
  commute_VV := D.commute_VV
  commute_UV i j a b h := D.commute_UV i j (a+k) b h
  commute_WU i j h a b hh := D.commute_WU i j h a (b+k) hh
  commute_WV := D.commute_WV
  commutator_UW i j a b h := by
    simpa only [add_assoc,add_comm k b] using D.commutator_UW i j (a+k) b h
  commutator_WV := D.commutator_WV
  commute_TT := D.commute_TT
  conj_TU l i a := by
    simpa only [add_sub_assoc,sub_add_eq_add_sub] using D.conj_TU l i (a+k)
  conj_TV := D.conj_TV
  conj_TW := D.conj_TW
  diagonal_W := D.diagonal_W

def shiftHom (k : ℤ) : (AuxiliaryGroup p) →* AuxiliaryGroup p := ofData p (shiftData p (data p) k)

@[simp] theorem shiftHom_T (k : ℤ) (i : Fin 3) : shiftHom p k ((data p).T i) = (data p).T i := by
  simp [shiftHom,data,shiftData,evaluate]

@[simp] theorem shiftHom_U (k : ℤ) (i : Fin 3) (a : ℤ) :
    shiftHom p k ((data p).U i a) = (data p).U i (a+k) := by
  simp [shiftHom,data,shiftData,evaluate]

@[simp] theorem shiftHom_V (k : ℤ) (i : Fin 3) (a : ℤ) :
    shiftHom p k ((data p).V i a) = (data p).V i a := by
  simp [shiftHom,data,shiftData,evaluate]

@[simp] theorem shiftHom_W (k : ℤ) (i j : Fin 3) (a : ℤ) :
    shiftHom p k ((data p).W i j a) = (data p).W i j a := by
  simp [shiftHom,data,shiftData,evaluate]

theorem shiftHom_comp (k l : ℤ) : (shiftHom p k).comp (shiftHom p l) = shiftHom p (l+k) := by
  apply PresentedGroup.ext
  intro s
  cases s <;> simp [MonoidHom.comp_apply,shiftHom,shiftData,data,evaluate,add_assoc]

theorem shiftHom_zero : shiftHom p 0 = MonoidHom.id (AuxiliaryGroup p) := by
  apply PresentedGroup.ext
  intro s
  cases s <;> simp [shiftHom,shiftData,data,evaluate]

def shiftAut (k : ℤ) : AuxiliaryGroup p ≃* AuxiliaryGroup p where
  toFun := shiftHom p k
  invFun := shiftHom p (-k)
  left_inv a := by
    have h := DFunLike.congr_fun (shiftHom_comp p (-k) k) a
    simpa only [add_neg_cancel,shiftHom_zero,MonoidHom.id_apply,MonoidHom.comp_apply] using h
  right_inv a := by
    have h := DFunLike.congr_fun (shiftHom_comp p k (-k)) a
    simpa only [neg_add_cancel,shiftHom_zero,MonoidHom.id_apply,MonoidHom.comp_apply] using h
  map_mul' := (shiftHom p k).map_mul

theorem shiftAut_z (k N : ℤ) : shiftAut p k (z p N) = z p (N+k) := by
  change shiftHom p k ⁅(data p).U 0 0,(data p).V 0 N⁆ = (data p).centralZ (N+k)
  rw [map_commutatorElement,shiftHom_U,shiftHom_V,zero_add]
  exact ((data p).centralZ_eq (N+k) 0 k N (by omega)).symm

/-- The central-element and shift claims of Note198 Lemma 2.3 for the actual
presented group. This is an order-dividing-p assertion, not exact order p;
exact order is supplied only by the subsequent finite-quotient lemma. -/
theorem lemma_2_3 (N : ℤ) :
    (∀ (i : Fin 3) (a b : ℤ), a + b = N →
      z p N = ⁅(data p).U i a, (data p).V i b⁆) ∧
    (∀ g : AuxiliaryGroup p, Commute (z p N) g) ∧
    z p N ^ p = 1 ∧ shiftAut p 1 (z p N) = z p (N + 1) := by
  exact ⟨fun i a b h => (data p).centralZ_eq N i a b h,
    z_central p N, z_power p N, shiftAut_z p 1 N⟩

end Presentation

end PrimeGroup

end Note198
