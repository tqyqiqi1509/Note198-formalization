import OAI.Algebra.Finitistic.Localization.OddDouble
import Lean.Elab.Tactic.Omega

/-! The manuscript's §7.3 construction for every odd shift. -/
namespace Note198.OddDoubleGeneral

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Preadditive CategoryTheory.Pretriangulated
open CategoryTheory.Idempotents OAI.LittleFinitistic.OddDouble

variable {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ]
variable [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

local instance : HasFiniteBiproducts (Karoubi C) := Karoubi.karoubi_hasFiniteBiproducts
local instance : HasBinaryBiproducts (Karoubi C) := hasBinaryBiproducts_of_finite_biproducts (Karoubi C)

/-- The cone uses the shift of the first double and the given s-th double. -/
theorem step_nested (U : Karoubi C) (s : ℤ)
    (hs : ∃ S : C, Nonempty ((toKaroubi C).obj S ≅ U ⊞ formalShift U s)) :
    ∃ Z : C, Nonempty ((toKaroubi C).obj Z ≅
      U ⊞ formalShift (formalShift (formalShift U 1) s) 1) := by
  classical
  obtain ⟨S, ⟨eA⟩⟩ := odd_double_one U
  obtain ⟨Y, ⟨eB⟩⟩ := hs
  let A := (toKaroubi C).obj S
  let B := (toKaroubi C).obj Y
  let F := formalShiftFunctor (C := C) s
  let H := formalShiftFunctor (C := C) 1
  let P := formalShift U 1
  let Q := F.obj U
  let iA : U ⟶ A := biprod.inl ≫ eA.inv
  let rA : A ⟶ U := eA.hom ≫ biprod.fst
  let iP : P ⟶ A := biprod.inr ≫ eA.inv
  let rP : A ⟶ P := eA.hom ≫ biprod.snd
  let iB : U ⟶ B := biprod.inl ≫ eB.inv
  let rB : B ⟶ U := eB.hom ≫ biprod.fst
  let iQ : Q ⟶ B := biprod.inr ≫ eB.inv
  let rQ : B ⟶ Q := eB.hom ≫ biprod.snd
  have hA : iA ≫ rA = 𝟙 U := by
    simp only [iA, rA, assoc, Iso.inv_hom_id_assoc, biprod.inl_fst]
  have hP : iP ≫ rP = 𝟙 P := by
    change (biprod.inr ≫ eA.inv) ≫ eA.hom ≫ biprod.snd = 𝟙 (formalShift U 1)
    rw [assoc, eA.inv_hom_id_assoc]
    exact biprod.inr_snd (X := U) (Y := formalShift U 1)
  have hB : iB ≫ rB = 𝟙 U := by
    simp only [iB, rB, assoc, Iso.inv_hom_id_assoc, biprod.inl_fst]
  have hQ : iQ ≫ rQ = 𝟙 Q := by
    change (biprod.inr ≫ eB.inv) ≫ eB.hom ≫ biprod.snd = 𝟙 (formalShift U s)
    rw [assoc, eB.inv_hom_id_assoc]
    exact biprod.inr_snd (X := U) (Y := formalShift U s)
  have htotalA : rA ≫ iA + rP ≫ iP = 𝟙 A := by
    change (eA.hom ≫ biprod.fst) ≫ (biprod.inl ≫ eA.inv) +
      (eA.hom ≫ biprod.snd) ≫ (biprod.inr ≫ eA.inv) = 𝟙 A
    calc
      _ = eA.hom ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ eA.inv := by
        simp only [comp_add, add_comp, assoc]
      _ = 𝟙 A := by rw [biprod.total, id_comp, eA.hom_inv_id]
  have htotalB : rB ≫ iB + rQ ≫ iQ = 𝟙 B := by
    change (eB.hom ≫ biprod.fst) ≫ (biprod.inl ≫ eB.inv) +
      (eB.hom ≫ biprod.snd) ≫ (biprod.inr ≫ eB.inv) = 𝟙 B
    calc
      _ = eB.hom ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ eB.inv := by
        simp only [comp_add, add_comp, assoc]
      _ = 𝟙 B := by rw [biprod.total, id_comp, eB.hom_inv_id]
  let δ : F.obj A ⟶ B := F.map rA ≫ iQ
  let γ : B ⟶ F.obj A := rQ ≫ F.map iA
  have hδγ : δ ≫ γ = F.map (rA ≫ iA) := by
    dsimp only [δ, γ]
    rw [assoc, ← assoc iQ rQ, hQ, id_comp, ← F.map_comp]
  have hγδ : γ ≫ δ = rQ ≫ iQ := by
    dsimp only [δ, γ]
    rw [assoc, ← assoc (F.map iA) (F.map rA), ← F.map_comp, hA, F.map_id, id_comp]
  have hreg : δ ≫ γ ≫ δ = δ := by
    rw [← assoc, hδγ]
    dsimp only [δ]
    rw [F.map_comp, assoc, ← assoc (F.map iA) (F.map rA), ← F.map_comp,
      hA, F.map_id, id_comp]
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle δ.f
  let T := Triangle.mk δ.f g h
  have hu : T.mor₁ ≫ γ.f ≫ T.mor₁ = T.mor₁ := congrArg Karoubi.Hom.f hreg
  have hq : formalCokernel T γ.f hu = retractProjector iB rB hB := by
    refine Karoubi.ext (P := formalCokernel T γ.f hu)
      (Q := retractProjector iB rB hB) rfl ?_
    change (𝟙 B.X - γ.f ≫ δ.f) ≫ 𝟙 B.X = 𝟙 B.X ≫ (rB.f ≫ iB.f)
    rw [comp_id, id_comp]
    have he : 𝟙 B - γ ≫ δ = rB ≫ iB := by rw [hγδ, ← htotalB]; abel
    have he' := congrArg (Karoubi.inclusionHom B B) he
    rw [map_sub] at he'
    exact he'
  have hP' : H.map (F.map iP) ≫ H.map (F.map rP) = 𝟙 (H.obj (F.obj P)) := by
    rw [← H.map_comp, ← F.map_comp, hP, F.map_id, H.map_id]
  have hp : formalKernel T γ.f hu =
      retractProjector (H.map (F.map iP)) (H.map (F.map rP)) hP' := by
    refine Karoubi.ext (P := formalKernel T γ.f hu)
      (Q := retractProjector (H.map (F.map iP)) (H.map (F.map rP)) hP') rfl ?_
    change (𝟙 (F.obj A).X - δ.f ≫ γ.f)⟦(1 : ℤ)⟧' ≫ 𝟙 _ =
      𝟙 _ ≫ ((H.map (F.map rP)).f ≫ (H.map (F.map iP)).f)
    rw [comp_id, id_comp]
    have he : 𝟙 (F.obj A) - δ ≫ γ = F.map (rP ≫ iP) := by
      rw [hδγ, ← F.map_id, ← F.map_sub]
      congr 1
      rw [← htotalA]
      abel
    have hFA : (F.obj A).p = 𝟙 (F.obj A).X := (shiftFunctor C s).map_id S
    have he' := congrArg (Karoubi.inclusionHom (F.obj A) (F.obj A)) he
    rw [map_sub] at he'
    change (F.obj A).p - δ.f ≫ γ.f = (F.map (rP ≫ iP)).f at he'
    rw [hFA] at he'
    rw [he']
    change (shiftFunctor C (1 : ℤ)).map ((shiftFunctor C s).map (rP.f ≫ iP.f)) = _
    simp only [Functor.map_comp]
    rfl
  obtain ⟨econe⟩ := regular_cone_iso T γ.f hu hT
  rw [hq, hp] at econe
  refine ⟨Z, ⟨econe ≪≫ biprod.mapIso (retractProjectorIso iB rB hB)
    (retractProjectorIso (H.map (F.map iP)) (H.map (F.map rP)) hP')⟩⟩

/-- Each constructed odd double yields the next odd double. -/
theorem step (U : Karoubi C) (s : ℤ)
    (hs : ∃ S : C, Nonempty ((toKaroubi C).obj S ≅ U ⊞ formalShift U s)) :
    ∃ Z : C, Nonempty ((toKaroubi C).obj Z ≅ U ⊞ formalShift U (s + 2)) := by
  obtain ⟨Z, ⟨e⟩⟩ := step_nested U s hs
  have ea : formalShift (formalShift (formalShift U 1) s) 1 ≅ formalShift U (s + 2) := by
    have e' := formalShiftAdd (formalShift U 1) s 1 ≪≫ formalShiftAdd U 1 (s + 1)
    have heq : 1 + (s + 1) = s + 2 := by omega
    simpa only [heq] using e'
  exact ⟨Z, ⟨e ≪≫ biprod.mapIso (Iso.refl U) ea⟩⟩

/-- All positive odd shifts, indexed by n, are represented by actual objects. -/
theorem all_odd (U : Karoubi C) (n : ℕ) :
    ∃ Z : C, Nonempty ((toKaroubi C).obj Z ≅ U ⊞ formalShift U (2 * (n : ℤ) + 1)) := by
  induction n with
  | zero => simpa using odd_double_one U
  | succ n ih =>
    have h := step U (2 * (n : ℤ) + 1) ih
    have heq : (2 * (n : ℤ) + 1) + 2 = 2 * ((n + 1 : ℕ) : ℤ) + 1 := by
      push_cast
      omega
    simpa only [heq] using h

/-- The quantifier used in §7.3: every odd integer s at least three. -/
theorem manuscript_all_odd (U : Karoubi C) (s : ℤ) (hs : 3 ≤ s) (hodd : Odd s) :
    ∃ Z : C, Nonempty ((toKaroubi C).obj Z ≅ U ⊞ formalShift U s) := by
  obtain ⟨n, hn⟩ := hodd
  have hn0 : 0 ≤ n := by omega
  have hncast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
  have h := all_odd U n.toNat
  have heq : 2 * (n.toNat : ℤ) + 1 = s := by omega
  simpa only [heq] using h

end Note198.OddDoubleGeneral