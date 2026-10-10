import Note198.FiniteSelectionSource
import Note198.GroupAlgebraSelection
import Note198.SimpleSelection

namespace Note198.FiniteSelectionRestriction
noncomputable section
open MonoidAlgebra
open scoped BigOperators
universe u
variable (k : Type u) [Field k]

variable (p m : ℕ) [Fact p.Prime] [NeZero m]
def quotientMap : GroupAlgebraSelection.Ring k p →ₐ[k]
    MonoidAlgebra k (FiniteSelectionSource.F p m) :=
  MonoidAlgebra.mapDomainAlgHom k k (PrimeGroup.finiteQuotientMap p m)

theorem quotientMap_centralElement (i : Fin m) :
    quotientMap k p m (GroupAlgebraSelection.centralElement k p i.val) =
      single (PrimeGroup.quotientCentralEmbedding p m
        (Multiplicative.ofAdd (Pi.single i 1))) 1 := by
  simp [quotientMap, GroupAlgebraSelection.centralElement,
    PrimeGroup.quotientCentralEmbedding_basis]

def restrictedSource : ModuleCat.{u} (GroupAlgebraSelection.Ring k p) :=
  (ModuleCat.restrictScalars (quotientMap k p m).toRingHom).obj
    (ModuleCat.of (MonoidAlgebra k (FiniteSelectionSource.F p m))
      (FiniteSelectionSource.sourceIdeal k p m))

theorem restrictedSource_nontrivial (hp : (p : k) ≠ 0) :
    Nontrivial (restrictedSource k p m) :=
  FiniteSelectionSource.sourceIdeal_nontrivial k p m hp

/-- Restricting along the quotient algebra map preserves the actual k-vector space. -/
def sourceVectorEquiv : Selection.vectorObject (k := k) (restrictedSource k p m) ≃ₗ[k]
    FiniteSelectionSource.sourceIdeal k p m where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change (quotientMap k p m) (algebraMap k (GroupAlgebraSelection.Ring k p) c) •
      (show FiniteSelectionSource.sourceIdeal k p m from x) =
      c • (show FiniteSelectionSource.sourceIdeal k p m from x)
    rw [AlgHom.commutes]
    exact algebraMap_smul (MonoidAlgebra k (FiniteSelectionSource.F p m)) c
      (show FiniteSelectionSource.sourceIdeal k p m from x)

theorem restrictedSource_finiteDimensional :
    FiniteDimensional k (Selection.vectorObject (k := k) (restrictedSource k p m)) := by
  letI := FiniteSelectionSource.sourceIdeal_finiteDimensional k p m
  exact FiniteDimensional.of_injective (sourceVectorEquiv k p m).toLinearMap
    (sourceVectorEquiv k p m).injective

section NumericAverages
variable {B : Type*} [AddCommMonoid B]
theorem sumTwo (f : ZMod 2 → B) : ∑ a, f a = f 0 + f 1 := by
  rw [← Equiv.sum_comp (ZMod.finEquiv 2).toEquiv f]
  simp [Fin.sum_univ_succ, ZMod.finEquiv] <;> rfl

theorem sumThree (f : ZMod 3 → B) : ∑ a, f a = f 0 + f 1 + f 2 := by
  rw [← Equiv.sum_comp (ZMod.finEquiv 3).toEquiv f]
  simp [Fin.sum_univ_succ, ZMod.finEquiv, add_assoc] <;> rfl
end NumericAverages

theorem selectorTwo (i : Fin m) : FiniteSelectionSource.selector k 2 m i =
    (2 : k)⁻¹ • (1 + single (PrimeGroup.quotientCentralEmbedding 2 m
      (Multiplicative.ofAdd (Pi.single i 1))) 1) := by
  unfold FiniteSelectionSource.selector
  rw [sumTwo]
  simp [← MonoidAlgebra.one_def]

theorem selectorThree (i : Fin m) : FiniteSelectionSource.selector k 3 m i =
    (3 : k)⁻¹ • (1 + single (PrimeGroup.quotientCentralEmbedding 3 m
      (Multiplicative.ofAdd (Pi.single i 1))) 1 +
      single (PrimeGroup.quotientCentralEmbedding 3 m
        (Multiplicative.ofAdd (Pi.single i 1))) 1 ^ 2) := by
  have hpow : (Multiplicative.ofAdd (Pi.single i (1 : ZMod 3) : Fin m → ZMod 3)) ^ 2 =
      Multiplicative.ofAdd (Pi.single i (2 : ZMod 3) : Fin m → ZMod 3) := by
    change 2 • (Pi.single i (1 : ZMod 3) : Fin m → ZMod 3) = Pi.single i (2 : ZMod 3)
    ext j
    by_cases h : i = j
    · subst j
      simp [Pi.single_apply, two_nsmul]
    · simp [Pi.single_apply, h]
  have hsingle : (single (PrimeGroup.quotientCentralEmbedding 3 m
      (Multiplicative.ofAdd (Pi.single i (2 : ZMod 3)))) 1 :
      MonoidAlgebra k (FiniteSelectionSource.F 3 m)) =
      single (PrimeGroup.quotientCentralEmbedding 3 m
        (Multiplicative.ofAdd (Pi.single i (1 : ZMod 3)))) 1 ^ 2 := by
    rw [single_pow, ← map_pow, hpow]
    simp
  unfold FiniteSelectionSource.selector
  rw [sumThree]
  simp only [Pi.single_zero, ofAdd_zero, map_one, ← MonoidAlgebra.one_def, hsingle, Nat.cast_ofNat]

theorem quotientMap_idempotentTwo (i : Fin m) :
    quotientMap k 2 m (GroupAlgebraSelection.idempotentTwo k i.val) =
      FiniteSelectionSource.selector k 2 m i := by
  rw [selectorTwo]
  simp [GroupAlgebraSelection.idempotentTwo, quotientMap_centralElement]

theorem quotientMap_idempotentThree (i : Fin m) :
    quotientMap k 3 m (GroupAlgebraSelection.idempotentThree k i.val) =
      FiniteSelectionSource.selector k 3 m i := by
  rw [selectorThree]
  simp [GroupAlgebraSelection.idempotentThree, quotientMap_centralElement]

theorem eAtTwo (hp : (2 : k) ≠ 0) (q : ℕ) :
    Selection.eAt (GroupAlgebraSelection.dataTwo k hp) q =
      GroupAlgebraSelection.idempotentTwo k q := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [Selection.eAt, ih]
      change GroupAlgebraSelection.automorphism k 2 1
        (GroupAlgebraSelection.idempotentTwo k q) = _
      rw [GroupAlgebraSelection.automorphism_idempotentTwo]
      congr 1 <;> omega

theorem eAtThree (hp : (3 : k) ≠ 0) (q : ℕ) :
    Selection.eAt (GroupAlgebraSelection.dataThree k hp) q =
      GroupAlgebraSelection.idempotentThree k q := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [Selection.eAt, ih]
      change GroupAlgebraSelection.automorphism k 3 1
        (GroupAlgebraSelection.idempotentThree k q) = _
      rw [GroupAlgebraSelection.automorphism_idempotentThree]
      congr 1 <;> omega

theorem restrictedSource_identityTwo (hp : (2 : k) ≠ 0) (q : ℕ) (hq : q < m - 1) :
    Selection.IdentityAt (GroupAlgebraSelection.dataTwo k hp) (restrictedSource k 2 m) q := by
  intro x
  apply Subtype.ext
  change quotientMap k 2 m (Selection.eAt (GroupAlgebraSelection.dataTwo k hp) q) * x.val = x.val
  let i : Fin m := ⟨q, by omega⟩
  rw [eAtTwo]
  change quotientMap k 2 m (GroupAlgebraSelection.idempotentTwo k i.val) * x.val = x.val
  rw [quotientMap_idempotentTwo]
  apply x.property.1
  intro h
  have hv := congrArg Fin.val h
  change q = m - 1 at hv
  omega

theorem restrictedSource_zeroTwo (hp : (2 : k) ≠ 0) :
    Selection.ZeroAt (GroupAlgebraSelection.dataTwo k hp) (restrictedSource k 2 m) (m - 1) := by
  intro x
  apply Subtype.ext
  change quotientMap k 2 m (Selection.eAt (GroupAlgebraSelection.dataTwo k hp) (m - 1)) * x.val = 0
  rw [eAtTwo]
  change quotientMap k 2 m (GroupAlgebraSelection.idempotentTwo k
    (FiniteSelectionSource.lastIndex m).val) * x.val = 0
  rw [quotientMap_idempotentTwo]
  exact x.property.2

theorem restrictedSource_identityThree (hp : (3 : k) ≠ 0) (q : ℕ) (hq : q < m - 1) :
    Selection.IdentityAt (GroupAlgebraSelection.dataThree k hp) (restrictedSource k 3 m) q := by
  intro x
  apply Subtype.ext
  change quotientMap k 3 m (Selection.eAt (GroupAlgebraSelection.dataThree k hp) q) * x.val = x.val
  let i : Fin m := ⟨q, by omega⟩
  rw [eAtThree]
  change quotientMap k 3 m (GroupAlgebraSelection.idempotentThree k i.val) * x.val = x.val
  rw [quotientMap_idempotentThree]
  apply x.property.1
  intro h
  have hv := congrArg Fin.val h
  change q = m - 1 at hv
  omega

theorem restrictedSource_zeroThree (hp : (3 : k) ≠ 0) :
    Selection.ZeroAt (GroupAlgebraSelection.dataThree k hp) (restrictedSource k 3 m) (m - 1) := by
  intro x
  apply Subtype.ext
  change quotientMap k 3 m (Selection.eAt (GroupAlgebraSelection.dataThree k hp) (m - 1)) * x.val = 0
  rw [eAtThree]
  change quotientMap k 3 m (GroupAlgebraSelection.idempotentThree k
    (FiniteSelectionSource.lastIndex m).val) * x.val = 0
  rw [quotientMap_idempotentThree]
  exact x.property.2

/-- Actual finite-dimensional simple quotients with precisely m selection steps,
for the p=2 branch. The source, its nonzero vector and selector actions are constructed. -/
theorem exists_simple_two (hp : (2 : k) ≠ 0) :
    ∃ N : Submodule (GroupAlgebraSelection.Ring k 2) (restrictedSource k 2 m),
      IsSimpleModule (GroupAlgebraSelection.Ring k 2) (restrictedSource k 2 m ⧸ N) ∧
      FiniteDimensional k (Selection.vectorObject (k := k)
        (ModuleCat.of (GroupAlgebraSelection.Ring k 2) (restrictedSource k 2 m ⧸ N))) ∧
      (∀ n < m, Nontrivial (Selection.iterate (GroupAlgebraSelection.dataTwo k hp)
        (ModuleCat.of (GroupAlgebraSelection.Ring k 2) (restrictedSource k 2 m ⧸ N)) n)) ∧
      Subsingleton (Selection.iterate (GroupAlgebraSelection.dataTwo k hp)
        (ModuleCat.of (GroupAlgebraSelection.Ring k 2) (restrictedSource k 2 m ⧸ N)) m) := by
  letI := restrictedSource_nontrivial k 2 m hp
  letI := restrictedSource_finiteDimensional k 2 m
  exact Selection.exists_simple_with_extinction (GroupAlgebraSelection.dataTwo k hp)
    (restrictedSource k 2 m) m (Nat.pos_of_ne_zero (NeZero.ne m))
    (restrictedSource_identityTwo k m hp) (restrictedSource_zeroTwo k m hp)

/-- The p=3 branch supplies the construction in characteristic two. -/
theorem exists_simple_three (hp : (3 : k) ≠ 0) :
    ∃ N : Submodule (GroupAlgebraSelection.Ring k 3) (restrictedSource k 3 m),
      IsSimpleModule (GroupAlgebraSelection.Ring k 3) (restrictedSource k 3 m ⧸ N) ∧
      FiniteDimensional k (Selection.vectorObject (k := k)
        (ModuleCat.of (GroupAlgebraSelection.Ring k 3) (restrictedSource k 3 m ⧸ N))) ∧
      (∀ n < m, Nontrivial (Selection.iterate (GroupAlgebraSelection.dataThree k hp)
        (ModuleCat.of (GroupAlgebraSelection.Ring k 3) (restrictedSource k 3 m ⧸ N)) n)) ∧
      Subsingleton (Selection.iterate (GroupAlgebraSelection.dataThree k hp)
        (ModuleCat.of (GroupAlgebraSelection.Ring k 3) (restrictedSource k 3 m ⧸ N)) m) := by
  letI := restrictedSource_nontrivial k 3 m hp
  letI := restrictedSource_finiteDimensional k 3 m
  exact Selection.exists_simple_with_extinction (GroupAlgebraSelection.dataThree k hp)
    (restrictedSource k 3 m) m (Nat.pos_of_ne_zero (NeZero.ne m))
    (restrictedSource_identityThree k m hp) (restrictedSource_zeroThree k m hp)

end
end Note198.FiniteSelectionRestriction
