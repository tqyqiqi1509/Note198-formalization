import Note198.SelectingFamilyCountBounded
import Note198.InflationScalars

namespace Note198.SelectingFamilyInflatedModule
noncomputable section
open CategoryTheory OAI OAI.LittleFinitistic
open scoped ModuleCat.Algebra
attribute [local instance] HasDerivedCategory.standard HasExt.standard
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)
variable (F : SelectingBrickFamily.SourceFamily k R S)
open SelectingOrdinaryAlgebra

/-- The exact A-module used by actual derived base change and finite bar.
Its action is projection A→D followed by the actual first-block action. -/
abbrev module (m : ℕ+) : ModuleCat.{u} (A E S) :=
  @ModuleCat.of (A E S) inferInstance (SelectingFamilyFiniteBar.firstModule E S F m)
    inferInstance (DerivedBar.ParityBridge.inflatedModule (D E S) (X E S)
      (SelectingFamilyFiniteBar.firstModule E S F m))

/-- Both actions evaluate the same composited actual first projection.
The underlying map and its inverse are the identity on the three copies. -/
def brickEquiv (m : ℕ+) : module E S F m ≃ₗ[A E S] SelectingBrickFamily.module E S F m where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def brickScalarEquiv (m : ℕ+) : module E S F m ≃ₗ[k] SelectingBrickFamily.module E S F m where
  toFun := brickEquiv E S F m
  invFun := (brickEquiv E S F m).symm
  left_inv := (brickEquiv E S F m).left_inv
  right_inv := (brickEquiv E S F m).right_inv
  map_add' := (brickEquiv E S F m).map_add
  map_smul' c x := by
    change brickEquiv E S F m (algebraMap k (A E S) c • x) =
      c • brickEquiv E S F m x
    exact ((brickEquiv E S F m).map_smul (algebraMap k (A E S) c) x).trans
      (IsScalarTower.algebraMap_smul (A E S) c (brickEquiv E S F m x))

theorem module_finite (m : ℕ+) : FiniteDimensional k (module E S F m) := by
  letI := SelectingBrickFamily.finite E S F m
  exact Module.Finite.of_surjective (brickScalarEquiv E S F m).symm.toLinearMap
    (brickScalarEquiv E S F m).symm.surjective

theorem module_nontrivial (m : ℕ+) : Nontrivial (module E S F m) := by
  letI : Nontrivial (F.V m) := by
    have h := F.alive m 0 m.pos
    change Nontrivial (F.V m) at h
    exact h
  letI : Nontrivial (SelectingBrickFamily.module E S F m) :=
    inferInstanceAs (Nontrivial (F.V m × F.V m × F.V m))
  let e := brickEquiv E S F m
  obtain ⟨x,y,hxy⟩ := exists_pair_ne (SelectingBrickFamily.module E S F m)
  exact ⟨⟨e.symm x,e.symm y,fun h => hxy (e.symm.injective h)⟩⟩

theorem brick_dimension_eq (m : ℕ+) :
    projectiveDimension (module E S F m) =
      projectiveDimension (ModuleCat.of (A E S) (SelectingBrickFamily.module E S F m)) :=
  ModuleCat.projectiveDimension_eq_of_linearEquiv (brickEquiv E S F m)

theorem brick_isomorphism (m : ℕ+) : Nonempty
    (module E S F m ≃ₗ[A E S] SelectingBrickFamily.module E S F m) :=
  ⟨brickEquiv E S F m⟩
end
end Note198.SelectingFamilyInflatedModule
