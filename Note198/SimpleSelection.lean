import Note198.Selection
import Note198.SimpleQuotient

namespace Note198.Selection
noncomputable section
open CategoryTheory
universe u

/-- The quotient chosen in Proposition 2.1 is genuinely simple. Its
prescribed central actions survive quotienting, so the same exact extinction
time holds. This theorem still requires construction of the source module. -/
theorem exists_simple_with_extinction
    {k R : Type u} [Field k] [Ring R] [Algebra k R]
    (S : Data k R) (M : ModuleCat.{u} R)
    [Nontrivial M] [FiniteDimensional k (vectorObject (k := k) M)]
    (m : ℕ) (hm : 0 < m)
    (hid : ∀ q < m - 1, IdentityAt S M q)
    (hzero : ZeroAt S M (m - 1)) :
    ∃ N : Submodule R M,
      IsSimpleModule R (M ⧸ N) ∧
      FiniteDimensional k (vectorObject (k := k) (ModuleCat.of R (M ⧸ N))) ∧
      (∀ n < m, Nontrivial (iterate S (ModuleCat.of R (M ⧸ N)) n)) ∧
      Subsingleton (iterate S (ModuleCat.of R (M ⧸ N)) m) := by
  letI : Module k M := (vectorObject (k := k) M).isModule
  letI : IsScalarTower k R M := ⟨fun c r x => by
    rw [Algebra.smul_def]
    change (algebraMap k R c * r) • x = algebraMap k R c • (r • x)
    exact mul_smul _ _ _⟩
  letI : FiniteDimensional k M := (inferInstance : FiniteDimensional k (vectorObject (k := k) M))
  obtain ⟨N, hs, hf⟩ := Note198.exists_finite_simple_quotient k R M
  letI := hs
  letI := hf
  letI : Nontrivial (ModuleCat.of R (M ⧸ N)) := IsSimpleModule.nontrivial R (M ⧸ N)
  have hidentity : ∀ q < m - 1,
      IdentityAt S (ModuleCat.of R (M ⧸ N)) q := by
    intro q hq
    exact Note198.quotient_identity_action N (eAt S q) (hid q hq)
  have hzero' : ZeroAt S (ModuleCat.of R (M ⧸ N)) (m - 1) :=
    Note198.quotient_zero_action N (eAt S (m - 1)) hzero
  have hext := extinction_criterion S (ModuleCat.of R (M ⧸ N)) m hm hidentity hzero'
  refine ⟨N, hs, ?_, hext.1, hext.2⟩
  change FiniteDimensional k (M ⧸ N)
  exact hf

end
end Note198.Selection
