import Mathlib.RingTheory.Ideal.Operations
import Lean.Elab.Tactic.Omega

namespace Note198
universe u

/-- A word-vanishing theorem implies vanishing of the actual ideal power,
including all sums used in ideal multiplication. No commutativity is used. -/
theorem ideal_power_zero_of_words {A : Type u} [Ring A] (I : Ideal A) (N : ℕ)
    (hwords : ∀ ds : List A, ds.length = N → (∀ d ∈ ds, d ∈ I) → ds.prod = 0) :
    I ^ N = ⊥ := by
  have aux : ∀ n : ℕ, ∀ m : ℕ, n + m = N → ∀ x ∈ I ^ n,
      ∀ ds : List A, ds.length = m → (∀ d ∈ ds, d ∈ I) → x * ds.prod = 0 := by
    intro n
    induction n with
    | zero =>
      intro m hm x hx ds hd hall
      have hz := hwords ds (by omega) hall
      rw [hz, mul_zero]
    | succ n ih =>
      intro m hm x hx ds hd hall
      rw [Submodule.pow_succ] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        rw [mul_assoc]
        change a * (b :: ds).prod = 0
        apply ih (m + 1) (by omega) a ha (b :: ds)
        · simp only [List.length_cons, hd]
        · intro d hmem
          rcases List.mem_cons.mp hmem with h | h
          · simpa [h] using hb
          · exact hall d h
      · intro a b ha hb
        simp only [add_mul, ha, hb, zero_add]
  apply le_bot_iff.mp
  intro x hx
  change x = 0
  simpa using aux N 0 (by omega) x hx [] rfl (by simp)

end Note198
