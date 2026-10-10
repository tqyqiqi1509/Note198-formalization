import Lean.Elab.Tactic.Omega

/-! Arithmetic steps of the even/odd iterates and linear bounds in Section 6,
and the vertex count and radical exponent estimates in Section 7 of Note198.
The symbols a and c below stand only for already established projective
dimensions. These lemmas do not assert a derived tensor or pd formula.
-/
namespace Note198

/-- The largest even-iterate shift occurs at q = j. -/
theorem maximal_even_shift (b j q : Nat) (hq : q ≤ j) :
    j * b + 3 * q + 2 * j ≤ (b + 5) * j := by
  rw [Nat.add_mul, Nat.mul_comm j b]
  omega

theorem maximal_odd_shift (b j q : Nat) (hq : q ≤ j) :
    j * b + 3 * q + 2 * j + 1 ≤ (b + 5) * j + 1 := by
  rw [Nat.add_mul, Nat.mul_comm j b]
  omega

theorem top_even_shift (b j : Nat) :
    j * b + 3 * j + 2 * j = (b + 5) * j := by
  rw [Nat.add_mul, Nat.mul_comm j b]
  omega

theorem top_odd_shift (b j : Nat) :
    j * b + 3 * j + 2 * j + 1 = (b + 5) * j + 1 := by
  rw [Nat.add_mul, Nat.mul_comm j b]
  omega

/-- The upper-bound step once pd_B ≤ 2 and pd_E ≤ l + 2 are proved. -/
theorem final_term_upper_bounds (b l m j a c : Nat)
    (hj : j < m) (ha : a ≤ 2) (hc : c ≤ l + 2) :
    (b + 5) * j + a ≤ (b + 5) * (m - 1) + l + 3 ∧
    (b + 5) * j + 1 + c ≤ (b + 5) * (m - 1) + l + 3 := by
  have hle : j ≤ m - 1 := by omega
  have hmul := Nat.mul_le_mul_left (b + 5) hle
  constructor <;> omega

/-- A maximum containing the odd final term has the claimed lower bound. -/
theorem final_term_lower_bound (b m c d : Nat)
    (h : (b + 5) * (m - 1) + 1 + c ≤ d) :
    (b + 5) * (m - 1) + 1 ≤ d := by omega

/-- The number of primitive vertices of B × (B ⊗ C). -/
theorem vertex_count (l : Nat) : 3 + 3 * (l + 1) = 3 * l + 6 := by omega

/-- Every seven-letter radical word containing one O factor has too many
left E factors (at least 4) or too many right B factors (at least 3). -/
theorem radical_O_exponents (i j : Nat) (h : i + j = 6) :
    4 ≤ i ∨ 3 ≤ j := by omega

theorem radical_T_exponents (i j : Nat) (h : i + j = 6) :
    3 ≤ i ∨ 4 ≤ j := by omega

end Note198
