import Mathlib.Tactic

/-! # Solutions — Practice 2: Natural numbers and induction -/

namespace Solutions.Naturals

/-- `sumTo n = 0 + 1 + ⋯ + n` -/
def sumTo : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

theorem zero_add' (n : ℕ) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, ih]

theorem sumTo_formula (n : ℕ) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumTo, mul_add, ih]
    ring

theorem add_comm' (a b : ℕ) : a + b = b + a := by
  omega

theorem two_mul_even (n : ℕ) : Even (2 * n) := by
  exact ⟨n, by ring⟩

theorem le_sq (n : ℕ) : n ≤ n ^ 2 := by
  rcases n with _ | n
  · simp
  · nlinarith

end Solutions.Naturals
