import Mathlib.Tactic

/-! # Solutions — Practice 0: First steps with Lean -/

namespace Solutions.Basics

/- The definitions from the lesson, repeated so this file stands alone. -/

def double (n : ℕ) : ℕ := 2 * n

theorem double_two : double 2 = 4 := by rfl

/- Exercise 1: both sides compute to `4`, so `rfl` closes the goal. -/
theorem my_first_proof : 2 + 2 = 4 := by
  rfl

/- Exercise 2: the missing value is `3 * n`. -/
def triple (n : ℕ) : ℕ :=
  3 * n

/- Exercise 3: `triple 3` computes to `9`, so again `rfl`. -/
theorem triple_three : triple 3 = 9 := by
  rfl

/- Exercise 4: `n` is a variable, so nothing computes — `simp` rewrites
`n + 0` to `n` (twice) using the library fact `Nat.add_zero`. -/
theorem add_zero_twice (n : ℕ) : n + 0 + 0 = n := by
  simp

/- Exercise 5: assume `hp : p`, split the `∧` with `constructor`, and use
`hp` for both halves. One-liner alternative: `intro hp; exact ⟨hp, hp⟩`. -/
theorem and_self' (p : Prop) : p → p ∧ p := by
  intro hp
  constructor
  · exact hp
  · exact hp

/- Exercise 6: `rw [triple_three]` turns the goal into `9 + 1 = 10`,
which `rw` then finishes automatically with `rfl`. -/
theorem triple_three_plus_one : triple 3 + 1 = 10 := by
  rw [triple_three]

end Solutions.Basics
