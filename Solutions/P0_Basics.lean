import Mathlib.Tactic

/-! # Solutions — Practice 0: First steps in Lean -/

namespace Solutions.Basics

def greeting : String := "Hello, Lean!"

def double (n : Nat) : Nat := 2 * n

theorem double_two : double 2 = 4 := by rfl

theorem add_zero' (n : Nat) : n + 0 = n := by simp

theorem and_swap (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  constructor
  · exact h.2
  · exact h.1

-- Exercise 2
def triple (n : Nat) : Nat := 3 * n

-- Exercise 3
theorem triple_three : triple 3 = 9 := by
  rfl

-- Exercise 4
theorem mul_one' (n : Nat) : n * 1 = n := by
  simp

-- Exercise 5
theorem and_self_intro (p : Prop) (hp : p) : p ∧ p := by
  constructor
  · exact hp
  · exact hp

-- Exercise 6
theorem and_swap_twice (p q : Prop) (h : p ∧ q) : p ∧ q := by
  exact and_swap q p (and_swap p q h)

end Solutions.Basics
