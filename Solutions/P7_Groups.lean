import Mathlib.Tactic
import Mathlib.Algebra.Group.Basic

/-! # Set 7 · Groups

Prove facts about every group at once, from the axioms. -/

namespace Solutions.Groups
variable {G : Type} [Group G]

/-- Hint: multiply both sides on the left by `a⁻¹`: `congrArg (a⁻¹ * ·) h`, then `simpa`.
Goal:
G : Type
inst : Group G
a b c : G
h : a * b = a * c
⊢ b = c -/
theorem cancel_left (a b c : G) (h : a * b = a * c) : b = c := by
  have := congrArg (a⁻¹ * ·) h
  simpa using this

/-- Hint: plug something clever into `h`. What is `e * 1`?
Goal:
G : Type
inst : Group G
e : G
h : ∀ (x : G), e * x = x
⊢ e = 1 -/
theorem unique_identity (e : G) (h : ∀ x : G, e * x = x) : e = 1 := by
  simpa using h 1

/-- Hint: Mathlib calls this `mul_inv_rev`. Socks and shoes: take off in reverse order.
Goal:
G : Type
inst : Group G
a b : G
⊢ (a * b)⁻¹ = b⁻¹ * a⁻¹ -/
theorem inv_mul' (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  exact mul_inv_rev a b

/-- Hint: `inv_eq_of_mul_eq_one_right : a * b = 1 → a⁻¹ = b`.
Goal:
G : Type
inst : Group G
a : G
h : a * a = 1
⊢ a⁻¹ = a -/
theorem inv_eq_self (a : G) (h : a * a = 1) : a⁻¹ = a := by
  exact inv_eq_of_mul_eq_one_right h

/-- Hint: every element is its own inverse (previous exercise). Then `a * b = (a * b)⁻¹ = b⁻¹ * a⁻¹ = b * a`, as a `calc`.
Goal:
G : Type
inst : Group G
h : ∀ (x : G), x * x = 1
a b : G
⊢ a * b = b * a -/
theorem comm_of_sq_one (h : ∀ x : G, x * x = 1) (a b : G) : a * b = b * a := by
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h a)
  have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (h b)
  have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (h (a * b))
  calc a * b = (a * b)⁻¹ := hab.symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [ha, hb]

end Solutions.Groups
