import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic

/-! # Solutions — Practice 3: Real numbers, sets and functions (using Mathlib) -/

namespace Solutions.RealsSets
open Function

theorem two_mul_le_sq_add_sq (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem abs_triangle (a b c : ℝ) : |a - c| ≤ |a - b| + |b - c| := by
  exact abs_sub_le a b c

theorem inter_subset_left' {α : Type} (A B : Set α) : A ∩ B ⊆ A := by
  intro x hx
  exact hx.1

theorem injective_comp' {α β γ : Type} (f : α → β) (g : β → γ)
    (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) := by
  intro x y h
  exact hf (hg h)

theorem exists_bigger (n : ℕ) : ∃ m, n < m := by
  exact ⟨n + 1, by omega⟩

theorem prime_seven : Nat.Prime 7 := by
  norm_num

end Solutions.RealsSets
