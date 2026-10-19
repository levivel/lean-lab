import LeanLab.Placeholder
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic

/-! # Practice 3: Real numbers, sets and functions (using Mathlib)

Replace every `[...]` with a proof. Put your cursor inside a proof to see
the goal in the Lean Infoview panel.

Tactics to try: `nlinarith [sq_nonneg (a - b)]`, `exact?` (asks Mathlib to find a
lemma), `intro`, `exact ⟨_, _⟩`, `omega`, `norm_num`.

Grade yourself: `leanlab check Practice/P3_RealsSets.lean`
Stuck? `leanlab solution P3_RealsSets` -/

namespace Practice.RealsSets
open Function

theorem two_mul_le_sq_add_sq (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  [...]

theorem abs_triangle (a b c : ℝ) : |a - c| ≤ |a - b| + |b - c| := by
  [...]

theorem inter_subset_left' {α : Type} (A B : Set α) : A ∩ B ⊆ A := by
  [...]

theorem injective_comp' {α β γ : Type} (f : α → β) (g : β → γ)
    (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) := by
  [...]

theorem exists_bigger (n : ℕ) : ∃ m, n < m := by
  [...]

theorem prime_seven : Nat.Prime 7 := by
  [...]

end Practice.RealsSets
