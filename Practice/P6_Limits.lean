import LeanLab.Placeholder
import Mathlib.Tactic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # Set 6 · Sequences and limits

The ε–N definition of a limit, written out by hand, and the first theorems about it.

Replace every `[...]` with a proof. Put your cursor inside a proof to see
the goal in the Lean Infoview panel.

Grade yourself: `leanlab check Practice/P6_Limits.lean`
Stuck? `leanlab solution P6_Limits` -/

namespace Practice.Limits

/-- `a n → L`: for every ε > 0, from some N on, `a n` is within ε of L. -/
def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε

/-- Hint: `intro ε hε`, any N works, and `simp` turns `|c - c|` into 0.
Goal:
c : ℝ
⊢ ConvergesTo (fun _ ↦ c) c -/
theorem conv_const (c : ℝ) : ConvergesTo (fun _ ↦ c) c := by
  [...]

/-- Hint: use the N from `h`. The difference `(a n + c) - (L + c)` is just `a n - L`.
Goal:
a : ℕ → ℝ
L c : ℝ
h : ConvergesTo a L
⊢ ConvergesTo (fun n ↦ a n + c) (L + c) -/
theorem conv_add_const (a : ℕ → ℝ) (L c : ℝ) (h : ConvergesTo a L) :
    ConvergesTo (fun n ↦ a n + c) (L + c) := by
  [...]

/-- Hint: same N as before; for `n ≥ N` you also have `n + 1 ≥ N` (`omega`).
Goal:
a : ℕ → ℝ
L : ℝ
h : ConvergesTo a L
⊢ ConvergesTo (fun n ↦ a (n + 1)) L -/
theorem conv_shift (a : ℕ → ℝ) (L : ℝ) (h : ConvergesTo a L) :
    ConvergesTo (fun n ↦ a (n + 1)) L := by
  [...]

/-- Hint: if `a → L` and `L ≠ 0`... no: here simply scale ε. Use `h (ε / 2)` and `abs_mul`.
Goal:
a : ℕ → ℝ
L : ℝ
h : ConvergesTo a L
⊢ ConvergesTo (fun n ↦ 2 * a n) (2 * L) -/
theorem conv_two_mul (a : ℕ → ℝ) (L : ℝ) (h : ConvergesTo a L) :
    ConvergesTo (fun n ↦ 2 * a n) (2 * L) := by
  [...]

/-- Hint: Archimedes: `exists_nat_gt (1 / ε)` gives N with 1/ε < N. Clear denominators with `div_lt_iff₀`, then `nlinarith`.
Goal:
⊢ ConvergesTo (fun n ↦ 1 / ((n : ℝ) + 1)) 0 -/
theorem conv_one_div : ConvergesTo (fun n ↦ 1 / ((n : ℝ) + 1)) 0 := by
  [...]

end Practice.Limits
