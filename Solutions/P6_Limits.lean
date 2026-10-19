import Mathlib.Tactic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # Set 6 · Sequences and limits

The ε–N definition of a limit, written out by hand, and the first theorems about it. -/

namespace Solutions.Limits

/-- `a n → L`: for every ε > 0, from some N on, `a n` is within ε of L. -/
def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε

/-- Hint: `intro ε hε`, any N works, and `simp` turns `|c - c|` into 0.
Goal:
c : ℝ
⊢ ConvergesTo (fun _ ↦ c) c -/
theorem conv_const (c : ℝ) : ConvergesTo (fun _ ↦ c) c := by
  intro ε hε
  exact ⟨0, fun n _ ↦ by simp [hε]⟩

/-- Hint: use the N from `h`. The difference `(a n + c) - (L + c)` is just `a n - L`.
Goal:
a : ℕ → ℝ
L c : ℝ
h : ConvergesTo a L
⊢ ConvergesTo (fun n ↦ a n + c) (L + c) -/
theorem conv_add_const (a : ℕ → ℝ) (L c : ℝ) (h : ConvergesTo a L) :
    ConvergesTo (fun n ↦ a n + c) (L + c) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  have := hN n hn
  simpa [add_sub_add_right_eq_sub] using this

/-- Hint: same N as before; for `n ≥ N` you also have `n + 1 ≥ N` (`omega`).
Goal:
a : ℕ → ℝ
L : ℝ
h : ConvergesTo a L
⊢ ConvergesTo (fun n ↦ a (n + 1)) L -/
theorem conv_shift (a : ℕ → ℝ) (L : ℝ) (h : ConvergesTo a L) :
    ConvergesTo (fun n ↦ a (n + 1)) L := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn ↦ hN (n + 1) (by omega)⟩

/-- Hint: if `a → L` and `L ≠ 0`... no: here simply scale ε. Use `h (ε / 2)` and `abs_mul`.
Goal:
a : ℕ → ℝ
L : ℝ
h : ConvergesTo a L
⊢ ConvergesTo (fun n ↦ 2 * a n) (2 * L) -/
theorem conv_two_mul (a : ℕ → ℝ) (L : ℝ) (h : ConvergesTo a L) :
    ConvergesTo (fun n ↦ 2 * a n) (2 * L) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  have := hN n hn
  have e : 2 * a n - 2 * L = 2 * (a n - L) := by ring
  simp only [e, abs_mul, abs_two]
  linarith

/-- Hint: Archimedes: `exists_nat_gt (1 / ε)` gives N with 1/ε < N. Clear denominators with `div_lt_iff₀`, then `nlinarith`.
Goal:
⊢ ConvergesTo (fun n ↦ 1 / ((n : ℝ) + 1)) 0 -/
theorem conv_one_div : ConvergesTo (fun n ↦ 1 / ((n : ℝ) + 1)) 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n + 1 := by positivity
  have hNε : 1 < N * ε := (div_lt_iff₀ hε).mp hN
  rw [sub_zero, abs_of_pos (by positivity), div_lt_iff₀ hpos]
  nlinarith

end Solutions.Limits
