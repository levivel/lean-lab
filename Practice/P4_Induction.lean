import LeanLab.Placeholder
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Set 4 · Induction, deeper

Sums, powers, Fibonacci and lists: induction on numbers and on data.

Replace every `[...]` with a proof. Put your cursor inside a proof to see
the goal in the Lean Infoview panel.

Grade yourself: `leanlab check Practice/P4_Induction.lean`
Stuck? `leanlab solution P4_Induction` -/

namespace Practice.Induction
open Finset

/-- `oddSum n = 1 + 3 + ⋯ + (2n - 1)` -/
def oddSum : ℕ → ℕ
  | 0 => 0
  | n + 1 => oddSum n + (2 * n + 1)

/-- The Fibonacci numbers 0, 1, 1, 2, 3, 5, … -/
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Reverse a list, the slow way. -/
def myRev {α : Type} : List α → List α
  | [] => []
  | x :: xs => myRev xs ++ [x]

/-- Hint: the first n odd numbers add up to a square. Induct, unfold `oddSum`, use `ih`, finish with `ring`.
Goal:
n : ℕ
⊢ oddSum n = n ^ 2 -/
theorem oddSum_eq (n : ℕ) : oddSum n = n ^ 2 := by
  [...]

/-- Hint: in the step, `pow_succ` turns `2 ^ (k+1)` into `2 ^ k * 2`; then `linarith` can use `ih`.
Goal:
n : ℕ
⊢ n + 1 ≤ 2 ^ n -/
theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  [...]

/-- Hint: `fib (k + 2)` is `fib k + fib (k + 1)` by definition, so `rfl` proves that fact. Then `omega`.
Goal:
n : ℕ
⊢ ∑ i ∈ range n, fib i + 1 = fib (n + 1) -/
theorem fib_sum (n : ℕ) : ∑ i ∈ range n, fib i + 1 = fib (n + 1) := by
  [...]

/-- Hint: induct on the list itself: cases `nil` and `cons x xs`. `simp [myRev, ih]` does the step.
Goal:
α : Type
l : List α
⊢ (myRev l).length = l.length -/
theorem myRev_length {α : Type} (l : List α) : (myRev l).length = l.length := by
  [...]

/-- Hint: same shape as `myRev_length`, with `List.reverse_cons`.
Goal:
α : Type
l : List α
⊢ myRev l = l.reverse -/
theorem myRev_eq_reverse {α : Type} (l : List α) : myRev l = l.reverse := by
  [...]

end Practice.Induction
