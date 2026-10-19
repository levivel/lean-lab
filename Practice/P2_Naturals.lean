import LeanLab.Placeholder
import Mathlib.Tactic

/-! # Practice 2: Natural numbers and induction

Replace every `[...]` with a proof. Put your cursor inside a proof to see
the goal in the Lean Infoview panel.

Tactics to try: `induction n with | zero => … | succ k ih => …`, `rw [...]`,
`ring`, `omega`, `simp`, `nlinarith`, and `⟨witness, proof⟩` for `Even`/`∃`.

Grade yourself: `leanlab check Practice/P2_Naturals.lean`
Stuck? `leanlab solution P2_Naturals` -/

namespace Practice.Naturals

/-- `sumTo n = 0 + 1 + ⋯ + n` -/
def sumTo : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

theorem zero_add' (n : ℕ) : 0 + n = n := by
  [...]

theorem sumTo_formula (n : ℕ) : 2 * sumTo n = n * (n + 1) := by
  [...]

theorem add_comm' (a b : ℕ) : a + b = b + a := by
  [...]

theorem two_mul_even (n : ℕ) : Even (2 * n) := by
  [...]

theorem le_sq (n : ℕ) : n ≤ n ^ 2 := by
  [...]

end Practice.Naturals
