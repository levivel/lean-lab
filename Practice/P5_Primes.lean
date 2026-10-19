import LeanLab.Placeholder
import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.Group.Nat.Even

/-! # Set 5 · Divisibility and primes

`a ∣ b` means `∃ k, b = a * k`. From there to Euclid's infinitely many primes.

Replace every `[...]` with a proof. Put your cursor inside a proof to see
the goal in the Lean Infoview panel.

Grade yourself: `leanlab check Practice/P5_Primes.lean`
Stuck? `leanlab solution P5_Primes` -/

namespace Practice.Primes

/-- Hint: `obtain ⟨k, rfl⟩ := h1` replaces b by a * k. Do it twice, then give the witness.
Goal:
a b c : ℕ
h1 : a ∣ b
h2 : b ∣ c
⊢ a ∣ c -/
theorem dvd_trans' (a b c : ℕ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  [...]

/-- Hint: unpack both divisibilities; the witness for the sum is the sum of the witnesses.
Goal:
a b c : ℤ
h1 : a ∣ b
h2 : a ∣ c
⊢ a ∣ b + c -/
theorem dvd_add' (a b c : ℤ) (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b + c := by
  [...]

/-- Hint: an even number is `k + k`. Square it and find the new witness.
Goal:
n : ℕ
h : Even n
⊢ Even (n ^ 2) -/
theorem even_sq (n : ℕ) (h : Even n) : Even (n ^ 2) := by
  [...]

/-- Hint: split on `n % 3` (three cases, via `omega`) and let `simp` compute each remainder.
Goal:
n : ℕ
⊢ 3 ∣ n ^ 3 + 2 * n -/
theorem three_dvd (n : ℕ) : 3 ∣ n ^ 3 + 2 * n := by
  [...]

/-- Hint: `Nat.dvd_one` says `p ∣ 1 ↔ p = 1`, and a prime is bigger than 1 (`hp.one_lt`).
Goal:
p : ℕ
hp : Nat.Prime p
⊢ ¬p ∣ 1 -/
theorem prime_not_dvd_one (p : ℕ) (hp : p.Prime) : ¬ p ∣ 1 := by
  [...]

/-- Hint: Mathlib's `Nat.exists_infinite_primes (n + 1)` gives a prime `p ≥ n + 1`.
Goal:
n : ℕ
⊢ ∃ p, n < p ∧ Nat.Prime p -/
theorem exists_prime_gt (n : ℕ) : ∃ p, n < p ∧ p.Prime := by
  [...]

/-- Hint: concrete numbers, so a decision tactic can just compute.
Goal:
⊢ Nat.gcd 84 120 = 12 -/
theorem gcd_example : Nat.gcd 84 120 = 12 := by
  [...]

end Practice.Primes
