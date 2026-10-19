import Mathlib.Tactic

/-! # Practice 1: Logic

Replace every `sorry` with a proof. Put your cursor inside a proof to see
the goal in the Lean Infoview panel.

Tactics to try: `intro`, `exact`, `rintro ⟨h1, h2⟩`, `rintro (h1 | h2)`,
`constructor`, `left`, `right`, `apply`.

Grade yourself: `leanlab check Practice/P1_Logic.lean`
Stuck? `leanlab solution P1_Logic` -/

namespace Practice.Logic
variable (P Q R : Prop)

theorem imp_self' : P → P := by
  sorry

theorem and_swap' : P ∧ Q → Q ∧ P := by
  sorry

theorem or_swap' : P ∨ Q → Q ∨ P := by
  sorry

theorem imp_trans' : (P → Q) → (Q → R) → P → R := by
  sorry

theorem not_not_intro' : P → ¬¬P := by
  sorry

theorem contrapositive' : (P → Q) → ¬Q → ¬P := by
  sorry

theorem and_or_distrib' : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  sorry

theorem not_forall_of_exists_not' (α : Type) (p : α → Prop) :
    (∃ x, ¬ p x) → ¬ ∀ x, p x := by
  sorry

end Practice.Logic
