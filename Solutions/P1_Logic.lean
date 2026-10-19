import Mathlib.Tactic

/-! # Solutions — Practice 1: Logic -/

namespace Solutions.Logic
variable (P Q R : Prop)

theorem imp_self' : P → P := by
  intro h
  exact h

theorem and_swap' : P ∧ Q → Q ∧ P := by
  rintro ⟨hp, hq⟩
  exact ⟨hq, hp⟩

theorem or_swap' : P ∨ Q → Q ∨ P := by
  rintro (hp | hq)
  · right; exact hp
  · left; exact hq

theorem imp_trans' : (P → Q) → (Q → R) → P → R := by
  intro hpq hqr hp
  exact hqr (hpq hp)

theorem not_not_intro' : P → ¬¬P := by
  intro hp hnp
  exact hnp hp

theorem contrapositive' : (P → Q) → ¬Q → ¬P := by
  intro hpq hnq hp
  exact hnq (hpq hp)

theorem and_or_distrib' : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  rintro ⟨hp, hq | hr⟩
  · left; exact ⟨hp, hq⟩
  · right; exact ⟨hp, hr⟩

theorem not_forall_of_exists_not' (α : Type) (p : α → Prop) :
    (∃ x, ¬ p x) → ¬ ∀ x, p x := by
  rintro ⟨x, hx⟩ h
  exact hx (h x)

end Solutions.Logic
