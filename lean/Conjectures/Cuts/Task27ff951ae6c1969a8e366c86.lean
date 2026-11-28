import Mathlib

/-! Reordering the two prime summands.
Any representation as a sum of two primes and five powers of two can be
reordered so that the second prime does not exceed the first. -/

theorem Conjectures.Cuts.Task27ff951ae6c1969a8e366c86 : (∀ (x1 x2 x3 : ℕ), Nat.Prime x2 → Nat.Prime x3 → ∀ (x6 : Fin (5 : ℕ) → ℕ), x1 = x2 + x3 + ∑ x7 : Fin (5 : ℕ), (2 : ℕ) ^ (x6 x7 + (1 : ℕ)) → ∃ (x8 : ℕ) (x9 : ℕ), Nat.Prime x8 ∧ Nat.Prime x9 ∧ ∃ (x10 : Fin (5 : ℕ) → ℕ), x1 = x8 + x9 + ∑ x11 : Fin (5 : ℕ), (2 : ℕ) ^ (x10 x11 + (1 : ℕ)) ∧ x9 ≤ x8) := by
  intro x1 x2 x3 hx2 hx3 x6 hx1
  rcases le_total x3 x2 with h | h
  · refine ⟨x2, x3, hx2, hx3, x6, ?_, h⟩
    exact hx1
  · refine ⟨x3, x2, hx3, hx2, x6, ?_, h⟩
    rw [Nat.add_comm x3 x2]
    exact hx1
