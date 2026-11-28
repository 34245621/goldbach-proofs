import Mathlib

theorem Conjectures.Goldbach.PowerHeightBound :
    ∀ p j X : ℕ, 2 ≤ p → p ^ j ≤ X → j ≤ Nat.log 2 X := by
  intro p j X hp hX
  have htwo : 2 ^ j ≤ X := (Nat.pow_le_pow_left hp j).trans hX
  exact Nat.le_log_of_pow_le Nat.one_lt_two htwo
