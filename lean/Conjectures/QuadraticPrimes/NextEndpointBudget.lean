import Mathlib

theorem Conjectures.QuadraticPrimes.NextEndpointBudget :
    ∀ s : ℚ, (5611320508261 / 9000000000000 : ℚ) - s + 2 * (((13241 / 10000 : ℚ) ^ 2) - ((5 / 4 : ℚ) ^ 2)) < 1 ↔ (44655088261 / 9000000000000 : ℚ) < s := by
  intro s
  constructor <;> intro h <;> norm_num at h ⊢ <;> linarith
