import Mathlib

theorem Conjectures.QuadraticPrimes.OddDivisibleByTwo :
    ∀ n : ℕ, Odd n → 2 ∣ n ^ 2 + 1 := by
  rintro n ⟨k, hk⟩
  refine ⟨2 * k * k + 2 * k + 1, ?_⟩
  rw [hk]
  ring
