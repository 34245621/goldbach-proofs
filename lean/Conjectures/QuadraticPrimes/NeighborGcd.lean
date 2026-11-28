import Mathlib

theorem Conjectures.QuadraticPrimes.NeighborGcd :
    ∀ n d:ℕ,d∣n^2+1 → d∣(n+1)^2+1 → d∣5 := by
  intro n d h1 h2
  rw [← ZMod.natCast_eq_zero_iff] at h1 h2 ⊢
  push_cast at h1 h2
  have hd : (2 * (n : ZMod d) + 1) = 0 := by
    linear_combination h2 - h1
  linear_combination 4 * h1 - (2 * (n : ZMod d) + 1) * hd + 2 * hd
