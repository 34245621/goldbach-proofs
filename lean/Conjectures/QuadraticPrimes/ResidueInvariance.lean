import Mathlib

theorem Conjectures.QuadraticPrimes.ResidueInvariance :
    ∀ (m a b : ℕ), a % m = b % m → (a ^ 2 + 1) % m = (b ^ 2 + 1) % m := by
  intro m a b h
  have hm : Nat.ModEq m a b := h
  exact Nat.ModEq.add_right 1 (Nat.ModEq.pow 2 hm)
