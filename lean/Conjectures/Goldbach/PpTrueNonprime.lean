import Mathlib

theorem Conjectures.Goldbach.PpTrueNonprime :
    ∀ p a : ℕ, p.Prime → 2≤a → ¬ Nat.Prime (p^a) :=
  fun _ _ _ exponent_bound => Nat.Prime.not_prime_pow exponent_bound
