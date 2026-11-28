import Mathlib

theorem Conjectures.Goldbach.PpDivisorCoprime :
    ∀ p a n : ℕ, 0<a → ((p^a).Coprime n ↔ p.Coprime n) := by
  intro p a n ha
  exact Nat.coprime_pow_left_iff ha p n
