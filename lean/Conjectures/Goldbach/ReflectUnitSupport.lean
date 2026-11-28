import Mathlib

theorem Conjectures.Goldbach.ReflectUnitSupport :
    ∀ n k : ℕ, k ≤ n → (Nat.Coprime k n ↔ Nat.Coprime (n-k) n) := by
  intro n k hk
  exact (Nat.coprime_self_sub_left hk).symm
