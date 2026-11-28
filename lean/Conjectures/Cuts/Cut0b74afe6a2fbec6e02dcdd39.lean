import Mathlib

-- child 1 zh: 存在起点 N，使每个 n ≥ N 的 2*n^6 都有满足 p ≤ q 的两素数表示（有序版本，与冻结命题同为真/假）。
-- child 1 en: There is a threshold N such that every 2*n^6 with n ≥ N has a two-prime representation with p ≤ q (an ordered version, equivalent in truth to the frozen statement).
-- child 2 zh: 存在起点 N，使每个 n ≥ N 的 2*n^6 都有两素数表示且两素数不相等（2*n^6 的两素因子必不相等）。
-- child 2 en: There is a threshold N such that every 2*n^6 with n ≥ N has two distinct prime summands (necessarily distinct since n^6 is not prime).

theorem Conjectures.Cuts.Cut0b74afe6a2fbec6e02dcdd39
    (h₁ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2*n^6 ∧ p ≤ q)
    (h₂ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2*n^6 ∧ p ≠ q) :
    (∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2*n^6) := by
  obtain ⟨N, hN⟩ := h₁
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨p, q, hp, hq, hpq, hle⟩ := hN n hn
  exact ⟨p, q, hp, hq, hpq⟩
