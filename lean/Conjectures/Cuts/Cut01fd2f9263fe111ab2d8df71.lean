import Mathlib

-- child 1 zh: 每个偶数 N 都能写成两个素数与恰好六个二的正整数次幂之和（去掉「充分大」限制的更强闭前提）。
-- child 1 en: Every even N is a sum of two primes and exactly six positive powers of two (stronger premise without the eventual restriction).
-- child 2 zh: 存在起点 N₀，使每个 N ≥ N₀ 的偶数有带序关系 p ≤ q 的六幂表示。
-- child 2 en: There is a threshold N₀ such that every even N ≥ N₀ admits such a representation with the ordering p ≤ q.

theorem Conjectures.Cuts.Cut01fd2f9263fe111ab2d8df71
    (h₁ : ∀ N : ℕ, Even N → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ ∃ a : Fin 6 → ℕ, N = p + q + ∑ i : Fin 6, 2 ^ (a i + 1))
    (h₂ : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ ∃ a : Fin 6 → ℕ, N = p + q + ∑ i : Fin 6, 2 ^ (a i + 1) ∧ p ≤ q) :
    (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ ∃ a : Fin 6 → ℕ, N = p + q + ∑ i : Fin 6, 2 ^ (a i + 1)) := by
  obtain ⟨N₀, hN₀⟩ := h₂
  refine ⟨N₀, ?_⟩
  intro N hN hEven
  obtain ⟨p, q, hp, hq, a, hrepr, hle⟩ := hN₀ N hN hEven
  exact ⟨p, q, hp, hq, a, hrepr⟩
