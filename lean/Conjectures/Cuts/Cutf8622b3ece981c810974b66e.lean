import Mathlib

-- child 1 zh: 证明充分大偶数的两个素数与五个正指数二幂表示，不要求两个素数有序。
-- child 1 en: Prove the unordered five-power representation for every sufficiently large even integer.
-- child 2 zh: 任意一个两素数与五个正指数二幂表示都可交换两个素数，使第二个素数不大于第一个。
-- child 2 en: Swap the primes in any such representation to enforce the requested ordering.

theorem Conjectures.Cuts.Cutf8622b3ece981c810974b66e
    (hMain : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ ∃ a : Fin 5 → ℕ,
        N = p + q + ∑ i : Fin 5, (2 : ℕ) ^ (a i + (1 : ℕ)))
    (hSwap : ∀ (N p q : ℕ), Nat.Prime p → Nat.Prime q → ∀ a : Fin 5 → ℕ,
      N = p + q + ∑ i : Fin 5, (2 : ℕ) ^ (a i + (1 : ℕ)) →
        ∃ p' q' : ℕ, Nat.Prime p' ∧ Nat.Prime q' ∧ ∃ a' : Fin 5 → ℕ,
          N = p' + q' + ∑ i : Fin 5, (2 : ℕ) ^ (a' i + (1 : ℕ)) ∧ q' ≤ p') :
    (∃ (x1 : ℕ), ∀ (x2 : ℕ), x1 ≤ x2 → Even x2 → ∃ (x5 : ℕ) (x6 : ℕ), Nat.Prime x5 ∧ Nat.Prime x6 ∧ ∃ (x7 : Fin (5 : ℕ) → ℕ), x2 = x5 + x6 + ∑ x8 : Fin (5 : ℕ), (2 : ℕ) ^ (x7 x8 + (1 : ℕ)) ∧ x6 ≤ x5) := by
  obtain ⟨N₀, h⟩ := hMain
  refine ⟨N₀, fun N hN hEven => ?_⟩
  obtain ⟨p, q, hp, hq, a, heq⟩ := h N hN hEven
  exact hSwap N p q hp hq a heq
