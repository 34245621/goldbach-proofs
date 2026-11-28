import Mathlib

/-!
# 拆题：L-goldbach-linnik-six-subpower-shift

父题：对每个 ε > 0，存在阈值 N₀，使所有偶数 N ≥ N₀ 都能写成两个素数加上六个二的正整数次幂，
并且幂和部分不超过 N^ε。

拆法把「阈值」与「对所有阈值都成立的表示」分开：

* `child 1`：对**任意**阈值 N₀ 都成立（比父题强：父题只需一个阈值）；
* `child 2`：存在正整数阈值（例如 1）。

父题 ⇐ child 1 ∧ child 2：取 N₀ = 1 即得。
-/

-- child 1 zh: 对任意阈值 N₀、任意偶数 N ≥ N₀，N 都有两个素数加六个二幂的表示且幂和 ≤ N^ε。
-- child 1 en: For every threshold N0 and every even N >= N0, N is a sum of two primes and six powers of two, with the power sum at most N^eps.
-- child 2 zh: 存在正整数阈值。
-- child 2 en: There exists a positive natural threshold.

theorem Conjectures.Cuts.Cut6c879f9c0bb5b08027fae3ef
    (hMain : ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ ∃ a : Fin 6 → ℕ, N = p + q + ∑ i : Fin 6, 2 ^ (a i + 1) ∧
        ((∑ i : Fin 6, (2 : ℕ) ^ (a i + 1) : ℕ) : ℝ) ≤ (N : ℝ) ^ ε)
    (hConst : ∃ N₀ : ℕ, 0 < N₀) :
    (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ ∃ a : Fin 6 → ℕ, N = p + q + ∑ i : Fin 6, 2 ^ (a i + 1) ∧ ((∑ i : Fin 6, (2 : ℕ) ^ (a i + 1) : ℕ) : ℝ) ≤ (N : ℝ) ^ ε) := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hConst
  exact ⟨N₀, hMain ε hε N₀⟩
