import Mathlib

-- child 1 zh: 用非零模 p 类的总质量构造公共主项，控制模 p² 正位移相关和向上的偏差。
-- child 1 en: Bound the upper excess of the p²-shift correlation over the common main term from mass in nonzero classes modulo p.
-- child 2 zh: 控制同一主项超过模 p 正位移相关均值的部分，为去除对角项留出误差。
-- child 2 en: Bound the shortfall of the averaged p-shift correlation from the same main term, including the cost of removing the diagonal.

theorem Conjectures.Cuts.Cute2a18c6df7f98b58f66cde40
    (hUpper :
      let corr := fun (w : ℕ → ℝ) (X q : ℕ) =>
        ∑ d ∈ Finset.Icc 1 ((X - 1) / q),
          ∑ k ∈ Finset.range (X - q * d), w k * w (k + q * d)
      let main := fun (X p : ℕ) =>
        (∑ k ∈ Finset.range X with ¬ p ∣ k, ArithmeticFunction.vonMangoldt k) ^ 2 /
          (2 * (p : ℝ) * ((p : ℝ) - 1))
      ∀ (ε : ℝ), 0 < ε → ∃ N₀ : ℕ, ∀ (N p : ℕ),
        N₀ ≤ N → 2 ≤ N → Nat.Prime p → (p ^ 2) ^ 2 ≤ N → N ≤ 4 * (p ^ 2) ^ 2 →
          ∀ X ≤ N, corr (fun k => ArithmeticFunction.vonMangoldt k) X (p ^ 2) -
            main X p ≤ (N : ℝ) ^ (1 + ε) / 2)
    (hLower :
      let corr := fun (w : ℕ → ℝ) (X q : ℕ) =>
        ∑ d ∈ Finset.Icc 1 ((X - 1) / q),
          ∑ k ∈ Finset.range (X - q * d), w k * w (k + q * d)
      let main := fun (X p : ℕ) =>
        (∑ k ∈ Finset.range X with ¬ p ∣ k, ArithmeticFunction.vonMangoldt k) ^ 2 /
          (2 * (p : ℝ) * ((p : ℝ) - 1))
      ∀ (ε : ℝ), 0 < ε → ∃ N₀ : ℕ, ∀ (N p : ℕ),
        N₀ ≤ N → 2 ≤ N → Nat.Prime p → (p ^ 2) ^ 2 ≤ N → N ≤ 4 * (p ^ 2) ^ 2 →
          ∀ X ≤ N, main X p - corr (fun k => ArithmeticFunction.vonMangoldt k) X p / (p : ℝ) ≤
            (N : ℝ) ^ (1 + ε) / 2) :
    (have x1 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x1 : ℕ → ℝ) (x2 x3 : ℕ) => ∑ x4 ∈ Finset.Icc (1 : ℕ) ((x2 - (1 : ℕ)) / x3), ∑ x5 ∈ Finset.range (x2 - x3 * x4), x1 x5 * x1 (x5 + x3 * x4); ∀ (x2 : ℝ), (0 : ℝ) < x2 → ∃ (x4 : ℕ), ∀ (x5 x6 : ℕ), x4 ≤ x5 → (2 : ℕ) ≤ x5 → Nat.Prime x6 → (x6 ^ (2 : ℕ)) ^ (2 : ℕ) ≤ x5 → x5 ≤ (4 : ℕ) * (x6 ^ (2 : ℕ)) ^ (2 : ℕ) → ∀ x12 ≤ x5, x1 (fun (x14 : ℕ) => ArithmeticFunction.vonMangoldt x14) x12 (x6 ^ (2 : ℕ)) - x1 (fun (x14 : ℕ) => ArithmeticFunction.vonMangoldt x14) x12 x6 / ↑x6 ≤ ↑x5 ^ ((1 : ℝ) + x2)) := by
  intro corr ε hε
  obtain ⟨NUpper, upper⟩ := hUpper ε hε
  obtain ⟨NLower, lower⟩ := hLower ε hε
  refine ⟨max NUpper NLower, ?_⟩
  intro N p hN hN₂ hp hp₄ h₄p₄ X hX
  have upperAt := upper N p ((le_max_left _ _).trans hN) hN₂ hp hp₄ h₄p₄ X hX
  have lowerAt := lower N p ((le_max_right _ _).trans hN) hN₂ hp hp₄ h₄p₄ X hX
  dsimp only [corr]
  linarith only [upperAt, lowerAt]
