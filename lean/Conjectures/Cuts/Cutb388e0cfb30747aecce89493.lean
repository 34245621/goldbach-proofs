import Mathlib

-- child 1 zh: 有限段：起点 16384 ≤ x2 ≤ 10^6 的对数平方窗密度。
-- child 1 en: The finite stretch: the log-square window density for starts 16384 <= x2 <= 10^6.
-- child 2 zh: 尾段：起点 x2 ≥ 10^6 的对数平方窗密度。
-- child 2 en: The tail: the log-square window density for starts x2 >= 10^6.

theorem Conjectures.Cuts.Cutb388e0cfb30747aecce89493
    (h₁ : ∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), (16384 : ℕ) ≤ x2 → x2 ≤ 1000000 →
      (1 : ℕ) + ⌊x1 * Real.log ↑x2 ^ (2 : ℕ)⌋₊ ≤
        {x4 ∈ Finset.Ioc x2 ⌊↑x2 + (123 : ℝ) * Real.log ↑x2 ^ (2 : ℕ)⌋₊ |
          (0 : ℕ) < {x5 ∈ Finset.range (x4 + (1 : ℕ)) | Nat.Prime x5 ∧ Odd x5 ∧
            Nat.Prime (x4 - x5) ∧ Odd (x4 - x5)}.card}.card)
    (h₂ : ∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), 1000000 ≤ x2 →
      (1 : ℕ) + ⌊x1 * Real.log ↑x2 ^ (2 : ℕ)⌋₊ ≤
        {x4 ∈ Finset.Ioc x2 ⌊↑x2 + (123 : ℝ) * Real.log ↑x2 ^ (2 : ℕ)⌋₊ |
          (0 : ℕ) < {x5 ∈ Finset.range (x4 + (1 : ℕ)) | Nat.Prime x5 ∧ Odd x5 ∧
            Nat.Prime (x4 - x5) ∧ Odd (x4 - x5)}.card}.card) :
    (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), (16384 : ℕ) ≤ x2 →
      (1 : ℕ) + ⌊x1 * Real.log ↑x2 ^ (2 : ℕ)⌋₊ ≤
        {x4 ∈ Finset.Ioc x2 ⌊↑x2 + (123 : ℝ) * Real.log ↑x2 ^ (2 : ℕ)⌋₊ |
          (0 : ℕ) < {x5 ∈ Finset.range (x4 + (1 : ℕ)) | Nat.Prime x5 ∧ Odd x5 ∧
            Nat.Prime (x4 - x5) ∧ Odd (x4 - x5)}.card}.card) := by
  classical
  obtain ⟨c₁, hc₁, hP₁⟩ := h₁
  obtain ⟨c₂, hc₂, hP₂⟩ := h₂
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, ?_⟩
  intro x2 hx2
  have hL : (0 : ℝ) ≤ Real.log ↑x2 ^ (2 : ℕ) := sq_nonneg _
  have hmono₁ : ⌊min c₁ c₂ * Real.log ↑x2 ^ (2 : ℕ)⌋₊ ≤ ⌊c₁ * Real.log ↑x2 ^ (2 : ℕ)⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_right (min_le_left c₁ c₂) hL)
  have hmono₂ : ⌊min c₁ c₂ * Real.log ↑x2 ^ (2 : ℕ)⌋₊ ≤ ⌊c₂ * Real.log ↑x2 ^ (2 : ℕ)⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_right (min_le_right c₁ c₂) hL)
  by_cases hcut : x2 ≤ 1000000
  · have hb := hP₁ x2 hx2 hcut
    omega
  · have hcut' : 1000000 ≤ x2 := le_of_lt (not_le.mp hcut)
    have hb := hP₂ x2 hcut'
    omega
