import Mathlib

/-! Cut of `L-goldbach-cut-2f402ff23dc64550ab2f25a7` into an initial segment and a tail.

child 1 zh: 初段 n ≤ 10^12（无阈值，纯有限区间）。
child 1 en: Initial segment n <= 10^12 (no threshold; pure finite range).
child 2 zh: 尾段 n > 10^12（保留阈值）。
child 2 en: Tail n > 10^12 (threshold retained).
-/

theorem Conjectures.Cuts.Cut8f843e20400131ce35cf136d
    (h1 : ∀ (x1 : ℝ), (0 : ℝ) < x1 → x1 ≤ (1 : ℝ) → ∀ (x5 : ℕ), x5 ≤ (10 : ℕ) ^ (12 : ℕ) → Even x5 → ∃ (x8 : ℕ) (x9 : ℕ), Nat.Prime x8 ∧ Nat.Prime x9 ∧ ∃ (x10 : Fin (6 : ℕ) → ℕ), x5 = x8 + x9 + ∑ x11 : Fin (6 : ℕ), (2 : ℕ) ^ (x10 x11 + (1 : ℕ)) ∧ (↑(∑ x11 : Fin (6 : ℕ), (2 : ℕ) ^ (x10 x11 + (1 : ℕ))) : ℝ) ≤ (↑x5 : ℝ) ^ x1 ∧ x9 ≤ x8)
    (h2 : ∀ (x1 : ℝ), (0 : ℝ) < x1 → x1 ≤ (1 : ℝ) → ∃ (x4 : ℕ), ∀ (x5 : ℕ), x4 ≤ x5 → (10 : ℕ) ^ (12 : ℕ) < x5 → Even x5 → ∃ (x8 : ℕ) (x9 : ℕ), Nat.Prime x8 ∧ Nat.Prime x9 ∧ ∃ (x10 : Fin (6 : ℕ) → ℕ), x5 = x8 + x9 + ∑ x11 : Fin (6 : ℕ), (2 : ℕ) ^ (x10 x11 + (1 : ℕ)) ∧ (↑(∑ x11 : Fin (6 : ℕ), (2 : ℕ) ^ (x10 x11 + (1 : ℕ))) : ℝ) ≤ (↑x5 : ℝ) ^ x1 ∧ x9 ≤ x8) :
    (∀ (x1 : ℝ), (0 : ℝ) < x1 → x1 ≤ (1 : ℝ) → ∃ (x4 : ℕ), ∀ (x5 : ℕ), x4 ≤ x5 → Even x5 → ∃ (x8 : ℕ) (x9 : ℕ), Nat.Prime x8 ∧ Nat.Prime x9 ∧ ∃ (x10 : Fin (6 : ℕ) → ℕ), x5 = x8 + x9 + ∑ x11 : Fin (6 : ℕ), (2 : ℕ) ^ (x10 x11 + (1 : ℕ)) ∧ (↑(∑ x11 : Fin (6 : ℕ), (2 : ℕ) ^ (x10 x11 + (1 : ℕ))) : ℝ) ≤ (↑x5 : ℝ) ^ x1 ∧ x9 ≤ x8) := by
  intro x1 hx1 hx1'
  obtain ⟨N, H⟩ := h2 x1 hx1 hx1'
  refine ⟨max N ((10 : ℕ) ^ (12 : ℕ)), ?_⟩
  intro n hn he
  by_cases h : n ≤ (10 : ℕ) ^ (12 : ℕ)
  · exact h1 x1 hx1 hx1' n h he
  · push_neg at h
    exact H n (le_trans (le_max_left _ _) hn) h he
