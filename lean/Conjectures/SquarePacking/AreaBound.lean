import Mathlib

theorem Conjectures.SquarePacking.AreaBound :
    ∀ (n : ℕ) (s : ℝ), 0 ≤ s → (n : ℝ) ≤ s ^ 2 → Real.sqrt (n : ℝ) ≤ s := by
  intro n s hs hns
  exact Real.sqrt_le_iff.mpr ⟨hs, hns⟩
