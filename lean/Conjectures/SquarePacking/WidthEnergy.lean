import Mathlib

theorem Conjectures.SquarePacking.WidthEnergy :
    ∀ c s : ℝ, c ^ 2 + s ^ 2 = 1 → (|c| + |s|) ^ 2 ≤ 2 := by
  intro c s h
  nlinarith only [h, sq_abs c, sq_abs s, sq_nonneg (|c| - |s|)]
