import Mathlib

theorem Conjectures.SquarePacking.RotationNorm :
    ∀ (a b x y : ℝ), a ^ 2 + b ^ 2 = 1 → (a * x - b * y) ^ 2 + (b * x + a * y) ^ 2 = x ^ 2 + y ^ 2 := by
  intro a b x y h
  calc
    (a * x - b * y) ^ 2 + (b * x + a * y) ^ 2 = (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := by ring
    _ = x ^ 2 + y ^ 2 := by rw [h, one_mul]
