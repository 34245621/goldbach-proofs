import Mathlib

theorem Conjectures.SquarePacking.RotationDistance :
    ∀ (a b x y u v : ℝ), a ^ 2 + b ^ 2 = 1 → ((a * x - b * y) - (a * u - b * v)) ^ 2 + ((b * x + a * y) - (b * u + a * v)) ^ 2 = (x - u) ^ 2 + (y - v) ^ 2 := by
  intro a b x y u v h
  linear_combination ((x - u) ^ 2 + (y - v) ^ 2) * h
