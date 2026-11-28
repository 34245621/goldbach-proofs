import Mathlib

theorem Conjectures.Goldbach.CrossTailMixed :
    ∀ (a b : ℂ), ‖a+b‖^2 - ‖a‖^2 - ‖b‖^2 = 2*(a*star b).re := by
  intro a b
  simp only [Complex.sq_norm, Complex.normSq_add, Complex.star_def]
  ring
