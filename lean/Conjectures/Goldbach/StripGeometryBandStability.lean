import Mathlib

theorem Conjectures.Goldbach.StripGeometryBandStability :
    ∀ (s : ℂ) (A B : ℝ), (A≤|(1-s).im| ∧ |(1-s).im|<B) ↔ (A≤|s.im| ∧ |s.im|<B) := by
  intro s A B
  have h : (1 - s).im = -s.im := by simp
  rw [h, abs_neg]
