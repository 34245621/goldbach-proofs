import Mathlib

theorem Conjectures.Goldbach.StripGeometryMirrorRadius :
    ∀ s : ℂ, ‖(1-s)-(1/2:ℂ)‖ = ‖s-(1/2:ℂ)‖ := by
  intro s
  have h : (1 - s) - (1/2:ℂ) = -(s - (1/2:ℂ)) := by ring
  rw [h, norm_neg]
