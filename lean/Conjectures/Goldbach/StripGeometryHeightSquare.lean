import Mathlib

theorem Conjectures.Goldbach.StripGeometryHeightSquare :
    ∀ s : ℂ, s.re=1/2 → Complex.normSq s = 1/4+s.im^2 := by
  intro s h
  rw [Complex.normSq_apply, h]
  ring
