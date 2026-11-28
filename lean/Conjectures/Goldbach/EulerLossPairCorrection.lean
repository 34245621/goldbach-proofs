import Mathlib

theorem Conjectures.Goldbach.EulerLossPairCorrection :
    ∀ z w : ℂ, (1-z)*(1-w)-(1-z-w)=z*w := by
  intro z w
  ring
