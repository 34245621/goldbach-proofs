import Mathlib

open scoped BigOperators

theorem Conjectures.Goldbach.HeightRealProduct :
    ∀ (u v : ℂ) (x : ℝ), (u * star v * Complex.exp ((x:ℂ)*Complex.I)).re = (u*star v).re*Real.cos x - (u*star v).im*Real.sin x := by
  intro u v x
  rw [Complex.exp_mul_I]
  simp [Complex.mul_re, Complex.mul_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
