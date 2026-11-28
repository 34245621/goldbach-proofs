import Mathlib

theorem Conjectures.Goldbach.StripGeometryInverseHeight :
    ∀ (s : ℂ) (T : ℝ), 0<T → T≤|s.im| → ‖s⁻¹‖≤1/T := by
  intro s T hT him
  have hle : T ≤ ‖s‖ := le_trans him (Complex.abs_im_le_norm s)
  have hpos : (0:ℝ) < ‖s‖ := lt_of_lt_of_le hT hle
  rw [norm_inv, one_div]
  exact (inv_le_inv₀ hpos hT).mpr hle
