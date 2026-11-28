import Mathlib

open scoped BigOperators

namespace Conjectures.Goldbach

theorem MinorSineKernelOriginBound :
    ∀ x : ℝ, |Real.sin x| ≤ min 1 |x| := by
  intro x
  exact le_min (Real.abs_sin_le_one x) (Real.abs_sin_le_abs (x := x))

end Conjectures.Goldbach
