import Mathlib

theorem Conjectures.NoThreeInLine.IntegerParabola :
    ∀ (a b c : ℤ), a ≠ b → a ≠ c → b ≠ c → (b - a) * (c ^ 2 - a ^ 2) ≠ (b ^ 2 - a ^ 2) * (c - a) := by
  intro a b c hab hac hbc h
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hca : c - a ≠ 0 := sub_ne_zero.mpr hac.symm
  have hcb : c - b ≠ 0 := sub_ne_zero.mpr hbc.symm
  have hprod : (b - a) * (c - a) * (c - b) = 0 := by
    linear_combination h
  exact (mul_ne_zero (mul_ne_zero hba hca) hcb) hprod
