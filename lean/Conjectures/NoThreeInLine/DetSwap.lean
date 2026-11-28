import Mathlib

theorem Conjectures.NoThreeInLine.DetSwap :
    ∀ x y u v:ℤ, y*u-x*v= -(x*v-y*u) := by
  intro x y u v
  ring
