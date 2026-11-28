import Mathlib

theorem Conjectures.NoThreeInLine.DetShear :
    ∀ x y u v t:ℤ, x*(v+t*u)-(y+t*x)*u=x*v-y*u := by
  intro x y u v t
  ring
