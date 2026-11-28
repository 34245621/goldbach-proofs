import Mathlib

theorem Conjectures.QuadraticPrimes.LeventQuadraticChirpShift :
    ∀ (p : ℕ) [NeZero p] (t h n : ZMod p), ZMod.stdAddChar (t*(n+h)^2) = ZMod.stdAddChar (t*h^2) * ZMod.stdAddChar (2*t*h*n) * ZMod.stdAddChar (t*n^2) := by
  intro p _ t h n
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  ring
