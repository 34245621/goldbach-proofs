import Mathlib

theorem Conjectures.Goldbach.ResidueBlocksMergeScales :
    ∀ (q d k : ℕ), d ∣ q → k % q % d = k % d := by
  intro q d k h
  first
  | exact Nat.mod_mod_of_dvd k h
  | exact?
