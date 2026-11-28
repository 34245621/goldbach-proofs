import Mathlib

theorem Conjectures.Goldbach.PpExpCutoff :
    ∀ p a n : ℕ, 2≤p → p^a≤n → a≤Nat.log 2 n := by
  intro p a n hp h
  exact Nat.le_log_of_pow_le (by norm_num) (le_trans (Nat.pow_le_pow_left hp a) h)
