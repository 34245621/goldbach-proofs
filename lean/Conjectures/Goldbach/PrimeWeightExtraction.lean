import Mathlib

theorem Conjectures.Goldbach.PrimeWeightExtraction :
    ∀ (n : ℕ) (w : ℕ → ℝ), (∀ k : ℕ, ¬ Nat.Prime k → w k = 0) → 0 < Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  intro n w hsupport hpos
  by_contra hnone
  have hz : Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hlt := Finset.mem_range.mp hp
    by_cases hprime : Nat.Prime p
    · have hcomposite : ¬ Nat.Prime (n - p) := by
        intro hq
        exact hnone ⟨p, n - p, hprime, hq, by omega⟩
      rw [hsupport _ hcomposite, mul_zero]
    · rw [hsupport _ hprime, zero_mul]
  exact (ne_of_gt hpos) hz
