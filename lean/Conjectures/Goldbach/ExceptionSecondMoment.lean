import Mathlib

theorem Conjectures.Goldbach.ExceptionSecondMoment :
    ∀ (I F : Finset ℕ) (e : ℕ → ℝ) (B : ℝ), F ⊆ I → 0 < B → (∀ n ∈ F, B ≤ |e n|) → (F.card : ℝ) * B ^ 2 ≤ Finset.sum I (fun n => |e n| ^ 2) := by
  intro I F e B hFI hB hthreshold
  calc
    (F.card : ℝ) * B ^ 2 = Finset.sum F (fun _ => B ^ 2) := by
      simp [nsmul_eq_mul]
    _ ≤ Finset.sum F (fun n => |e n| ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      exact pow_le_pow_left₀ hB.le (hthreshold n hn) 2
    _ ≤ Finset.sum I (fun n => |e n| ^ 2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hFI
      intro n _ _
      exact sq_nonneg (|e n|)
