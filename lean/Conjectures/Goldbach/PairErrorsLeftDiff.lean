import Mathlib

theorem Conjectures.Goldbach.PairErrorsLeftDiff :
    let C := fun (a b : ℕ → ℝ) (n : ℕ) => ∑ k ∈ Finset.range (n+1), a k*b (n-k); ∀ a b d n,C a b n-C d b n=C (fun k => a k-d k) b n := by
  dsimp only
  intro a b d n
  simp only [sub_mul, Finset.sum_sub_distrib]
