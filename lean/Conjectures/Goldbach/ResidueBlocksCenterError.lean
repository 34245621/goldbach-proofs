import Mathlib

open scoped BigOperators

theorem Conjectures.Goldbach.ResidueBlocksCenterError :
    ∀ (q : ℕ) (w : Fin q → ℝ), 0 < q →
      (∑ a, (w a - (∑ b, w b) / (q : ℝ))) = 0 := by
  intro q w hq
  have hq₀ : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_div_cancel₀ _ hq₀, sub_self]
