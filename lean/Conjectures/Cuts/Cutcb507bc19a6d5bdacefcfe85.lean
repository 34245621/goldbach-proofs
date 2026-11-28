import Mathlib

-- child 1 en: RH bound for the diagonal self-correlation.
-- child 1 zh: 黎曼猜想下对角自相关项的界。
-- child 2 en: RH bound for the off-diagonal centered correlation.
-- child 2 zh: 黎曼猜想下非对角中心化相关项的界。
theorem Conjectures.Cuts.Cutcb507bc19a6d5bdacefcfe85
    (h₁ : let z := fun n : ℕ => ArithmeticFunction.vonMangoldt n - (1 : ℝ);
      RiemannHypothesis →
        ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
          |∑ a ∈ Finset.Icc 1 N,
            ∑ b ∈ Finset.Icc 1 (N - a) with b = a, z a * z b|
            ≤ C * (N : ℝ) * (Real.log (N : ℝ)) ^ 2)
    (h₂ : let z := fun n : ℕ => ArithmeticFunction.vonMangoldt n - (1 : ℝ);
      RiemannHypothesis →
        ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
          |∑ a ∈ Finset.Icc 1 N,
            ∑ b ∈ Finset.Icc 1 (N - a) with b ≠ a, z a * z b|
            ≤ C * (N : ℝ) * (Real.log (N : ℝ)) ^ 2) :
    (let z := fun n : ℕ => ArithmeticFunction.vonMangoldt n - (1 : ℝ);
      RiemannHypothesis →
        ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
          |∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N - a), z a * z b|
            ≤ C * (N : ℝ) * (Real.log (N : ℝ)) ^ 2) := by
  dsimp only
  intro hRH
  rcases h₁ hRH with ⟨C₁, hC₁, hdiag⟩
  rcases h₂ hRH with ⟨C₂, hC₂, hoff⟩
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro N hN
  let z : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n - 1
  let d : ℕ → ℝ := fun n =>
    ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 (n - a) with b = a, z a * z b
  let o : ℕ → ℝ := fun n =>
    ∑ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 (n - a) with b ≠ a, z a * z b
  have hsplit :
      (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N - a), z a * z b) = d N + o N := by
    dsimp [d, o]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_filter_add_sum_filter_not]
  have hd := hdiag N hN
  have ho := hoff N hN
  rw [hsplit]
  calc
    |d N + o N| ≤ |d N| + |o N| := abs_add_le _ _
    _ ≤ C₁ * (N : ℝ) * (Real.log (N : ℝ)) ^ 2 +
        C₂ * (N : ℝ) * (Real.log (N : ℝ)) ^ 2 := add_le_add hd ho
    _ = (C₁ + C₂) * (N : ℝ) * (Real.log (N : ℝ)) ^ 2 := by ring
