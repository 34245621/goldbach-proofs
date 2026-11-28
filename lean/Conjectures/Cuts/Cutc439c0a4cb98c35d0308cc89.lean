import Mathlib

-- child 1 zh: 以自适应周期排除局部半密度区间上正密度的低表示目标。
-- child 1 en: Rule out dense interval models with positive density of targets of arbitrarily low convolution.
-- child 2 zh: 把素数和表示的正密度例外转移成保留所有有限模类前缀质量的稠密区间模型。
-- child 2 en: Transfer positive-density prime-sum exceptions to dense interval models preserving progression prefixes.

theorem Conjectures.Cuts.Cutc439c0a4cb98c35d0308cc89
    (h₁ : ¬ (∃ k : ℕ, ∀ j : ℕ, 0 < j → ∃ N ≥ j, ∃ f : Bool → ℕ → ℝ,
      (∀ b i, f b i ∈ Set.Icc 0 1) ∧
      (∀ b t, t ≤ N → ∀ q ∈ Finset.Icc 1 j, ∀ a < q,
        (t : ℝ)/2 ≤ q * (∑ i ∈ (Finset.range t).filter (fun i => i % q = a), f b i) + (N : ℝ)/j) ∧
      ∃ E : Finset ℕ, E ⊆ Finset.Ico ((N+1)/2) N ∧ N ≤ k * E.card ∧
        ∀ t ∈ E, (∑ i ∈ Finset.range (t+1), f false i * f true (t-i)) ≤ (N : ℝ)/j))
    (h₂ : (∃ A : Set ℕ, (∀ n ∈ A, Nat.Prime n) ∧
      (∀ q a : ℕ, 0 < q → a < q → Nat.Coprime a q → ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ N ≥ T,
        let primes := (Finset.Icc 1 N).filter (fun n => Nat.Prime n ∧ n % q = a)
        (1/2-ε)*(primes.card : ℝ) ≤ (((primes : Set ℕ) ∩ A).ncard : ℝ)) ∧
      ∃ η : ℝ, 0 < η ∧ ∀ T : ℕ, ∃ N ≥ T,
        η*(N : ℝ) < ((Set.Icc 1 N ∩ {n | Even n ∧ ¬∃ p ∈ A, ∃ q ∈ A, p+q=n}).ncard : ℝ)) → (∃ k : ℕ, ∀ j : ℕ, 0 < j → ∃ N ≥ j, ∃ f : Bool → ℕ → ℝ,
      (∀ b i, f b i ∈ Set.Icc 0 1) ∧
      (∀ b t, t ≤ N → ∀ q ∈ Finset.Icc 1 j, ∀ a < q,
        (t : ℝ)/2 ≤ q * (∑ i ∈ (Finset.range t).filter (fun i => i % q = a), f b i) + (N : ℝ)/j) ∧
      ∃ E : Finset ℕ, E ⊆ Finset.Ico ((N+1)/2) N ∧ N ≤ k * E.card ∧
        ∀ t ∈ E, (∑ i ∈ Finset.range (t+1), f false i * f true (t-i)) ≤ (N : ℝ)/j)) : (∀ (x1 : Set ℕ),   (∀ x2 ∈ x1, Nat.Prime x2) →     (∀ (x3 x4 : ℕ),         (0 : ℕ) < x3 →           x4 < x3 →             x4.Coprime x3 →               ∀ (x8 : ℝ),                 (0 : ℝ) < x8 →                   ∃ (x10 : ℕ),                     ∀ x11 ≥ x10,                       have x13 : Finset ℕ := {x13 ∈ Finset.Icc (1 : ℕ) x11 | Nat.Prime x13 ∧ x13 % x3 = x4};                       ((1 / 2 : ℝ) - x8) * ↑x13.card ≤ ↑(↑x13 ∩ x1).ncard) →       ∀ (x4 : ℕ), (0 : ℕ) < x4 → ∀ (x6 : ℝ), (0 : ℝ) < x6 → ∃ (x8 : ℕ), ∀ x9 ≥ x8, ↑(Set.Icc (1 : ℕ) x9 ∩ {x11 : ℕ | (Even x11 ∧ ¬∃ x12 ∈ x1, ∃ x13 ∈ x1, x12 + x13 = x11) ∧ Even (x11 + x4) ∧ ¬∃ x12 ∈ x1, ∃ x13 ∈ x1, x12 + x13 = x11 + x4}).ncard ≤ x6 * ↑x9) := by
  classical
  intro A hpri hd h hh η hη
  by_contra! hbad
  apply h₁
  apply h₂
  refine ⟨A, hpri, hd, η, hη, ?_⟩
  intro T
  obtain ⟨N, hN, hcount⟩ := hbad T
  refine ⟨N, hN, lt_of_lt_of_le hcount ?_⟩
  exact_mod_cast Set.ncard_le_ncard (by
    intro n hn
    refine ⟨hn.1, hn.2.1.1, ?_⟩
    rintro ⟨p, hp, q, hq, heq⟩
    exact hn.2.1.2 p hp q hq heq) ((Set.finite_Icc 1 N).inter_of_left _)
