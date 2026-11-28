import Mathlib

-- child 1 zh: 在每个充分靠后的倍增区间内，按重数计算的低指数表示数，其每个奇数的平均值最终至少为 1/(2 log 2) 减去任意给定的正误差。
-- child 1 en: In each sufficiently late dyadic interval, the mean number of low-band representations per odd target is at least 1/(2 log 2) minus any prescribed positive error.
-- child 2 zh: 对每个有表示的奇数扣除首次表示后，其余表示的总数占区间奇数总量的比值，最终比 1/(2 log 2) 减去二分之一再低一个固定正量。
-- child 2 en: After removing the first representation of each hit, the extra representations per odd target are eventually below 1/(2 log 2) minus one half by a fixed positive margin.

theorem Conjectures.Cuts.Cut89d566b052481f7b3b3245b2
    (h₁ : ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ X ≥ T,
      let O := (Finset.Ico X (2 * X)).filter Odd
      let r (m : ℕ) := ((Finset.Icc 1 (Nat.log 2 X / 2 / 2)).filter
        (fun e => Nat.Prime (m - 2 ^ e))).card
      (1 / (2 * Real.log 2) - ε) * (O.card : ℝ) ≤ ((∑ m ∈ O, r m : ℕ) : ℝ))
    (h₂ : ∃ δ : ℝ, 0 < δ ∧ ∃ T : ℕ, ∀ X ≥ T,
      let O := (Finset.Ico X (2 * X)).filter Odd
      let r (m : ℕ) := ((Finset.Icc 1 (Nat.log 2 X / 2 / 2)).filter
        (fun e => Nat.Prime (m - 2 ^ e))).card
      ((∑ m ∈ O, (r m - 1) : ℕ) : ℝ) ≤ (1 / (2 * Real.log 2) - 1 / 2 - δ) * (O.card : ℝ)) : (∃ (x1 : ℝ),   (0 : ℝ) < x1 ∧     ∃ (x2 : ℕ),       ∀ x3 ≥ x2,         have x5 : Finset ℕ := Finset.filter Odd (Finset.Ico x3 ((2 : ℕ) * x3));         have x6 : ℕ := Nat.log (2 : ℕ) x3 / (2 : ℕ);         ((1 / 2 : ℝ) + x1) * ↑x5.card ≤ ↑{x7 ∈ x5 | (0 : ℕ) < {x8 ∈ Finset.Icc (1 : ℕ) (x6 / (2 : ℕ)) | Nat.Prime (x7 - (2 : ℕ) ^ x8)}.card}.card) := by
  classical
  obtain ⟨δ, hδ, T₂, hduplicates⟩ := h₂
  obtain ⟨T₁, hmass⟩ := h₁ (δ / 2) (by linarith)
  refine ⟨δ / 2, by linarith, max T₁ T₂, ?_⟩
  intro X hX
  let O := (Finset.Ico X (2 * X)).filter Odd
  let r (m : ℕ) := ((Finset.Icc 1 (Nat.log 2 X / 2 / 2)).filter
      (fun e => Nat.Prime (m - 2 ^ e))).card
  let μ : ℝ := 1 / (2 * Real.log 2)
  have hmassX := hmass X (le_trans (le_max_left _ _) hX)
  have hdupX := hduplicates X (le_trans (le_max_right _ _) hX)
  change (μ - δ / 2) * (O.card : ℝ) ≤ ((∑ m ∈ O, r m : ℕ) : ℝ) at hmassX
  change ((∑ m ∈ O, (r m - 1) : ℕ) : ℝ) ≤
    (μ - 1 / 2 - δ) * (O.card : ℝ) at hdupX
  change (1 / 2 + δ / 2) * (O.card : ℝ) ≤
    (((O.filter (fun m => 0 < r m)).card : ℕ) : ℝ)
  have decomp (s : Finset ℕ) (f : ℕ → ℕ) :
      (∑ m ∈ s, f m) = (s.filter (fun m => 0 < f m)).card + ∑ m ∈ s, (f m - 1) := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    split <;> omega
  have heq : ((∑ m ∈ O, r m : ℕ) : ℝ) =
      ((O.filter (fun m => 0 < r m)).card : ℝ) + ((∑ m ∈ O, (r m - 1) : ℕ) : ℝ) := by
    exact_mod_cast decomp O r
  linarith only [hmassX, hdupX, heq]
