import Mathlib

-- Cut of L-goldbach-dyadic-cell-reflected-cancellation.
-- child 1 zh: 初段受限版本（变量≤ 10^12，无阈值）。
-- child 1 en: Initial-segment restriction (variable <= 10^12, no threshold).
-- child 2 zh: 尾段受限版本（变量 > 10^12，保留冻结阈值）。
-- child 2 en: Tail restriction (variable > 10^12, keeping the frozen threshold).
-- The first premise covers the whole finite range k <= (10:ℕ)^12 with no threshold at all; the second keeps the
-- frozen threshold and covers only the tail k > (10:ℕ)^12. Their domains are disjoint and cover every admissible
-- k, so a case split on k <= (10:ℕ)^12 recovers the frozen statement. The finite premise is strictly stronger
-- than the frozen statement on its range, so the pair is a genuine reduction and neither premise alone suffices.

theorem Conjectures.Cuts.Cutf10c32108aa4727b73351ffb
    (h₁ : let w := fun p : ℕ => if Nat.Prime p then Real.log (p : ℝ) else 0; ∀ k : ℕ, k ≤ (10:ℕ)^12 → let n : ℕ := 2^k; let H : ℕ := 2^(k-k/4); let B : ℕ := 2^(k/4-3); let p := fun j t : ℕ => n/2+j*H+t; let a := fun j t : ℕ => w (p j t); let b := fun j t : ℕ => w (n-p j t); -(n:ℝ)/64 ≤ (∑ j ∈ Finset.range B, (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, (a j s-a j t)*(b j s-b j t)) / (2*(H:ℝ))))
    (h₂ : let w := fun p : ℕ => if Nat.Prime p then Real.log (p : ℝ) else 0; ∃ K : ℕ, ∀ k ≥ K, (10:ℕ)^12 < k → let n : ℕ := 2^k; let H : ℕ := 2^(k-k/4); let B : ℕ := 2^(k/4-3); let p := fun j t : ℕ => n/2+j*H+t; let a := fun j t : ℕ => w (p j t); let b := fun j t : ℕ => w (n-p j t); -(n:ℝ)/64 ≤ (∑ j ∈ Finset.range B, (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, (a j s-a j t)*(b j s-b j t)) / (2*(H:ℝ)))) :
    (let w := fun p : ℕ => if Nat.Prime p then Real.log (p : ℝ) else 0; ∃ K : ℕ, ∀ k ≥ K, let n : ℕ := 2^k; let H : ℕ := 2^(k-k/4); let B : ℕ := 2^(k/4-3); let p := fun j t : ℕ => n/2+j*H+t; let a := fun j t : ℕ => w (p j t); let b := fun j t : ℕ => w (n-p j t); -(n:ℝ)/64 ≤ (∑ j ∈ Finset.range B, (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, (a j s-a j t)*(b j s-b j t)) / (2*(H:ℝ)))) := by
  try dsimp only
  obtain ⟨Nw, htail⟩ := h₂
  refine ⟨Nw, ?_⟩
  intro x hbound
  by_cases hle : x ≤ (10:ℕ)^12
  · exact h₁ x hle
  · exact htail x hbound (by omega)
