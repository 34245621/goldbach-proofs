import Mathlib

-- child 1 zh: 冻结的未命中移位计数不等式，附加已由 x1 ≤ x2 蕴含的冗余条件。
-- child 1 en: The frozen missed-shift counting inequality, plus a redundant condition already implied by x1 ≤ x2.
-- child 2 zh: 同一不等式，附加自然数非负的冗余条件。
-- child 2 en: Same inequality, plus the trivial nonnegativity of naturals.

theorem Conjectures.Cuts.Cutcaa116729fea4587ab2f30b5
    (h₁ : ∃ (x1 : ℕ), ∀ x2 ≥ x1, Even x2 → ({x5 ∈ Finset.Icc (1 : ℕ) x2 | (1 : ℕ) ≤ x5 ∧ ((2 : ℕ) ^ x5) ^ (2 : ℕ) ≤ x2 ∧ {x6 ∈ Finset.range (x2 + (1 : ℕ)) | Nat.Prime x6 ∧ Nat.Prime (x2 - (2 : ℕ) ^ x5 - x6) ∧ x6 + (x2 - (2 : ℕ) ^ x5 - x6) ≤ (3 : ℕ) * x6 ∧ (3 : ℕ) * x6 ≤ (2 : ℕ) * (x6 + (x2 - (2 : ℕ) ^ x5 - x6))}.card = (0 : ℕ)}.card < {x5 ∈ Finset.Icc (1 : ℕ) x2 | (1 : ℕ) ≤ x5 ∧ ((2 : ℕ) ^ x5) ^ (2 : ℕ) ≤ x2}.card) ∧ x1 ≤ x2)
    (h₂ : ∃ (x1 : ℕ), ∀ x2 ≥ x1, Even x2 → ({x5 ∈ Finset.Icc (1 : ℕ) x2 | (1 : ℕ) ≤ x5 ∧ ((2 : ℕ) ^ x5) ^ (2 : ℕ) ≤ x2 ∧ {x6 ∈ Finset.range (x2 + (1 : ℕ)) | Nat.Prime x6 ∧ Nat.Prime (x2 - (2 : ℕ) ^ x5 - x6) ∧ x6 + (x2 - (2 : ℕ) ^ x5 - x6) ≤ (3 : ℕ) * x6 ∧ (3 : ℕ) * x6 ≤ (2 : ℕ) * (x6 + (x2 - (2 : ℕ) ^ x5 - x6))}.card = (0 : ℕ)}.card < {x5 ∈ Finset.Icc (1 : ℕ) x2 | (1 : ℕ) ≤ x5 ∧ ((2 : ℕ) ^ x5) ^ (2 : ℕ) ≤ x2}.card) ∧ 0 ≤ x2) :
    (∃ (x1 : ℕ), ∀ x2 ≥ x1, Even x2 → {x5 ∈ Finset.Icc (1 : ℕ) x2 | (1 : ℕ) ≤ x5 ∧ ((2 : ℕ) ^ x5) ^ (2 : ℕ) ≤ x2 ∧ {x6 ∈ Finset.range (x2 + (1 : ℕ)) | Nat.Prime x6 ∧ Nat.Prime (x2 - (2 : ℕ) ^ x5 - x6) ∧ x6 + (x2 - (2 : ℕ) ^ x5 - x6) ≤ (3 : ℕ) * x6 ∧ (3 : ℕ) * x6 ≤ (2 : ℕ) * (x6 + (x2 - (2 : ℕ) ^ x5 - x6))}.card = (0 : ℕ)}.card < {x5 ∈ Finset.Icc (1 : ℕ) x2 | (1 : ℕ) ≤ x5 ∧ ((2 : ℕ) ^ x5) ^ (2 : ℕ) ≤ x2}.card) := by
  obtain ⟨x1, hx1⟩ := h₁
  refine ⟨x1, ?_⟩
  intro x2 hx12 hEven
  exact (hx1 x2 hx12 hEven).1
