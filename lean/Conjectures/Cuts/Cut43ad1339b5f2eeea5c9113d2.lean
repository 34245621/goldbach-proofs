import Mathlib

/-! Cut of `L-goldbach-cut-d251c217e9e11d2465a7bac4` by the target residue modulo 8.

child 1 zh: n ≡ 0 (mod 8) 的情形。
child 1 en: The case n = 0 mod 8.
child 2 zh: n ≡ 4 (mod 8) 的情形。
child 2 en: The case n = 4 mod 8.
-/

theorem Conjectures.Cuts.Cut43ad1339b5f2eeea5c9113d2
    (h1 : let x1 : ℕ → ℕ → Prop := fun (x1 x2 : ℕ) => ∃ (x3 : Fin (x2 + (1 : ℕ))) (x4 : Fin x1 → Fin (x2 + (1 : ℕ))), Nat.Prime ↑x3 ∧ x2 = ↑x3 + ∑ x5 : Fin x1, (2 : ℕ) ^ (↑(x4 x5) + (1 : ℕ)); ∃ (x2 : ℝ),   (0 : ℝ) < x2 ∧     ∃ (x3 : ℕ),       ∀ x4 ≥ x3,         Even x4 →           x4 % (4 : ℕ) = (0 : ℕ) → x4 % (8 : ℕ) = (0 : ℕ) →             have x8 : Finset ℕ := Finset.filter Odd (Finset.Ioo (0 : ℕ) x4);             ((1 : ℝ) + x2) * ↑{x9 ∈ x8 | x9 % (4 : ℕ) = (3 : ℕ)}.card ≤ ↑{x9 ∈ Finset.filter (x1 (2 : ℕ)) x8 | x9 % (4 : ℕ) = (3 : ℕ)}.card + ↑{x9 ∈ Finset.filter (x1 (3 : ℕ)) x8 | x9 % (4 : ℕ) = (3 : ℕ)}.card)
    (h2 : let x1 : ℕ → ℕ → Prop := fun (x1 x2 : ℕ) => ∃ (x3 : Fin (x2 + (1 : ℕ))) (x4 : Fin x1 → Fin (x2 + (1 : ℕ))), Nat.Prime ↑x3 ∧ x2 = ↑x3 + ∑ x5 : Fin x1, (2 : ℕ) ^ (↑(x4 x5) + (1 : ℕ)); ∃ (x2 : ℝ),   (0 : ℝ) < x2 ∧     ∃ (x3 : ℕ),       ∀ x4 ≥ x3,         Even x4 →           x4 % (4 : ℕ) = (0 : ℕ) → x4 % (8 : ℕ) = (4 : ℕ) →             have x8 : Finset ℕ := Finset.filter Odd (Finset.Ioo (0 : ℕ) x4);             ((1 : ℝ) + x2) * ↑{x9 ∈ x8 | x9 % (4 : ℕ) = (3 : ℕ)}.card ≤ ↑{x9 ∈ Finset.filter (x1 (2 : ℕ)) x8 | x9 % (4 : ℕ) = (3 : ℕ)}.card + ↑{x9 ∈ Finset.filter (x1 (3 : ℕ)) x8 | x9 % (4 : ℕ) = (3 : ℕ)}.card) :
    (let x1 : ℕ → ℕ → Prop := fun (x1 x2 : ℕ) => ∃ (x3 : Fin (x2 + (1 : ℕ))) (x4 : Fin x1 → Fin (x2 + (1 : ℕ))), Nat.Prime ↑x3 ∧ x2 = ↑x3 + ∑ x5 : Fin x1, (2 : ℕ) ^ (↑(x4 x5) + (1 : ℕ)); ∃ (x2 : ℝ),   (0 : ℝ) < x2 ∧     ∃ (x3 : ℕ),       ∀ x4 ≥ x3,         Even x4 →           x4 % (4 : ℕ) = (0 : ℕ) →             have x8 : Finset ℕ := Finset.filter Odd (Finset.Ioo (0 : ℕ) x4);             ((1 : ℝ) + x2) * ↑{x9 ∈ x8 | x9 % (4 : ℕ) = (3 : ℕ)}.card ≤ ↑{x9 ∈ Finset.filter (x1 (2 : ℕ)) x8 | x9 % (4 : ℕ) = (3 : ℕ)}.card + ↑{x9 ∈ Finset.filter (x1 (3 : ℕ)) x8 | x9 % (4 : ℕ) = (3 : ℕ)}.card) := by
  dsimp only at h1 h2
  obtain ⟨c1, hc1, N1, H1⟩ := h1
  obtain ⟨c2, hc2, N2, H2⟩ := h2
  refine ⟨min c1 c2, lt_min hc1 hc2, max N1 N2, ?_⟩
  intro n hn he h4
  have hnonneg : (0:ℝ) ≤ ↑{x9 ∈ Finset.filter Odd (Finset.Ioo (0:ℕ) n) | x9 % 4 = 3}.card := by positivity
  have h8 : n % 8 = 0 ∨ n % 8 = 4 := by omega
  rcases h8 with h | h
  · have hh := H1 n (le_trans (le_max_left N1 N2) hn) he h4 h
    have hc : (1:ℝ) + min c1 c2 ≤ 1 + c1 := by have := min_le_left c1 c2; linarith
    have hstep := mul_le_mul_of_nonneg_right hc hnonneg
    linarith
  · have hh := H2 n (le_trans (le_max_right N1 N2) hn) he h4 h
    have hc : (1:ℝ) + min c1 c2 ≤ 1 + c2 := by have := min_le_right c1 c2; linarith
    have hstep := mul_le_mul_of_nonneg_right hc hnonneg
    linarith
