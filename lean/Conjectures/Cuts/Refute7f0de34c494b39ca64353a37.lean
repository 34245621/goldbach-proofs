import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Counterexample at n = 0 (with ε = 1): a representation 0 = p + q + Σ 2^(aᵢ+1) would need a
prime p ≤ 0, but every prime is at least 2. -/

theorem Conjectures.Cuts.Refute7f0de34c494b39ca64353a37 : ¬ (∀ (x1 : ℝ), (0 : ℝ) < x1 → x1 ≤ (1 : ℝ) → ∀ x4 ≤ (10 : ℕ) ^ (12 : ℕ), Even x4 → ∃ (x7 : ℕ) (x8 : ℕ), Nat.Prime x7 ∧ Nat.Prime x8 ∧ ∃ (x9 : Fin (6 : ℕ) → ℕ), x4 = x7 + x8 + ∑ x10 : Fin (6 : ℕ), (2 : ℕ) ^ (x9 x10 + (1 : ℕ)) ∧ (↑(∑ x10 : Fin (6 : ℕ), (2 : ℕ) ^ (x9 x10 + (1 : ℕ))) : ℝ) ≤ (↑x4 : ℝ) ^ x1 ∧ x8 ≤ x7) := by
  intro h
  obtain ⟨p, q, hp, _, a, hn, -⟩ := h 1 one_pos le_rfl 0 (by norm_num) ⟨0, rfl⟩
  have h2 := hp.two_le
  omega
