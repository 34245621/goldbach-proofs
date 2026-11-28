import Mathlib

-- child 1 zh: 在 exp(10) < x ≤ 10^6 的较低中段认证倒数素数和的显式上界。
-- child 1 en: Certify the explicit reciprocal-prime upper bound in the lower mid-range exp(10) < x ≤ 10^6.
-- child 2 zh: 在 10^6 < x ≤ 10^12 的较高中段认证同一显式上界。
-- child 2 en: Certify the same explicit upper bound in the upper mid-range 10^6 < x ≤ 10^12.

theorem Conjectures.Cuts.Cutdd3011810d589f3734e841b1
    (h₁ : ∀ x : ℝ, Real.exp 10 < x → x ≤ (10 : ℝ) ^ 6 →
      (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤
        Real.log (Real.log x) + 0.261497 + 2 / (Real.sqrt x * Real.log x))
    (h₂ : ∀ x : ℝ, (10 : ℝ) ^ 6 < x → x ≤ (10 : ℝ) ^ 12 →
      (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤
        Real.log (Real.log x) + 0.261497 + 2 / (Real.sqrt x * Real.log x)) :
    (∀ (x1 : ℝ), Real.exp (10 : ℝ) < x1 → x1 ≤ (10 : ℝ) ^ (12 : ℕ) →
      ∑ x4 ∈ Finset.range ⌈x1⌉₊ with Nat.Prime x4, (1 : ℝ) / ↑x4 ≤
        Real.log (Real.log x1) + 0.261497 + (2 : ℝ) / (√x1 * Real.log x1)) := by
  classical
  intro x hxlower hxupper
  by_cases hx : x ≤ (10 : ℝ) ^ 6
  · exact h₁ x hxlower hx
  · exact h₂ x (lt_of_not_ge hx) hxupper
