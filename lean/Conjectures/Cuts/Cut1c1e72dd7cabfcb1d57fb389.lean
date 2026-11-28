import Mathlib

-- child 1 zh: 在 10^15 < x 上证明 Mertens 倒数素数和的显式单侧下界。
-- child 1 en: Prove the explicit lower reciprocal-prime bound on the upper tail.
-- child 2 zh: 在 10^15 < x 上证明 Mertens 倒数素数和的显式单侧上界。
-- child 2 en: Prove the explicit upper reciprocal-prime bound on the upper tail.

theorem Conjectures.Cuts.Cut1c1e72dd7cabfcb1d57fb389
    (hLower : let M0 : ℝ := Real.eulerMascheroniConstant +
      ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ))
      ∀ x : ℝ, (10 : ℝ) ^ 15 < x →
        Real.log (Real.log x) + M0 - (2964e-9 : ℝ) / Real.log x ≤
          ∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
    (hUpper : let M0 : ℝ := Real.eulerMascheroniConstant +
      ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ))
      ∀ x : ℝ, (10 : ℝ) ^ 15 < x →
        (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤
          Real.log (Real.log x) + M0 + (6836e-9 : ℝ) / Real.log x) :
    (have x1 : ℝ := Real.eulerMascheroniConstant + ∑' (x1 : Nat.Primes), (Real.log ((1 : ℝ) - (1 : ℝ) / (↑(↑x1 : ℕ) : ℝ)) + (1 : ℝ) / (↑(↑x1 : ℕ) : ℝ)); ∀ (x2 : ℝ), (10 : ℝ) ^ (15 : ℕ) < x2 → Real.log (Real.log x2) + x1 - 2964e-9 / Real.log x2 ≤ ∑ x4 ∈ Finset.range ⌈x2⌉₊ with Nat.Prime x4, (1 : ℝ) / (↑x4 : ℝ) ∧ ∑ x4 ∈ Finset.range ⌈x2⌉₊ with Nat.Prime x4, (1 : ℝ) / (↑x4 : ℝ) ≤ Real.log (Real.log x2) + x1 + 6836e-9 / Real.log x2) := by
  dsimp only
  intro x hxlower
  exact ⟨hLower x hxlower, hUpper x hxlower⟩
