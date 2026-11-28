import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

-- child 1 zh: 当各滑动区间长度至多为一时，无条件建立常数为 5/2 的切比雪夫二阶矩估计。
-- child 1 en: Prove an unconditional Chebyshev second-moment bound with constant 5/2 whenever the moving interval has length at most one.
-- child 2 zh: 在区间最大长度超过一的范围，证明黎曼猜想下的单对数切比雪夫二阶矩估计。
-- child 2 en: Prove the single-logarithm second-moment estimate under RH when the maximum moving interval length exceeds one.

theorem Conjectures.Cuts.Cut84750ccd4a1a3e479ea7b8ae
  (hSmall : ∀ x δ : ℝ, 100 ≤ x → 0 < δ → δ ≤ 1/100 → δ*x ≤ 1 →
    (intervalIntegral (fun y : ℝ => (Chebyshev.theta ((1+δ)*y)-Chebyshev.theta y-δ*y)^2)
      (1:ℝ) x MeasureTheory.volume) ≤ (5/2:ℝ)*δ*Real.log ((20001/10000:ℝ)/δ)*x^2)
  (hRemaining : RiemannHypothesis → ∀ x δ : ℝ, (10 : ℝ)^13 ≤ x → 0 < δ → δ ≤ 1/(10 : ℝ)^13 → 1 < δ*x → (intervalIntegral (fun y : ℝ => (Chebyshev.theta ((1+δ)*y) - Chebyshev.theta y - δ*y)^2) (1 : ℝ) x MeasureTheory.volume) ≤ (25571/10000 : ℝ)*δ*Real.log ((20001/10000 : ℝ)/δ)*x^2) : (let θ := fun t : ℝ => ∑ p ∈ (Finset.Icc 2 ⌊t⌋₊).filter Nat.Prime, Real.log (p : ℝ); RiemannHypothesis → ∀ x δ : ℝ, (10 : ℝ)^13 ≤ x → 0 < δ → δ ≤ 1/(10 : ℝ)^13 → (intervalIntegral (fun y : ℝ => (θ ((1+δ)*y) - θ y - δ*y)^2) (1 : ℝ) x MeasureTheory.volume) ≤ (25571/10000 : ℝ)*δ*Real.log ((20001/10000 : ℝ)/δ)*x^2) := by
  intro θ hRH x δ hx hd hd'
  have hθ : θ = Chebyshev.theta := by
    funext y
    rw [Chebyshev.theta_eq_sum_Icc]
    dsimp only [θ]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_filter,Finset.mem_Icc,Nat.zero_le,true_and]
    exact ⟨fun h => ⟨h.1.2,h.2⟩, fun h => ⟨⟨h.2.two_le,h.1⟩,h.2⟩⟩
  rw [hθ]
  by_cases ht : δ*x ≤ 1
  · have hs := hSmall x δ (by norm_num at hx; linarith) hd (by norm_num at hd'; linarith) ht
    have hlog : 0 ≤ Real.log ((20001/10000:ℝ)/δ) :=
      Real.log_nonneg ((le_div_iff₀ hd).mpr (by norm_num at hd'; linarith))
    exact hs.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num) hd.le) hlog) (sq_nonneg _))
  · exact hRemaining hRH x δ hx hd hd' (lt_of_not_ge ht)
