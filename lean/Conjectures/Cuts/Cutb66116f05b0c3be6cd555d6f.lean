import Mathlib

/-!
# 拆题：L-goldbach-grimmelt-log-endpoint

父题：存在常数 B, C > 0，使对数幂尺度 `X^(7/120)·(log X)^B ≤ H` 的窗口里，
哥德巴赫例外集计数 ≤ `C·H/(log X)^A`。

拆法把「常数」与「对任意 admissible 常数都成立的阈值」分开：

* `child 1`：对**任意** B, C > 0 与任意 A > 0，都存在阈值 X₀ 使该界成立
  （比父题强：父题只需一对常数）；
* `child 2`：存在正实数 B, C（例如 B = C = 1）。

父题 ⇐ child 1 ∧ child 2：先取出 child 2 的常数，再交给 child 1。
-/

-- child 1 zh: 对任意 A > 0 与任意正实数 B、C，存在阈值 X₀，使所有 X ≥ X₀ 的相应窗口例外集计数 ≤ C·H/(log X)^A。
-- child 1 en: For every A > 0 and every positive real B, C there is a threshold X0 beyond which the window exception count is at most C·H/(log X)^A.
-- child 2 zh: 存在正实数 B 与 C。
-- child 2 en: There exist positive real constants B and C.

theorem Conjectures.Cuts.Cutb66116f05b0c3be6cd555d6f
    (hMain : ∀ A : ℝ, 0 < A → ∀ B C : ℝ, 0 < B → 0 < C → ∃ X₀ : ℕ, ∀ X H : ℕ, X₀ ≤ X → H ≤ X →
      (X:ℝ)^((7:ℝ)/120) * (Real.log (X:ℝ))^B ≤ (H:ℝ) →
      ((((Finset.Icc (X-H) X).filter (fun n => 4 ≤ n ∧ Even n ∧ ∀ p ∈ Finset.range (n+1), ¬ (Nat.Prime p ∧ Nat.Prime (n-p)))).card):ℝ) ≤ C*(H:ℝ)/(Real.log (X:ℝ))^A)
    (hConst : ∃ B C : ℝ, 0 < B ∧ 0 < C) :
    (∀ A : ℝ, 0 < A → ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ X₀ : ℕ, ∀ X H : ℕ, X₀ ≤ X → H ≤ X → (X:ℝ)^((7:ℝ)/120) * (Real.log (X:ℝ))^B ≤ (H:ℝ) → ((((Finset.Icc (X-H) X).filter (fun n => 4 ≤ n ∧ Even n ∧ ∀ p ∈ Finset.range (n+1), ¬ (Nat.Prime p ∧ Nat.Prime (n-p)))).card):ℝ) ≤ C*(H:ℝ)/(Real.log (X:ℝ))^A) := by
  intro A hA
  obtain ⟨B, C, hB, hC⟩ := hConst
  exact ⟨B, C, hB, hC, hMain A hA B C hB hC⟩
