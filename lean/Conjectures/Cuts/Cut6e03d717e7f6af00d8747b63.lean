import Mathlib

/-!
# 拆题：Johnston–Starichkova 引理 5.1 按模数 d ≤ x^(1/3) / d > x^(1/3) 二分

父题（JS Lemma 5.1 的算术级数素数计数总装，纯 Mathlib GRH 形式）：
对 `X₂ ≥ 4·10^18`、`x ≥ X₂`、`3 ≤ d ≤ √x`、`gcd a d = 1`，

`|π(x; d, a) − Li(x)/φ(d)| ≤ c_π(X₂)·√x·log x`。

按模数大小切成两支：

* `d ≤ x^(1/3)`：显式公式里 `log d` 的损失小，`ψ(x;d,a)` 的主项误差可以直接被 `c_π` 的
  常数项 `3/(8π)` 吸收；
* `d > x^(1/3)`：`log d` 与 `log x` 同阶，需要先把高次素数幂 `p^k (k ≥ 2)` 扣干净，
  再用分部求和把 `θ` 的误差转成 `π` 的误差，`c_π` 的 `1/log X₂` 项正是为这一段准备的。

两支覆盖 `3 ≤ d ≤ √x`，按 `d ≤ x^(1/3)` 分情况即得父题。
-/

-- child 1 zh: 3 ≤ d ≤ x^(1/3) 时的算术级数素数计数界。
-- child 1 en: the AP prime-counting bound for 3 ≤ d ≤ x^(1/3).
-- child 2 zh: x^(1/3) < d ≤ √x 时的算术级数素数计数界。
-- child 2 en: the AP prime-counting bound for x^(1/3) < d ≤ √x.

theorem Conjectures.Cuts.Cut6e03d717e7f6af00d8747b63
    (h₁ : (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0) → let li2 : ℝ := Real.eulerMascheroniConstant + Real.log (Real.log 2) + ∑' k : ℕ, (Real.log 2) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * ((k + 1).factorial : ℝ)); ∀ X₂ : ℝ, 4 * (10 : ℝ) ^ 18 ≤ X₂ → let c_pi : ℝ := 3 / (8 * Real.pi) + (6 + 1 / Real.pi) / (4 * Real.log X₂) + 6 / (Real.log X₂) ^ 2 + li2 / (Real.sqrt X₂ * Real.log X₂); ∀ x : ℝ, X₂ ≤ x → ∀ d a : ℕ, 3 ≤ d → (d : ℝ) ≤ Real.sqrt x → (d : ℝ) ≤ x ^ (1 / 3 : ℝ) → Nat.Coprime a d → |(((Finset.range (Nat.floor x + 1)).filter (fun p => p.Prime ∧ Nat.ModEq d p a)).card : ℝ) - (∫ t in (2 : ℝ)..x, 1 / Real.log t) / (Nat.totient d : ℝ)| ≤ c_pi * Real.sqrt x * Real.log x)
    (h₂ : (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0) → let li2 : ℝ := Real.eulerMascheroniConstant + Real.log (Real.log 2) + ∑' k : ℕ, (Real.log 2) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * ((k + 1).factorial : ℝ)); ∀ X₂ : ℝ, 4 * (10 : ℝ) ^ 18 ≤ X₂ → let c_pi : ℝ := 3 / (8 * Real.pi) + (6 + 1 / Real.pi) / (4 * Real.log X₂) + 6 / (Real.log X₂) ^ 2 + li2 / (Real.sqrt X₂ * Real.log X₂); ∀ x : ℝ, X₂ ≤ x → ∀ d a : ℕ, 3 ≤ d → (d : ℝ) ≤ Real.sqrt x → x ^ (1 / 3 : ℝ) < (d : ℝ) → Nat.Coprime a d → |(((Finset.range (Nat.floor x + 1)).filter (fun p => p.Prime ∧ Nat.ModEq d p a)).card : ℝ) - (∫ t in (2 : ℝ)..x, 1 / Real.log t) / (Nat.totient d : ℝ)| ≤ c_pi * Real.sqrt x * Real.log x) :
    ((∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0) → let li2 : ℝ := Real.eulerMascheroniConstant + Real.log (Real.log 2) + ∑' k : ℕ, (Real.log 2) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * ((k + 1).factorial : ℝ)); ∀ X₂ : ℝ, 4 * (10 : ℝ) ^ 18 ≤ X₂ → let c_pi : ℝ := 3 / (8 * Real.pi) + (6 + 1 / Real.pi) / (4 * Real.log X₂) + 6 / (Real.log X₂) ^ 2 + li2 / (Real.sqrt X₂ * Real.log X₂); ∀ x : ℝ, X₂ ≤ x → ∀ d a : ℕ, 3 ≤ d → (d : ℝ) ≤ Real.sqrt x → Nat.Coprime a d → |(((Finset.range (Nat.floor x + 1)).filter (fun p => p.Prime ∧ Nat.ModEq d p a)).card : ℝ) - (∫ t in (2 : ℝ)..x, 1 / Real.log t) / (Nat.totient d : ℝ)| ≤ c_pi * Real.sqrt x * Real.log x) := by
  intro hgrh
  dsimp only at h₁ h₂ ⊢
  intro X2 hX2
  intro x hx d a hd hdroot hcop
  by_cases h : (d : ℝ) ≤ x ^ (1 / 3 : ℝ)
  · exact h₁ hgrh X2 hX2 x hx d a hd hdroot h hcop
  · exact h₂ hgrh X2 hX2 x hx d a hd hdroot (lt_of_not_ge h) hcop
