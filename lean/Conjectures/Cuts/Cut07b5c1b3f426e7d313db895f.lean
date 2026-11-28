import Mathlib

open Filter

-- child 1 zh: 在全部实频率上，冯·曼戈尔特指数和与对数素数指数和之差的模最终至多为 n 的 2/3 次幂。
-- child 1 en: Uniformly for real frequencies, the difference between the von Mangoldt and prime logarithmic sums has norm at most n to the power 2/3 for all sufficiently large n.
-- child 2 zh: 对任意正 δ，在原题的扩宽弧之外，冯·曼戈尔特指数和的模最终至多为 n 的 3/4+δ 次幂。
-- child 2 en: For every positive δ, the von Mangoldt sum outside the original wide arcs eventually has norm at most n to the power 3/4+δ.

theorem Conjectures.Cuts.Cut07b5c1b3f426e7d313db895f
    (h₁ : let w := fun k : ℕ => if k.Prime then Real.log (k : ℝ) else 0
          let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
          let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) =>
            ∑ k ∈ Finset.range (n + 1), (u k : ℂ) * E ((k : ℝ) * t)
          ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ,
            ‖S n ArithmeticFunction.vonMangoldt t - S n w t‖ ≤ (n : ℝ)^(2/3 : ℝ))
    (h₂ : let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
          let S := fun (n : ℕ) (t : ℝ) => ∑ k ∈ Finset.range (n + 1),
            (ArithmeticFunction.vonMangoldt k : ℂ) * E ((k : ℝ) * t)
          let Q := fun n : ℕ => (Nat.log 2 (n + 2)) ^ 2
          let B := fun n : ℕ => ⌊(n : ℝ) ^ (1/3 : ℝ)⌋₊
          let H := fun n : ℕ => 256 * B n * Q n
          let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ,
            1 ≤ q ∧ q ≤ B n ∧ a ≤ q ∧ a.Coprime q ∧
            |t - (a : ℝ) / q| ≤ (H n : ℝ) / ((q : ℝ) * n)}
          ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Set.Icc (0 : ℝ) 1,
            t ∉ arcs n → ‖S n t‖ ≤ (n : ℝ) ^ (3/4 + δ)) :
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ wideArcs n → ‖S n w t‖ ≤ (n : ℝ) ^ (3 / 4 + η)) := by
  intro w E S Q B H arcs η hη
  obtain ⟨N₁, corr⟩ := h₁
  have hδ : 0 < η/2 := by positivity
  obtain ⟨N₂, main⟩ := h₂ (η/2) hδ
  have grow := (tendsto_rpow_atTop hδ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop N₁, eventually_ge_atTop N₂,
    eventually_ge_atTop (1 : ℕ), grow.eventually_ge_atTop 2] with n hn₁ hn₂ hn hpow
  intro t ht harc
  have hone : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : 0 < (n : ℝ) := zero_lt_one.trans_le hone
  have hfactor : 2 ≤ (n : ℝ) ^ (η/2) := hpow
  have hcorr : ‖S n w t - S n ArithmeticFunction.vonMangoldt t‖ ≤ (n : ℝ)^(2/3 : ℝ) := by
    rw [norm_sub_rev]
    exact corr n hn₁ t
  have hmain : ‖S n ArithmeticFunction.vonMangoldt t‖ ≤ (n : ℝ)^(3/4 + η/2) :=
    main n hn₂ t ht harc
  calc
    ‖S n w t‖ ≤ ‖S n w t - S n ArithmeticFunction.vonMangoldt t‖ +
        ‖S n ArithmeticFunction.vonMangoldt t‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (S n w t - S n ArithmeticFunction.vonMangoldt t) (S n ArithmeticFunction.vonMangoldt t)
    _ ≤ (n : ℝ)^(2/3 : ℝ) + (n : ℝ)^(3/4 + η/2) := add_le_add hcorr hmain
    _ ≤ (n : ℝ)^(3/4 + η/2) * 2 := by
      rw [mul_two]
      exact add_le_add (Real.rpow_le_rpow_of_exponent_le hone (by linarith : (2/3 : ℝ) ≤ 3/4 + η/2)) le_rfl
    _ ≤ (n : ℝ)^(3/4 + η/2) * (n : ℝ)^(η/2) :=
      mul_le_mul_of_nonneg_left hfactor (Real.rpow_nonneg hpos.le _)
    _ = (n : ℝ)^(3/4 + η) := by rw [← Real.rpow_add hpos]; congr 1; ring
