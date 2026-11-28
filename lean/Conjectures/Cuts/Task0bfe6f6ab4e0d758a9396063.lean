import Mathlib

open Filter

private theorem uniform_prime_power_error :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
    let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) =>
      Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t))
    ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ,
      ‖S n ArithmeticFunction.vonMangoldt t - S n w t‖ ≤ (n:ℝ)^(2/3:ℝ) := by
  intro w E S
  have ht : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/6)).comp_tendsto ht).bound
    (by norm_num : (0:ℝ) < 1/2)
  apply eventually_atTop.mp
  filter_upwards [hlog, eventually_ge_atTop (1:ℕ)] with n hl hn
  intro t
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0:ℝ) < n := zero_lt_one.trans_le hn'
  have hl' : Real.log (n:ℝ) ≤ 1/2 * (n:ℝ)^(1/6:ℝ) := by
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hn'),
      abs_of_nonneg (Real.rpow_nonneg hpos.le (1/6:ℝ))] using hl
  have hnon (k : ℕ) : 0 ≤ ArithmeticFunction.vonMangoldt k - w k := by
    by_cases hk : k.Prime <;> simp [w,hk,ArithmeticFunction.vonMangoldt_apply_prime]
  calc
    _ = ‖∑ k ∈ Finset.range (n+1), ((ArithmeticFunction.vonMangoldt k - w k : ℝ):ℂ) *
        E ((k:ℝ)*t)‖ := by simp only [S,Complex.ofReal_sub,sub_mul,Finset.sum_sub_distrib]
    _ ≤ ∑ k ∈ Finset.range (n+1), ‖((ArithmeticFunction.vonMangoldt k - w k : ℝ):ℂ) *
        E ((k:ℝ)*t)‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt k - w k) := by
      simp only [norm_mul,E,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (hnon _)]
    _ = Chebyshev.psi n - Chebyshev.theta n := by
      rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
      simp [Chebyshev.psi,Chebyshev.theta,w,Finset.sum_filter,Finset.sum_sub_distrib]
    _ ≤ 2*Real.sqrt n*Real.log n := Chebyshev.psi_sub_theta_le hn'
    _ ≤ 2*Real.sqrt n*(1/2*(n:ℝ)^(1/6:ℝ)) := by gcongr
    _ = _ := by
      rw [Real.sqrt_eq_rpow]
      calc 2 * (n:ℝ)^(1/2:ℝ) * (1/2*(n:ℝ)^(1/6:ℝ)) =
               (n:ℝ)^(1/2:ℝ) * (n:ℝ)^(1/6:ℝ) := by ring
           _ = _ := by rw [←Real.rpow_add hpos]; norm_num

theorem Conjectures.Cuts.Task0bfe6f6ab4e0d758a9396063 : (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log ↑x1 else (0 : ℝ); have x2 : ℝ → ℂ := fun (x2 : ℝ) => Complex.exp (↑((2 : ℝ) * Real.pi * x2) * Complex.I); have x3 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℕ → ℝ) (x5 : ℝ) => ∑ x6 ∈ Finset.range (x3 + (1 : ℕ)), ↑(x4 x6) * x2 (↑x6 * x5); ∃ (x4 : ℕ), ∀ x5 ≥ x4, ∀ (x7 : ℝ), ‖x3 x5 (⇑ArithmeticFunction.vonMangoldt) x7 - x3 x5 x1 x7‖ ≤ ↑x5 ^ (2 / 3 : ℝ)) := by
  exact uniform_prime_power_error
