import Mathlib
import Conjectures.Goldbach.UnconditionalMinorFiveSixths

open Filter

private theorem square_band_envelope (x q : ℝ) (hx : 1 ≤ x) (hq : 0 < q)
    (hsmall : q^2 ≤ x) (hlarge : x ≤ 4*q^2) :
    OAI.Problem337.Vaughan.approximationEnvelope x q ≤ 4*x^(4/5:ℝ) := by
  have hx' : 0 < x := by linarith
  have ha : Real.sqrt x ≤ 2*q := (Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith⟩
  have hb : q ≤ Real.sqrt x := (Real.le_sqrt hq.le hx'.le).mpr hsmall
  have hquarter : (x^(1/4:ℝ))^2 = Real.sqrt x := by
    rw [← Real.rpow_mul_natCast hx'.le, Real.sqrt_eq_rpow]
    norm_num
  have hroot : x^(1/4:ℝ)/2 ≤ Real.sqrt q := by
    apply (Real.le_sqrt (by positivity) hq.le).mpr
    nlinarith only [hquarter,ha,hq.le]
  have hl : x / Real.sqrt q ≤ 2*x^(3/4:ℝ) := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hq)).mpr
    have hid : x^(3/4:ℝ)*x^(1/4:ℝ) = x := by rw [←Real.rpow_add hx']; norm_num
    nlinarith only [mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg hx'.le (3/4:ℝ)),hid]
  have hr : Real.sqrt (x*q) ≤ x^(3/4:ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    calc x*q ≤ x*Real.sqrt x := mul_le_mul_of_nonneg_left hb hx'.le
         _ = (x^(3/4:ℝ))^2 := by
           rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hx'.le,
             mul_comm, ← Real.rpow_add_one hx'.ne']
           norm_num
  have hle := Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (3/4:ℝ) ≤ 4/5)
  unfold OAI.Problem337.Vaughan.approximationEnvelope
  linarith

private theorem square_band_bound :
    let S := fun (N : ℕ) (x : ℝ) => ∑ m ∈ Finset.range N,
      ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
        Complex.exp (((2*Real.pi*(m : ℝ)*x : ℝ) : ℂ)*Complex.I)
    ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ N q a : ℕ, K ≤ N → 2 ≤ N →
      Nat.Prime q → q^2 ≤ N → N ≤ 4*q^2 → a < q → Nat.Coprime a q →
      ∀ θ : ℝ, |θ - (a:ℝ)/(q:ℝ)| ≤ 1/(q:ℝ)^2 → ‖S N θ‖ ≤ (N:ℝ)^(4/5+δ) := by
  intro S δ hδ
  have ht : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlogs := ((isLittleO_log_rpow_rpow_atTop (4:ℝ) hδ).comp_tendsto ht).bound
    (by norm_num : (0:ℝ) < 1/65000)
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    ((OAI.Problem337.Vaughan.eventually_vonMangoldt_sum_log_bound.and hlogs).and
      ((Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1))
  refine ⟨K, ?_⟩
  intro n q a hn hn2 hq hsmall hlarge _ hcop θ hclose
  obtain ⟨⟨hv,hl⟩,hL⟩ := hK n hn
  let x : ℝ := n
  let L := Real.log x
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ n by omega)
  have hx : 0 < x := by linarith
  change 1 ≤ L at hL
  change ‖L^(4:ℝ)‖ ≤ 1/65000 * ‖x^δ‖ at hl
  have hlog : L^4 ≤ 1/65000*x^δ := by
    simpa only [Real.rpow_ofNat,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ L^4),
      abs_of_nonneg (Real.rpow_nonneg hx.le δ)] using hl
  have hsmall' : (q:ℝ)^2 ≤ x := by dsimp [x]; exact_mod_cast hsmall
  have hlarge' : x ≤ 4*(q:ℝ)^2 := by dsimp [x]; exact_mod_cast hlarge
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq.pos
  have hen := square_band_envelope x q hx1 hq' hsmall' hlarge'
  have hvq := hv θ (a:ℤ) q hq.pos hcop.isCoprime (by simpa using hclose)
    (show q ≤ n by nlinarith [hq.pos])
  let f (k : ℕ) := ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ) *
    Complex.exp (((2*Real.pi*(k : ℝ)*θ : ℝ) : ℂ)*Complex.I)
  have hsum : (∑ k ∈ Finset.range (n+1), f k) = OAI.Problem337.Vaughan.weightedSum
      (Finset.Ioc 0 n) (fun k => OAI.Problem337.VaughanBilinear.phase (θ*k))
        ArithmeticFunction.vonMangoldt := by
    rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
    simp only [f, OAI.Problem337.Vaughan.weightedSum,OAI.Problem337.VaughanBilinear.phase,
      ArithmeticFunction.map_zero,Complex.ofReal_zero,zero_mul,zero_add,Real.fourierChar_apply]
    exact Finset.sum_congr rfl (fun k _ => by rw [mul_assoc, mul_comm (k:ℝ) θ])
  rw [←hsum] at hvq
  have hb : ‖∑ k ∈ Finset.range (n+1), f k‖ ≤ 64800 * L^4 * x^(4/5:ℝ) :=
    hvq.trans (by calc
      _ ≤ 16200 * L^4 * (4*x^(4/5:ℝ)) := mul_le_mul_of_nonneg_left hen (by positivity)
      _ = _ := by ring)
  have hf : ‖f n‖ ≤ L := by
    simpa only [f,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] using
        (show ArithmeticFunction.vonMangoldt n ≤ L from ArithmeticFunction.vonMangoldt_le_log)
  have hs := norm_sub_le (∑ k ∈ Finset.range (n+1), f k) (f n)
  rw [Finset.sum_range_succ, add_sub_cancel_right] at hs
  have hL4 : L ≤ L^4 := by simpa only [pow_one] using pow_le_pow_right₀ hL (by decide : 1 ≤ 4)
  have hX : 1 ≤ x^(4/5:ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hLx : L ≤ L^4*x^(4/5:ℝ) := hL4.trans (le_mul_of_one_le_right (by positivity) hX)
  change ‖∑ k ∈ Finset.range n, f k‖ ≤ x^(4/5+δ)
  rw [Real.rpow_add hx]
  have htotal := mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hx.le (4/5:ℝ))
  rw [Finset.sum_range_succ] at hb
  nlinarith only [hs,hb,hf,hLx,htotal,mul_nonneg (show 0 ≤ L^4 by positivity)
    (Real.rpow_nonneg hx.le (4/5:ℝ))]

theorem Conjectures.Cuts.Task4251c7d2ab587801b0b6fa1b : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => ∑ x3 ∈ Finset.range x1, ↑(ArithmeticFunction.vonMangoldt x3) * Complex.exp (↑((2 : ℝ) * Real.pi * ↑x3 * x2) * Complex.I); ∀ (x2 : ℝ), (0 : ℝ) < x2 → ∃ (x4 : ℕ), ∀ (x5 x6 x7 : ℕ), x4 ≤ x5 → (2 : ℕ) ≤ x5 → Nat.Prime x6 → x6 ^ (2 : ℕ) ≤ x5 → x5 ≤ (4 : ℕ) * x6 ^ (2 : ℕ) → x7 < x6 → x7.Coprime x6 → ∀ (x15 : ℝ), |x15 - ↑x7 / ↑x6| ≤ (1 : ℝ) / ↑x6 ^ (2 : ℕ) → ‖x1 x5 x15‖ ≤ ↑x5 ^ ((4 / 5 : ℝ) + x2)) := by
  exact square_band_bound
