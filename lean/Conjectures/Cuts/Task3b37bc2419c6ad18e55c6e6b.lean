import Mathlib
import Conjectures.Goldbach.RhSchoenfeldPsi
import Conjectures.Goldbach.ExplicitPsiSubTheta

/- The zero-sum estimate and the reflection argument use the Goldbach module
   RhSchoenfeldPsi and its references to Andrew V. Sutherland and RHPrimeError.
   Copyright 2026 Andrew V. Sutherland, 2024 James Sundstrom, 2025 Stefan Kebekus,
   and 2026 Matteo Cipollina. Licensed under the Apache License, Version 2.0.
   The estimates retaining the logarithmic saving and the integration bounds below
   are specialized to this tail. -/
namespace SchoenfeldPrimeTail

open Real MeasureTheory

private theorem log_ge_dyadic {x : ℝ} {k : ℕ} (h : (2 : ℝ)^k ≤ x) :
    (k : ℝ) * 0.693 ≤ Real.log x := by
  calc (k : ℝ) * 0.693 ≤ k * Real.log 2 := by
         gcongr
         linarith [Real.log_two_gt_d9]
       _ = Real.log ((2 : ℝ)^k) := (Real.log_pow ..).symm
       _ ≤ _ := Real.log_le_log (by positivity) h

private theorem psi_refined (hRH : RiemannHypothesis) {x : ℝ} (hx : 30000 ≤ x) :
    |Chebyshev.psi x - x| ≤ √x * (Real.log x ^ 2 / (8 * π) - 0.18 * Real.log x + 2) := by
  let n := ⌊x⌋₊
  let y := Real.sqrt (n : ℝ)
  let z := Real.sqrt x
  have hx0 : 0 < x := by linarith
  have hn : 30000 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxsub : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hpsi : Chebyshev.psi x = Chebyshev.psi (n : ℝ) := Chebyshev.psi_eq_psi_coe_floor x
  obtain ⟨hy, hu, hl⟩ := SchoenfeldRH.Large.nat_bound SchoenfeldRH.zeroSumW
    (fun m t hm ht => SchoenfeldRH.psi_sub_le_of_RH hRH m hm t ht)
    (fun m t hm ht he => SchoenfeldRH.sub_psi_le_of_RH hRH m hm t ht he)
    (fun B hB => SchoenfeldRH.zeroSumW_le_of_RH hRH B hB) SchoenfeldRH.zeroSumW_nonneg n hn
  change 173.2 ≤ y at hy
  let A := Real.log (y / π) ^ 2 / (2 * π)
  change Chebyshev.psi (n : ℝ) - n ≤ y + (y + 1) * (A + 1 / 2) + 4 at hu
  change (n : ℝ) - Chebyshev.psi (n : ℝ) ≤ y + (y + 1) * (A + 1 / 2) + 3 at hl
  have hy0 : 0 < y := by linarith
  have hyz : y ≤ z := Real.sqrt_le_sqrt hnx
  have hp := Real.pi_gt_three
  have hly : 0 ≤ Real.log (y / π) := Real.log_nonneg ((le_div_iff₀ Real.pi_pos).2 (by linarith [Real.pi_lt_four]))
  have hlogy : Real.log (y / π) ≤ Real.sqrt y := by
    have h₁ := Real.log_le_log (div_pos hy0 Real.pi_pos) (show y / π ≤ y by
      apply div_le_self hy0.le; linarith)
    have h₂ := SchoenfeldRH.Large.log_le_two_sqrt_div_e hy0
    have he : 2 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    apply h₁.trans (h₂.trans ?_)
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    nlinarith [mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg y)]
  have hsq := pow_le_pow_left₀ hly hlogy 2
  rw [Real.sq_sqrt hy0.le] at hsq
  have hAc : A ≤ y / 6 := by
    dsimp [A]
    calc _ ≤ y / (2 * π) := div_le_div_of_nonneg_right hsq (by positivity)
         _ ≤ y / 6 := div_le_div_of_nonneg_left hy0.le (by norm_num) (by linarith)
  have hquot : |Chebyshev.psi x - x| ≤ y * (7 / 4 + A) := by
    rw [hpsi, abs_le]
    constructor <;> nlinarith only [hy, hu, hl, hnx, hxsub, hAc]
  have hB : Real.log (y / π) ≤ Real.log (z / π) :=
    Real.log_le_log (div_pos hy0 Real.pi_pos) (div_le_div_of_nonneg_right hyz Real.pi_pos.le)
  have htransfer : y * (7 / 4 + A) ≤ z * (7 / 4 + Real.log (z / π) ^ 2 / (2 * π)) := by
    dsimp [A]
    gcongr
  have hpL := SchoenfeldRH.Large.log_pi_gt
  have hpU : Real.log π ≤ 1.2 := by
    have he := Real.exp_one_gt_d9
    have h := Real.log_le_sub_one_of_pos (div_pos Real.pi_pos (Real.exp_pos 1))
    rw [Real.log_div Real.pi_ne_zero (Real.exp_ne_zero _), Real.log_exp] at h
    have hdiv : π / Real.exp 1 ≤ 1.2 := (div_le_iff₀ (Real.exp_pos _)).2 (by linarith [Real.pi_lt_d4])
    linarith
  have hpCoef : 0.36 * π ≤ Real.log π := by linarith [Real.pi_lt_d4]
  have hpSq : (Real.log π) ^ 2 ≤ 1.2 ^ 2 := pow_le_pow_left₀ (by linarith) hpU 2
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hBnd : 7 / 4 + Real.log (z / π) ^ 2 / (2 * π) ≤
      Real.log x ^ 2 / (8 * π) - 0.18 * Real.log x + 2 := by
    rw [Real.log_div (Real.sqrt_pos.2 hx0).ne' Real.pi_ne_zero, show Real.log z = Real.log x / 2 from Real.log_sqrt hx0.le]
    field_simp [Real.pi_ne_zero]
    nlinarith only [mul_le_mul_of_nonneg_right hpCoef hL0, hpSq, hp]
  exact hquot.trans (htransfer.trans (mul_le_mul_of_nonneg_left hBnd (Real.sqrt_nonneg x)))


private theorem log_four_upper : Real.log 4 ≤ 1.4 := by
  rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
  linarith [Real.log_two_lt_d9]

private theorem sixth_root_log {x : ℝ} (hx : 10^12 ≤ x) :
    2 * (x ^ (1 / 3 : ℝ) * Real.log x) ≤ 0.6 * √x := by
  let u : ℝ := x ^ (1 / 6 : ℝ)
  have hx0 : 0 < x := by linarith
  have hu : 100 ≤ u := by
    have hpow : (100 : ℝ)^6 ≤ x := by norm_num at hx ⊢; exact hx
    have hr := Real.rpow_le_rpow (by positivity) hpow (by norm_num : 0 ≤ (1 / 6 : ℝ))
    simpa only [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 100), Nat.cast_ofNat,
      show (6 : ℝ)*(1/6) = 1 by norm_num, Real.rpow_one, u] using hr
  have hlog100 : Real.log 100 ≤ 5 := by
    apply Real.log_le_iff_le_exp (by norm_num) |>.2
    rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    calc (100 : ℝ) ≤ 2.7 ^ 5 := by norm_num
         _ ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
  have hsmall := Real.log_le_sub_one_of_pos (show 0 < u / 100 by positivity)
  rw [Real.log_div (by linarith : u ≠ 0) (by norm_num)] at hsmall
  have hlogu : Real.log u = (1 / 6 : ℝ) * Real.log x := Real.log_rpow hx0 _
  have hlog : 2 * Real.log x ≤ 0.6 * u := by linarith
  have hroot : x ^ (1 / 3 : ℝ) * u = √x := by
    rw [Real.sqrt_eq_rpow, show x ^ (1 / 3 : ℝ) * u = x ^ ((1 / 3 : ℝ) + 1 / 6) from
      (Real.rpow_add hx0 _ _).symm]; norm_num
  calc 2 * (x ^ (1 / 3 : ℝ) * Real.log x) = x ^ (1 / 3 : ℝ) * (2 * Real.log x) := by ring
       _ ≤ x ^ (1 / 3 : ℝ) * (0.6 * u) := mul_le_mul_of_nonneg_left hlog (by positivity)
       _ = 0.6 * √x := by rw [← hroot]; ring

private theorem theta_from_psi {x E F : ℝ} (hψ : |Chebyshev.psi x - x| ≤ E)
    (hF : Chebyshev.psi x - Chebyshev.theta x ≤ F) : |Chebyshev.theta x - x| ≤ E + F := by
  have hd := sub_nonneg.mpr (Chebyshev.theta_le_psi x)
  obtain ⟨hlo,hhi⟩ := abs_le.mp hψ
  rw [abs_le]; constructor <;> linarith

private theorem theta_refined (hRH : RiemannHypothesis) {x : ℝ} (hx : 10^12 ≤ x) :
    |Chebyshev.theta x - x| ≤ √x * (Real.log x ^ 2 / (8 * π) - 0.18 * Real.log x + 4) := by
  have h := Conjectures.Goldbach.ExplicitPsiSubTheta_aux.bound (x := x) (by linarith)
  have hf := sixth_root_log hx
  have hd : Chebyshev.psi x - Chebyshev.theta x ≤ 2 * √x := by
    have h4 := mul_le_mul_of_nonneg_right log_four_upper (Real.sqrt_nonneg x)
    nlinarith only [h.2, hf, h4]
  apply (theta_from_psi (psi_refined hRH (by linarith : 30000 ≤ x)) hd).trans
  ring_nf; rfl

private theorem theta_mid (hRH : RiemannHypothesis) {x : ℝ} (hx : 100 ≤ x) :
    |Chebyshev.theta x - x| ≤ 2 * √x * Real.log x ^ 2 := by
  have hx1 : 1 ≤ x := by linarith
  have hL' := log_ge_dyadic (k := 6) (x := x) (by norm_num; linarith)
  have hL : 4 ≤ Real.log x := by norm_num at hL'; linarith
  have h13 : x ^ (1/3 : ℝ) ≤ √x := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hdiff := (Conjectures.Goldbach.ExplicitPsiSubTheta_aux.bound (x := x) (by linarith)).2
  have h₂ : Chebyshev.psi x - Chebyshev.theta x ≤ √x * Real.log x ^ 2 := by
    have h₁ : Real.log 4 + 2 * Real.log x ≤ Real.log x ^ 2 := by nlinarith [log_four_upper, sq_nonneg (Real.log x - 2)]
    have h₃ := mul_le_mul_of_nonneg_right h13 (show 0 ≤ Real.log x by linarith)
    nlinarith only [hdiff, h₃, mul_le_mul_of_nonneg_left h₁ (Real.sqrt_nonneg x)]
  have hψ : |Chebyshev.psi x - x| ≤ √x * Real.log x ^ 2 := by
    have h := if hx' : 30000 ≤ x then (SchoenfeldRH.schoenfeld_large_of_RH hRH x hx').le
      else (SchoenfeldRH.schoenfeld_small x (by linarith) (le_of_not_ge hx')).le
    exact h.trans (div_le_self (by positivity) (by linarith [Real.pi_gt_three]))
  nlinarith only [theta_from_psi hψ h₂]

private theorem theta_high (hRH : RiemannHypothesis) {x : ℝ} (hx : 10^12 ≤ x) :
    |Chebyshev.theta x - x| ≤ √x * Real.log x ^ 2 / (8 * π) := by
  have hL := log_ge_dyadic (k := 39) (x := x) (by norm_num at hx ⊢; linarith)
  norm_num at hL
  have hdrop : Real.log x ^ 2 / (8 * π) - 0.18 * Real.log x + 4 ≤ Real.log x ^ 2 / (8 * π) := by linarith
  exact (theta_refined hRH hx).trans (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hdrop (Real.sqrt_nonneg x))


private noncomputable def g (t : ℝ) := Chebyshev.theta t / (t * Real.log t ^ 2) - 1 / Real.log t ^ 2

private theorem g_form {t : ℝ} (ht : 0 < t) : g t = (Chebyshev.theta t - t) / (t * Real.log t ^ 2) := by
  unfold g
  by_cases hz : Real.log t = 0
  · simp [hz]
  · field_simp

private theorem g_integrable {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) : IntervalIntegrable g volume a b := by
  have hF {s : ℝ} (hs : 2 ≤ s) : IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / (t * Real.log t ^ 2)) volume 2 s :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hs).mpr (Chebyshev.integrableOn_theta_div_id_mul_log_sq s)
  exact ((hF ha).symm.trans (hF hb)).sub (Chebyshev.intervalIntegrable_one_div_log_sq (by linarith) (by linarith))

private theorem prime_count_identity {x : ℝ} (hx : 2 ≤ x) (d : ℝ) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) - ((∫ t in (2 : ℝ)..x, 1 / Real.log t) + d) =
      (Chebyshev.theta x - x) / Real.log x + (∫ t in (2 : ℝ)..x, g t) + (2 / Real.log 2 - d) := by
  have hU : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    intro t ht
    have hp : 1 < t := by linarith [ht.1]
    exact (continuousAt_const.div (Real.continuousAt_log (by linarith)) (Real.log_pos hp).ne').continuousWithinAt
  have hV := Chebyshev.intervalIntegrable_one_div_log_sq (a := (2:ℝ)) (b := x) (by norm_num) (by linarith)
  have hF : IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / (t * Real.log t ^ 2)) volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr (Chebyshev.integrableOn_theta_div_id_mul_log_sq x)
  have hpart := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => t / Real.log t) (f' := fun t => 1 / Real.log t - 1 / Real.log t^2)
    (a := (2:ℝ)) (b := x) (fun t ht => by
      rw [Set.uIcc_of_le hx] at ht
      have hpos : t ≠ 0 := by linarith [ht.1]
      have hlog := (Real.log_pos (by linarith [ht.1] : 1 < t)).ne'
      have hder := (hasDerivAt_id t).div (Real.hasDerivAt_log hpos) hlog
      have hident : 1 / Real.log t - 1 / Real.log t ^ 2 =
          (1 * Real.log t - id t * t⁻¹) / Real.log t ^ 2 := by
        field_simp [hpos,hlog]
        change (Real.log t - 1) * t = Real.log t * t - t
        ring
      rw [hident]
      exact hder) (hU.sub hV)
  rw [intervalIntegral.integral_sub hU hV] at hpart
  rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral hx, sub_div]
  simp only [g, intervalIntegral.integral_sub hF hV]
  linarith

private theorem integral_g_bound {a b c : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c)
    (hb : ∀ t ∈ Set.Icc a b, |Chebyshev.theta t - t| ≤ c * √t * Real.log t^2) :
    |∫ t in a..b, g t| ≤ 2*c*√b := by
  have hi : IntervalIntegrable (fun t : ℝ => c / √t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    intro t ht
    exact (continuousAt_const.div Real.continuous_sqrt.continuousAt (Real.sqrt_pos.mpr (by linarith [ht.1])).ne').continuousWithinAt
  have hmono : |∫ t in a..b, g t| ≤ ∫ t in a..b, c / √t := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le hab _ hi
    apply Filter.Eventually.of_forall
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hs := Real.sqrt_pos.mpr ht0
    have hL := Real.log_pos (by linarith [ht.1] : 1 < t)
    rw [Real.norm_eq_abs, g_form ht0, abs_div, abs_of_pos (mul_pos ht0 (sq_pos_of_pos hL))]
    calc _ ≤ (c * √t * Real.log t ^ 2) / (t * Real.log t ^ 2) :=
           div_le_div_of_nonneg_right (hb t ⟨ht.1.le,ht.2⟩) (by positivity)
         _ = c / √t := by field_simp; nlinarith [Real.sq_sqrt ht0.le]
  have hev : ∫ t in a..b, c / √t = 2*c*√b - 2*c*√a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => 2*c*√t) _ hi
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    convert (Real.hasDerivAt_sqrt ht0.ne').const_mul (2*c) using 1
    field_simp
  rw [hev] at hmono
  linarith [mul_nonneg (show 0 ≤ 2*c by positivity) (Real.sqrt_nonneg a)]

private theorem integral_tail (hRH : RiemannHypothesis) {x : ℝ} (hx : 10^12 ≤ x) :
    |∫ t in (2:ℝ)..x, g t| ≤ 4000400 + 0.08 * √x := by
  let K : ℝ := 10^12
  have hK : (100:ℝ) ≤ K := by norm_num [K]
  have hkroot : Real.sqrt K = 1000000 := by rw [show K = (1000000 : ℝ)^2 by norm_num [K], Real.sqrt_sq (by norm_num)]
  have hsmall : |∫ t in (2:ℝ)..100, g t| ≤ 400 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (2:ℝ)) (b := 100) (f := g) (C := 4) (fun t ht => by
      rw [Set.uIoc_of_le (by norm_num : (2:ℝ) ≤ 100)] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      have hlog : 1/2 ≤ Real.log t := by
        linarith [Real.log_le_log (by norm_num : (0:ℝ)<2) ht.1.le, Real.log_two_gt_d9]
      have hth := Chebyshev.theta_le_log4_mul_x ht0.le
      have htAbs : |Chebyshev.theta t - t| ≤ t := by
        rw [abs_le]; constructor
        · linarith [Chebyshev.theta_nonneg t]
        · nlinarith [mul_le_mul_of_nonneg_right log_four_upper ht0.le]
      rw [Real.norm_eq_abs, g_form ht0, abs_div, abs_of_pos (mul_pos ht0 (by positivity : 0 < Real.log t ^ 2))]
      apply (div_le_iff₀ (by positivity)).2
      have h₁ : 1 ≤ 4 * Real.log t ^ 2 := by nlinarith [sq_nonneg (Real.log t - 1 / 2)]
      nlinarith only [htAbs, mul_le_mul_of_nonneg_left h₁ ht0.le])
    rw [Real.norm_eq_abs] at h
    norm_num at h
    linarith
  have hmid := integral_g_bound (a := 100) (b := K) (c := 2) (by norm_num) hK (by norm_num)
    (fun t ht => theta_mid hRH ht.1)
  rw [hkroot] at hmid
  have hhigh := integral_g_bound (a := K) (b := x) (c := 1 / (8 * π)) (by norm_num [K]) hx (by positivity)
    (fun t ht => by convert theta_high hRH ht.1 using 1; ring)
  have hc : 2 * (1 / (8 * π)) ≤ (0.08 : ℝ) := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith [Real.pi_gt_d4]
  have hI {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) := g_integrable ha hb
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := (2:ℝ)) (b := K) (c := x) (hI le_rfl (by norm_num [K])) (hI (by norm_num [K]) (by linarith : 2 ≤ x)),
      ← intervalIntegral.integral_add_adjacent_intervals (a := (2:ℝ)) (b := 100) (c := K) (hI le_rfl (by norm_num)) (hI (by norm_num) (by norm_num [K]))]
  calc _ ≤ (|∫ t in (2:ℝ)..100, g t| + |∫ t in (100:ℝ)..K, g t|) + |∫ t in K..x, g t| :=
           (abs_add_le ..).trans (add_le_add (abs_add_le ..) le_rfl)
       _ ≤ _ := by
         have h := add_le_add (add_le_add hsmall hmid) (hhigh.trans (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg x)))
         convert h using 1; ring


private noncomputable def offset : ℝ := Real.eulerMascheroniConstant + Real.log (Real.log 2) +
  ∑' k : ℕ, (Real.log 2)^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))

private theorem offset_bound : |2 / Real.log 2 - offset| ≤ 10 := by
  let u (k : ℕ) := (Real.log 2)^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))
  have h₀ : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h₁ : Real.log 2 ≤ 3/4 := by linarith [Real.log_two_lt_d9]
  have hu : ∀ k, 0 ≤ u k := fun k => by dsimp [u]; positivity
  have hmajor (k : ℕ) : u k ≤ ((3/4 : ℝ)^k) := by
    have hf : (1 : ℝ) ≤ (k+1).factorial := by exact_mod_cast Nat.factorial_pos (k+1)
    have hk : (1 : ℝ) ≤ ↑(k+1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    dsimp [u]
    calc _ ≤ (Real.log 2) ^ (k+1) := div_le_self (by positivity) (one_le_mul_of_one_le_of_one_le hk hf)
         _ ≤ (3/4 : ℝ)^(k+1) := pow_le_pow_left₀ h₀ h₁ _
         _ ≤ _ := by rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) (by norm_num)
  have hgeo := summable_geometric_of_lt_one (by norm_num : 0 ≤ (3/4 : ℝ)) (by norm_num)
  have hsum0 : 0 ≤ ∑' k, u k := tsum_nonneg hu
  have hsum := (hgeo.of_nonneg_of_le hu hmajor).tsum_le_tsum hmajor hgeo
  rw [tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 3/4) (by norm_num)] at hsum
  norm_num at hsum
  have hlower : -(Real.log 2) ≤ Real.log (Real.log 2) := by
    calc -Real.log 2 = Real.log (1 / 2 : ℝ) := by rw [one_div, Real.log_inv]
         _ ≤ _ := Real.log_le_log (by norm_num) (by linarith [Real.log_two_gt_d9])
  have hupper : Real.log (Real.log 2) ≤ 0 := Real.log_nonpos h₀ (by linarith)
  have hdiv : 2 / Real.log 2 ≤ 4 := (div_le_iff₀ (by positivity)).mpr (by linarith [Real.log_two_gt_d9])
  change |2 / Real.log 2 - (Real.eulerMascheroniConstant + Real.log (Real.log 2) + ∑' k, u k)| ≤ 10
  rw [abs_le]; constructor <;> linarith [Real.one_half_lt_eulerMascheroniConstant,
    Real.eulerMascheroniConstant_lt_two_thirds, (show 0 ≤ 2 / Real.log 2 by positivity)]

private theorem pi_tail (hRH : RiemannHypothesis) {x : ℝ} (hx : 4 * 10^18 ≤ x) :
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - ((∫ t in (2 : ℝ)..x, 1 / Real.log t) + offset)| ≤
      √x * Real.log x / (8 * π) := by
  have hlog := log_ge_dyadic (k := 61) (x := x) (by norm_num at hx ⊢; linarith)
  norm_num at hlog
  have hlogpos : 0 < Real.log x := by linarith
  have hroot : 2000000000 ≤ √x := Real.le_sqrt_of_sq_le (by norm_num at hx ⊢; linarith)
  have hfrac : 4 / Real.log x ≤ 0.096 := (div_le_iff₀ hlogpos).2 (by linarith)
  have hxK : (10:ℝ)^12 ≤ x := by linarith
  have hend : |(Chebyshev.theta x - x) / Real.log x| ≤ √x * Real.log x / (8 * π) - 0.084 * √x := by
    rw [abs_div,abs_of_pos hlogpos]
    calc _ ≤ (√x * (Real.log x^2/(8*π) - 0.18*Real.log x + 4)) / Real.log x :=
           div_le_div_of_nonneg_right (theta_refined hRH hxK) hlogpos.le
         _ = √x * Real.log x / (8*π) - 0.18 * √x + √x * (4 / Real.log x) := by
           field_simp [hlogpos.ne', Real.pi_ne_zero]
         _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left hfrac (Real.sqrt_nonneg x)]
  rw [prime_count_identity (by linarith : 2 ≤ x)]
  calc _ ≤ (|(Chebyshev.theta x - x) / Real.log x| + |∫ t in (2:ℝ)..x, g t|) + |2 / Real.log 2 - offset| :=
            (abs_add_le ..).trans (add_le_add (abs_add_le ..) le_rfl)
       _ ≤ _ := by linarith only [hend, integral_tail hRH hxK, offset_bound, hroot]

section
open Complex Real

private theorem rh_of_half_plane
    (h : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) : RiemannHypothesis := by
  intro s hzero htriv hs1
  by_contra hre
  rcases lt_or_gt_of_ne hre with hlt | hgt
  swap
  · exact h s hgt hs1 hzero
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hzero
    norm_num at hzero
  have hw : 1 / 2 < (1 - s).re := by
    rw [sub_re, one_re]
    linarith
  have hw1 : 1 - s ≠ 1 := fun h0 => hs0 (by linear_combination -h0)
  have hwn : ∀ n : ℕ, 1 - s ≠ -n := by
    intro n h0
    have := congrArg re h0
    rw [neg_re, natCast_re] at this
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hfe := riemannZeta_one_sub hwn hw1
  rw [sub_sub_cancel, hzero] at hfe
  have hζ : riemannZeta (1 - s) ≠ 0 := h _ hw hw1
  have hΓ : Gamma (1 - s) ≠ 0 := Gamma_ne_zero hwn
  have hpow : (2 * (π : ℂ)) ^ (-(1 - s)) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    exact fun h0 => mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero) h0.1
  have hcos : cos (π * (1 - s) / 2) = 0 := by
    by_contra hc
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpow) hΓ) hc) hζ hfe.symm
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.1 hcos
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hsk : s = -2 * (k : ℂ) := by
    have h3 : (π : ℂ) * (s + 2 * k) = 0 := by linear_combination -2 * hk
    have h4 := (mul_eq_zero.1 h3).resolve_left hπ
    linear_combination h4
  have hk1 : 1 ≤ k := by
    by_contra hk1
    have hk0 : k ≤ 0 := by omega
    rcases eq_or_lt_of_le hk0 with hk0 | hk0
    · exact hs0 (by simp [hsk, hk0])
    · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
      have : s.re = -2 * (k : ℝ) := by simp [hsk]
      linarith
  refine htriv ⟨(k - 1).toNat, ?_⟩
  have hcast : (((k - 1).toNat : ℤ) : ℂ) = ((k - 1 : ℤ) : ℂ) := by
    rw [Int.toNat_of_nonneg (by omega)]
  rw [Int.cast_natCast] at hcast
  rw [hcast, hsk]
  push_cast
  ring

end
end SchoenfeldPrimeTail

open SchoenfeldPrimeTail

theorem Conjectures.Cuts.Task3b37bc2419c6ad18e55c6e6b : ((∀ (x1 : ℕ) [x2 : NeZero x1] (x3 : DirichletCharacter ℂ x1) (x4 : ℂ), (1 / 2 : ℝ) < x4.re → x3 ≠ (1 : DirichletCharacter ℂ x1) ∨ x4 ≠ (1 : ℂ) → DirichletCharacter.LFunction x3 x4 ≠ (0 : ℂ)) → ∀ (x2 : ℝ), (4 : ℝ) * (10 : ℝ) ^ (18 : ℕ) ≤ x2 → |↑(Finset.filter Nat.Prime (Finset.range (⌊x2⌋₊ + (1 : ℕ)))).card - ((∫ (x4 : ℝ) in (2 : ℝ)..x2, (1 : ℝ) / Real.log x4) + (Real.eulerMascheroniConstant + Real.log (Real.log (2 : ℝ)) + ∑' (x4 : ℕ), Real.log (2 : ℝ) ^ (x4 + (1 : ℕ)) / (↑(x4 + (1 : ℕ)) * ↑(x4 + (1 : ℕ)).factorial)))| ≤ √x2 * Real.log x2 / ((8 : ℝ) * Real.pi)) := by
  intro h x hx
  have hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
    intro s hs hne
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      h 1 (1 : DirichletCharacter ℂ 1) s hs (Or.inr hne)
  simpa only [← Nat.primesLE_eq_filter_range, Nat.primesLE_card_eq_primeCounting, offset] using
    pi_tail (rh_of_half_plane hz) hx
