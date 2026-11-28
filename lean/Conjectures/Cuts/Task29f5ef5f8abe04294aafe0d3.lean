import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace SelbergSmallWidth
open MeasureTheory Set

private theorem jump (y : ℝ) (hy : 0 ≤ y) :
    Chebyshev.theta (y+1) - Chebyshev.theta y ≤ Real.log (y+1) := by
  have hset : Finset.Ioc 0 (⌊y⌋₊+1) =
      insert (⌊y⌋₊+1) (Finset.Ioc 0 ⌊y⌋₊) := by
    ext k
    simp only [Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hnot : ⌊y⌋₊+1 ∉ Finset.Ioc 0 ⌊y⌋₊ := by simp
  rw [Chebyshev.theta, Chebyshev.theta, Nat.floor_add_one hy, hset,
    Finset.sum_filter, Finset.sum_filter, Finset.sum_insert hnot, add_sub_cancel_right]
  split_ifs with h
  · exact Real.log_le_log (by positivity) (by push_cast; linarith [Nat.floor_le hy])
  · exact Real.log_nonneg (by linarith)

private theorem first_moment (x c : ℝ) (hc : 1 ≤ c) (hcx : c ≤ x) :
    (∫ y in (1:ℝ)..x, (Chebyshev.theta (c*y) - Chebyshev.theta y)) ≤
      (c*x-x) * Chebyshev.theta (c*x) := by
  have hc0 : 0 < c := by linarith
  have hx : 0 ≤ x := by linarith
  have hxx : x ≤ c*x := by nlinarith
  have hmono : Monotone (fun y : ℝ => Chebyshev.theta (c*y)) :=
    Chebyshev.theta_mono.comp (fun _ _ h => mul_le_mul_of_nonneg_left h hc0.le)
  have hi (a b : ℝ) : IntervalIntegrable Chebyshev.theta volume a b :=
    Chebyshev.theta_mono.intervalIntegrable
  rw [intervalIntegral.integral_sub hmono.intervalIntegrable (hi 1 x),
    intervalIntegral.integral_comp_mul_left _ hc0.ne',mul_one,smul_eq_mul]
  have hpositive : 0 ≤ ∫ y in c..c*x, Chebyshev.theta y :=
    intervalIntegral.integral_nonneg_of_forall (hcx.trans hxx) Chebyshev.theta_nonneg
  have hsmall : 0 ≤ ∫ y in (1:ℝ)..c, Chebyshev.theta y :=
    intervalIntegral.integral_nonneg_of_forall hc Chebyshev.theta_nonneg
  have hfac : c⁻¹ ≤ 1 := (inv_le_one₀ hc0).mpr hc
  have h₁ := intervalIntegral.integral_add_adjacent_intervals (hi 1 c) (hi c x)
  have h₂ := intervalIntegral.integral_add_adjacent_intervals (hi c x) (hi x (c*x))
  have h₃ := intervalIntegral.integral_mono_on hxx (hi x (c*x))
    (intervalIntegrable_const (c := Chebyshev.theta (c*x))) (fun y hy => Chebyshev.theta_mono hy.2)
  rw [intervalIntegral.integral_const,smul_eq_mul] at h₃
  linarith [mul_le_mul_of_nonneg_right hfac hpositive]

theorem integrated_small_width (x δ : ℝ) (hx : 100 ≤ x) (hd : 0 < δ)
    (hd' : δ ≤ 1/100) (ht : δ*x ≤ 1) :
    (∫ y in (1:ℝ)..x, (Chebyshev.theta ((1+δ)*y) - Chebyshev.theta y - δ*y)^2) ≤
      (5/2:ℝ)*δ*Real.log ((20001/10000:ℝ)/δ)*x^2 := by
  let c := 1+δ
  let L := Real.log ((20001/10000:ℝ)/δ)
  let f := fun y : ℝ => Chebyshev.theta (c*y)-Chebyshev.theta y
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hc : 1 ≤ c := by dsimp [c]; linarith
  have hc0 : 0 < c := by linarith
  have hcx : c ≤ x := by dsimp [c]; linarith
  have hL : 1 ≤ L := by
    have hg : (4:ℝ) ≤ (20001/10000:ℝ)/δ := (le_div_iff₀ hd).mpr (by linarith)
    have hl : (1:ℝ) ≤ Real.log 4 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith [Real.log_two_gt_d9]
    exact hl.trans (Real.log_le_log (by norm_num) hg)
  have hcmono : Monotone (fun y : ℝ => Chebyshev.theta (c*y)) :=
    Chebyshev.theta_mono.comp (fun _ _ h => mul_le_mul_of_nonneg_left h hc0.le)
  have hfi : IntervalIntegrable f volume 1 x :=
    hcmono.intervalIntegrable.sub Chebyshev.theta_mono.intervalIntegrable
  have hgi : IntervalIntegrable (fun y => L*f y+δ*x) volume 1 x :=
    (hfi.const_mul L).add intervalIntegrable_const
  have bound (y : ℝ) (hy : y ∈ Icc 1 x) : (f y - δ*y)^2 ≤ L*f y+δ*x := by
    have hy0 : 0 ≤ y := by linarith [hy.1]
    have hdy : δ*y ≤ δ*x := mul_le_mul_of_nonneg_left hy.2 hd.le
    have hfy0 : 0 ≤ f y := sub_nonneg.mpr
      (Chebyshev.theta_mono (by dsimp [c]; nlinarith [mul_nonneg hd.le hy0]))
    have hj : f y ≤ Real.log (y+1) := by
      apply le_trans (sub_le_sub_right (Chebyshev.theta_mono (show c*y ≤ y+1 by
        dsimp [c]; linarith)) _)
      exact jump _ hy0
    have hfy : f y ≤ L := hj.trans (Real.log_le_log (by linarith)
      ((le_div_iff₀ hd).mpr (by nlinarith)))
    have ht0 : 0 ≤ δ*y := mul_nonneg hd.le hy0
    nlinarith [mul_nonneg hfy0 (sub_nonneg.mpr hfy), mul_nonneg hfy0 ht0,
      mul_nonneg ht0 (sub_nonneg.mpr (hdy.trans ht))]
  have hmeas : Measurable (fun y => (f y - δ*y)^2) :=
    ((hcmono.measurable.sub Chebyshev.theta_mono.measurable).sub
      (measurable_const.mul measurable_id)).pow_const 2
  have hsi : IntervalIntegrable (fun y => (f y - δ*y)^2) volume 1 x := by
    apply hgi.mono_fun' hmeas.aestronglyMeasurable
    rw [Set.uIoc_of_le hx1]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f y-δ*y))] using bound y ⟨hy.1.le,hy.2⟩
  have hm := first_moment x c hc hcx
  have hfour : Real.log 4 ≤ 7/5 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9]
  have htheta : Chebyshev.theta (c*x) ≤ (3/2)*x := by
    apply (Chebyshev.theta_le_log4_mul_x (by positivity)).trans
    apply le_trans (mul_le_mul_of_nonneg_right hfour (mul_nonneg hc0.le hx0.le))
    dsimp [c]
    nlinarith [mul_le_mul_of_nonneg_right hd' hx0.le]
  change (∫ y in (1:ℝ)..x, (f y-δ*y)^2) ≤ (5/2:ℝ)*δ*L*x^2
  apply (intervalIntegral.integral_mono_on hx1 hsi hgi bound).trans
  rw [intervalIntegral.integral_add (hfi.const_mul L) intervalIntegrable_const,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const,smul_eq_mul]
  have he : c*x-x = δ*x := by dsimp [c]; ring
  change (∫ y in (1:ℝ)..x, f y) ≤ _ at hm
  rw [he] at hm
  have hmul := mul_le_mul_of_nonneg_left (hm.trans (mul_le_mul_of_nonneg_left htheta
    (mul_nonneg hd.le hx0.le))) (by linarith : 0 ≤ L)
  nlinarith [mul_nonneg (sub_nonneg.mpr hL) (mul_nonneg hd.le (sq_nonneg x)),
    mul_nonneg hd.le hx0.le]

end SelbergSmallWidth

theorem Conjectures.Cuts.Task29f5ef5f8abe04294aafe0d3 : ∀ x δ : ℝ, 100 ≤ x → 0 < δ → δ ≤ 1/100 → δ*x ≤ 1 →
    (intervalIntegral (fun y : ℝ => (Chebyshev.theta ((1+δ)*y)-Chebyshev.theta y-δ*y)^2)
      (1:ℝ) x MeasureTheory.volume) ≤ (5/2:ℝ)*δ*Real.log ((20001/10000:ℝ)/δ)*x^2 :=
  SelbergSmallWidth.integrated_small_width
