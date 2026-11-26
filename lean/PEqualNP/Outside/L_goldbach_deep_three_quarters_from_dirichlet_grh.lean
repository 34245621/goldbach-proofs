import Mathlib


/-!
Conditional analytic proof for the deep three-quarters task.
The critical-line input is explicit in the final theorem.

The logarithmic derivative, residue and finite-character machinery is adapted
from DNZJSJ's goldbach-proofs PR #2486, f3613cf846dfb3e7fe7d04fe6ce51c6ee25e7d4f (Apache-2.0).
The dyadic oscillatory integral estimates are from 34245621's PR #2511,
cba708bd00210b8e17a7f7f9d5e48b74599f48c5. The Dirichlet approximation and rational main-term
estimates are from Esythium's PR #2512 at 9117b0e8465c7323ed09c4673b5ceac9a7ef8118.
The continuous Mellin window, contour to the right of the critical line,
uniform additive-twist transfer and dyadic summation connect those inputs.
-/

section
namespace GoldbachSmoothing

open Complex DirichletCharacter MeasureTheory
open scoped BigOperators

noncomputable section

def twistedCoefficient {q : ℕ} (χ : DirichletCharacter ℂ q) : ℕ → ℂ :=
  (fun n : ℕ => χ (n : ZMod q)) * (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))

theorem twistedCoefficient_zero {q : ℕ} (χ : DirichletCharacter ℂ q) :
    twistedCoefficient χ 0 = 0 := by
  simp [twistedCoefficient]

theorem LSeries_twistedCoefficient_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (twistedCoefficient χ) s = -logDeriv (LFunction χ) s := by
  rw [twistedCoefficient, χ.LSeries_twist_vonMangoldt_eq hs,
    ← χ.deriv_LFunction_eq_deriv_LSeries hs, ← χ.LFunction_eq_LSeries hs]
  simp only [logDeriv, Pi.div_apply, neg_div]
end
end GoldbachSmoothing
open scoped BigOperators Topology
open Asymptotics Complex Filter Finset MeasureTheory Set

noncomputable section

namespace GoldbachGrhGrowth

variable {q : ℕ} [NeZero q]

/-- The average value of a Dirichlet character over a full period. -/
def charMean (χ : DirichletCharacter ℂ q) : ℂ :=
  (q : ℂ)⁻¹ * ∑ a : ZMod q, χ a

open scoped Classical in
theorem charMean_eq (χ : DirichletCharacter ℂ q) :
    charMean χ = if χ = 1 then (q.totient : ℂ) / (q : ℂ) else 0 := by
  by_cases hχ : χ = 1
  · subst χ
    simp [charMean, MulChar.sum_one_eq_card_units,
      ZMod.card_units_eq_totient, div_eq_inv_mul]
  · simp only [charMean, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero, ite_eq_right hχ]

private theorem level_mul_charMean (χ : DirichletCharacter ℂ q) :
    (q : ℂ) * charMean χ = ∑ a : ZMod q, χ a := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  simp only [charMean, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]

theorem norm_charMean_le_one (χ : DirichletCharacter ℂ q) : ‖charMean χ‖ ≤ 1 := by
  classical
  by_cases hχ : χ = 1
  · simp only [charMean_eq, ite_eq_left hχ, norm_div, Complex.norm_natCast]
    apply (div_le_one (by exact_mod_cast q.pos_of_neZero)).2
    exact_mod_cast q.totient_le
  · simp [charMean_eq, hχ]

/-- The character sum over the positive integers at most `n`. -/
def charPartialSum (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  ∑ k ∈ range n, χ ((k + 1 : ℕ) : ZMod q)

omit [NeZero q] in
theorem norm_charPartialSum_le (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖charPartialSum χ n‖ ≤ (n : ℝ) := by
  calc
    _ ≤ ∑ k ∈ range n, ‖χ ((k + 1 : ℕ) : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ range n, (1 : ℝ) := Finset.sum_le_sum fun k _ => χ.norm_le_one _
    _ = n := by simp

private theorem sum_character_block (χ : DirichletCharacter ℂ q) (m : ℕ) :
    (∑ k ∈ range q, χ ((m + k : ℕ) : ZMod q)) = ∑ a : ZMod q, χ a := by
  let e : Fin q ≃ ZMod q :=
    { toFun := fun k => (k.val : ZMod q)
      invFun := fun a => ⟨a.val, a.val_lt⟩
      left_inv := fun k => Fin.ext (by simp [Nat.mod_eq_of_lt k.isLt])
      right_inv := ZMod.natCast_zmod_val }
  rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ => χ ((m + k : ℕ) : ZMod q)) q]
  refine Fintype.sum_equiv (e.trans (Equiv.addRight (m : ZMod q))) _ _ fun k => ?_
  change χ ((m + k.val : ℕ) : ZMod q) = χ ((k.val : ZMod q) + (m : ZMod q))
  rw [Nat.cast_add, add_comm]

/-- The centered character sum at a natural-number endpoint. -/
def integerRemainder (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  charPartialSum χ n - (n : ℂ) * charMean χ

theorem integerRemainder_periodic (χ : DirichletCharacter ℂ q) :
    Function.Periodic (integerRemainder χ) q := by
  intro n
  have hBlock : (∑ k ∈ range q, χ ((n + k + 1 : ℕ) : ZMod q)) = ∑ a : ZMod q, χ a := by
    simpa only [Nat.add_assoc, Nat.add_comm 1] using sum_character_block χ (n + 1)
  simp only [integerRemainder, charPartialSum, Finset.sum_range_add]
  rw [hBlock]
  simp only [Nat.cast_add, add_mul, level_mul_charMean]
  abel

theorem norm_integerRemainder_le (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖integerRemainder χ n‖ ≤ 2 * (q : ℝ) := by
  rw [← (integerRemainder_periodic χ).map_mod_nat n]
  let r := n % q
  have hr : (r : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.mod_lt n q.pos_of_neZero).le
  calc
    _ ≤ ‖charPartialSum χ r‖ + ‖(r : ℂ) * charMean χ‖ := norm_sub_le _ _
    _ ≤ (r : ℝ) + (r : ℝ) := by
      refine add_le_add (norm_charPartialSum_le χ r) ?_
      rw [norm_mul, Complex.norm_natCast]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (norm_charMean_le_one χ) r.cast_nonneg
    _ ≤ _ := by linarith

/-- The centered character sum for real endpoints, extended by zero at `x ≤ 1`. -/
def periodicRemainder (χ : DirichletCharacter ℂ q) : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator fun x => charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ

theorem norm_periodicRemainder_le (χ : DirichletCharacter ℂ q) (x : ℝ) :
    ‖periodicRemainder χ x‖ ≤ 3 * (q : ℝ) := by
  by_cases hx : x ∈ Ioi (1 : ℝ)
  · have hx0 : 0 ≤ x := zero_le_one.trans (mem_Ioi.mp hx).le
    have hd : ‖(⌊x⌋₊ : ℂ) - (x : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le hx0))]
      linarith [Nat.lt_floor_add_one x]
    have hsplit : charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ =
        integerRemainder χ ⌊x⌋₊ + ((⌊x⌋₊ : ℂ) - (x : ℂ)) * charMean χ := by
      unfold integerRemainder
      ring
    rw [periodicRemainder, indicator_of_mem hx, hsplit]
    calc
      _ ≤ ‖integerRemainder χ ⌊x⌋₊‖ + ‖((⌊x⌋₊ : ℂ) - (x : ℂ)) * charMean χ‖ :=
        norm_add_le _ _
      _ ≤ 2 * (q : ℝ) + 1 := by
        refine add_le_add (norm_integerRemainder_le χ _) ?_
        rw [norm_mul]
        simpa only [one_mul] using mul_le_mul hd (norm_charMean_le_one χ) (norm_nonneg _) zero_le_one
      _ ≤ _ := by
        have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt q.pos_of_neZero)
        linarith
  · rw [periodicRemainder, indicator_of_notMem hx, norm_zero]
    positivity

omit [NeZero q] in
private theorem measurable_partialSum_floor (χ : DirichletCharacter ℂ q) :
    Measurable (fun x : ℝ => charPartialSum χ ⌊x⌋₊) :=
  (measurable_of_countable (charPartialSum χ)).comp measurable_id.nat_floor

private theorem measurable_centeredCharSum (χ : DirichletCharacter ℂ q) :
    Measurable (fun x : ℝ => charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ) :=
  (measurable_partialSum_floor χ).sub (continuous_ofReal.measurable.mul_const _)

theorem measurable_periodicRemainder (χ : DirichletCharacter ℂ q) :
    Measurable (periodicRemainder χ) :=
  (measurable_centeredCharSum χ).indicator measurableSet_Ioi

/-- The Mellin transform of the centered sum, with exponent `-s-1` in the integral. -/
def remainderMellin (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  mellin (periodicRemainder χ) (-s)

theorem remainderMellin_eq_integral (χ : DirichletCharacter ℂ q) (s : ℂ) :
    remainderMellin χ s = ∫ x : ℝ in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) *
      (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ) := by
  have hIntegrand : (fun x : ℝ => (x : ℂ) ^ (-s - 1) • periodicRemainder χ x) =
      (Ioi (1 : ℝ)).indicator (fun x => (x : ℂ) ^ (-s - 1) *
        (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ)) := by
    ext x
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · simp only [periodicRemainder, indicator_of_mem hx, smul_eq_mul]
    · simp only [periodicRemainder, indicator_of_notMem hx, smul_zero]
  rw [remainderMellin, mellin, hIntegrand, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict_of_subset (Set.Ioi_subset_Ioi zero_le_one)]

private theorem norm_weightedRemainder_le (χ : DirichletCharacter ℂ q) (s : ℂ)
    {x : ℝ} (hx : x ∈ Ioi (1 : ℝ)) :
    ‖(x : ℂ) ^ (-s - 1) * (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ)‖ ≤
      (3 * (q : ℝ)) * x ^ (-s.re - 1) := by
  have hx0 : 0 < x := zero_lt_one.trans (mem_Ioi.mp hx)
  have hBound := norm_periodicRemainder_le χ x
  rw [periodicRemainder, indicator_of_mem hx] at hBound
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, sub_re, neg_re, one_re]
  exact (mul_le_mul_of_nonneg_left hBound (Real.rpow_nonneg hx0.le _)).trans_eq (mul_comm _ _)

private theorem weightedRemainder_integrableOn (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1) *
      (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ)) (Ioi (1 : ℝ)) := by
  have hp : -s.re - 1 < -1 := by linarith
  have hBound := (integrableOn_Ioi_rpow_of_lt hp zero_lt_one).const_mul (3 * (q : ℝ))
  refine Integrable.mono' hBound ?_ ?_
  · have hKernel : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) := by
      intro x hx
      exact (continuousAt_ofReal_cpow_const x _ (Or.inr (zero_lt_one.trans (mem_Ioi.mp hx)).ne')).continuousWithinAt
    exact (hKernel.aestronglyMeasurable measurableSet_Ioi).mul
      (measurable_centeredCharSum χ).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_weightedRemainder_le χ s hx

theorem norm_remainderMellin_le (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    ‖remainderMellin χ s‖ ≤ (3 * (q : ℝ)) / s.re := by
  rw [remainderMellin_eq_integral]
  have hp : -s.re - 1 < -1 := by linarith
  have hBound := (integrableOn_Ioi_rpow_of_lt hp zero_lt_one).const_mul (3 * (q : ℝ))
  refine (norm_integral_le_of_norm_le hBound ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_weightedRemainder_le χ s hx
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt hp zero_lt_one]
    rw [show -s.re - 1 + 1 = -s.re by ring, Real.one_rpow]
    simp only [div_neg, neg_div, neg_neg, mul_one_div]

theorem differentiableAt_remainderMellin (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 0 < s.re) : DifferentiableAt ℂ (remainderMellin χ) s := by
  have hLoc : LocallyIntegrableOn (periodicRemainder χ) (Ioi (0 : ℝ)) := by
    refine (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2 fun K _ hK => ?_
    exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne
      (measurable_periodicRemainder χ).aestronglyMeasurable
      (Eventually.of_forall (norm_periodicRemainder_le χ))
  have hTop : periodicRemainder χ =O[atTop] fun x : ℝ => x ^ (-(0 : ℝ)) := by
    refine IsBigO.of_bound (3 * (q : ℝ)) (Eventually.of_forall fun x => ?_)
    simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using norm_periodicRemainder_le χ x
  have hBot : periodicRemainder χ =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-(-s.re - 1)) := by
    refine IsBigO.of_bound 0 ?_
    have hNear : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) := nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
    filter_upwards [hNear] with x hx
    have hOutside : x ∉ Ioi (1 : ℝ) := fun h => (mem_Iio.mp hx).not_gt (mem_Ioi.mp h)
    simp only [periodicRemainder, indicator_of_notMem hOutside, norm_zero, zero_mul, le_refl]
  have hNeg : (-s).re < 0 := by simpa only [neg_re, neg_lt_zero] using hs
  have hAbove : -s.re - 1 < (-s).re := by rw [neg_re]; linarith
  exact (mellin_differentiableAt_of_isBigO_rpow hLoc hTop hNeg hBot hAbove).comp s
    differentiableAt_id.neg

omit [NeZero q] in
private def seriesCoefficient (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  if n = 0 then 0 else χ (n : ZMod q)

omit [NeZero q] in
private theorem sum_seriesCoefficient_eq (χ : DirichletCharacter ℂ q) (n : ℕ) :
    (∑ k ∈ Finset.Icc 0 n, seriesCoefficient χ k) = charPartialSum χ n := by
  rw [← Nat.range_succ_eq_Icc_zero, Finset.sum_range_succ']
  simp [seriesCoefficient, charPartialSum]

private theorem integral_centeringTerm (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1) * ((x : ℂ) * charMean χ)) (Ioi (1 : ℝ)) ∧
      (∫ x : ℝ in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) * ((x : ℂ) * charMean χ)) =
        charMean χ / (s - 1) := by
  have hPower : (-s).re < -1 := by rw [neg_re]; linarith
  have hIntegrand (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :
      (x : ℂ) ^ (-s - 1) * ((x : ℂ) * charMean χ) = charMean χ * (x : ℂ) ^ (-s) := by
    have hx0 : 0 < x := zero_lt_one.trans (Set.mem_Ioi.mp hx)
    have hProd : (x : ℂ) ^ (-s - 1) * (x : ℂ) = (x : ℂ) ^ (-s) := by
      simpa only [sub_add_cancel, cpow_one] using
        (cpow_add (-s - 1) 1 (ofReal_ne_zero.mpr hx0.ne')).symm
    rw [← mul_assoc, hProd, mul_comm]
  constructor
  · have hInt : IntegrableOn (fun x : ℝ => charMean χ * (x : ℂ) ^ (-s)) (Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_cpow_of_lt hPower zero_lt_one).const_mul (charMean χ)
    exact hInt.congr_fun (fun x hx => (hIntegrand x hx).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi hIntegrand, integral_const_mul,
      integral_Ioi_cpow_of_lt hPower zero_lt_one]
    rw [show -s + 1 = -(s - 1) by ring]
    simp only [ofReal_one, one_cpow, div_neg, neg_div, neg_neg, mul_one_div]

/-- Abel summation on the half-plane of absolute convergence. -/
theorem LFunction_eq_centeredMellin_of_one_lt_re (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) : DirichletCharacter.LFunction χ s =
      s * (remainderMellin χ s + charMean χ / (s - 1)) := by
  let f : ℝ → ℂ := fun x => (x : ℂ) ^ (-s)
  have hs0 : s ≠ 0 := by
    intro h
    norm_num [h] at hs
  have hDiff : ∀ x ∈ Ici (1 : ℝ), DifferentiableAt ℝ f x := by
    intro x hx
    exact (hasDerivAt_ofReal_cpow_const (zero_lt_one.trans_le (Set.mem_Ici.mp hx)).ne'
      (neg_ne_zero.mpr hs0)).differentiableAt
  have hDerivLoc : LocallyIntegrableOn (deriv f) (Ici (1 : ℝ)) := by
    have hNeg : (-s).re < 0 := by rw [neg_re]; linarith
    refine ((integrableOn_Ioi_deriv_ofReal_cpow (t := (1 / 2 : ℝ)) (by norm_num) hNeg).mono_set
      (fun x hx => ?_)).locallyIntegrableOn
    exact (by norm_num : (1 / 2 : ℝ) < 1).trans_le (Set.mem_Ici.mp hx)
  have hPowerLim : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - s.re)) atTop (𝓝 0) := by
    simpa only [neg_sub, Function.comp_def] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hs)).comp tendsto_natCast_atTop_atTop
  have hBoundary : Tendsto (fun n : ℕ => f n * ∑ k ∈ Finset.Icc 0 n, seriesCoefficient χ k)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hPowerLim
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    simp only [f, norm_mul, Complex.ofReal_natCast, norm_natCast_cpow_of_pos hn, neg_re,
      sum_seriesCoefficient_eq]
    calc
      _ ≤ (n : ℝ) ^ (-s.re) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left (norm_charPartialSum_le χ n) (Real.rpow_nonneg n.cast_nonneg _)
      _ = _ := by
        rw [← Real.rpow_add_one (Nat.cast_ne_zero.mpr hn.ne'), neg_add_eq_sub]
  have hSumDom : (fun x : ℝ => ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, seriesCoefficient χ k) =O[atTop]
      fun x : ℝ => x := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [sum_seriesCoefficient_eq, one_mul, Real.norm_of_nonneg hx.le]
    exact (norm_charPartialSum_le χ _).trans (Nat.floor_le hx.le)
  have hDerivativeDom : (fun x : ℝ => deriv f x * ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, seriesCoefficient χ k)
      =O[atTop] fun x : ℝ => x ^ (-s.re) := by
    refine ((isBigO_deriv_ofReal_cpow_const_atTop (-s)).mul hSumDom).congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [neg_re, ← Real.rpow_add_one hx.ne', sub_add_cancel]
  have hDominatingIntegral : IntegrableAtFilter (fun x : ℝ => x ^ (-s.re)) atTop :=
    ⟨Ioi (1 : ℝ), Ioi_mem_atTop _, integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one⟩
  have hAbel := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (seriesCoefficient χ)
    (by simp [seriesCoefficient]) hDiff hDerivLoc hBoundary hDerivativeDom hDominatingIntegral
  have hCoeff (n : ℕ) : f n * seriesCoefficient χ n =
      LSeries.term (fun k : ℕ => χ (k : ZMod q)) s n := by
    by_cases hn : n = 0
    · subst n
      simp [seriesCoefficient]
    · simp [f, seriesCoefficient, hn, cpow_neg, div_eq_inv_mul]
  have hSum : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n,
      f k * seriesCoefficient χ k) atTop (𝓝 (LSeries (fun k : ℕ => χ (k : ZMod q)) s)) := by
    simp_rw [hCoeff, ← Nat.range_succ_eq_Icc_zero]
    exact (χ.LSeriesSummable_of_one_lt_re hs).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hSeriesIdentity : DirichletCharacter.LFunction χ s = (0 : ℂ) -
      ∫ x : ℝ in Ioi (1 : ℝ), deriv f x * ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, seriesCoefficient χ k := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    exact tendsto_nhds_unique hSum hAbel
  calc
    _ = (0 : ℂ) - ∫ x : ℝ in Ioi (1 : ℝ), (-s) *
        ((x : ℂ) ^ (-s - 1) * charPartialSum χ ⌊x⌋₊) := by
      rw [hSeriesIdentity]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx0 : x ≠ 0 := (zero_lt_one.trans (Set.mem_Ioi.mp hx)).ne'
      simp only [f, deriv_ofReal_cpow_const (-s) hx0, sum_seriesCoefficient_eq, mul_assoc]
    _ = s * (∫ x : ℝ in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) * charPartialSum χ ⌊x⌋₊) := by
      rw [integral_const_mul, zero_sub, neg_mul, neg_neg]
    _ = _ := by
      have hSplit (x : ℝ) : (x : ℂ) ^ (-s - 1) * charPartialSum χ ⌊x⌋₊ =
          (x : ℂ) ^ (-s - 1) * (charPartialSum χ ⌊x⌋₊ - (x : ℂ) * charMean χ) +
            (x : ℂ) ^ (-s - 1) * ((x : ℂ) * charMean χ) := by ring
      simp_rw [hSplit]
      rw [integral_add (weightedRemainder_integrableOn χ (zero_lt_one.trans hs))
        (integral_centeringTerm χ hs).1, ← remainderMellin_eq_integral, (integral_centeringTerm χ hs).2]

private theorem eq_on_right_halfPlane {f g : ℂ → ℂ}
    (hf : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ f z)
    (hg : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ g z)
    (hfg : ∀ z : ℂ, 1 < z.re → f z = g z) {s : ℂ} (hs : 0 < s.re) : f s = g s := by
  let U : Set ℂ := {z | 0 < z.re}
  have hUOpen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUConnected : IsPreconnected U :=
    ((convex_Ioi (0 : ℝ)).linear_preimage reCLM.toLinearMap).isPreconnected
  have hFA : AnalyticOnNhd ℂ f U :=
    DifferentiableOn.analyticOnNhd (fun z hz => (hf z hz).differentiableWithinAt) hUOpen
  have hGA : AnalyticOnNhd ℂ g U :=
    DifferentiableOn.analyticOnNhd (fun z hz => (hg z hz).differentiableWithinAt) hUOpen
  have h2 : (2 : ℂ) ∈ U := by norm_num [U]
  have hAbsConv : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
  have hEq : f =ᶠ[𝓝 (2 : ℂ)] g := by
    filter_upwards [hAbsConv] with z hz
    exact hfg z hz
  exact hFA.eqOn_of_preconnected_of_eventuallyEq hGA hUConnected h2 hEq hs

/-- The centered Mellin representation of a nonprincipal L-function on the right half-plane. -/
theorem LFunction_eq_remainderMellin (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) : DirichletCharacter.LFunction χ s = s * remainderMellin χ s := by
  refine eq_on_right_halfPlane (f := DirichletCharacter.LFunction χ)
    (g := fun z : ℂ => z * remainderMellin χ z)
    (fun z _ => DirichletCharacter.differentiable_LFunction hχ z) ?_ ?_ hs
  · intro z hz
    exact differentiableAt_id.mul (differentiableAt_remainderMellin χ hz)
  · intro z hz
    rw [LFunction_eq_centeredMellin_of_one_lt_re χ hz]
    simp only [charMean_eq, ite_eq_right hχ, zero_div, add_zero]

/-- The Mellin representation of the principal L-function after removing its pole. -/
theorem LFunctionTrivChar₁_eq_remainderMellin {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunctionTrivChar₁ q s =
      (s - 1) * s * remainderMellin (1 : DirichletCharacter ℂ q) s +
        s * charMean (1 : DirichletCharacter ℂ q) := by
  let χ : DirichletCharacter ℂ q := 1
  refine eq_on_right_halfPlane (f := DirichletCharacter.LFunctionTrivChar₁ q)
    (g := fun z : ℂ => (z - 1) * z * remainderMellin χ z + z * charMean χ)
    (fun z _ => DirichletCharacter.differentiable_LFunctionTrivChar₁ q z) ?_ ?_ hs
  · intro z hz
    have hId : DifferentiableAt ℂ (fun w : ℂ => w) z := differentiableAt_id
    have hSub : DifferentiableAt ℂ (fun w : ℂ => w - 1) z := hId.sub_const 1
    exact (((hSub.mul hId).mul (differentiableAt_remainderMellin χ hz)).add (hId.mul_const _))
  · intro z hz
    have hz1 : z ≠ 1 := by
      intro h
      norm_num [h] at hz
    rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz1]
    change (z - 1) * DirichletCharacter.LFunction χ z = _
    rw [LFunction_eq_centeredMellin_of_one_lt_re χ hz]
    field_simp [sub_ne_zero.mpr hz1]

open scoped Classical in
/-- A uniform growth bound for the Dirichlet L-function, with the principal pole removed. -/
theorem norm_regularizedLFunction_le (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 / 8 ≤ s.re) :
    ‖(if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q s
      else DirichletCharacter.LFunction χ s)‖ ≤ 25 * (q : ℝ) * (1 + ‖s‖) ^ 2 := by
  have hs0 : 0 < s.re := (by norm_num : (0 : ℝ) < 1 / 8).trans_le hs
  have hRemainder : ‖remainderMellin χ s‖ ≤ 24 * (q : ℝ) := by
    calc
      _ ≤ (3 * (q : ℝ)) / s.re := norm_remainderMellin_le χ hs0
      _ ≤ (3 * (q : ℝ)) / (1 / 8 : ℝ) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hs
      _ = _ := by ring
  let M := 1 + ‖s‖
  have hM : 1 ≤ M := by
    dsimp [M]
    linarith [norm_nonneg s]
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hSM : ‖s‖ ≤ M := by
    dsimp [M]
    linarith
  have hSubM : ‖s - 1‖ ≤ M := by
    simpa only [M, norm_one, add_comm] using norm_sub_le s (1 : ℂ)
  have hMSq : M ≤ M ^ 2 := by
    rw [pow_two]
    exact le_mul_of_one_le_right hM0 hM
  have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt q.pos_of_neZero)
  have hMq : M ≤ (q : ℝ) * M ^ 2 :=
    hMSq.trans (le_mul_of_one_le_left (sq_nonneg _) hq)
  change ‖(if χ = 1 then _ else _)‖ ≤ 25 * (q : ℝ) * M ^ 2
  by_cases hχ : χ = 1
  · subst χ
    rw [ite_eq_left rfl, LFunctionTrivChar₁_eq_remainderMellin hs0]
    calc
      _ ≤ ‖(s - 1) * s * remainderMellin (1 : DirichletCharacter ℂ q) s‖ +
          ‖s * charMean (1 : DirichletCharacter ℂ q)‖ := norm_add_le _ _
      _ ≤ M ^ 2 * (24 * (q : ℝ)) + M := by
        apply add_le_add
        · simp only [norm_mul, pow_two]
          exact mul_le_mul (mul_le_mul hSubM hSM (norm_nonneg _) hM0) hRemainder
            (norm_nonneg _) (mul_nonneg hM0 hM0)
        · rw [norm_mul]
          simpa only [mul_one] using mul_le_mul hSM (norm_charMean_le_one (1 : DirichletCharacter ℂ q))
            (norm_nonneg _) hM0
      _ ≤ M ^ 2 * (24 * (q : ℝ)) + (q : ℝ) * M ^ 2 := add_le_add le_rfl hMq
      _ = _ := by ring
  · rw [ite_eq_right hχ, LFunction_eq_remainderMellin χ hχ hs0, norm_mul]
    calc
      _ ≤ M ^ 2 * (24 * (q : ℝ)) :=
        mul_le_mul (hSM.trans hMSq) hRemainder (norm_nonneg _) (sq_nonneg _)
      _ = 24 * (q : ℝ) * M ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num) q.cast_nonneg) (sq_nonneg _)

end GoldbachGrhGrowth

namespace Goldbach

private theorem summable_inv_sq_shift (k : ℕ) :
    Summable (fun n : ℕ ↦ (((n + k : ℕ) : ℝ) ^ 2)⁻¹) :=
  (summable_nat_add_iff (f := fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) k).mpr
    (Real.summable_nat_pow_inv.mpr (by decide))

private theorem inv_sq_tail_le_three_fourths :
    (∑' n : ℕ, (((n + 2 : ℕ) : ℝ) ^ 2)⁻¹) ≤ (3 / 4 : ℝ) := by
  let u : ℕ → ℝ := fun n ↦ ((n + 2 : ℕ) : ℝ)⁻¹
  have hTail : (∑' n : ℕ, (((n + 3 : ℕ) : ℝ) ^ 2)⁻¹) ≤ (1 / 2 : ℝ) := by
    apply le_of_tendsto' (summable_inv_sq_shift 3).hasSum.tendsto_sum_nat
    intro n
    calc
      _ ≤ ∑ m ∈ Finset.range n, (u m - u (m + 1)) := by
        apply Finset.sum_le_sum
        intro m _
        have hm₂ : 0 < (m : ℝ) + 2 := by positivity
        have hm₃ : 0 < (m : ℝ) + 3 := by positivity
        calc
          _ ≤ (((m : ℝ) + 2) * ((m : ℝ) + 3))⁻¹ := by
            rw [Nat.cast_add, Nat.cast_ofNat]
            apply inv_anti₀ (mul_pos hm₂ hm₃)
            rw [pow_two]
            exact mul_le_mul_of_nonneg_right (by linarith) hm₃.le
          _ = _ := by
            simp only [u, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
            rw [show (m : ℝ) + 1 + 2 = (m : ℝ) + 3 by ring]
            field_simp [hm₂.ne', hm₃.ne']
            ring
      _ = u 0 - u n := Finset.sum_range_sub' u n
      _ ≤ _ := (sub_le_self _ (by dsimp [u]; positivity)).trans_eq (by norm_num [u])
  have hSplit := (summable_inv_sq_shift 2).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.zero_add, Nat.add_assoc,
    show (1 + 2 : ℕ) = 3 by decide, Nat.cast_ofNat] at hSplit
  rw [← hSplit, show ((2 : ℝ) ^ 2)⁻¹ = 1 / 4 by norm_num]
  linarith only [hTail]

/-- A uniform positive lower bound for the Dirichlet L-function on `Re s = 2`. -/
theorem one_fourth_le_norm_LFunction_anchor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (1 / 4 : ℝ) ≤ ‖χ.LFunction (⟨2, t⟩ : ℂ)‖ := by
  let s : ℂ := ⟨2, t⟩
  let term : ℕ → ℂ := LSeries.term (fun n : ℕ ↦ χ (n : ZMod q)) s
  have hs : 1 < s.re := by norm_num [s]
  have hTerm : Summable term := χ.LSeriesSummable_of_one_lt_re hs
  have hLFunction : χ.LFunction s = ∑' n : ℕ, term n := χ.LFunction_eq_LSeries hs
  have hTerm01 : (∑ n ∈ Finset.range 2, term n) = 1 := by
    rw [show (2 : ℕ) = 1 + 1 by decide, Finset.sum_range_succ, Finset.sum_range_one]
    simp [term]
  have hSplit := hTerm.sum_add_tsum_nat_add 2
  rw [hTerm01] at hSplit
  have hTermTail : Summable (fun n : ℕ ↦ term (n + 2)) :=
    (summable_nat_add_iff (f := term) 2).mpr hTerm
  have hTermNorm (n : ℕ) : ‖term (n + 2)‖ ≤ (((n + 2 : ℕ) : ℝ) ^ 2)⁻¹ := by
    dsimp [term]
    rw [LSeries.norm_term_eq, ite_eq_right (by omega : n + 2 ≠ 0), show s.re = 2 from rfl,
      show (((n + 2 : ℕ) : ℝ) ^ (2 : ℝ)) = (((n + 2 : ℕ) : ℝ) ^ (2 : ℕ)) by
        exact Real.rpow_natCast _ 2, ← one_div]
    exact div_le_div_of_nonneg_right (χ.norm_le_one _) (by positivity)
  have hNormTail : ‖∑' n : ℕ, term (n + 2)‖ ≤ (3 / 4 : ℝ) :=
    (norm_tsum_le_tsum_norm hTermTail.norm).trans
      ((hTermTail.norm.tsum_le_tsum hTermNorm (summable_inv_sq_shift 2)).trans
        inv_sq_tail_le_three_fourths)
  have hSumNorm : (1 : ℝ) ≤ ‖χ.LFunction s‖ + ‖∑' n : ℕ, term (n + 2)‖ := calc
    _ = ‖(1 : ℂ)‖ := norm_one.symm
    _ = ‖χ.LFunction s - ∑' n : ℕ, term (n + 2)‖ := by
      rw [hLFunction, ← hSplit, add_sub_cancel_right]
    _ ≤ _ := norm_sub_le _ _
  change (1 / 4 : ℝ) ≤ ‖χ.LFunction s‖
  linarith only [hNormTail, hSumNorm]

/-- The same anchor bound after multiplication by the factor that cancels a pole at one. -/
theorem one_fourth_le_norm_mul_sub_one_LFunction_anchor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (1 / 4 : ℝ) ≤ ‖((⟨2, t⟩ : ℂ) - 1) * χ.LFunction (⟨2, t⟩ : ℂ)‖ := by
  have hFactor : (1 : ℝ) ≤ ‖(⟨2, t⟩ : ℂ) - 1‖ := by
    have h := Complex.re_le_norm ((⟨2, t⟩ : ℂ) - 1)
    change (2 : ℝ) - 1 ≤ _ at h
    linarith only [h]
  rw [norm_mul]
  exact (one_fourth_le_norm_LFunction_anchor χ t).trans
    (le_mul_of_one_le_left (norm_nonneg _) hFactor)

end Goldbach

namespace Goldbach

open Metric Set MeromorphicOn

/-- The zeros in the open critical strip at height at most one from `t`. -/
def criticalZeroSlice (f : ℂ → ℂ) (t : ℝ) : Set ℂ :=
  {z | 0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ 1 ∧ f z = 0}

private theorem jensen_mem_inner {z : ℂ} {t : ℝ} (hre : z.re = 1 / 2)
    (him : |z.im - t| ≤ 1) : z ∈ closedBall (⟨2, t⟩ : ℂ) (29 / 16) := by
  rw [mem_closedBall, dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 29 / 16)).mp
  have himSq : (z.im - t) ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr him
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, hre]
  nlinarith only [himSq]

private theorem jensen_re_of_mem_outer {z : ℂ} {t : ℝ}
    (hz : z ∈ closedBall (⟨2, t⟩ : ℂ) (15 / 8)) : 1 / 8 ≤ z.re := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have hre := (Complex.abs_re_le_norm (z - (⟨2, t⟩ : ℂ))).trans hz
  simp only [Complex.sub_re] at hre
  linarith only [(abs_le.mp hre).1]

private theorem jensen_norm_of_mem_outer {z : ℂ} {t : ℝ}
    (hz : z ∈ closedBall (⟨2, t⟩ : ℂ) (15 / 8)) : 1 + ‖z‖ ≤ 3 * (2 + |t|) := by
  rw [mem_closedBall, dist_eq_norm] at hz
  let center : ℂ := ⟨2, t⟩
  have hcenter : ‖center‖ ≤ 2 + |t| := by
    simpa [center] using Complex.norm_le_abs_re_add_abs_im center
  have hnorm : ‖z‖ ≤ ‖z - center‖ + ‖center‖ := by
    simpa only [sub_add_cancel] using norm_add_le (z - center) center
  linarith only [hz, hcenter, hnorm, abs_nonneg t]

private theorem jensen_analytic_outer {f : ℂ → ℂ} {t : ℝ}
    (hAnalytic : AnalyticOnNhd ℂ f {z | 0 < z.re}) :
    AnalyticOnNhd ℂ f (closedBall (⟨2, t⟩ : ℂ) (15 / 8)) := by
  intro z hz
  exact hAnalytic z (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 8)
    (jensen_re_of_mem_outer hz))

/-- For a holomorphic function with fixed growth and anchor bounds, the total divisor mass
in the closed disk of radius `29 / 16` about `2 + it` grows at most logarithmically. -/
theorem jensen_diskDivisor_bound {A b : ℝ} (hA : 0 < A) (hb : 0 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) (f : ℂ → ℂ) (t : ℝ), 0 < q →
      AnalyticOnNhd ℂ f {z | 0 < z.re} →
      (∀ z : ℂ, 1 / 8 ≤ z.re → ‖f z‖ ≤ A * (q : ℝ) * (1 + ‖z‖) ^ 2) →
      b ≤ ‖f (⟨2, t⟩ : ℂ)‖ →
      ((∑ᶠ z : ℂ, divisor f (closedBall (⟨2, t⟩ : ℂ) (29 / 16)) z : ℤ) : ℝ) ≤
        K * Real.log (2 * (q : ℝ) * (2 + |t|)) := by
  classical
  let r : ℝ := 29 / 16
  let R : ℝ := 15 / 8
  have hr : 0 < r := by norm_num [r]
  have hR : 0 < R := by norm_num [R]
  have hrR : r < R := by norm_num [r, R]
  let B : ℝ := 1 + 9 * A
  let bMin : ℝ := min 1 b
  let D : ℝ := B / bMin
  let logRatio : ℝ := Real.log (R / r)
  let logFactor : ℝ := 2 + Real.log D / Real.log 2
  have hB : 1 ≤ B := by dsimp [B]; linarith only [hA]
  have hbMin : 0 < bMin := lt_min zero_lt_one hb
  have hD : 1 ≤ D := by
    apply (le_div_iff₀ hbMin).mpr
    simpa only [one_mul] using (min_le_left (1 : ℝ) b).trans hB
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogRatio : 0 < logRatio := Real.log_pos ((one_lt_div hr).mpr hrR)
  have hlogCoeff : 0 ≤ Real.log D / Real.log 2 := div_nonneg hlogD hlog2.le
  have hlogFactor : 0 < logFactor := by dsimp [logFactor]; linarith only [hlogCoeff]
  refine ⟨logFactor / logRatio, div_pos hlogFactor hlogRatio, ?_⟩
  intro q f t hq hAnalytic hGrowth hAnchor
  let c : ℂ := ⟨2, t⟩
  let v : ℝ := 2 + |t|
  let w : ℝ := 2 * (q : ℝ) * v
  let M : ℝ := B * w ^ 2
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast Nat.succ_le_of_lt hq
  have hq₀ : (0 : ℝ) ≤ q := by positivity
  have hv : 2 ≤ v := by dsimp [v]; linarith only [abs_nonneg t]
  have hw : 2 ≤ w := by
    have hq₂ : (1 : ℝ) ≤ 2 * (q : ℝ) := by linarith only [hq₁]
    exact hv.trans (le_mul_of_one_le_left (by linarith only [hv]) hq₂)
  have hw₀ : 0 < w := by linarith only [hw]
  have hM : 1 ≤ M := by
    have hWs : 1 ≤ w ^ 2 := by nlinarith only [hw, sq_nonneg (w - 2)]
    exact one_le_mul_of_one_le_of_one_le hB hWs
  have hAnchorMin : bMin ≤ ‖f c‖ := (min_le_right 1 b).trans hAnchor
  have hFpos : 0 < ‖f c‖ := hbMin.trans_le hAnchorMin
  have hFc : f c ≠ 0 := norm_pos_iff.mp hFpos
  have hOuter : AnalyticOnNhd ℂ f (closedBall c R) := by
    exact jensen_analytic_outer hAnalytic
  have hBound : ∀ z ∈ closedBall c R, ‖f z‖ ≤ M := by
    intro z hz
    have hnorm : 1 + ‖z‖ ≤ 3 * v := jensen_norm_of_mem_outer hz
    have hnormSq : (1 + ‖z‖) ^ 2 ≤ (3 * v) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by linarith only [hv])).mpr hnorm
    have hqSq : (q : ℝ) ≤ (2 * (q : ℝ)) ^ 2 := by
      have hqSelf : (q : ℝ) ≤ (q : ℝ) * (q : ℝ) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hq₁ hq₀
      nlinarith only [hqSelf, sq_nonneg (q : ℝ)]
    have hqvSq : (q : ℝ) * v ^ 2 ≤ w ^ 2 := calc
      _ ≤ (2 * (q : ℝ)) ^ 2 * v ^ 2 := mul_le_mul_of_nonneg_right hqSq (sq_nonneg v)
      _ = _ := by dsimp [w]; ring
    calc
      ‖f z‖ ≤ A * (q : ℝ) * (1 + ‖z‖) ^ 2 := hGrowth z (jensen_re_of_mem_outer hz)
      _ ≤ A * (q : ℝ) * (3 * v) ^ 2 := mul_le_mul_of_nonneg_left hnormSq (mul_nonneg hA.le hq₀)
      _ = 9 * A * ((q : ℝ) * v ^ 2) := by ring
      _ ≤ 9 * A * w ^ 2 := mul_le_mul_of_nonneg_left hqvSq (by positivity)
      _ ≤ M := mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (sq_nonneg w)
  have hJensen : ((∑ᶠ z : ℂ, divisor f (closedBall c |r|) z : ℤ) : ℝ) ≤
      Real.log (M / ‖f c‖) / logRatio := by
    have hOuterAbs : AnalyticOnNhd ℂ f (closedBall c |R|) := by simpa [abs_of_pos hR] using hOuter
    have hCircle : ∀ z ∈ sphere c |R|, ‖f z‖ ≤ M := by
      intro z hz
      apply hBound z
      simpa only [abs_of_pos hR] using sphere_subset_closedBall hz
    exact AnalyticOnNhd.sum_divisor_le (r := r) (R := R) (M := M)
      (by simpa only [abs_of_pos hr] using hr)
      (by simpa only [abs_of_pos hr, abs_of_pos hR] using hrR)
      hM hOuterAbs hFc hCircle
  have hLogW : Real.log 2 ≤ Real.log w := Real.log_le_log (by norm_num) hw
  have hLogBound : Real.log (M / ‖f c‖) ≤ logFactor * Real.log w := by
    have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
    have hDivBound : M / ‖f c‖ ≤ D * w ^ 2 := calc
      _ ≤ M / bMin := div_le_div_of_nonneg_left hMpos.le hbMin hAnchorMin
      _ = _ := by dsimp [M, D]; ring
    calc
      _ ≤ Real.log (D * w ^ 2) := Real.log_le_log (div_pos hMpos hFpos) hDivBound
      _ = 2 * Real.log w + Real.log D := by
        rw [Real.log_mul (by linarith only [hD]) (pow_ne_zero _ hw₀.ne'), Real.log_pow]
        norm_num [add_comm]
      _ = 2 * Real.log w + (Real.log D / Real.log 2) * Real.log 2 := by
        rw [div_mul_cancel₀ _ hlog2.ne']
      _ ≤ 2 * Real.log w + (Real.log D / Real.log 2) * Real.log w :=
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hLogW hlogCoeff))
      _ = _ := by dsimp [logFactor]; ring
  change ((∑ᶠ z : ℂ, divisor f (closedBall c r) z : ℤ) : ℝ) ≤
    (logFactor / logRatio) * Real.log w
  calc
    _ = ((∑ᶠ z : ℂ, divisor f (closedBall c |r|) z : ℤ) : ℝ) :=
      congrArg (fun U : Set ℂ ↦ ((∑ᶠ z : ℂ, divisor f U z : ℤ) : ℝ))
        (congrArg (closedBall c) (abs_of_pos hr).symm)
    _ ≤ Real.log (M / ‖f c‖) / logRatio := hJensen
    _ ≤ (logFactor * Real.log w) / logRatio :=
      div_le_div_of_nonneg_right hLogBound hlogRatio.le
    _ = _ := by ring

/-- A fixed polynomial growth bound and a positive anchor bound give a uniform logarithmic
bound on the number of critical-strip zeros, counted with multiplicity, in each height slice.
The zero-line hypothesis places the entire slice in the smaller Jensen disk. -/
theorem jensen_criticalZeroSlice_bound {A b : ℝ} (hA : 0 < A) (hb : 0 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) (f : ℂ → ℂ) (t : ℝ), 0 < q →
      AnalyticOnNhd ℂ f {z | 0 < z.re} →
      (∀ z : ℂ, 1 / 8 ≤ z.re → ‖f z‖ ≤ A * (q : ℝ) * (1 + ‖z‖) ^ 2) →
      b ≤ ‖f (⟨2, t⟩ : ℂ)‖ →
      (∀ z : ℂ, 0 < z.re → z.re < 1 → f z = 0 → z.re = 1 / 2) →
      (criticalZeroSlice f t).Finite ∧
        (∑ᶠ z : ℂ, (criticalZeroSlice f t).indicator
          (fun z ↦ (analyticOrderNatAt f z : ℝ)) z) ≤
          K * Real.log (2 * (q : ℝ) * (2 + |t|)) := by
  classical
  obtain ⟨K, hK, hDiskBound⟩ := jensen_diskDivisor_bound hA hb
  refine ⟨K, hK, ?_⟩
  intro q f t hq hAnalytic hGrowth hAnchor hLine
  let c : ℂ := ⟨2, t⟩
  let r : ℝ := 29 / 16
  let R : ℝ := 15 / 8
  have hFc : f c ≠ 0 := norm_pos_iff.mp (hb.trans_le hAnchor)
  have hCenter : c ∈ closedBall c R := mem_closedBall_self (by norm_num [R])
  have hOuter : AnalyticOnNhd ℂ f (closedBall c R) := jensen_analytic_outer hAnalytic
  have hInnerSubset : closedBall c r ⊆ closedBall c R :=
    closedBall_subset_closedBall (by norm_num [r, R])
  have hInner : AnalyticOnNhd ℂ f (closedBall c r) := hOuter.mono hInnerSubset
  have hOrderCenter : analyticOrderAt f c ≠ ⊤ := by
    rw [(hOuter c hCenter).analyticOrderAt_eq_zero.mpr hFc]
    exact ENat.zero_ne_top
  let countDivisor : ℂ → ℤ := fun z ↦ divisor f (closedBall c r) z
  let countSlice : ℂ → ℝ := (criticalZeroSlice f t).indicator
    (fun z ↦ (analyticOrderNatAt f z : ℝ))
  have hSliceOrder (z : ℂ) (hz : z ∈ criticalZeroSlice f t) :
      countDivisor z = (analyticOrderNatAt f z : ℤ) ∧ 0 < analyticOrderNatAt f z := by
    have hre := hLine z hz.1 hz.2.1 hz.2.2.2
    have hzInner : z ∈ closedBall c r := jensen_mem_inner hre hz.2.2.1
    have hzOuter : z ∈ closedBall c R := hInnerSubset hzInner
    have hOrder : analyticOrderAt f z ≠ ⊤ := hOuter.analyticOrderAt_ne_top_of_isPreconnected
      isPreconnected_closedBall hCenter hzOuter hOrderCenter
    constructor
    · change divisor f (closedBall c r) z = _
      rw [hInner.divisor_apply hzInner, ← Nat.cast_analyticOrderNatAt hOrder,
        ENat.map_natCast, WithTop.untop₀_coe]
    · apply Nat.pos_of_ne_zero
      intro hZero
      apply (hInner z hzInner).analyticOrderAt_ne_zero.mpr hz.2.2.2
      rw [← Nat.cast_analyticOrderNatAt hOrder, hZero, Nat.cast_zero]
  have hDivFinite : (Function.support countDivisor).Finite :=
    (divisor f (closedBall c r)).finiteSupport (isCompact_closedBall c r)
  have hSliceFinite : (criticalZeroSlice f t).Finite := by
    apply hDivFinite.subset
    intro z hz
    change countDivisor z ≠ 0
    rw [(hSliceOrder z hz).1]
    exact_mod_cast (hSliceOrder z hz).2.ne'
  refine ⟨hSliceFinite, ?_⟩
  have hSliceCountFinite : (Function.support countSlice).Finite := by
    apply hSliceFinite.subset
    intro z hz
    by_contra hNot
    exact hz (Set.indicator_of_notMem hNot _)
  let divisorOverReal : ℂ → ℝ := fun z ↦ (countDivisor z : ℝ)
  have hDivCountFinite : (Function.support divisorOverReal).Finite := by
    apply hDivFinite.subset
    intro z hz
    simpa [Function.mem_support, divisorOverReal] using hz
  change (∑ᶠ z : ℂ, countSlice z) ≤ K * Real.log (2 * (q : ℝ) * (2 + |t|))
  calc
    _ ≤ ∑ᶠ z : ℂ, divisorOverReal z := by
      apply finsum_le_finsum hSliceCountFinite hDivCountFinite
      intro z
      by_cases hz : z ∈ criticalZeroSlice f t
      · simp [countSlice, divisorOverReal, Set.indicator_of_mem hz, (hSliceOrder z hz).1]
      · rw [show countSlice z = 0 from Set.indicator_of_notMem hz _]
        have hNonnegative : (0 : ℤ) ≤ countDivisor z := hInner.divisor_nonneg z
        change (0 : ℝ) ≤ (countDivisor z : ℝ)
        exact_mod_cast hNonnegative
    _ = ((∑ᶠ z : ℂ, countDivisor z : ℤ) : ℝ) :=
      (map_finsum (Int.castRingHom ℝ) hDivFinite).symm
    _ ≤ _ := hDiskBound q f t hq hAnalytic hGrowth hAnchor

end Goldbach

namespace Goldbach

open Complex DirichletCharacter Set

abbrev GRH := ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
  0 < s.re → s.re < 1 → LFunction χ s = 0 → s.re = 1 / 2

noncomputable def regularizedL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ := by
  classical
  exact if χ = 1 then LFunctionTrivChar₁ q else LFunction χ

noncomputable def principalFlag {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ := by
  classical
  exact if χ = 1 then 1 else 0

theorem analytic_regularizedL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (regularizedL χ) univ := by
  intro s _
  by_cases hχ : χ = 1
  · simpa only [regularizedL, hχ, ite_true] using (differentiable_LFunctionTrivChar₁ q).analyticAt s
  · simpa only [regularizedL, hχ, ite_false] using (differentiable_LFunction hχ).analyticAt s

theorem regularizedL_zero_line {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hGRH : GRH)
    {s : ℂ} (hs : 0 < s.re) (hz : regularizedL χ s = 0) : s.re = 1 / 2 := by
  by_cases hχ : χ = 1
  · subst χ
    have hzero : LFunctionTrivChar₁ q s = 0 := by simpa only [regularizedL, eq_self, ite_true] using hz
    by_cases hs1 : s = 1
    · subst s
      exact False.elim (LFunctionTrivChar₁_apply_one_ne_zero q hzero)
    rw [LFunctionTrivChar₁, Function.update_of_ne hs1, mul_eq_zero] at hzero
    have hL : LFunction (1 : DirichletCharacter ℂ q) s = 0 :=
      hzero.resolve_left (sub_ne_zero.mpr hs1)
    have hslt : s.re < 1 := lt_of_not_ge fun hge =>
      LFunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ q) (Or.inr hs1) hge hL
    exact hGRH q 1 s hs hslt hL
  · have hL : LFunction χ s = 0 := by simpa only [regularizedL, hχ, ite_false] using hz
    have hslt : s.re < 1 := lt_of_not_ge fun hge =>
      LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hge hL
    exact hGRH q χ s hs hslt hL

theorem norm_regularizedL_anchor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (1 / 4 : ℝ) ≤ ‖regularizedL χ (⟨2, t⟩ : ℂ)‖ := by
  by_cases hχ : χ = 1
  · subst χ
    have hs : (⟨2, t⟩ : ℂ) ≠ 1 := by
      intro h
      have he := congrArg Complex.re h
      norm_num at he
    simp only [regularizedL, eq_self, ite_true]
    rw [LFunctionTrivChar₁, Function.update_of_ne hs]
    exact one_fourth_le_norm_mul_sub_one_LFunction_anchor (1 : DirichletCharacter ℂ q) t
  · simpa only [regularizedL, hχ, ite_false] using one_fourth_le_norm_LFunction_anchor χ t

theorem uniform_dirichlet_zero_slice (hGRH : GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
      (criticalZeroSlice (regularizedL χ) t).Finite ∧
        (∑ᶠ z : ℂ, (criticalZeroSlice (regularizedL χ) t).indicator
          (fun z => (analyticOrderNatAt (regularizedL χ) z : ℝ)) z) ≤
          C * Real.log (2 * (q : ℝ) * (2 + |t|)) := by
  obtain ⟨C, hC, hJensen⟩ :=
    jensen_criticalZeroSlice_bound (A := 25) (b := 1 / 4) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro q _ χ t
  exact hJensen q (regularizedL χ) t (Nat.pos_of_ne_zero (NeZero.ne q))
    ((analytic_regularizedL χ).mono (subset_univ _))
    (fun s hs => by
      have hg := GoldbachGrhGrowth.norm_regularizedLFunction_le χ hs
      by_cases hχ : χ = 1
      · simpa only [regularizedL, hχ, ite_true] using hg
      · simpa only [regularizedL, hχ, ite_false] using hg)
    (norm_regularizedL_anchor χ t) (fun s hs _ hzero => regularizedL_zero_line χ hGRH hs hzero)

theorem logDeriv_regularizedL_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s ≠ 1) (hL : LFunction χ s ≠ 0) :
    logDeriv (regularizedL χ) s = logDeriv (LFunction χ) s + principalFlag χ / (s - 1) := by
  by_cases hχ : χ = 1
  · subst χ
    simp only [regularizedL, principalFlag, eq_self, ite_true, logDeriv, Pi.div_apply]
    rw [deriv_LFunctionTrivChar₁_apply_of_ne_one q hs,
      LFunctionTrivChar₁, Function.update_of_ne hs]
    field_simp [sub_ne_zero.mpr hs, hL]
  · simp [regularizedL, principalFlag, hχ]

end Goldbach

open scoped BigOperators Topology
open Complex Filter Metric Set

noncomputable section

namespace GoldbachGrhLogDerivative

/- The argument uses the local zero separation and Borel–Carathéodory method in
`Zeta23/WeilEF/Landau.lean` (Anthropic, PBC), with direct Mathlib lemmas for primitives,
Jensen's inequality, factorized meromorphic functions and Cauchy's derivative bound. -/

private theorem exists_normalizedLog_on_ball {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (ball (0 : ℂ) R))
    (hg0 : ∀ z ∈ ball (0 : ℂ) R, g z ≠ 0) :
    ∃ J : ℂ → ℂ, J 0 = 0 ∧
      (∀ z ∈ ball (0 : ℂ) R, HasDerivAt J (logDeriv g z) z) ∧
      (∀ z ∈ ball (0 : ℂ) R, (J z).re = Real.log ‖g z‖ - Real.log ‖g 0‖) := by
  let U : Set ℂ := ball 0 R
  have hLog : DifferentiableOn ℂ (logDeriv g) U := by
    intro z hz
    change DifferentiableWithinAt ℂ (fun w => deriv g w / g w) U z
    exact ((hg z hz).deriv.differentiableAt.div (hg z hz).differentiableAt
      (hg0 z hz)).differentiableWithinAt
  obtain ⟨J, hJ0, hJ⟩ := hLog.isExactOn_ball.with_val_at 0 0
  refine ⟨J, hJ0, hJ, ?_⟩
  let k : ℂ → ℂ := fun z => exp (-J z) * g z
  have hk (z : ℂ) (hz : z ∈ U) : HasDerivAt k 0 z := by
    have hD := (hJ z hz).neg.cexp.mul (hg z hz).differentiableAt.hasDerivAt
    convert hD using 1
    simp only [logDeriv_apply]
    field_simp [hg0 z hz]
    norm_num
  have hc : (0 : ℂ) ∈ U := mem_ball_self hR
  have hConst : EqOn k (fun _ => g 0) U := by
    refine isOpen_ball.eqOn_of_deriv_eq (convex_ball _ _).isPreconnected
      (fun z hz => (hk z hz).differentiableAt.differentiableWithinAt) (differentiableOn_const (g 0))
      ?_ hc (by simp [k, hJ0])
    intro z hz
    rw [(hk z hz).deriv, deriv_const]
  intro z hz
  have hAt := hConst hz
  change exp (-J z) * g z = g 0 at hAt
  have hExp : exp (J z) * g 0 = g z := by
    rw [← hAt, ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
  have hNorm := congrArg norm hExp
  rw [norm_mul, norm_exp] at hNorm
  have hLn := congrArg Real.log hNorm
  rw [Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr (hg0 0 hc)), Real.log_exp] at hLn
  linarith

/-- On the inner disk, the derivative of the normalized logarithm is bounded by its upper real
part bound on the outer disk. The constants arise from Borel–Carathéodory and a Cauchy circle. -/
theorem norm_logDeriv_of_zeroFree_ball {g : ℂ → ℂ} {M : ℝ} (hM : 0 < M)
    (hg : AnalyticOnNhd ℂ g (ball (0 : ℂ) (22 / 25)))
    (hg0 : ∀ z ∈ ball (0 : ℂ) (22 / 25), g z ≠ 0)
    (hgBound : ∀ z ∈ ball (0 : ℂ) (22 / 25),
      Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ M) {z : ℂ} (hz : ‖z‖ ≤ 83 / 100) :
    ‖logDeriv g z‖ ≤ 4200 * M := by
  have hR : (0 : ℝ) < 22 / 25 := by norm_num
  obtain ⟨J, hJ0, hJDeriv, hJRe⟩ := exists_normalizedLog_on_ball hR hg hg0
  have hJDiff : DifferentiableOn ℂ J (ball (0 : ℂ) (22 / 25)) :=
    fun w hw => (hJDeriv w hw).differentiableAt.differentiableWithinAt
  have hRadius : (0 : ℝ) < 1 / 100 := by norm_num
  have hLocalNorm (w : ℂ) (hw : w ∈ closedBall z (1 / 100)) : ‖w‖ ≤ 21 / 25 := by
    rw [mem_closedBall, Complex.dist_eq] at hw
    linarith [norm_le_norm_sub_add w z]
  have hLocal : closedBall z (1 / 100) ⊆ ball (0 : ℂ) (22 / 25) := by
    intro w hw
    exact mem_ball_zero_iff.mpr ((hLocalNorm w hw).trans_lt (by norm_num))
  have hLocalDiff : DiffContOnCl ℂ J (ball z (1 / 100)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hRadius.ne']
    exact hJDiff.mono hLocal
  have hJImage : MapsTo J (ball (0 : ℂ) (22 / 25)) {w | w.re ≤ M} := by
    intro w hw
    change (J w).re ≤ M
    rw [hJRe w hw]
    exact hgBound w hw
  have hLocalBound (w : ℂ) (hw : w ∈ sphere z (1 / 100)) : ‖J w‖ ≤ 42 * M := by
    have hws := sphere_subset_closedBall hw
    have hwBig := hLocal hws
    have hSmall := hLocalNorm w hws
    have hDpos : 0 < (22 / 25 : ℝ) - ‖w‖ := by linarith
    refine (borelCaratheodory_zero hM hJDiff hJImage hR hwBig hJ0).trans ?_
    apply (div_le_iff₀ hDpos).mpr
    nlinarith [mul_nonneg hM.le (sub_nonneg.mpr hSmall)]
  have hCauchy := norm_deriv_le_of_forall_mem_sphere_norm_le hRadius hLocalDiff hLocalBound
  have hzBig : z ∈ ball (0 : ℂ) (22 / 25) :=
    mem_ball_zero_iff.mpr (hz.trans_lt (by norm_num))
  rw [(hJDeriv z hzBig).deriv] at hCauchy
  calc
    _ ≤ (42 * M) / (1 / 100 : ℝ) := hCauchy
    _ = _ := by ring

open MeromorphicOn in
private theorem factor_inner_divisor {f : ℂ → ℂ} {U V : Set ℂ}
    (hVU : V ⊆ U) (hCompact : IsCompact V) (hf : AnalyticOnNhd ℂ f U)
    (hFiniteOrder : ∀ z ∈ U, meromorphicOrderAt f z ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ (∀ z ∈ V, g z ≠ 0) ∧
      EqOn f ((∏ᶠ ρ, (· - ρ) ^ divisor f V ρ) * g)
        (U \ Function.support (divisor f V)) := by
  let D := divisor f V
  let P : ℂ → ℂ := ∏ᶠ ρ, (· - ρ) ^ D ρ
  let Q : ℂ → ℂ := P⁻¹ • f
  let g := toMeromorphicNFOn Q U
  have hDfin : (D : ℂ → ℤ).HasFiniteSupport := D.finiteSupport hCompact
  have hPNF : MeromorphicNFOn P U := Function.FactorizedRational.meromorphicNFOn D U
  have hQMer : MeromorphicOn Q U := hPNF.meromorphicOn.inv.smul hf.meromorphicOn
  have hGNF : MeromorphicNFOn g U := meromorphicNFOn_toMeromorphicNFOn Q U
  have hPOrd (z : ℂ) : meromorphicOrderAt P z = (D z : WithTop ℤ) :=
    Function.FactorizedRational.meromorphicOrderAt_eq D hDfin
  have hGOrd (z : ℂ) (hz : z ∈ U) :
      meromorphicOrderAt g z = -(D z : WithTop ℤ) + meromorphicOrderAt f z := by
    rw [← meromorphicOrderAt_congr (hQMer.toMeromorphicNFOn_eq_self_on_nhdsNE hz).symm]
    change meromorphicOrderAt (P⁻¹ • f) z = _
    rw [meromorphicOrderAt_smul (hPNF.meromorphicOn z hz).inv (hf.meromorphicOn z hz),
      meromorphicOrderAt_inv, hPOrd]
  have hOrdInner (z : ℂ) (hz : z ∈ V) : (D z : WithTop ℤ) = meromorphicOrderAt f z := by
    change (divisor f V z : WithTop ℤ) = _
    rw [(hf.mono hVU).meromorphicOn.divisor_apply hz]
    lift meromorphicOrderAt f z to ℤ using hFiniteOrder z (hVU hz) with n hn
    simp
  have hGZeroOrder (z : ℂ) (hz : z ∈ V) : meromorphicOrderAt g z = 0 := by
    rw [hGOrd z (hVU hz), ← hOrdInner z hz, ← WithTop.LinearOrderedAddCommGroup.coe_neg,
      ← WithTop.coe_add]
    simp
  refine ⟨g, ?_, ?_, ?_⟩
  · intro z hz
    apply (hGNF hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    by_cases hzV : z ∈ V
    · rw [hGZeroOrder z hzV]
    · have hzD : D z = 0 := by
        by_contra h
        exact hzV (D.supportWithinDomain h)
      rw [hGOrd z hz, hzD, WithTop.coe_zero, neg_zero, zero_add]
      exact (hf z hz).meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr (hf z hz)
  · intro z hz
    exact (hGNF (hVU hz)).meromorphicOrderAt_eq_zero_iff.mp (hGZeroOrder z hz)
  · intro z hz
    have hzD : D z = 0 := by simpa only [Function.mem_support, not_not] using hz.2
    have hPOrd0 : meromorphicOrderAt P z = 0 := by rw [hPOrd, hzD, WithTop.coe_zero]
    have hPNZ : P z ≠ 0 := (hPNF hz.1).meromorphicOrderAt_eq_zero_iff.mp hPOrd0
    have hPA : AnalyticAt ℂ P z :=
      (hPNF hz.1).meromorphicOrderAt_nonneg_iff_analyticAt.mp hPOrd0.ge
    have hQA : AnalyticAt ℂ Q z := (hPA.inv hPNZ).mul (hf z hz.1)
    have hGQ : g z = Q z := by
      change toMeromorphicNFOn Q U z = Q z
      rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hQMer hz.1,
        toMeromorphicNFAt_eq_self.mpr hQA.meromorphicNFAt]
    change f z = P z * g z
    rw [hGQ]
    change f z = P z * ((P z)⁻¹ * f z)
    rw [← mul_assoc, mul_inv_cancel₀ hPNZ, one_mul]

private theorem logDeriv_finset_zeroFactors {Z : Finset ℂ} {m : ℂ → ℕ} {z : ℂ}
    (hz : ∀ ρ ∈ Z, z ≠ ρ) :
    logDeriv (fun w : ℂ => ∏ ρ ∈ Z, (w - ρ) ^ m ρ) z =
      ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) := by
  have hd (ρ : ℂ) : HasDerivAt (fun w : ℂ => w - ρ) 1 z := (hasDerivAt_id z).sub_const ρ
  have hProd : (fun w : ℂ => ∏ ρ ∈ Z, (w - ρ) ^ m ρ) =
      ∏ ρ ∈ Z, (fun w : ℂ => (w - ρ) ^ m ρ) := by
    funext w
    rw [Finset.prod_apply]
  rw [hProd, logDeriv_prod (f := fun ρ w => (w - ρ) ^ m ρ)
    (fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr (hz ρ hρ)))
    (fun ρ _ => (hd ρ).differentiableAt.pow _)]
  apply Finset.sum_congr rfl
  intro ρ _
  rw [logDeriv_fun_pow (hd ρ).differentiableAt, logDeriv_apply, (hd ρ).deriv]
  ring

open MeromorphicOn in
/-- Landau's approximation by simple poles in a normalized unit disk. Jensen's inequality
bounds the sum of multiplicities. The remaining analytic factor is controlled on the smaller disk. -/
theorem logDeriv_partial_fraction_unit {f : ℂ → ℂ} {B : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1)) (hf0 : f 0 = 1) (hB : 2 ≤ B)
    (hfB : ∀ w ∈ sphere (0 : ℂ) (24 / 25), ‖f w‖ ≤ B) :
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ closedBall (0 : ℂ) (22 / 25) | f ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) ≤ Real.log B / Real.log (12 / 11)) ∧
      ∀ z : ℂ, ‖z‖ ≤ 83 / 100 → f z ≠ 0 →
        ‖logDeriv f z - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ ≤
          130200 * Real.log B := by
  classical
  let U := closedBall (0 : ℂ) 1
  let V := closedBall (0 : ℂ) (22 / 25)
  let W := closedBall (0 : ℂ) (24 / 25)
  have hVU : V ⊆ U := closedBall_subset_closedBall (by norm_num)
  have hWU : W ⊆ U := closedBall_subset_closedBall (by norm_num)
  have hVW : V ⊆ W := closedBall_subset_closedBall (by norm_num)
  have h0U : (0 : ℂ) ∈ U := mem_closedBall_self (by norm_num)
  have hf0NZ : f 0 ≠ 0 := by rw [hf0]; exact one_ne_zero
  have hFinA (z : ℂ) (hz : z ∈ U) : analyticOrderAt f z ≠ ⊤ :=
    hf.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall _ _).isPreconnected h0U hz
      (by simp [(hf 0 h0U).analyticOrderAt_eq_zero.mpr hf0NZ])
  have hFinM (z : ℂ) (hz : z ∈ U) : meromorphicOrderAt f z ≠ ⊤ := by
    rw [(hf z hz).meromorphicOrderAt_eq]
    lift analyticOrderAt f z to ℕ using hFinA z hz with n hn
    simp
  let D := divisor f V
  have hDfin : (D : ℂ → ℤ).HasFiniteSupport := D.finiteSupport (isCompact_closedBall ..)
  let Z := hDfin.toFinset
  let K := ∑ ρ ∈ Z, analyticOrderNatAt f ρ
  have hSupport : V ∩ f ⁻¹' {0} = Function.support D :=
    (hf.mono hVU).meromorphicNFOn.zero_set_eq_divisor_support (fun v => hFinM v (hVU v.2))
  have hZeq : (↑Z : Set ℂ) = {ρ ∈ V | f ρ = 0} := by
    rw [show (↑Z : Set ℂ) = Function.support D from hDfin.coe_toFinset, ← hSupport]
    rfl
  have hρV (ρ : ℂ) (hρ : ρ ∈ Z) : ρ ∈ V := D.supportWithinDomain (hDfin.mem_toFinset.mp hρ)
  have hm (ρ : ℂ) (hρ : ρ ∈ Z) : D ρ = (analyticOrderNatAt f ρ : ℤ) := by
    change divisor f V ρ = _
    rw [(hf.mono hVU).divisor_apply (hρV ρ hρ), ← Nat.cast_analyticOrderNatAt (hFinA ρ (hVU (hρV ρ hρ)))]
    simp
  have hCount : (K : ℝ) ≤ Real.log B / Real.log (12 / 11) := by
    have hFsum : (∑ᶠ u, D u) = ∑ ρ ∈ Z, D ρ :=
      finsum_eq_sum_of_support_subset _ fun _ hu => hDfin.mem_toFinset.mpr hu
    have hK : (K : ℤ) = ∑ ρ ∈ Z, D ρ := by
      simp only [K, Nat.cast_sum]
      exact Finset.sum_congr rfl fun ρ hρ => (hm ρ hρ).symm
    have hJ := AnalyticOnNhd.sum_divisor_le (r := (22 / 25 : ℝ)) (R := 24 / 25) (M := B)
      (by norm_num) (by norm_num) (by linarith)
      (by simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24 / 25)] using hf.mono hWU)
      hf0NZ (by simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24 / 25)] using hfB)
    have hRatio : (24 / 25 : ℝ) / (22 / 25) = 12 / 11 := by norm_num
    have hAbs : |(22 / 25 : ℝ)| = 22 / 25 := abs_of_nonneg (by norm_num)
    rw [hAbs] at hJ
    have hJ' : ((∑ᶠ u, D u : ℤ) : ℝ) ≤ Real.log B / Real.log (12 / 11) := by
      simpa only [D, V, hf0, norm_one, div_one, hRatio] using hJ
    rw [hFsum, ← hK, Int.cast_natCast] at hJ'
    exact hJ'
  obtain ⟨g, hg, hgNZ, hFactor⟩ := factor_inner_divisor hVU (isCompact_closedBall ..) hf hFinM
  let P : ℂ → ℂ := fun w => ∏ ρ ∈ Z, (w - ρ) ^ analyticOrderNatAt f ρ
  have hProd : (∏ᶠ ρ, (· - ρ) ^ D ρ) = P := by
    have hDiff : (fun ρ : ℂ => (· - ρ) ^ D ρ).mulSupport ⊆ Z := by
      intro ρ hρ
      refine hDfin.mem_toFinset.mpr ?_
      by_contra hOutside
      have hD0 : D ρ = 0 := by simpa only [Function.mem_support, not_not] using hOutside
      exact hρ (by simp [hD0])
    rw [finprod_eq_prod_of_mulSupport_subset _ hDiff]
    funext w
    rw [Finset.prod_apply]
    exact Finset.prod_congr rfl fun ρ hρ => by simp [hm ρ hρ]
  have hFac : EqOn f (P * g) (U \ Function.support D) := by
    simpa only [← hProd] using hFactor
  have hOuter (w : ℂ) (hw : w ∈ sphere (0 : ℂ) (24 / 25)) :
      ‖g w‖ ≤ B * (25 / 2 : ℝ) ^ K := by
    have hwNorm : ‖w‖ = 24 / 25 := mem_sphere_zero_iff_norm.mp hw
    have hwU : w ∈ U := hWU (sphere_subset_closedBall hw)
    have hwNot : w ∉ Function.support D := by
      intro hwD
      have hwV : w ∈ V := D.supportWithinDomain hwD
      have hN : ‖w‖ ≤ 22 / 25 := by simpa only [V, mem_closedBall_iff_norm, sub_zero] using hwV
      linarith
    have hEq : f w = P w * g w := hFac ⟨hwU, hwNot⟩
    have hDist (ρ : ℂ) (hρ : ρ ∈ Z) : (2 / 25 : ℝ) ≤ ‖w - ρ‖ := by
      have hRho : ‖ρ‖ ≤ 22 / 25 := by
        simpa only [V, mem_closedBall_iff_norm, sub_zero] using hρV ρ hρ
      exact (show (2 / 25 : ℝ) ≤ ‖w‖ - ‖ρ‖ by linarith).trans (norm_sub_norm_le w ρ)
    have hPBound : (2 / 25 : ℝ) ^ K ≤ ‖P w‖ := by
      simp only [P, norm_prod, norm_pow, K, ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_le_prod₀ (fun _ _ => by positivity)
        (fun ρ hρ => pow_le_pow_left₀ (by norm_num) (hDist ρ hρ) _)
    have hAt := hfB w hw
    rw [hEq, norm_mul] at hAt
    have hMul : ‖g w‖ * (2 / 25 : ℝ) ^ K ≤ B := by
      rw [mul_comm]
      exact (mul_le_mul_of_nonneg_right hPBound (norm_nonneg _)).trans hAt
    have hDiv := (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2 / 25) K)).mpr hMul
    rw [div_eq_mul_inv, ← inv_pow, show ((2 / 25 : ℝ)⁻¹) = 25 / 2 by norm_num] at hDiv
    exact hDiv
  have hMax (w : ℂ) (hw : w ∈ W) : ‖g w‖ ≤ B * (25 / 2 : ℝ) ^ K := by
    apply norm_le_of_forall_mem_frontier_norm_le (U := W) isBounded_closedBall
    · apply DifferentiableOn.diffContOnCl
      simpa only [W, closure_closedBall] using (hg.mono hWU).differentiableOn
    · simpa only [W, frontier_closedBall'] using hOuter
    · simpa only [W, closure_closedBall] using hw
  have h0Not : (0 : ℂ) ∉ Function.support D := by
    rw [← hSupport]
    simp [hf0]
  have hP0 : ‖P 0‖ ≤ 1 := by
    simp only [P, norm_prod, norm_pow, zero_sub, norm_neg]
    refine Finset.prod_le_one₀ (fun _ _ => by positivity) fun ρ hρ => ?_
    have hρN : ‖ρ‖ ≤ 22 / 25 := by
      simpa only [V, mem_closedBall_iff_norm, sub_zero] using hρV ρ hρ
    exact pow_le_one₀ (norm_nonneg _) (hρN.trans (by norm_num))
  have hG0 : 1 ≤ ‖g 0‖ := by
    have hFactor0 : f 0 = P 0 * g 0 := hFac ⟨h0U, h0Not⟩
    calc
      1 = ‖f 0‖ := by simp [hf0]
      _ = ‖P 0‖ * ‖g 0‖ := by rw [hFactor0, norm_mul]
      _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hP0 (norm_nonneg _)
  have hLogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hLogRatio : 0 < Real.log (12 / 11 : ℝ) := Real.log_pos (by norm_num)
  have hLogPow : Real.log (25 / 2 : ℝ) ≤ 30 * Real.log (12 / 11 : ℝ) := by
    calc
      _ ≤ Real.log ((12 / 11 : ℝ) ^ (30 : ℕ)) := Real.log_le_log (by norm_num) (by norm_num)
      _ = _ := by rw [Real.log_pow]; norm_num
  have hKLog : (K : ℝ) * Real.log (25 / 2 : ℝ) ≤ 30 * Real.log B := by
    calc
      _ ≤ (K : ℝ) * (30 * Real.log (12 / 11 : ℝ)) := mul_le_mul_of_nonneg_left hLogPow K.cast_nonneg
      _ = 30 * ((K : ℝ) * Real.log (12 / 11 : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ((le_div_iff₀ hLogRatio).mp hCount) (by norm_num)
  have hReg (w : ℂ) (hw : w ∈ ball (0 : ℂ) (22 / 25)) :
      Real.log ‖g w‖ - Real.log ‖g 0‖ ≤ 31 * Real.log B := by
    have hwV := ball_subset_closedBall hw
    have hL : Real.log ‖g w‖ ≤ Real.log (B * (25 / 2 : ℝ) ^ K) :=
      Real.log_le_log (norm_pos_iff.mpr (hgNZ w hwV)) (hMax w (hVW hwV))
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hL
    linarith [Real.log_nonneg hG0]
  refine ⟨Z, hZeq, ?_, ?_⟩
  · simpa only [K, Nat.cast_sum] using hCount
  · intro z hz hfz
    have hzI : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (hz.trans_lt (by norm_num))
    have hzNot : z ∉ Function.support D := by
      rw [← hSupport]
      simp [hfz]
    have hLocal : f =ᶠ[𝓝 z] fun w => P w * g w := by
      filter_upwards [(isOpen_ball.sdiff hDfin.isClosed).mem_nhds ⟨hzI, hzNot⟩] with w hw
      exact hFac ⟨ball_subset_closedBall hw.1, hw.2⟩
    have hfacZ : f z = P z * g z := hLocal.eq_of_nhds
    have hPZ : P z ≠ 0 := fun h => hfz (by simp [hfacZ, h])
    have hGZ : g z ≠ 0 := fun h => hfz (by simp [hfacZ, h])
    have hdP : DifferentiableAt ℂ P z := DifferentiableAt.fun_finsetProd fun ρ _ =>
      ((differentiable_id.sub_const ρ).differentiableAt).pow _
    have hFrac : logDeriv f z = logDeriv P z + logDeriv g z := by
      have hEq : logDeriv f z = logDeriv (fun w => P w * g w) z := by
        simp only [logDeriv_apply, hLocal.deriv_eq, hfacZ]
      rw [hEq]
      exact logDeriv_mul z hPZ hGZ hdP (hg z (ball_subset_closedBall hzI)).differentiableAt
    have hNonzero (ρ : ℂ) (hρ : ρ ∈ Z) : z ≠ ρ := by
      intro h
      have hρD : ρ ∈ Function.support D := hDfin.mem_toFinset.mp hρ
      exact hzNot (h ▸ hρD)
    rw [hFrac, show logDeriv P z = _ from logDeriv_finset_zeroFactors hNonzero, add_sub_cancel_left]
    calc
      _ ≤ 4200 * (31 * Real.log B) := norm_logDeriv_of_zeroFree_ball (by positivity)
        (hg.mono (ball_subset_closedBall.trans hVU))
        (fun w hw => hgNZ w (ball_subset_closedBall hw)) hReg hz
      _ = _ := by ring

/-- Landau's approximation on an arbitrary closed disk, obtained by affine scaling of the
normalized unit-disk statement. -/
theorem logDeriv_partial_fraction_disk {f : ℂ → ℂ} {c : ℂ} {R B : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hf0 : f c ≠ 0) (hB : 2 ≤ B)
    (hfB : ∀ w ∈ closedBall c (24 / 25 * R), ‖f w‖ ≤ B * ‖f c‖) :
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ closedBall c (22 / 25 * R) | f ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) ≤ Real.log B / Real.log (12 / 11)) ∧
      ∀ s ∈ closedBall c (83 / 100 * R), f s ≠ 0 →
        ‖logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤
          130200 / R * Real.log B := by
  let A : ℂ → ℂ := fun w => c + (R : ℂ) * w
  let G : ℂ → ℂ := fun w => (f c)⁻¹ * f (A w)
  have hRC : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  have hAanalytic (w : ℂ) : AnalyticAt ℂ A w :=
    analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have hADeriv (w : ℂ) : deriv A w = (R : ℂ) := by
    simp [A]
  have hAinj : Function.Injective A := by
    intro z w hEq
    change c + (R : ℂ) * z = c + (R : ℂ) * w at hEq
    exact mul_left_cancel₀ hRC (add_left_cancel hEq)
  have hANorm (w : ℂ) : ‖A w - c‖ = R * ‖w‖ := by
    simp only [A, add_sub_cancel_left, norm_mul, Complex.norm_of_nonneg hR.le]
  have hAInv (s : ℂ) : A ((s - c) / (R : ℂ)) = s := by
    simp only [A]
    field_simp [hRC]
    ring
  have hAMem {w : ℂ} {r : ℝ} (hw : ‖w‖ ≤ r) : A w ∈ closedBall c (r * R) := by
    rw [mem_closedBall_iff_norm, hANorm]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hw hR.le
  have hInvNorm {s : ℂ} {r : ℝ} (hs : s ∈ closedBall c (r * R)) :
      ‖(s - c) / (R : ℂ)‖ ≤ r := by
    rw [mem_closedBall_iff_norm] at hs
    rw [norm_div, Complex.norm_of_nonneg hR.le]
    exact (div_le_iff₀ hR).mpr hs
  have hAMemOne {w : ℂ} (hw : ‖w‖ ≤ 1) : A w ∈ closedBall c R := by
    simpa only [one_mul] using hAMem hw
  have hGanalytic : AnalyticOnNhd ℂ G (closedBall (0 : ℂ) 1) := by
    intro w hw
    have hwNorm : ‖w‖ ≤ 1 := by simpa only [mem_closedBall_iff_norm, sub_zero] using hw
    exact analyticAt_const.mul ((hf (A w) (hAMemOne hwNorm)).comp (hAanalytic w))
  have hG0 : G 0 = 1 := by simp [G, A, hf0]
  have hGBound (w : ℂ) (hw : w ∈ sphere (0 : ℂ) (24 / 25)) : ‖G w‖ ≤ B := by
    have hwNorm : ‖w‖ ≤ 24 / 25 := (mem_sphere_zero_iff_norm.mp hw).le
    have hNormPos := norm_pos_iff.mpr hf0
    calc
      _ = ‖f c‖⁻¹ * ‖f (A w)‖ := by simp only [G, norm_mul, norm_inv]
      _ ≤ ‖f c‖⁻¹ * (B * ‖f c‖) := mul_le_mul_of_nonneg_left (hfB (A w) (hAMem hwNorm))
        (inv_nonneg.mpr hNormPos.le)
      _ = B := by rw [mul_comm B, ← mul_assoc, inv_mul_cancel₀ hNormPos.ne', one_mul]
  have hOrd (w : ℂ) (hw : ‖w‖ ≤ 1) :
      analyticOrderNatAt G w = analyticOrderNatAt f (A w) := by
    have hComp : AnalyticAt ℂ (f ∘ A) w := (hf (A w) (hAMemOne hw)).comp (hAanalytic w)
    calc
      _ = analyticOrderNatAt (f ∘ A) w := analyticOrderNatAt_fun_const_mul hComp (inv_ne_zero hf0)
      _ = _ := by
        unfold analyticOrderNatAt
        rw [analyticOrderAt_comp_of_deriv_ne_zero (hAanalytic w) (by rw [hADeriv]; exact hRC)]
  obtain ⟨Z₀, hZ₀, hCount, hBound⟩ := logDeriv_partial_fraction_unit hGanalytic hG0 hB hGBound
  have hZero (w : ℂ) : w ∈ Z₀ ↔ ‖w‖ ≤ 22 / 25 ∧ f (A w) = 0 := by
    change w ∈ (↑Z₀ : Set ℂ) ↔ _
    rw [hZ₀]
    simp [G, hf0]
  have hZeroNorm (w : ℂ) (hw : w ∈ Z₀) : ‖w‖ ≤ 1 :=
    ((hZero w).mp hw).1.trans (by norm_num)
  let embedding : ℂ ↪ ℂ := ⟨A, hAinj⟩
  let Z := Z₀.map embedding
  refine ⟨Z, ?_, ?_, ?_⟩
  · ext ρ
    change ρ ∈ Z ↔ ρ ∈ closedBall c (22 / 25 * R) ∧ f ρ = 0
    simp only [Z, Finset.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨hwNorm, hwZero⟩ := (hZero w).mp hw
      exact ⟨hAMem hwNorm, hwZero⟩
    · rintro ⟨hρ, hρZero⟩
      refine ⟨(ρ - c) / (R : ℂ), (hZero _).mpr ⟨hInvNorm hρ, ?_⟩, hAInv ρ⟩
      rwa [hAInv]
  · simp only [Z, Finset.sum_map]
    have hSum : (∑ w ∈ Z₀, (analyticOrderNatAt f (A w) : ℝ)) =
        ∑ w ∈ Z₀, (analyticOrderNatAt G w : ℝ) :=
      Finset.sum_congr rfl fun w hw => by rw [hOrd w (hZeroNorm w hw)]
    exact hSum.le.trans hCount
  · intro s hs hfs
    let w := (s - c) / (R : ℂ)
    have hAw : A w = s := hAInv s
    have hw : ‖w‖ ≤ 83 / 100 := hInvNorm hs
    have hw₁ : ‖w‖ ≤ 1 := hw.trans (by norm_num)
    have hGw : G w ≠ 0 := by simp [G, hAw, hf0, hfs]
    have hG := hBound w hw hGw
    have hLD : logDeriv G w = (R : ℂ) * logDeriv f s := by
      calc
        _ = logDeriv (f ∘ A) w := logDeriv_const_mul w _ (inv_ne_zero hf0)
        _ = _ := by
          rw [logDeriv_comp (hf (A w) (hAMemOne hw₁)).differentiableAt
            (hAanalytic w).differentiableAt, hADeriv, hAw, mul_comm]
    have hLDF : logDeriv f s = (R : ℂ)⁻¹ * logDeriv G w := by
      rw [hLD, ← mul_assoc, inv_mul_cancel₀ hRC, one_mul]
    have hTerms : (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)) =
        (R : ℂ)⁻¹ * ∑ u ∈ Z₀, (analyticOrderNatAt G u : ℂ) / (w - u) := by
      simp only [Z, Finset.sum_map, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u hu => ?_
      change (analyticOrderNatAt f (A u) : ℂ) / (s - A u) = _
      rw [← hOrd u (hZeroNorm u hu)]
      have hShift : s - A u = (R : ℂ) * (w - u) := by
        rw [← hAw]
        simp only [A]
        ring
      calc
        _ = ((analyticOrderNatAt G u : ℂ) / (w - u)) / (R : ℂ) := by
          rw [hShift, div_div, mul_comm]
        _ = _ := div_eq_inv_mul _ _
    rw [hLDF, hTerms, ← mul_sub, norm_mul, norm_inv, Complex.norm_of_nonneg hR.le]
    calc
      _ ≤ R⁻¹ * (130200 * Real.log B) := mul_le_mul_of_nonneg_left hG (inv_nonneg.mpr hR.le)
      _ = _ := by ring

end GoldbachGrhLogDerivative

namespace Goldbach

open Complex Metric Set
open scoped BigOperators

/-- Uniform logarithmic derivative bound on the right of Re s = 9/20, at a point with a
given positive separation from the zeros of the regularized L-function. -/
theorem norm_logDeriv_regularizedL_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t σ d : ℝ),
      9 / 20 ≤ σ → σ ≤ 2 → 0 < d →
      (∀ ρ : ℂ, 0 < ρ.re → regularizedL χ ρ = 0 → d ≤ ‖(⟨σ, t⟩ : ℂ) - ρ‖) →
      ‖logDeriv (regularizedL χ) (⟨σ, t⟩ : ℂ)‖ ≤
        C * Real.log (2 * (q : ℝ) * (2 + |t|)) * (1 + d⁻¹) := by
  let R : ℝ := 15 / 8
  let A : ℝ := 130200 / R
  let E : ℝ := (Real.log (12 / 11 : ℝ))⁻¹
  have hR : 0 < R := by norm_num [R]
  have hA : 0 < A := div_pos (by norm_num) hR
  have hE : 0 < E := inv_pos.mpr (Real.log_pos (by norm_num))
  refine ⟨13 * (A + E), mul_pos (by norm_num) (add_pos hA hE), ?_⟩
  intro q _ χ t σ d hσlo hσhi hd hSep
  let f := regularizedL χ
  let c : ℂ := ⟨2, t⟩
  let s : ℂ := ⟨σ, t⟩
  let K : ℝ := 2 + |t|
  let B : ℝ := 900 * (q : ℝ) * K ^ 2
  let L : ℝ := Real.log (2 * (q : ℝ) * K)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.succ_le_of_lt q.pos_of_neZero
  have hq0 : 0 < (q : ℝ) := zero_lt_one.trans_le hq1
  have hK2 : 2 ≤ K := le_add_of_nonneg_right (abs_nonneg t)
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 < K := zero_lt_one.trans_le hK1
  have hB0 : 0 < B := by
    dsimp only [B]
    positivity
  have hB2 : 2 ≤ B := by
    calc
      (2 : ℝ) ≤ 900 * 1 * 1 := by norm_num
      _ ≤ B := mul_le_mul (mul_le_mul_of_nonneg_left hq1 (by norm_num))
        (one_le_pow₀ hK1) zero_le_one (by positivity)
  have hReLower (w : ℂ) (hw : w ∈ closedBall c R) : (1 / 8 : ℝ) ≤ w.re := by
    have hDist := mem_closedBall_iff_norm.mp hw
    have hRe := abs_re_le_norm (w - c)
    rw [sub_re, show c.re = 2 from rfl] at hRe
    have hLower := neg_le_abs (w.re - 2)
    dsimp only [R] at hDist
    linarith
  have hcform : c = (2 : ℂ) + (t : ℂ) * I := by
    apply Complex.ext <;> simp [c, Complex.mul_re, Complex.mul_im]
  have hcnorm : ‖c‖ ≤ K := by
    rw [hcform]
    calc
      _ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = _ := by simp [K, norm_real, Real.norm_eq_abs]
  have hAnchor : (1 / 4 : ℝ) ≤ ‖f c‖ := norm_regularizedL_anchor χ t
  have hf0 : f c ≠ 0 := norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 4).trans_le hAnchor)
  have hf : AnalyticOnNhd ℂ f (closedBall c R) := (analytic_regularizedL χ).mono (subset_univ _)
  have hfB (w : ℂ) (hw : w ∈ closedBall c (24 / 25 * R)) : ‖f w‖ ≤ B * ‖f c‖ := by
    have hwBig := closedBall_subset_closedBall (show (24 / 25 : ℝ) * R ≤ R by norm_num [R]) hw
    have hDist := mem_closedBall_iff_norm.mp hwBig
    have hwNorm : 1 + ‖w‖ ≤ 3 * K := by
      dsimp only [R] at hDist
      linarith only [norm_le_norm_sub_add w c, hDist, hcnorm, hK2]
    have hGrowth : ‖f w‖ ≤ 25 * (q : ℝ) * (1 + ‖w‖) ^ 2 := by
      have hRaw := GoldbachGrhGrowth.norm_regularizedLFunction_le χ (hReLower w hwBig)
      by_cases hχ : χ = 1 <;> simpa [f, regularizedL, hχ] using hRaw
    calc
      _ ≤ 25 * (q : ℝ) * (1 + ‖w‖) ^ 2 := hGrowth
      _ ≤ 25 * (q : ℝ) * (3 * K) ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hwNorm 2) (by positivity)
      _ = B * (1 / 4 : ℝ) := by
        dsimp only [B]
        ring
      _ ≤ B * ‖f c‖ := mul_le_mul_of_nonneg_left hAnchor hB0.le
  have hS : s ∈ closedBall c (83 / 100 * R) := by
    have hSub : s - c = ((σ - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [s, c]
    rw [mem_closedBall_iff_norm, hSub, norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hσhi)]
    dsimp only [R]
    linarith
  have hS0 : f s ≠ 0 := by
    intro hsz
    have hs : 0 < s.re := (by norm_num : (0 : ℝ) < 9 / 20).trans_le hσlo
    have h := hSep s hs hsz
    rw [sub_self, norm_zero] at h
    exact hd.not_ge h
  obtain ⟨Z, hZ, hMass, hApprox⟩ :=
    GoldbachGrhLogDerivative.logDeriv_partial_fraction_disk hR hf hf0 hB2 hfB
  have hTerms : ‖∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤
      (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) * d⁻¹ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    have hZmem : ρ ∈ (↑Z : Set ℂ) := hρ
    rw [hZ] at hZmem
    have hρLarge := closedBall_subset_closedBall (show (22 / 25 : ℝ) * R ≤ R by norm_num [R])
      hZmem.1
    have hρPos := (by norm_num : (0 : ℝ) < 1 / 8).trans_le (hReLower ρ hρLarge)
    have hρdist : d ≤ ‖s - ρ‖ := hSep ρ hρPos hZmem.2
    have hRecip : ‖s - ρ‖⁻¹ ≤ d⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hd hρdist
    rw [norm_div, Complex.norm_natCast, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hRecip (Nat.cast_nonneg _)
  have hLFormula : L = Real.log 2 + Real.log (q : ℝ) + Real.log K := by
    dsimp only [L]
    rw [Real.log_mul (by positivity) hK0.ne', Real.log_mul (by norm_num) hq0.ne']
  have hBLFormula : Real.log B = Real.log 900 + Real.log (q : ℝ) + 2 * Real.log K := by
    dsimp only [B]
    rw [Real.log_mul (by positivity) (pow_ne_zero _ hK0.ne'),
      Real.log_mul (by norm_num) hq0.ne', Real.log_pow]
    norm_num
  have hLog900 : Real.log 900 ≤ 10 * Real.log 2 := by
    calc
      _ ≤ Real.log ((2 : ℝ) ^ (10 : ℕ)) := Real.log_le_log (by norm_num) (by norm_num)
      _ = _ := by
        rw [Real.log_pow]
        norm_num
  have hLPos : 0 < L := by
    rw [hLFormula]
    linarith only [Real.log_nonneg hq1, Real.log_nonneg hK1, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hScaleLog : Real.log B ≤ 13 * L := by
    rw [hBLFormula, hLFormula]
    linarith only [hLog900, Real.log_nonneg hq1, Real.log_nonneg hK1,
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hRecip0 : 0 ≤ d⁻¹ := inv_nonneg.mpr hd.le
  have hBudget : A + E * d⁻¹ ≤ (A + E) * (1 + d⁻¹) := by
    nlinarith only [hE.le, mul_nonneg hA.le hRecip0]
  have hMass' := mul_le_mul_of_nonneg_right hMass hRecip0
  change ‖logDeriv f s‖ ≤ 13 * (A + E) * L * (1 + d⁻¹)
  calc
    _ ≤ ‖logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ +
        ‖∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ := norm_le_norm_sub_add _ _
    _ ≤ A * Real.log B + (Real.log B / Real.log (12 / 11)) * d⁻¹ :=
      (add_le_add (hApprox s hS hS0) (hTerms.trans hMass'))
    _ = Real.log B * (A + E * d⁻¹) := by
      dsimp only [E]
      rw [div_eq_mul_inv]
      ring
    _ ≤ (13 * L) * (A + E * d⁻¹) := mul_le_mul_of_nonneg_right hScaleLog (by positivity)
    _ ≤ (13 * L) * ((A + E) * (1 + d⁻¹)) := mul_le_mul_of_nonneg_left hBudget (by positivity)
    _ = _ := by ring

end Goldbach
namespace Goldbach

open Complex Set

noncomputable section

def logHeight (q : ℕ) (t : ℝ) : ℝ := Real.log (2 * (q : ℝ) * (2 + |t|))

def contourLog {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z : ℂ) : ℂ :=
  -logDeriv (regularizedL χ) z + principalFlag χ / (z - 1)

def UniformDirichletLogDerivative (C : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t d : ℝ),
    σ ∈ Icc (9 / 20 : ℝ) 2 → 0 < d →
    (∀ ρ : ℂ, 0 < ρ.re → regularizedL χ ρ = 0 → d ≤ ‖((σ : ℂ) + (t : ℂ) * I) - ρ‖) →
    ‖logDeriv (regularizedL χ) ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * logHeight q t * (1 + d⁻¹)

theorem logHeight_ge_one (q : ℕ) [NeZero q] (t : ℝ) : 1 ≤ logHeight q t := by
  have hq : 1 ≤ (q : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlog4 : 1 ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have harg : (4 : ℝ) ≤ 2 * (q : ℝ) * (2 + |t|) := calc
    _ ≤ 2 * (1 : ℝ) * (2 + |t|) := by linarith [abs_nonneg t]
    _ ≤ _ := by gcongr
  exact hlog4.trans (Real.log_le_log (by norm_num) harg)

end
end Goldbach
namespace Goldbach

open Complex DirichletCharacter MeromorphicOn Set

/-- The regularized Dirichlet L-function is nonzero at one. -/
theorem regularizedL_ne_zero_at_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    regularizedL χ 1 ≠ 0 := by
  by_cases hχ : χ = 1
  · simpa only [regularizedL, hχ, ite_true] using LFunctionTrivChar₁_apply_one_ne_zero q
  · simpa only [regularizedL, hχ, ite_false] using LFunction_apply_one_ne_zero hχ
end Goldbach
open Complex Set MeasureTheory
open scoped BigOperators Interval

namespace Goldbach

/- For a reference statement, see PrimeNumberTheoremAnd's ResidueCalcOnRectangles.lean at
   2c476fa6441c607096d93c8fc7ac0a227a655dae, licensed under Apache 2.0.
   The argument below uses the complex logarithm on each side of the rectangle. -/

/-- Counterclockwise boundary integral for the rectangle with real sides a and b
and imaginary sides c and d. -/
noncomputable def rectBoundaryIntegral (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x : ℝ in a..b, f (x + c * I)) - (∫ x : ℝ in a..b, f (x + d * I)) +
    I * (∫ y : ℝ in c..d, f (b + y * I)) - I * (∫ y : ℝ in c..d, f (a + y * I))

private lemma integral_div_affine (u v : ℂ) (a b : ℝ)
    (hpath : ∀ t ∈ [[a, b]], (t : ℂ) * v + u ∈ slitPlane) :
    (∫ t : ℝ in a..b, v / ((t : ℂ) * v + u)) =
      log ((b : ℂ) * v + u) - log ((a : ℂ) * v + u) := by
  have hint : IntervalIntegrable (fun t : ℝ => v / ((t : ℂ) * v + u)) volume a b :=
    (continuousOn_const.div (by fun_prop) fun t ht => slitPlane_ne_zero (hpath t ht)).intervalIntegrable
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => log ((s : ℂ) * v + u)) (fun t ht => ?_) hint
  have hreal : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := by
    have hf : (ofRealCLM : ℝ → ℂ) = (fun s : ℝ => (s : ℂ)) := rfl
    simpa only [hf, ofRealCLM_apply, ofReal_one] using (ofRealCLM.hasDerivAt (x := t))
  have haff : HasDerivAt (fun s : ℝ => (s : ℂ) * v + u) v t := by
    simpa only [one_mul] using (hreal.mul_const v).add_const u
  simpa only [Function.comp_def, smul_eq_mul, div_eq_mul_inv] using
    (hasDerivAt_log (hpath t ht)).scomp t haff

private lemma horizontal_inv (p : ℂ) (a b y : ℝ) (hy : y ≠ p.im) :
    (∫ x : ℝ in a..b, ((x : ℂ) + y * I - p)⁻¹) =
      log ((b : ℂ) + y * I - p) - log ((a : ℂ) + y * I - p) := by
  have hs (t : ℝ) : (t : ℂ) * 1 + ((y : ℂ) * I - p) ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    right
    simpa [add_im, sub_im, mul_im] using sub_ne_zero.mpr hy
  simpa only [mul_one, one_div, add_sub_assoc] using
    integral_div_affine ((y : ℂ) * I - p) 1 a b (fun t _ => hs t)

private lemma vertical_inv_right (p : ℂ) (x a b : ℝ) (hx : p.re < x) :
    I * (∫ y : ℝ in a..b, ((x : ℂ) + y * I - p)⁻¹) =
      log ((x : ℂ) + b * I - p) - log ((x : ℂ) + a * I - p) := by
  have hs (t : ℝ) : (t : ℂ) * I + ((x : ℂ) - p) ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    left
    simpa [add_re, sub_re, mul_re] using sub_pos.mpr hx
  rw [← intervalIntegral.integral_const_mul]
  simpa only [div_eq_mul_inv, ← add_sub_assoc, add_comm ((x : ℂ))] using
    integral_div_affine ((x : ℂ) - p) I a b (fun t _ => hs t)

private lemma vertical_inv_left (p : ℂ) (x a b : ℝ) (hx : x < p.re) :
    I * (∫ y : ℝ in a..b, ((x : ℂ) + y * I - p)⁻¹) =
      log (-((x : ℂ) + b * I - p)) - log (-((x : ℂ) + a * I - p)) := by
  have harg (t : ℝ) : (t : ℂ) * (-I) + (p - (x : ℂ)) = -((x : ℂ) + t * I - p) := by ring
  have hs (t : ℝ) : (t : ℂ) * (-I) + (p - (x : ℂ)) ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    left
    simpa [add_re, sub_re, mul_re, neg_re, neg_im] using sub_pos.mpr hx
  rw [← intervalIntegral.integral_const_mul]
  have h := integral_div_affine (p - (x : ℂ)) (-I) a b (fun t _ => hs t)
  simp only [harg] at h
  simpa only [div_eq_mul_inv, inv_neg, neg_mul, mul_neg, neg_neg] using h

private lemma log_sub_log_neg_pos {z : ℂ} (hz : 0 < z.im) :
    log z - log (-z) = (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [sub_re, log_re, mul_re]
  · simp [sub_im, log_im, mul_im, arg_neg_eq_arg_sub_pi_of_im_pos hz]

private lemma log_sub_log_neg_neg {z : ℂ} (hz : z.im < 0) :
    log z - log (-z) = -(Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [sub_re, log_re, mul_re, neg_re]
  · simp [sub_im, log_im, mul_im, arg_neg_eq_arg_add_pi_of_im_neg hz]

/-- The rectangle encloses p strictly, and the reciprocal has residue one there. -/
theorem rectBoundaryIntegral_inv_sub {a b c d : ℝ} {p : ℂ}
    (ha : a < p.re) (hb : p.re < b) (hc : c < p.im) (hd : p.im < d) :
    rectBoundaryIntegral (fun z => (z - p)⁻¹) a b c d = 2 * (Real.pi : ℂ) * I := by
  have htop : 0 < ((a : ℂ) + d * I - p).im := by
    simpa [add_im, sub_im, mul_im] using sub_pos.mpr hd
  have hbot : ((a : ℂ) + c * I - p).im < 0 := by
    simpa [add_im, sub_im, mul_im] using sub_neg.mpr hc
  unfold rectBoundaryIntegral
  rw [horizontal_inv p a b c hc.ne, horizontal_inv p a b d hd.ne',
    vertical_inv_right p b c d hb, vertical_inv_left p a c d ha]
  calc
    _ = (log ((a : ℂ) + d * I - p) - log (-((a : ℂ) + d * I - p))) -
        (log ((a : ℂ) + c * I - p) - log (-((a : ℂ) + c * I - p))) := by ring
    _ = _ := by rw [log_sub_log_neg_pos htop, log_sub_log_neg_neg hbot]; ring

private lemma integral_decompose {a b : ℝ} {f g : ℂ → ℂ}
    (S : Finset ℂ) (r : ℂ → ℂ) (γ : ℝ → ℂ) (hγ : Continuous γ)
    (hg : ContinuousOn (g ∘ γ) [[a, b]]) (haway : ∀ t ∈ [[a, b]], γ t ∉ S)
    (he : ∀ t ∈ [[a, b]], f (γ t) = g (γ t) + ∑ p ∈ S, r p / (γ t - p)) :
    (∫ t : ℝ in a..b, f (γ t)) =
      (∫ t : ℝ in a..b, g (γ t)) + ∑ p ∈ S, r p * (∫ t : ℝ in a..b, (γ t - p)⁻¹) := by
  have hterms (p : ℂ) (hp : p ∈ S) :
      ContinuousOn (fun t : ℝ => r p / (γ t - p)) [[a, b]] := by
    have hnum : ContinuousOn (fun _ : ℝ => r p) [[a, b]] := continuousOn_const
    have hdenom : ContinuousOn (fun t : ℝ => γ t - p) [[a, b]] :=
      (hγ.sub continuous_const).continuousOn
    exact hnum.div hdenom fun t ht => sub_ne_zero.mpr fun htp => haway t ht (htp.symm ▸ hp)
  have hsum : ContinuousOn (fun t : ℝ => ∑ p ∈ S, r p / (γ t - p)) [[a, b]] :=
    continuousOn_finsetSum S hterms
  calc
    _ = ∫ t : ℝ in a..b, g (γ t) + ∑ p ∈ S, r p / (γ t - p) :=
      intervalIntegral.integral_congr he
    _ = (∫ t : ℝ in a..b, g (γ t)) + ∑ p ∈ S, ∫ t : ℝ in a..b, r p / (γ t - p) := by
      have hgi : IntervalIntegrable (fun t : ℝ => g (γ t)) volume a b := hg.intervalIntegrable
      have hsi : IntervalIntegrable (fun t : ℝ => ∑ p ∈ S, r p / (γ t - p)) volume a b :=
        hsum.intervalIntegrable
      rw [intervalIntegral.integral_add hgi hsi]
      congr 1
      exact intervalIntegral.integral_finsetSum (fun p hp => (hterms p hp).intervalIntegrable)
    _ = _ := by simp_rw [div_eq_mul_inv, intervalIntegral.integral_const_mul]

private lemma rect_sum_combine (S : Finset ℂ) (r bot top right left : ℂ → ℂ) :
    (∑ p ∈ S, r p * bot p) - (∑ p ∈ S, r p * top p) +
      I * (∑ p ∈ S, r p * right p) - I * (∑ p ∈ S, r p * left p) =
    ∑ p ∈ S, r p * (bot p - top p + I * right p - I * left p) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- Boundary integration computes the sum of the residues at interior simple
poles if subtracting the principal parts leaves a continuous remainder that
is complex differentiable away from the poles. -/
theorem rectBoundaryIntegral_eq_sum_residues {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (f g : ℂ → ℂ) (S : Finset ℂ) (r : ℂ → ℂ)
    (hpoles : ∀ p ∈ S, a < p.re ∧ p.re < b ∧ c < p.im ∧ p.im < d)
    (hg : ContinuousOn g (Icc a b ×ℂ Icc c d))
    (hgd : ∀ z ∈ (Ioo a b ×ℂ Ioo c d) \ (S : Set ℂ), DifferentiableAt ℂ g z)
    (hfg : EqOn f (fun z => g z + ∑ p ∈ S, r p / (z - p))
      ((Icc a b ×ℂ Icc c d) \ (S : Set ℂ))) :
    rectBoundaryIntegral f a b c d = (2 * (Real.pi : ℂ) * I) * ∑ p ∈ S, r p := by
  have hgc : ContinuousOn g ([[a, b]] ×ℂ [[c, d]]) := by
    simpa only [uIcc_of_le hab, uIcc_of_le hcd] using hg
  have hgd' : ∀ z ∈ (Ioo (min a b) (max a b) ×ℂ Ioo (min c d) (max c d)) \ (S : Set ℂ),
      DifferentiableAt ℂ g z := by
    simpa only [min_eq_left hab, max_eq_right hab, min_eq_left hcd, max_eq_right hcd] using hgd
  have hzero : rectBoundaryIntegral g a b c d = 0 := by
    simpa only [rectBoundaryIntegral, smul_eq_mul] using
      Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
        g (⟨a, c⟩ : ℂ) (⟨b, d⟩ : ℂ) (S : Set ℂ) S.finite_toSet.countable hgc hgd'
  have edge {u v : ℝ} (γ : ℝ → ℂ) (hγ : Continuous γ)
      (hmem : MapsTo γ [[u, v]] (Icc a b ×ℂ Icc c d))
      (haway : ∀ t ∈ [[u, v]], γ t ∉ S) :=
    integral_decompose S r γ hγ (hg.comp hγ.continuousOn hmem) haway
      (fun t ht => hfg ⟨hmem ht, haway t ht⟩)
  have horizontal (y : ℝ) (hy : y ∈ Icc c d) (hy' : ∀ p ∈ S, y ≠ p.im) :=
    edge (u := a) (v := b) (fun x : ℝ => x + y * I) (by fun_prop)
      (fun t ht => by
        rw [mem_reProdIm]
        constructor
        · simpa [add_re, mul_re, uIcc_of_le hab] using ht
        · simpa [add_im, mul_im] using hy)
      (fun t _ hp => (hy' _ hp) (by simp [add_im, mul_im]))
  have vertical (x : ℝ) (hx : x ∈ Icc a b) (hx' : ∀ p ∈ S, x ≠ p.re) :=
    edge (u := c) (v := d) (fun y : ℝ => x + y * I) (by fun_prop)
      (fun t ht => by
        rw [mem_reProdIm]
        constructor
        · simpa [add_re, mul_re] using hx
        · simpa [add_im, mul_im, uIcc_of_le hcd] using ht)
      (fun t _ hp => (hx' _ hp) (by simp [add_re, mul_re]))
  have hdecomp :
      rectBoundaryIntegral f a b c d =
        rectBoundaryIntegral g a b c d +
          ∑ p ∈ S, r p * rectBoundaryIntegral (fun z => (z - p)⁻¹) a b c d := by
    unfold rectBoundaryIntegral
    rw [horizontal c ⟨le_rfl, hcd⟩ (fun p hp => (hpoles p hp).2.2.1.ne),
        horizontal d ⟨hcd, le_rfl⟩ (fun p hp => (hpoles p hp).2.2.2.ne'),
        vertical b ⟨hab, le_rfl⟩ (fun p hp => (hpoles p hp).2.1.ne'),
        vertical a ⟨le_rfl, hab⟩ (fun p hp => (hpoles p hp).1.ne)]
    rw [← rect_sum_combine]
    ring
  rw [hdecomp, hzero, zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨ha, hb, hc, hd⟩ := hpoles p hp
  rw [rectBoundaryIntegral_inv_sub ha hb hc hd]
  ring

end Goldbach

open Filter Set
open scoped BigOperators Topology

namespace Goldbach

private lemma analyticAt_logDeriv_of_ne_zero {F : ℂ → ℂ} {w : ℂ}
    (hF : AnalyticAt ℂ F w) (hFw : F w ≠ 0) : AnalyticAt ℂ (logDeriv F) w :=
  hF.deriv.div hF hFw

/-- The weighted logarithmic derivative at a finite-order zero has principal
part equal to its order times the weight at that zero, divided by the local
coordinate. The same formula applies at order zero. -/
theorem logDeriv_mul_local_polar_part {F K : ℂ → ℂ} {w : ℂ}
    (hF : AnalyticAt ℂ F w) (horder : analyticOrderAt F w ≠ ⊤)
    (hK : AnalyticAt ℂ K w) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G w ∧
      (fun z => logDeriv F z * K z - (analyticOrderNatAt F w : ℂ) * K w / (z - w))
        =ᶠ[𝓝[≠] w] G := by
  obtain ⟨A, hA, hA0, hfactor⟩ := hF.analyticOrderAt_ne_top.mp horder
  let m := analyticOrderNatAt F w
  let D : ℂ → ℂ := fun z => z - w
  have hD : Differentiable ℂ D := by dsimp [D]; fun_prop
  have hlogD (z : ℂ) : logDeriv D z = 1 / (z - w) := by
    simp [D, logDeriv_apply]
  have hfac : F =ᶠ[𝓝 w] fun z => D z ^ m * A z := by
    simpa only [D, m, smul_eq_mul] using hfactor
  have hz_ne : ∀ᶠ z in 𝓝[≠] w, z ≠ w := by
    simpa using (eventually_mem_nhdsWithin (a := w) (s := {w}ᶜ))
  have hlog : logDeriv F =ᶠ[𝓝[≠] w] fun z => (m : ℂ) / (z - w) + logDeriv A z := by
    filter_upwards [(logDeriv_congr_nhds hfac).filter_mono nhdsWithin_le_nhds,
      hA.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      (hA.continuousAt.eventually_ne hA0).filter_mono nhdsWithin_le_nhds, hz_ne]
      with z hdz hAz hAnz hzne
    have hDz : D z ≠ 0 := sub_ne_zero.mpr hzne
    rw [hdz, logDeriv_fun_mul (f := fun t => D t ^ m) (g := A) z (pow_ne_zero m hDz) hAnz
      (hD.differentiableAt.pow m) hAz.differentiableAt,
      logDeriv_fun_pow (f := D) hD.differentiableAt m, hlogD, mul_one_div]
  refine ⟨fun z => (m : ℂ) * dslope K w z + logDeriv A z * K z, ?_, ?_⟩
  · exact (analyticAt_const.mul (hK.dslope w)).add
      ((analyticAt_logDeriv_of_ne_zero hA hA0).mul hK)
  · filter_upwards [hlog, hz_ne] with z hz hzne
    have hds : dslope K w z = (K z - K w) / (z - w) := by
      apply (eq_div_iff (sub_ne_zero.mpr hzne)).mpr
      simpa only [smul_eq_mul, mul_comm] using sub_smul_dslope K w z
    change logDeriv F z * K z - (m : ℂ) * K w / (z - w) =
      (m : ℂ) * dslope K w z + logDeriv A z * K z
    rw [hz, hds]
    ring

private lemma analyticAt_principal_term (r p z : ℂ) (hz : z ≠ p) :
    AnalyticAt ℂ (fun t : ℂ => r / (t - p)) z := by
  have hnum : AnalyticAt ℂ (fun _ : ℂ => r) z := analyticAt_const
  have hdenom : AnalyticAt ℂ (fun t : ℂ => t - p) z := by fun_prop
  exact hnum.div hdenom (sub_ne_zero.mpr hz)

/-- Subtracting all principal parts of a weighted logarithmic derivative
leaves an analytic remainder. The equality is stated away from the finitely
many points where the principal parts have poles. -/
theorem logDeriv_mul_exists_analytic_remainder {F K : ℂ → ℂ} {U : Set ℂ}
    (S : Finset ℂ) (hSU : (S : Set ℂ) ⊆ U) (hF : AnalyticOnNhd ℂ F U)
    (hK : AnalyticOnNhd ℂ K U) (hzeros : ∀ z ∈ U, F z = 0 → z ∈ S)
    (horder : ∀ p ∈ S, analyticOrderAt F p ≠ ⊤) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G U ∧
      EqOn (fun z => logDeriv F z * K z)
        (fun z => G z + ∑ p ∈ S, (analyticOrderNatAt F p : ℂ) * K p / (z - p))
        (U \ (S : Set ℂ)) := by
  classical
  let r : ℂ → ℂ := fun p => (analyticOrderNatAt F p : ℂ) * K p
  have hlocal (p : ℂ) (hp : p ∈ S) :
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
        (fun z => logDeriv F z * K z - r p / (z - p)) =ᶠ[𝓝[≠] p] g :=
    logDeriv_mul_local_polar_part (hF p (hSU hp)) (horder p hp) (hK p (hSU hp))
  choose localPart hlocalA hlocalEq using hlocal
  let regular : ℂ → ℂ := fun z => logDeriv F z * K z - ∑ p ∈ S, r p / (z - p)
  let G : ℂ → ℂ := fun z =>
    if hz : z ∈ S then localPart z hz z - ∑ p ∈ S.erase z, r p / (z - p) else regular z
  refine ⟨G, ?_, ?_⟩
  · intro z hz
    by_cases hzS : z ∈ S
    · have havoid : ∀ᶠ t in 𝓝 z, t ∉ S.erase z :=
        (S.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
      have heq : ∀ᶠ t in 𝓝 z, t ≠ z →
          logDeriv F t * K t - r z / (t - z) = localPart z hzS t := by
        simpa using (eventually_nhdsWithin_iff.mp (hlocalEq z hzS))
      have hG : G =ᶠ[𝓝 z] fun t =>
          localPart z hzS t - ∑ p ∈ S.erase z, r p / (t - p) := by
        filter_upwards [havoid, heq] with t ht hEq
        by_cases htz : t = z
        · subst t
          simp only [G, dite_eq_left hzS]
        · have htS : t ∉ S := fun h => ht (Finset.mem_erase.mpr ⟨htz, h⟩)
          simp only [G, dite_eq_right htS, regular]
          rw [← Finset.sum_erase_add S (fun p => r p / (t - p)) hzS, ← hEq htz]
          ring
      have hA : AnalyticAt ℂ (fun t => ∑ p ∈ S.erase z, r p / (t - p)) z :=
        (S.erase z).analyticAt_fun_sum fun p hp =>
          analyticAt_principal_term (r p) p z (Finset.ne_of_mem_erase hp).symm
      exact ((hlocalA z hzS).sub hA).congr hG.symm
    · have havoid : ∀ᶠ t in 𝓝 z, t ∉ S :=
        S.finite_toSet.isClosed.isOpen_compl.mem_nhds hzS
      have hG : G =ᶠ[𝓝 z] regular := by
        filter_upwards [havoid] with t ht
        simp only [G, dite_eq_right ht]
      have hFz : F z ≠ 0 := fun hzF => hzS (hzeros z hz hzF)
      have hsum : AnalyticAt ℂ (fun t => ∑ p ∈ S, r p / (t - p)) z :=
        S.analyticAt_fun_sum fun p hp =>
          analyticAt_principal_term (r p) p z (fun h => hzS (h.symm ▸ hp))
      exact (((analyticAt_logDeriv_of_ne_zero (hF z hz) hFz).mul (hK z hz)).sub hsum).congr
        hG.symm
  · intro z hz
    have hzS : z ∉ S := hz.2
    change logDeriv F z * K z = G z + ∑ p ∈ S, r p / (z - p)
    simp only [G, dite_eq_right hzS, regular, sub_add_cancel]

end Goldbach

open Complex Filter Set MeasureTheory
open scoped BigOperators Interval Topology

namespace Goldbach

/-- Finite contour identity for the weighted logarithmic derivative with the
principal pole at one restored explicitly. -/
theorem rectBoundaryIntegral_neg_logDeriv_add_pole_mul
    {a b c d : ℝ} (F K : ℂ → ℂ) (S : Finset ℂ) (δ : ℂ)
    (ha : a < 1) (hb : 1 < b) (hc : c < 0) (hd : 0 < d)
    (hF : AnalyticOnNhd ℂ F (Icc a b ×ℂ Icc c d))
    (hK : AnalyticOnNhd ℂ K (Icc a b ×ℂ Icc c d))
    (hzeros : ∀ z ∈ Icc a b ×ℂ Icc c d, F z = 0 ↔ z ∈ S)
    (hinterior : ∀ p ∈ S, a < p.re ∧ p.re < b ∧ c < p.im ∧ p.im < d)
    (horder : ∀ p ∈ S, analyticOrderAt F p ≠ ⊤) (hF1 : F 1 ≠ 0) :
    rectBoundaryIntegral (fun z => (-logDeriv F z + δ / (z - 1)) * K z) a b c d =
      (2 * (Real.pi : ℂ) * I) * (δ * K 1 - ∑ p ∈ S, (analyticOrderNatAt F p : ℂ) * K p) := by
  classical
  let U := Icc a b ×ℂ Icc c d
  let T := insert (1 : ℂ) S
  let r : ℂ → ℂ := fun p => (analyticOrderNatAt F p : ℂ) * K p
  let coeff : ℂ → ℂ := fun p => if p = 1 then δ * K 1 else -r p
  have h1U : (1 : ℂ) ∈ U := by
    exact mem_reProdIm.mpr ⟨by simpa only [one_re] using Set.mem_Icc.mpr ⟨ha.le, hb.le⟩,
      by simpa only [one_im] using Set.mem_Icc.mpr ⟨hc.le, hd.le⟩⟩
  have h1S : (1 : ℂ) ∉ S := fun h => hF1 ((hzeros 1 h1U).mpr h)
  have hSU : (S : Set ℂ) ⊆ U := by
    intro p hp
    obtain ⟨hpa, hpb, hpc, hpd⟩ := hinterior p hp
    exact mem_reProdIm.mpr ⟨⟨hpa.le, hpb.le⟩, ⟨hpc.le, hpd.le⟩⟩
  have hT : ∀ p ∈ T, a < p.re ∧ p.re < b ∧ c < p.im ∧ p.im < d := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simpa only [one_re, one_im] using And.intro ha (And.intro hb (And.intro hc hd))
    · exact hinterior p hp
  have hcoeff1 : coeff 1 = δ * K 1 := ite_eq_left rfl
  have hcoeff (p : ℂ) (hp : p ∈ S) : coeff p = -r p := by
    have hp1 : p ≠ (1 : ℂ) := fun heq => h1S (heq ▸ hp)
    exact ite_eq_right hp1
  have hsum (z : ℂ) :
      (∑ p ∈ T, coeff p / (z - p)) =
        δ * K 1 / (z - 1) - ∑ p ∈ S, r p / (z - p) := by
    have hsumS : (∑ p ∈ S, coeff p / (z - p)) = -(∑ p ∈ S, r p / (z - p)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun p hp => by rw [hcoeff p hp, neg_div]
    change (∑ p ∈ insert (1 : ℂ) S, coeff p / (z - p)) = _
    rw [Finset.sum_insert h1S, hcoeff1, hsumS]
    exact (sub_eq_add_neg _ _).symm
  have hsum_coeff : (∑ p ∈ T, coeff p) = δ * K 1 - ∑ p ∈ S, r p := by
    have hsumS : (∑ p ∈ S, coeff p) = -(∑ p ∈ S, r p) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl hcoeff
    change (∑ p ∈ insert (1 : ℂ) S, coeff p) = _
    rw [Finset.sum_insert h1S, hcoeff1, hsumS, sub_eq_add_neg]
  obtain ⟨G, hG, hG_eq⟩ := logDeriv_mul_exists_analytic_remainder S hSU hF hK
    (fun z hz => (hzeros z hz).mp) horder
  let J : ℂ → ℂ := fun z => -G z + δ * dslope K 1 z
  have hJ : AnalyticOnNhd ℂ J U := by
    intro z hz
    exact (hG z hz).neg.add (analyticAt_const.mul ((hK z hz).dslope 1))
  have hJ_diff : ∀ z ∈ (Ioo a b ×ℂ Ioo c d) \ (T : Set ℂ), DifferentiableAt ℂ J z := by
    intro z hz
    obtain ⟨hr, hi⟩ := mem_reProdIm.mp hz.1
    exact (hJ z (mem_reProdIm.mpr ⟨Ioo_subset_Icc_self hr, Ioo_subset_Icc_self hi⟩)).differentiableAt
  have hEq : EqOn (fun z => (-logDeriv F z + δ / (z - 1)) * K z)
      (fun z => J z + ∑ p ∈ T, coeff p / (z - p)) (U \ (T : Set ℂ)) := by
    intro z hz
    have hzT : z ∉ T := hz.2
    have hzS : z ∉ S := fun h => hzT (Finset.mem_insert_of_mem h)
    have hz1 : z ≠ (1 : ℂ) := fun h => hzT (Finset.mem_insert.mpr (Or.inl h))
    have hGK := hG_eq ⟨hz.1, hzS⟩
    change logDeriv F z * K z = G z + ∑ p ∈ S, r p / (z - p) at hGK
    have hds : dslope K 1 z = (K z - K 1) / (z - 1) := by
      apply (eq_div_iff (sub_ne_zero.mpr hz1)).mpr
      simpa only [smul_eq_mul, mul_comm] using sub_smul_dslope K 1 z
    change (-logDeriv F z + δ / (z - 1)) * K z =
      (-G z + δ * dslope K 1 z) + ∑ p ∈ T, coeff p / (z - p)
    rw [hsum, hds]
    calc
      _ = -(logDeriv F z * K z) + δ / (z - 1) * K z := by ring
      _ = _ := by rw [hGK]; ring
  rw [rectBoundaryIntegral_eq_sum_residues (ha.le.trans hb.le) (hc.le.trans hd.le)
    _ J T coeff hT hJ.continuousOn hJ_diff hEq, hsum_coeff]

/-- Solve a rectangular contour identity for its right vertical integral. -/
theorem right_vertical_integral_of_rect {f : ℂ → ℂ} {a b c d : ℝ} {R : ℂ}
    (h : rectBoundaryIntegral f a b c d = 2 * (Real.pi : ℂ) * I * R) :
    (∫ y : ℝ in c..d, f (b + y * I)) =
      (∫ y : ℝ in c..d, f (a + y * I)) + 2 * (Real.pi : ℂ) * R +
        I * ((∫ x : ℝ in a..b, f (x + c * I)) - ∫ x : ℝ in a..b, f (x + d * I)) := by
  unfold rectBoundaryIntegral at h
  set bottom := (∫ x : ℝ in a..b, f (x + c * I))
  set top := (∫ x : ℝ in a..b, f (x + d * I))
  set left := (∫ y : ℝ in c..d, f (a + y * I))
  set right := (∫ y : ℝ in c..d, f (b + y * I))
  calc
    right = left - I * (bottom - top + I * right - I * left) + I * (bottom - top) := by
      ring_nf
      simp only [I_sq]
      ring
    _ = _ := by
      rw [h]
      ring_nf
      simp only [I_sq]
      ring

end Goldbach
namespace Goldbach

open Complex Filter MeasureTheory Set
open scoped BigOperators Interval Topology

theorem uniform_dirichlet_log_control : ∃ C : ℝ, 0 < C ∧ UniformDirichletLogDerivative C := by
  obtain ⟨C, hC, h⟩ := norm_logDeriv_regularizedL_le
  refine ⟨C, hC, ?_⟩
  intro q _ χ σ t d hσ hd hdist
  have hpoint : (⟨σ, t⟩ : ℂ) = (σ : ℂ) + (t : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [← hpoint] at hdist ⊢
  exact h q χ t σ d hσ.1 hσ.2 hd hdist
end Goldbach
end
end
end


section
section GoldbachGRHWindowParseval

open scoped BigOperators ComplexConjugate
open Finset

namespace GoldbachGRHWindow

noncomputable section

private theorem norm_energy_of_columns {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] (K : A → B → ℂ) (D : A → ℝ)
    (hK : ∀ r s : A, (∑ b : B, conj (K r b) * K s b) =
      if r = s then (D r : ℂ) else 0) (f : A → ℂ) :
    (∑ b : B, ‖∑ r : A, f r * K r b‖ ^ 2) =
      ∑ r : A, D r * ‖f r‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.conj_mul']
  calc
    _ = ∑ b : B, ∑ r : A, ∑ s : A, conj (f r) * f s * (conj (K r b) * K s b) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
      ring
    _ = ∑ r : A, ∑ s : A, conj (f r) * f s * (∑ b : B, conj (K r b) * K s b) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [hK, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      ring

variable {q : ℕ} [NeZero q]

local instance : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _

theorem additive_energy (f : ZMod q → ℂ) :
    (∑ a : ZMod q, ‖∑ r : ZMod q, f r * ZMod.stdAddChar (a * r)‖ ^ 2) =
      (q : ℝ) * ∑ r : ZMod q, ‖f r‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply norm_energy_of_columns (fun r a => ZMod.stdAddChar (a * r)) (fun _ => (q : ℝ))
  intro r s
  have hc (z : ZMod q) : conj (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
    rw [AddChar.map_neg_eq_inv]
    exact (Complex.inv_eq_conj (by simp [ZMod.stdAddChar_apply])).symm
  simp only [hc, ← AddChar.map_add_eq_mul, ← mul_neg, ← mul_add]
  by_cases h : r = s
  · simp [h, ZMod.card]
  · rw [ite_eq_right h]
    have hne : -r + s ≠ 0 := by
      simpa only [sub_eq_add_neg, add_comm] using (sub_ne_zero.mpr (fun he : s = r => h he.symm) : s - r ≠ 0)
    calc
      _ = ∑ a : ZMod q, ZMod.stdAddChar ((-r + s) * a) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [mul_comm]
      _ = 0 := AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hne)

omit [NeZero q] in
private theorem char_conj_of_unit (χ : DirichletCharacter ℂ q) {r : ZMod q}
    (hr : IsUnit r) : conj (χ r) = χ r⁻¹ := by
  have hχr : χ r ≠ 0 := (hr.map χ).ne_zero
  have hi : χ r⁻¹ = (χ r)⁻¹ := by
    calc
      _ = χ r⁻¹ * (χ r * (χ r)⁻¹) := by rw [mul_inv_cancel₀ hχr, mul_one]
      _ = _ := by rw [← mul_assoc, ← map_mul, ZMod.inv_mul_of_unit r hr, map_one, one_mul]
  exact (MulChar.star_apply' χ r).trans ((MulChar.inv_apply_eq_inv' χ r).trans hi.symm)

theorem multiplicative_energy (f : ZMod q → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ r : ZMod q, f r * χ r‖ ^ 2) =
      (q.totient : ℝ) * ∑ r ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖f r‖ ^ 2 := by
  rw [Finset.sum_filter, Finset.mul_sum]
  have hParseval := norm_energy_of_columns (fun r (χ : DirichletCharacter ℂ q) => χ r)
    (fun r : ZMod q => if IsUnit r then (q.totient : ℝ) else 0)
    (f := f) (by
      intro r s
      by_cases hr : IsUnit r
      · simp only [char_conj_of_unit _ hr, ite_eq_left hr, Complex.ofReal_natCast]
        exact DirichletCharacter.sum_char_inv_mul_char_eq ℂ hr s
      · simp [hr, MulChar.map_nonunit _ hr])
  rw [hParseval]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : IsUnit r <;> simp [hr]

/-- The additive coefficient of the unit-uniform residue distribution. -/
noncomputable def additiveModel (q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  (∑ u : (ZMod q)ˣ, ZMod.stdAddChar (a * (u : ZMod q))) / (q.totient : ℂ)

private noncomputable def residueSum (I : Finset ℕ) (w : ℕ → ℂ) (r : ZMod q) : ℂ :=
  ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r), w k

private noncomputable def residueError (I : Finset ℕ) (w : ℕ → ℂ) (r : ZMod q) : ℂ :=
  residueSum I w r - if IsUnit r then (I.card : ℂ) / (q.totient : ℂ) else 0

private theorem sum_residueSum_mul (I : Finset ℕ) (w : ℕ → ℂ) (K : ZMod q → ℂ) :
    (∑ r : ZMod q, residueSum I w r * K r) =
      ∑ k ∈ I, w k * K (k : ZMod q) := by
  calc
    _ = ∑ r : ZMod q, ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r),
        w k * K (k : ZMod q) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [residueSum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [(Finset.mem_filter.mp hk).2]
    _ = _ := Finset.sum_fiberwise I (fun k => (k : ZMod q)) _

private theorem sum_if_isUnit (F : ZMod q → ℂ) :
    (∑ r : ZMod q, if IsUnit r then F r else 0) = ∑ u : (ZMod q)ˣ, F (u : ZMod q) := by
  classical
  rw [← Finset.sum_filter]
  have hs : (univ : Finset (ZMod q)).filter IsUnit =
      (univ : Finset (ZMod q)ˣ).map ⟨(↑), Units.val_injective⟩ := by
    ext r
    simp [IsUnit]
  rw [hs, Finset.sum_map]
  rfl

private theorem residueError_character (I : Finset ℕ) (w : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) :
    (∑ r : ZMod q, residueError I w r * χ r) =
      (∑ k ∈ I, w k * χ (k : ZMod q)) - (if χ = 1 then (I.card : ℂ) else 0) := by
  classical
  unfold residueError
  simp only [sub_mul, Finset.sum_sub_distrib, sum_residueSum_mul]
  congr 1
  have hs : (∑ r : ZMod q, (if IsUnit r then (I.card : ℂ) / (q.totient : ℂ) else 0) * χ r) =
      ((I.card : ℂ) / (q.totient : ℂ)) * (∑ r : ZMod q, χ r) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hr : IsUnit r
    · simp [hr]
    · simp [hr, MulChar.map_nonunit χ hr]
  rw [hs]
  by_cases hχ : χ = 1
  · subst χ
    rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient, ite_eq_left rfl]
    exact div_mul_cancel₀ _ (by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne')
  · rw [MulChar.sum_eq_zero_of_ne_one hχ, mul_zero, ite_eq_right hχ]

private theorem residueError_additive (I : Finset ℕ) (w : ℕ → ℂ) (a : ZMod q) :
    (∑ r : ZMod q, residueError I w r * ZMod.stdAddChar (a * r)) =
      ∑ k ∈ I, (w k * ZMod.stdAddChar (a * (k : ZMod q)) - additiveModel q a) := by
  classical
  simp only [residueError, sub_mul, Finset.sum_sub_distrib, sum_residueSum_mul]
  congr 1
  calc
    _ = ((I.card : ℂ) / (q.totient : ℂ)) *
        (∑ r : ZMod q, if IsUnit r then ZMod.stdAddChar (a * r) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : IsUnit r <;> simp [hr]
    _ = _ := by
      rw [sum_if_isUnit, Finset.sum_const, nsmul_eq_mul]
      unfold additiveModel
      simp only [div_eq_mul_inv]
      ring

/-- Squared short-window error at all additive numerators, from uniform
    individual character bounds and an absolute mass bound at nonunits. -/
theorem sum_additive_window_error_sq_le (I : Finset ℕ) (w : ℕ → ℂ)
    (B P : ℝ) (_hB : 0 ≤ B) (_hP : 0 ≤ P)
    (hχ : ∀ χ : DirichletCharacter ℂ q,
      ‖(∑ k ∈ I, w k * χ (k : ZMod q)) - (if χ = 1 then (I.card : ℂ) else 0)‖ ≤ B)
    (hnon : (∑ k ∈ I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q)), ‖w k‖) ≤ P) :
    (∑ a : ZMod q,
      ‖∑ k ∈ I, (w k * ZMod.stdAddChar (a * (k : ZMod q)) - additiveModel q a)‖ ^ 2) ≤
      (q : ℝ) * (B ^ 2 + P ^ 2) := by
  classical
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hCard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hUnit : (∑ r ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖residueError I w r‖ ^ 2) ≤
      B ^ 2 := by
    apply le_of_mul_le_mul_left _ hφ
    rw [← multiplicative_energy]
    calc
      _ ≤ ∑ χ : DirichletCharacter ℂ q, B ^ 2 := by
        refine Finset.sum_le_sum fun χ _ => ?_
        rw [residueError_character]
        exact pow_le_pow_left₀ (norm_nonneg _) (hχ χ) 2
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hCard]
  let V : Finset (ZMod q) := univ.filter (fun r => ¬ IsUnit r)
  have hV : (∑ r ∈ V, ‖residueError I w r‖) ≤ P := by
    calc
      _ ≤ ∑ r ∈ V, ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r), ‖w k‖ := by
        refine Finset.sum_le_sum fun r hr => ?_
        have hr' : ¬ IsUnit r := (Finset.mem_filter.mp hr).2
        simpa [residueError, hr', residueSum] using
          norm_sum_le (I.filter (fun k : ℕ => (k : ZMod q) = r)) w
      _ = ∑ k ∈ I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q)), ‖w k‖ := by
        rw [Finset.sum_fiberwise_eq_sum_filter]
        simp [V]
      _ ≤ _ := hnon
  have hNonUnit : (∑ r ∈ V, ‖residueError I w r‖ ^ 2) ≤ P ^ 2 :=
    (Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)).trans
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hV 2)
  simp_rw [← residueError_additive]
  rw [additive_energy]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := (univ : Finset (ZMod q))) (p := IsUnit)]
  exact add_le_add hUnit hNonUnit

/-- The additive kernel written with the phase convention used in the frozen theorem. -/
theorem stdAddChar_mul_nat (a : ZMod q) (k : ℕ) :
    ZMod.stdAddChar (a * (k : ZMod q)) =
      Complex.exp (((2 * Real.pi * ((k : ℝ) * ((a.val : ℝ) / (q : ℝ))) : ℝ) : ℂ) *
        Complex.I) := by
  have ha : (↑(a.val * k) : ZMod q) = a * (k : ZMod q) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  calc
    _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (↑(a.val * k) : ℂ) / q) := by
      rw [← ha]
      simpa only [Int.cast_natCast] using ZMod.stdAddChar_coe (N := q) (a.val * k : ℕ)
    _ = _ := by
      congr 1
      push_cast
      ring

/-- Write the character of two natural residues without reducing either natural number. -/
theorem stdAddChar_nat_pair (a k : ℕ) :
    ZMod.stdAddChar ((a : ZMod q) * (k : ZMod q)) =
      Complex.exp (((2 * Real.pi * ((a : ℝ) * (k : ℝ) / (q : ℝ)) : ℝ) : ℂ) *
        Complex.I) := by
  have h := ZMod.stdAddChar_coe (N := q) (a * k : ℕ)
  push_cast at h
  rw [h]
  congr 1
  push_cast
  ring

/-- Express the unit-model coefficient as the exact reduced numerator sum
    occurring in the major-arc statements. -/
theorem additiveModel_eq_reduced_sum (a : ℕ) :
    additiveModel q (a : ZMod q) =
      (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        Complex.exp (((2 * Real.pi * ((a : ℝ) * (r : ℝ) / (q : ℝ)) : ℝ) : ℂ) *
          Complex.I)) / (q.totient : ℂ) := by
  unfold additiveModel
  congr 1
  apply Finset.sum_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q).val)
  · intro u _
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (ZMod.val_lt (u : ZMod q)), ZMod.val_coe_unit_coprime u⟩
  · intro u _ v _ huv
    apply Units.ext
    simpa only [ZMod.natCast_zmod_val] using congrArg (fun x : ℕ => (x : ZMod q)) huv
  · intro r hr
    obtain ⟨hrange, hcop⟩ := Finset.mem_filter.mp hr
    let hrunit : IsUnit (r : ZMod q) := (ZMod.isUnit_iff_coprime r q).mpr hcop
    exact ⟨hrunit.unit, Finset.mem_univ _, by
      rw [IsUnit.unit_spec, ZMod.val_natCast_of_lt (Finset.mem_range.mp hrange)]⟩
  · intro u _
    rw [← stdAddChar_nat_pair (q := q) a ((u : ZMod q).val), ZMod.natCast_zmod_val]

/-- A reduced numerator changes only the order of the same unit residues. -/
theorem additiveModel_of_unit (a : ZMod q) (ha : IsUnit a) :
    additiveModel q a = additiveModel q 1 := by
  unfold additiveModel
  apply congrArg (fun z : ℂ => z / (q.totient : ℂ))
  let e : (ZMod q)ˣ ≃ (ZMod q)ˣ := Equiv.mulLeft ha.unit
  refine Fintype.sum_equiv e (fun u => ZMod.stdAddChar (a * (u : ZMod q)))
    (fun u => ZMod.stdAddChar (1 * (u : ZMod q))) ?_
  intro u
  change ZMod.stdAddChar (a * (u : ZMod q)) =
    ZMod.stdAddChar (1 * (((ha.unit * u) : (ZMod q)ˣ) : ZMod q))
  rw [one_mul, Units.val_mul, IsUnit.unit_spec]

/-- Prime-logarithmic weights, represented in the complex field. -/
noncomputable def primeLog (k : ℕ) : ℂ :=
  ((if Nat.Prime k then Real.log (k : ℝ) else 0 : ℝ) : ℂ)

/-- A prime in a nonunit residue must divide the modulus. Its total
    logarithmic mass in any window is at most the logarithm of the modulus. -/
theorem primeLog_nonunit_mass_le (I : Finset ℕ) :
    (∑ k ∈ I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q)), ‖primeLog k‖) ≤
      Real.log (q : ℝ) := by
  let J := I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q))
  change (∑ k ∈ J, ‖primeLog k‖) ≤ _
  have hsub : J.filter Nat.Prime ⊆ q.primeFactors := by
    intro k hk
    obtain ⟨hkJ, hp⟩ := Finset.mem_filter.mp hk
    have hnu := (Finset.mem_filter.mp hkJ).2
    have hd : k ∣ q := by
      by_contra hnd
      exact hnu ((ZMod.isUnit_iff_coprime k q).mpr ((hp.coprime_iff_not_dvd).mpr hnd))
    exact Nat.mem_primeFactors.mpr ⟨hp, hd, NeZero.ne q⟩
  calc
    _ = ∑ k ∈ J.filter Nat.Prime, Real.log (k : ℝ) := by
      conv_rhs => rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hp : Nat.Prime k
      · have hk : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k from hp.pos)
        simp only [primeLog, ite_eq_left hp, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hk)]
      · simp [primeLog, hp]
    _ ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_
      exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
    _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
      symm
      exact Real.log_prod fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    _ ≤ _ := by
      apply Real.log_le_log (Finset.prod_pos fun p hp => by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd (NeZero.pos q) (Nat.prod_primeFactors_dvd q)

end

end GoldbachGRHWindow

end GoldbachGRHWindowParseval
section GoldbachGRHBandBase

/- The arithmetic foundation is adapted from muxkin's goldbach-proofs PR #2458,
   commit 25c1ef60495052eb22212b5560f90bbc6a4a0917 (Apache-2.0).
   Its source notes attributing earlier components are retained below. -/

/- The finite Ramanujan identities, kernel identities, CRT and prime-power computations
used below adapt DFQDZZ's goldbach-proofs PR #316, commit
e4ab24712555ae8c2c926adf19d368a9fb392c35 (Apache-2.0). Original credits are
retained with the corresponding sections. The multiplicative averaging, sieve estimates,
convolution bounds and the moving-modulus-window argument are derived below. -/

section

/-!
# An explicit lower bound for the Ramanujan-weighted major-arc model

The arithmetic and kernel estimates below are extracted from DFQDZZ's
goldbach-proofs PR #316 (commit e4ab24712555ae8c2c926adf19d368a9fb392c35,
Apache-2.0). The CRT and prime-power computations are credited below.
The estimate applies to every positive even target.
-/

open Finset Filter MeasureTheory

namespace GoldbachExplicitModeledMajor
noncomputable section

def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def cutoff (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2

def kernel (n : ℕ) (β : ℝ) : ℂ := ∑ k ∈ range (n + 1), phase ((k : ℝ) * β)

def width (n q : ℕ) : ℝ := (cutoff n : ℝ) / ((q : ℝ) * n)

def kernelMass (n : ℕ) (b : ℝ) : ℝ := ∫ β in -b..b, ‖kernel n β‖ ^ 2

private theorem continuous_kernel (n : ℕ) : Continuous (kernel n) := by
  unfold kernel phase
  fun_prop

theorem kernelMass_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (n : ℕ) :
    kernelMass n u ≤ kernelMass n v :=
  intervalIntegral.integral_mono_interval (neg_le_neg huv) (by linarith) huv
    (Eventually.of_forall fun _ => sq_nonneg _) (((continuous_kernel n).norm.pow 2).intervalIntegrable _ _)

private theorem kernel_on_zero_arc {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Set.Icc 0 (1 / (6 * (n : ℝ)))) : (n : ℝ) / 2 ≤ ‖kernel n t‖ := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnt := (le_div_iff₀ (show 0 < 6 * (n : ℝ) by positivity)).mp ht.2
  have hc (k : ℕ) (hk : k ∈ range (n + 1)) :
      1 / 2 ≤ (phase ((k : ℝ) * t)).re := by
    rw [phase, Complex.exp_ofReal_mul_I_re, ← Real.cos_pi_div_three]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) ht.1)
    · linarith [Real.pi_pos]
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hkt := mul_le_mul_of_nonneg_right hk' ht.1
    nlinarith only [mul_le_mul_of_nonneg_left hnt Real.pi_pos.le,
      mul_le_mul_of_nonneg_left hkt Real.pi_pos.le]
  calc
    _ ≤ ∑ _k ∈ range (n + 1), (1 / 2 : ℝ) := by simp; linarith
    _ ≤ ∑ k ∈ range (n + 1), (phase ((k : ℝ) * t)).re := sum_le_sum hc
    _ = (kernel n t).re := by rw [kernel, Complex.re_sum]
    _ ≤ _ := Complex.re_le_norm _

/-- Each width at least 1/(6n) captures a positive linear amount of the model's mass. -/
theorem kernelMass_floor {n : ℕ} (hn : 0 < n) {b : ℝ} (hb : 1 / (6 * (n : ℝ)) ≤ b) :
    (n : ℝ) / 24 ≤ kernelMass n b := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  let u : ℝ := 1 / (6 * (n : ℝ))
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hb0 : 0 ≤ b := hu.trans hb
  have hc := (continuous_kernel n).norm.pow 2
  calc
    _ = ∫ _t in (0 : ℝ)..u, ((n : ℝ) / 2) ^ 2 := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul, u]
      field_simp
      ring
    _ ≤ ∫ t in (0 : ℝ)..u, ‖kernel n t‖ ^ 2 :=
      intervalIntegral.integral_mono_on hu (by simp) (hc.intervalIntegrable _ _) fun _ ht =>
        pow_le_pow_left₀ (by positivity) (kernel_on_zero_arc hn ht) 2
    _ ≤ _ := intervalIntegral.integral_mono_interval (neg_nonpos.mpr hb0) hu hb
      (Eventually.of_forall fun _ => sq_nonneg _) (hc.intervalIntegrable _ _)

theorem cutoff_positive (n : ℕ) : 1 ≤ cutoff n :=
  Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (Nat.log_pos (by decide : 1 < 2) (by omega : 2 ≤ n+2)).ne')

theorem width_nonneg (n q : ℕ) : 0 ≤ width n q := by unfold width; positivity

end
end GoldbachExplicitModeledMajor

/- The finite CRT and prime-power calculations below adapt goldbach-proofs PRs #207 (XianWu18) and #203 (wzhxzkk), Apache-2.0. -/
namespace GoldbachExplicitModeledMajor.RamanujanCRT
private def unitsBelow (m : ℕ) := (Finset.range m).filter (fun a => Nat.Coprime a m)

private theorem unitsBelow_card (m : ℕ) : (unitsBelow m).card = m.totient := by
  unfold unitsBelow
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_congr_right (fun _ => Nat.coprime_comm)

private noncomputable def phase (m h a : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((h : ℝ) * a / m) : ℝ) : ℂ) * Complex.I)

private theorem phase_character (m h a : ℕ) [NeZero m] :
    phase m h a = ZMod.stdAddChar ((h : ZMod m) * (a : ZMod m)) := by
  have ch := ZMod.stdAddChar_coe (N := m) ((h * a : ℕ) : ℤ)
  push_cast at ch
  rw [ch]
  unfold phase
  push_cast
  congr 1
  ring

private theorem phase_modulus (m h a : ℕ) [NeZero m] :
    phase m h (a % m) = phase m h a := by
  simp only [phase_character, ZMod.natCast_mod]

private theorem phase_pair (q r h a b : ℕ) (hq : 0 < q) (hr : 0 < r) :
    phase (q*r) h ((r*a + q*b) % (q*r)) = phase q h a * phase r h b := by
  have : NeZero (q*r) := ⟨Nat.ne_of_gt (Nat.mul_pos hq hr)⟩
  rw [phase_modulus]
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  have qnz : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have rnz : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

theorem crt :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ q r h, 0<q → 0<r → Nat.Coprime q r → ram (q*r) h=ram q h*ram r h := by
  dsimp only
  intro q r h hq hr cop
  let combine (x : ℕ × ℕ) := (r*x.1 + q*x.2) % (q*r)
  let pairs := unitsBelow q ×ˢ unitsBelow r
  have member {m a : ℕ} : a ∈ unitsBelow m ↔ a < m ∧ Nat.Coprime a m := by
    simp only [unitsBelow, Finset.mem_filter, Finset.mem_range]
  have maps : pairs.image combine ⊆ unitsBelow (q*r) := by
    intro z hz
    obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    apply member.mpr
    refine ⟨Nat.mod_lt _ (Nat.mul_pos hq hr), ?_⟩
    change Nat.gcd ((r*a + q*b) % (q*r)) (q*r) = 1
    rw [← Nat.gcd_rec]
    change Nat.Coprime (q*r) (r*a + q*b)
    apply Nat.coprime_mul_iff_left.mpr
    constructor
    · rw [Nat.coprime_add_mul_left_right]
      exact cop.mul_right (member.mp ha).2.symm
    · rw [add_comm, Nat.coprime_add_mul_left_right]
      exact cop.symm.mul_right (member.mp hb).2.symm
  have injective : Set.InjOn combine (↑pairs) := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
    have congruence : r*a + q*b ≡ r*c + q*d [MOD q*r] := he
    apply Prod.ext
    · have hmod := congruence.of_dvd (dvd_mul_right q r)
      have reduced : r*a ≡ r*c [MOD q] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop reduced).eq_of_lt_of_lt
        (member.mp ha).1 (member.mp hc).1
    · have hmod := congruence.of_dvd (dvd_mul_left r q)
      have reduced : q*b ≡ q*d [MOD r] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop.symm reduced).eq_of_lt_of_lt
        (member.mp hb).1 (member.mp hd).1
  have covers : pairs.image combine = unitsBelow (q*r) := by
    apply Finset.eq_of_subset_of_card_le maps
    rw [Finset.card_image_of_injOn injective, unitsBelow_card, Nat.totient_mul cop]
    simp only [pairs, Finset.card_product, unitsBelow_card]
    exact le_rfl
  change (∑ z ∈ unitsBelow (q*r), phase (q*r) h z) =
    (∑ a ∈ unitsBelow q, phase q h a) * ∑ b ∈ unitsBelow r, phase r h b
  rw [← covers, Finset.sum_image injective, Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  exact Finset.sum_congr rfl (fun x _ => phase_pair q r h x.1 x.2 hq hr)

end GoldbachExplicitModeledMajor.RamanujanCRT
namespace GoldbachExplicitModeledMajor.RamanujanPower
open Finset

theorem primePower :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ p j h, Nat.Prime p → ram (p^(j+1)) h = (if p^(j+1) ∣ h then ((p^(j+1):ℕ):ℂ) else 0) - (if p^j ∣ h then ((p^j:ℕ):ℂ) else 0) := by
  intro E ram p j h hp
  have full (q : ℕ) (hq : 0 < q) :
      ∑ a ∈ range q, E ((h:ℝ) * a / q) = if q ∣ h then (q:ℂ) else 0 := by
    let : NeZero q := ⟨hq.ne'⟩
    calc
      _ = ∑ x : ZMod q, ZMod.stdAddChar ((h : ZMod q) * x) := by
        apply Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q))
        · intro a ha
          exact mem_univ _
        · intro a ha b hb hab
          simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha),
            ZMod.val_natCast_of_lt (mem_range.mp hb)] using congrArg ZMod.val hab
        · intro x _
          exact ⟨x.val, mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
        · intro a _
          have cast_eq : (h : ZMod q) * a = ((h * a : ℕ) : ℤ) := by push_cast; rfl
          rw [cast_eq, ZMod.stdAddChar_coe]
          dsimp [E]
          congr 1
          push_cast
          ring
      _ = _ := by
        by_cases hd : q ∣ h
        · have hz : (h : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff h q).mpr hd
          simp [hd, hz, ZMod.card]
        · have hz : (h : ZMod q) ≠ 0 := fun hz => hd ((ZMod.natCast_eq_zero_iff h q).mp hz)
          rw [ite_eq_right hd]
          exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hz)
  let m := p ^ j
  have hm : 0 < m := pow_pos hp.pos _
  let mult := (range m).image (fun b => p * b)
  have hsub : mult ⊆ range (p^(j+1)) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    rw [mem_range, pow_succ']
    exact Nat.mul_lt_mul_of_pos_left (mem_range.mp hb) hp.pos
  have hfilter : (range (p^(j+1))).filter (fun a => Nat.Coprime a (p^(j+1))) =
      range (p^(j+1)) \ mult := by
    rw [sdiff_eq_filter]
    apply filter_congr
    intro a ha
    rw [Nat.coprime_pow_right_iff (Nat.succ_pos j), Nat.coprime_comm, hp.coprime_iff_not_dvd]
    apply not_congr
    constructor
    · rintro ⟨b, rfl⟩
      apply mem_image.mpr
      refine ⟨b, mem_range.mpr ?_, rfl⟩
      rw [mem_range, pow_succ'] at ha
      exact (Nat.mul_lt_mul_left hp.pos).mp ha
    · intro ha'
      obtain ⟨b, _, rfl⟩ := mem_image.mp ha'
      exact dvd_mul_right _ _
  have removed : ∑ a ∈ mult, E ((h:ℝ)*a/(p^(j+1):ℕ)) =
      ∑ b ∈ range m, E ((h:ℝ)*b/m) := by
    rw [show mult = (range m).image (fun b => p * b) from rfl,
      sum_image (mul_right_injective₀ hp.ne_zero).injOn]
    apply sum_congr rfl
    intro b _
    congr 1
    rw [pow_succ']
    push_cast
    dsimp [m]
    push_cast
    field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne_zero]
  change ∑ a ∈ (range (p^(j+1))).filter _, E ((h:ℝ)*a/(p^(j+1):ℕ)) = _
  rw [hfilter, ← full _ (pow_pos hp.pos (j+1)), ← full _ hm, ← removed]
  exact eq_sub_of_add_eq (sum_sdiff hsub)

end GoldbachExplicitModeledMajor.RamanujanPower

namespace GoldbachExplicitModeledMajor

open Finset
open scoped ComplexConjugate
noncomputable section

def ram (q h : ℕ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => a.Coprime q), phase ((h : ℝ) * a / q)

theorem ram_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (h : ℕ) :
    ram (q * r) h = ram q h * ram r h := RamanujanCRT.crt q r h hq hr hc

theorem ram_primePower (p j h : ℕ) (hp : p.Prime) :
    ram (p ^ (j + 1)) h = (if p ^ (j + 1) ∣ h then ((p ^ (j + 1) : ℕ) : ℂ) else 0) -
      (if p ^ j ∣ h then ((p ^ j : ℕ) : ℂ) else 0) := RamanujanPower.primePower p j h hp

theorem ram_one (h : ℕ) : ram 1 h = 1 := by simp [ram, phase]

theorem ram_prime {p : ℕ} (hp : p.Prime) (h : ℕ) :
    ram p h = (if p ∣ h then (p : ℂ) else 0) - 1 := by
  simpa using ram_primePower p 0 h hp

private theorem ram_unit_power {p : ℕ} (hp : p.Prime) (j h : ℕ) (hc : h.Coprime p) :
    ram (p ^ (j + 1)) h = if j = 0 then -1 else 0 := by
  have hd := hp.coprime_iff_not_dvd.mp hc.symm
  have hpow (k : ℕ) : ¬ p ^ (k + 1) ∣ h :=
    fun hh => hd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans hh)
  rw [ram_primePower p j h hp, ite_eq_right (hpow j)]
  cases j with
  | zero => simp
  | succ k => simp [hpow k]

def localCoefficient (p n : ℕ) : ℝ :=
  if p ∣ n then 1 / ((p : ℝ) - 1) else -(1 / ((p : ℝ) - 1) ^ 2)

def coefficient (q n : ℕ) : ℂ := (ram q 1 / (q.totient : ℂ)) ^ 2 * conj (ram q n)

theorem coefficient_one (n : ℕ) : coefficient 1 n = 1 := by simp [coefficient, ram_one]

theorem coefficient_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (n : ℕ) :
    coefficient (q * r) n = coefficient q n * coefficient r n := by
  unfold coefficient
  rw [ram_mul hq hr hc, ram_mul hq hr hc, Nat.totient_mul hc, Nat.cast_mul, map_mul]
  ring

theorem coefficient_prime {p : ℕ} (hp : p.Prime) (n : ℕ) :
    coefficient p n = (localCoefficient p n : ℂ) := by
  have hone : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.mp h)
  have hne : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [coefficient, ram_prime hp, ram_prime hp, ite_eq_right hone, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le, Nat.cast_one]
  by_cases hd : p ∣ n <;> simp [localCoefficient, hd] <;> field_simp

theorem coefficient_higher_power {p : ℕ} (hp : p.Prime) (k n : ℕ) :
    coefficient (p ^ (k + 2)) n = 0 := by
  have h := ram_unit_power hp (k + 1) 1 (by simp)
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] at h
  simp [coefficient, h]

end
end GoldbachExplicitModeledMajor
end
end GoldbachGRHBandBase
section GoldbachGRHRamanujanMobius

open scoped BigOperators

namespace GoldbachExplicitModeledMajor

/-- The reduced-residue exponential sum at numerator one is the Möbius value. -/
theorem ram_one_eq_moebius (q : ℕ) :
    ram q 1 = (ArithmeticFunction.moebius q : ℂ) := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ k =>
      have hd (a : ℕ) : ¬ p ^ (a + 1) ∣ 1 := by
        intro ha
        exact (Nat.one_lt_pow (Nat.succ_ne_zero a) hp.one_lt).ne' (Nat.dvd_one.mp ha)
      rw [ram_primePower p k 1 hp,
        ArithmeticFunction.moebius_apply_prime_pow hp (Nat.succ_ne_zero k), ite_eq_right (hd k)]
      cases k with
      | zero => norm_num
      | succ k => simp [hd k]
  | coprime q r hq hr hqr iq ir =>
    rw [ram_mul (by omega) (by omega) hqr, iq, ir,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hqr, Int.cast_mul]

end GoldbachExplicitModeledMajor


namespace GoldbachGRHWindow

/-- A reduced additive numerator has the exact Möbius/totient model. -/
theorem additiveModel_eq_moebius {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) :
    additiveModel q a = (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) := by
  rw [additiveModel_of_unit a ha]
  have h := additiveModel_eq_reduced_sum (q := q) 1
  have hr : additiveModel q 1 =
      GoldbachExplicitModeledMajor.ram q 1 / (q.totient : ℂ) := by
    simpa only [Nat.cast_one, GoldbachExplicitModeledMajor.ram,
      GoldbachExplicitModeledMajor.phase] using h
  rw [hr, GoldbachExplicitModeledMajor.ram_one_eq_moebius]

end GoldbachGRHWindow

end GoldbachGRHRamanujanMobius
end


section
open Set MeasureTheory

namespace GoldbachOscillation

/-- The multiplier R(y) = y/(L²+y²) stays finite as the phase slope crosses zero. -/
private noncomputable def D (L y : ℝ) := L^2+y^2
private noncomputable def R (L y : ℝ) := y / D L y
private noncomputable def R' (L y : ℝ) := (L^2-y^2) / (D L y)^2
private noncomputable def J (L y : ℝ) := Real.arctan (y/L) / L
private noncomputable def wave (y : ℝ) := Complex.exp ((y:ℂ)*Complex.I)

private theorem D_pos {L : ℝ} (hL : 0 < L) (y : ℝ) : 0 < D L y := by unfold D; positivity

private theorem R_deriv {L : ℝ} (hL : 0 < L) (y : ℝ) : HasDerivAt (R L) (R' L y) y := by
  have h := (hasDerivAt_id y).div ((hasDerivAt_const y (L^2)).add ((hasDerivAt_id y).pow 2))
    (D_pos hL y).ne'
  convert h using 1
  · rfl
  unfold R' D
  simp
  ring

private theorem J_deriv {L : ℝ} (hL : 0 < L) (y : ℝ) : HasDerivAt (J L) (1 / D L y) y := by
  have h := ((Real.hasDerivAt_arctan (y/L)).comp y ((hasDerivAt_id y).div_const L)).div_const L
  convert h using 1
  · rfl
  unfold D
  field_simp [hL.ne']

private theorem wave_deriv (y : ℝ) :
    HasDerivAt wave (wave y * Complex.I) y := by
  simpa [wave] using! (((hasDerivAt_id (y:ℂ)).mul_const Complex.I).cexp).comp_ofReal

private theorem wave_norm (y : ℝ) : ‖wave y‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private theorem R_bound {L : ℝ} (hL : 0 < L) (y : ℝ) : |R L y| ≤ 1/L := by
  rw [R, abs_div, abs_of_pos (D_pos hL y)]
  apply (div_le_div_iff₀ (D_pos hL y) hL).mpr
  unfold D
  nlinarith only [sq_nonneg (L-|y|), sq_abs y, mul_nonneg hL.le (abs_nonneg y)]

private theorem R'_bound {L : ℝ} (hL : 0 < L) (y : ℝ) : |R' L y| ≤ 1 / D L y := by
  have hp := D_pos hL y
  rw [R', abs_div, abs_of_pos (sq_pos_of_pos hp)]
  have hab : |L^2-y^2| ≤ D L y := abs_le.mpr ⟨by dsimp [D]; nlinarith [sq_nonneg L],
    by dsimp [D]; nlinarith [sq_nonneg y]⟩
  apply (div_le_div_iff₀ (sq_pos_of_pos hp) hp).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hab hp.le]

private theorem remainder {L : ℝ} (hL : 0 < L) (y : ℝ) :
    1-y*R L y = L^2 / D L y := by
  unfold R
  field_simp [(D_pos hL y).ne']
  unfold D
  ring

private noncomputable def mainTerm (w f : ℝ → ℝ) (x : ℝ) : ℂ := (w x:ℂ)*wave (f x)
private noncomputable def primitive (L : ℝ) (w f p : ℝ → ℝ) (x : ℝ) : ℂ :=
  -Complex.I*((w x * R L (p x) : ℝ):ℂ)*wave (f x)
private noncomputable def errorTerm (L : ℝ) (w dw f p dp : ℝ → ℝ) (x : ℝ) : ℂ :=
  wave (f x) * (((w x * (1-p x*R L (p x)) : ℝ):ℂ) +
    Complex.I * ((dw x*R L (p x)+w x*R' L (p x)*dp x : ℝ):ℂ))

private theorem primitive_deriv {L x : ℝ} (hL : 0 < L) {w dw f p dp : ℝ → ℝ}
    (hw : HasDerivAt w (dw x) x) (hf : HasDerivAt f (p x) x) (hp : HasDerivAt p (dp x) x) :
    HasDerivAt (primitive L w f p) (mainTerm w f x - errorTerm L w dw f p dp x) x := by
  have hr := (R_deriv hL (p x)).comp x hp
  have hd := (((hw.mul hr).ofReal_comp.const_mul (-Complex.I)).mul ((wave_deriv (f x)).scomp x hf))
  convert hd using 1
  · rfl
  dsimp [mainTerm, errorTerm]
  push_cast
  ring_nf
  simp [Complex.I_sq]

private theorem primitive_bound {L x : ℝ} (hL : 0 < L) (w f p : ℝ → ℝ)
    (hw : |w x| ≤ 1) : ‖primitive L w f p x‖ ≤ 1/L := by
  simp only [primitive, norm_mul, norm_neg, Complex.norm_I, one_mul, wave_norm,
    mul_one, Complex.norm_real, Real.norm_eq_abs]
  simpa using mul_le_mul hw (R_bound hL (p x)) (abs_nonneg _) zero_le_one

private theorem error_bound {L x : ℝ} (hL : 0 < L) (w dw f p dp : ℝ → ℝ)
    (hw : |w x| ≤ 1) (hdw : |dw x| ≤ 1) (hcurv : L^2 ≤ 4*dp x) :
    ‖errorTerm L w dw f p dp x‖ ≤ 1/L + 5 * (dp x / D L (p x)) := by
  have hd := D_pos hL (p x)
  have hp : 0 ≤ dp x := by nlinarith only [sq_nonneg L,hcurv]
  rw [errorTerm, norm_mul, wave_norm, one_mul]
  apply (norm_add_le ..).trans
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    remainder hL, abs_of_nonneg (div_nonneg (sq_nonneg L) hd.le)]
  have hfirst := mul_le_of_le_one_left (div_nonneg (sq_nonneg L) hd.le) hw
  have hsecond : |dw x*R L (p x)| ≤ 1/L := by
    rw [abs_mul]
    simpa using mul_le_mul hdw (R_bound hL _) (abs_nonneg _) zero_le_one
  have hthird : |w x*R' L (p x)*dp x| ≤ dp x/D L (p x) := by
    simp only [abs_mul, abs_of_nonneg hp]
    have hs : |w x| * |R' L (p x)| ≤ 1/D L (p x) := by
      simpa using mul_le_mul hw (R'_bound hL _) (abs_nonneg _) zero_le_one
    simpa [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_right hs hp
  have hscale := div_le_div_of_nonneg_right hcurv hd.le
  rw [mul_div_assoc] at hscale
  have htriangle := abs_add_le (dw x*R L (p x)) (w x*R' L (p x)*dp x)
  linarith

/-- A regularized integration by parts works across a possible stationary point.
The arctangent controls the total variation of the multiplier. -/
private theorem regularized {a b L : ℝ} (hab : a ≤ b) (hlen : b-a ≤ 1) (hL : 0 < L)
    (w dw f p dp : ℝ → ℝ)
    (hw : ∀ x ∈ Icc a b, HasDerivAt w (dw x) x)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (p x) x)
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (dp x) x)
    (hcw : ContinuousOn dw (Icc a b)) (hcp : ContinuousOn dp (Icc a b))
    (hw1 : ∀ x ∈ Icc a b, |w x| ≤ 1) (hdw1 : ∀ x ∈ Icc a b, |dw x| ≤ 1)
    (hcurv : ∀ x ∈ Icc a b, L^2 ≤ 4*dp x) :
    ‖∫ x in a..b, mainTerm w f x‖ ≤ (3+5*Real.pi)/L := by
  have cw := HasDerivAt.continuousOn hw
  have cf := HasDerivAt.continuousOn hf
  have cp := HasDerivAt.continuousOn hp
  have cR : Continuous (R L) := continuous_iff_continuousAt.mpr fun y => (R_deriv hL y).continuousAt
  have cD : Continuous (D L) := by unfold D; fun_prop
  have cR' : Continuous (R' L) := by
    unfold R'
    exact (continuous_const.sub (continuous_id.pow 2)).div (cD.pow 2) (fun y => (sq_pos_of_pos (D_pos hL y)).ne')
  have cWave : Continuous wave := continuous_iff_continuousAt.mpr fun y => (wave_deriv y).continuousAt
  have cwav := cWave.comp_continuousOn cf
  have cr := cR.comp_continuousOn cp
  have cr' := cR'.comp_continuousOn cp
  have mainC : ContinuousOn (mainTerm w f) (Icc a b) := by unfold mainTerm; fun_prop
  have errC : ContinuousOn (errorTerm L w dw f p dp) (Icc a b) := by unfold errorTerm; fun_prop
  have mainI := mainC.intervalIntegrable_of_Icc (μ := volume) hab
  have errI := errC.intervalIntegrable_of_Icc (μ := volume) hab
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := primitive L w f p) (f' := fun x => mainTerm w f x - errorTerm L w dw f p dp x)
    (fun x hx => by rw [uIcc_of_le hab] at hx; exact primitive_deriv hL (hw x hx) (hf x hx) (hp x hx))
    (mainI.sub errI)
  rw [intervalIntegral.integral_sub mainI errI] at identity
  let density := fun x => dp x / D L (p x)
  have denC : ContinuousOn density (Icc a b) :=
    hcp.div (cD.comp_continuousOn cp) (fun x _ => (D_pos hL (p x)).ne')
  have di := denC.intervalIntegrable_of_Icc (μ := volume) hab
  have jd := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := J L ∘ p) (f' := density) (fun x hx => by
      rw [uIcc_of_le hab] at hx
      convert (J_deriv hL (p x)).comp x (hp x hx) using 1
      dsimp [density]; ring) di
  -- Integrating the positive density only costs the range of arctan, divided by L.
  have jbound : (∫ x in a..b, density x) ≤ Real.pi/L := by
    rw [jd]
    dsimp [J]
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ hL.le
    linarith only [Real.arctan_lt_pi_div_two (p b/L), Real.neg_pi_div_two_lt_arctan (p a/L)]
  have errBound := intervalIntegral.norm_integral_le_of_norm_le hab
    (g := fun x => 1/L + 5 * density x) (Filter.Eventually.of_forall fun x hx =>
      error_bound hL w dw f p dp (hw1 x ⟨hx.1.le,hx.2⟩) (hdw1 x ⟨hx.1.le,hx.2⟩) (hcurv x ⟨hx.1.le,hx.2⟩))
    (intervalIntegrable_const.add (di.const_mul 5))
  rw [intervalIntegral.integral_add intervalIntegrable_const (di.const_mul 5),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul] at errBound
  have lhs : (∫ x in a..b, mainTerm w f x) =
      (primitive L w f p b - primitive L w f p a) + ∫ x in a..b, errorTerm L w dw f p dp x :=
    sub_eq_iff_eq_add.mp identity
  rw [lhs]
  apply (norm_add_le ..).trans
  have nd := norm_sub_le (primitive L w f p b) (primitive L w f p a)
  have ba := primitive_bound hL w f p (hw1 a (left_mem_Icc.mpr hab))
  have bb := primitive_bound hL w f p (hw1 b (right_mem_Icc.mpr hab))
  have length := mul_le_mul_of_nonneg_right hlen (one_div_nonneg.mpr hL.le)
  rw [add_div, mul_div_assoc]
  rw [show 3/L = 3*(1/L) by ring]
  linarith only [ba,bb,nd,errBound,length,jbound]

private noncomputable def kernel (σ β γ x : ℝ) : ℂ :=
  ((x^(σ-1):ℝ):ℂ) * wave (β*x + γ*Real.log x)

private theorem dyadic_minus {a b γ σ : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hγ : 0 < γ) (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) (β : ℝ) :
    ‖∫ x in a..b, kernel σ β (-γ) x‖ ≤ (3+5*Real.pi)/Real.sqrt γ := by
  let w := fun x : ℝ => x^(σ-1)
  let dw := fun x : ℝ => (σ-1)*x^(σ-1-1)
  let f := fun x : ℝ => β*x+(-γ)*Real.log x
  let p := fun x : ℝ => β-γ/x
  let dp := fun x : ℝ => γ/x^2
  have hx {x : ℝ} (h : x ∈ Icc a b) : 1 ≤ x := ha.trans h.1
  have hxp {x : ℝ} (h : x ∈ Icc a b) : 0 < x := zero_lt_one.trans_le (hx h)
  apply regularized hab (by linarith) (Real.sqrt_pos.mpr hγ) w dw f p dp
  · intro x h
    exact Real.hasDerivAt_rpow_const (Or.inl (hxp h).ne')
  · intro x h
    have h' := ((hasDerivAt_id x).const_mul β).add ((Real.hasDerivAt_log (hxp h).ne').const_mul (-γ))
    convert h' using 1
    · rfl
    dsimp [p]; ring
  · intro x h
    have h' := (hasDerivAt_const x β).sub ((hasDerivAt_const x γ).div (hasDerivAt_id x) (hxp h).ne')
    convert h' using 1
    · rfl
    dsimp [dp]; ring
  · unfold dw; fun_prop (disch := solve_by_elim [ne_of_gt, hxp])
  · change ContinuousOn (fun x : ℝ => γ/x^2) (Icc a b)
    fun_prop (disch := intro x hx; exact pow_ne_zero 2 (hxp hx).ne')
  · intro x h
    dsimp [w]
    rw [abs_of_nonneg (Real.rpow_nonneg (hxp h).le _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (hx h) (by linarith)
  · intro x h
    dsimp [dw]
    rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hσ'), abs_of_nonneg (Real.rpow_nonneg (hxp h).le _)]
    have h1 : -(σ-1) ≤ 1 := by linarith
    have h2 := Real.rpow_le_one_of_one_le_of_nonpos (hx h) (show σ-1-1 ≤ 0 by linarith)
    simpa using mul_le_mul h1 h2 (Real.rpow_nonneg (hxp h).le _) zero_le_one
  · intro x h
    rw [Real.sq_sqrt hγ.le]
    change γ ≤ 4*(γ/x^2)
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos (hxp h))).mpr
    have h2 := pow_le_pow_left₀ (hxp h).le (h.2.trans hb) 2
    nlinarith only [mul_le_mul_of_nonneg_left h2 hγ.le]

open scoped ComplexConjugate

private theorem wave_add (u v : ℝ) : wave (u+v) = wave u * wave v := by
  unfold wave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem conjugate_kernel (σ β γ x : ℝ) :
    conj (kernel σ (-β) (-γ) x) = kernel σ β γ x := by
  unfold kernel wave
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp
  ring

private theorem dyadic {a b γ σ : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hγ : γ ≠ 0) (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) (β : ℝ) :
    ‖∫ x in a..b, kernel σ β γ x‖ ≤ min 1 ((3+5*Real.pi)/Real.sqrt |γ|) := by
  apply le_min
  · have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (f := kernel σ β γ) (C := 1) (fun x hx => by
        rw [uIoc_of_le hab] at hx
        have h1 := ha.trans hx.1.le
        rw [kernel, norm_mul, wave_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans h1) _)]
        exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith))
    rw [abs_of_nonneg (sub_nonneg.mpr hab), one_mul] at h
    exact h.trans (by linarith)
  · rcases lt_or_gt_of_ne hγ with hn | hpos
    · simpa [abs_of_neg hn] using dyadic_minus ha hab hb (neg_pos.mpr hn) hσ hσ' β
    · have id : (∫ x in a..b, kernel σ β γ x) = conj (∫ x in a..b, kernel σ (-β) (-γ) x) := by
        rw [← intervalIntegral.intervalIntegral_conj]
        exact intervalIntegral.integral_congr fun x _ => (conjugate_kernel σ β γ x).symm
      rw [id, Complex.norm_conj, abs_of_pos hpos]
      exact dyadic_minus ha hab hb hpos hσ hσ' (-β)

private theorem rescale {Y x : ℝ} (hY : 0 < Y) (hx : 0 < x) (σ β γ : ℝ) :
    kernel σ β γ (Y*x) = (((Y^(σ-1):ℝ):ℂ)*wave (γ*Real.log Y)) * kernel σ (β*Y) γ x := by
  unfold kernel
  rw [Real.mul_rpow hY.le hx.le, Real.log_mul hY.ne' hx.ne',
    show β*(Y*x)+γ*(Real.log Y+Real.log x) = γ*Real.log Y + ((β*Y)*x+γ*Real.log x) by ring, wave_add]
  push_cast
  ring

/- Away from a stationary point, integrate with the reciprocal of βx+γ.
Its fixed-sign derivative gives a total variation bound from the endpoints. -/
set_option maxHeartbeats 600000 in
private theorem separated {a b σ γ β H : ℝ} (ha : 0 < a) (hab : a ≤ b) (hσ : 0 ≤ σ)
    (hH : 0 < H) (hsep : ∀ x ∈ Icc a b, H ≤ |β*x+γ|) :
    ‖∫ x in a..b, kernel σ β γ x‖ ≤ 5*b^σ/H := by
  let F := fun x : ℝ => β*x + γ*Real.log x
  let p := fun x : ℝ => β+γ/x
  let W := fun x : ℝ => x^σ
  let dW := fun x : ℝ => σ*x^(σ-1)
  let z := fun x : ℝ => 1/(β*x+γ)
  let dz := fun x : ℝ => -β/(β*x+γ)^2
  let B := fun x : ℝ => -Complex.I*((W x*z x : ℝ):ℂ)*wave (F x)
  let er := fun x : ℝ => Complex.I*((dW x*z x+W x*dz x : ℝ):ℂ)*wave (F x)
  have pos {x : ℝ} (hx : x ∈ Icc a b) : 0 < x := ha.trans_le hx.1
  have nz {x : ℝ} (hx : x ∈ Icc a b) : β*x+γ ≠ 0 := abs_pos.mp (hH.trans_le (hsep x hx))
  have zd (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt z (dz x) x := by
    have h := (hasDerivAt_const x (1:ℝ)).div (((hasDerivAt_id x).const_mul β).add_const γ) (nz hx)
    convert h using 1 <;> first | rfl | (dsimp [dz]; ring)
  have wd (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt W (dW x) x :=
    Real.hasDerivAt_rpow_const (Or.inl (pos hx).ne')
  have fd (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt F (p x) x := by
    have h := ((hasDerivAt_id x).const_mul β).add ((Real.hasDerivAt_log (pos hx).ne').const_mul γ)
    convert h using 1 <;> first | rfl | (dsimp [p]; ring)
  have hB (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt B (kernel σ β γ x - er x) x := by
    have hv := ((((wd x hx).mul (zd x hx)).ofReal_comp.const_mul (-Complex.I)).mul
      ((wave_deriv (F x)).scomp x (fd x hx)))
    have unit : W x*z x*p x = x^(σ-1) := by
      dsimp [W,z,p]
      rw [Real.rpow_sub_one (pos hx).ne']
      field_simp [(nz hx),(pos hx).ne']
    have hu : (W x:ℂ)*(z x:ℂ)*(p x:ℂ) = ((x^(σ-1):ℝ):ℂ) := by exact_mod_cast unit
    convert hv using 1
    · rfl
    change ((x^(σ-1):ℝ):ℂ)*wave (F x) - er x = _
    dsimp only [er, Pi.mul_apply, Function.comp_apply]
    push_cast
    rw [← hu]
    simp only [Complex.real_smul]
    linear_combination ((W x:ℂ)*(z x:ℂ)*(p x:ℂ)*wave (F x)) * Complex.I_sq
  have cw := HasDerivAt.continuousOn wd
  have cz := HasDerivAt.continuousOn zd
  have cf := HasDerivAt.continuousOn fd
  have cdw : ContinuousOn dW (Icc a b) := by unfold dW; fun_prop (disch := solve_by_elim [ne_of_gt,pos])
  have cdz : ContinuousOn dz (Icc a b) := by unfold dz; fun_prop (disch := intro x hx; exact pow_ne_zero _ (nz hx))
  have cwave : Continuous wave := continuous_iff_continuousAt.mpr fun y => (wave_deriv y).continuousAt
  have cwF := cwave.comp_continuousOn cf
  have ce : ContinuousOn er (Icc a b) := by unfold er; fun_prop
  have ck : ContinuousOn (kernel σ β γ) (Icc a b) := by
    change ContinuousOn (fun x : ℝ => ((x^(σ-1):ℝ):ℂ)*wave (F x)) _
    have hc : ContinuousOn (fun x : ℝ => x^(σ-1)) (Icc a b) :=
      continuousOn_id.rpow_const fun _ hx => Or.inl (pos hx).ne'
    exact (Complex.continuous_ofReal.comp_continuousOn hc).mul cwF
  have ei := ce.intervalIntegrable_of_Icc (μ := volume) hab
  have ki := ck.intervalIntegrable_of_Icc (μ := volume) hab
  have fi := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := B)
    (f' := fun x => kernel σ β γ x - er x)
    (fun x hx => hB x ((uIcc_of_le hab) ▸ hx)) (ki.sub ei)
  rw [intervalIntegral.integral_sub ki ei] at fi
  have zi := cdz.intervalIntegrable_of_Icc (μ := volume) hab
  have wi := cdw.intervalIntegrable_of_Icc (μ := volume) hab
  have wint := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := W) (f' := dW)
    (fun x hx => wd x ((uIcc_of_le hab) ▸ hx)) wi
  have zint := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := z) (f' := dz)
    (fun x hx => zd x ((uIcc_of_le hab) ▸ hx)) zi
  have zmax (x : ℝ) (hx : x ∈ Icc a b) : |z x| ≤ 1/H := by
    simp only [z, abs_div, abs_one]
    exact one_div_le_one_div_of_le hH (hsep x hx)
  have Wmax (x : ℝ) (hx : x ∈ Icc a b) : |W x| ≤ b^σ := by
    rw [abs_of_nonneg (Real.rpow_nonneg (pos hx).le _)]
    exact Real.rpow_le_rpow (pos hx).le hx.2 hσ
  have Bmax (x : ℝ) (hx : x ∈ Icc a b) : ‖B x‖ ≤ b^σ/H := by
    simp only [B, norm_mul, norm_neg, Complex.norm_I, wave_norm, one_mul, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    simpa [div_eq_mul_inv] using mul_le_mul (Wmax x hx) (zmax x hx) (abs_nonneg _) (Real.rpow_nonneg (ha.trans_le hab).le _)
  -- The sign of β determines the monotonicity of the reciprocal on this interval.
  have zvar : (∫ x in a..b, |dz x|) ≤ 2/H := by
    have sign {x : ℝ} : 0 ≤ (β*x+γ)^2 := sq_nonneg _
    have za := abs_le.mp (zmax a (left_mem_Icc.mpr hab))
    have zb := abs_le.mp (zmax b (right_mem_Icc.mpr hab))
    rcases le_total 0 β with hp | hn
    · have he : (∫ x in a..b, |dz x|) = -(z b-z a) := by
        rw [← zint, ← intervalIntegral.integral_neg]
        exact intervalIntegral.integral_congr fun x _ => abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp) sign)
      rw [he,show 2/H = 2*(1/H) by ring]; linarith
    · have he : (∫ x in a..b, |dz x|) = z b-z a := by
        rw [← zint]
        exact intervalIntegral.integral_congr fun x _ => abs_of_nonneg (div_nonneg (neg_nonneg.mpr hn) sign)
      rw [he,show 2/H = 2*(1/H) by ring]; linarith
  have eBound (x : ℝ) (hx : x ∈ Icc a b) : ‖er x‖ ≤ dW x*(1/H) + b^σ*|dz x| := by
    simp only [er, norm_mul, Complex.norm_I, one_mul, wave_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
    apply (abs_add_le ..).trans
    rw [abs_mul (dW x) (z x), abs_mul (W x) (dz x), abs_of_nonneg (show 0 ≤ dW x from mul_nonneg hσ (Real.rpow_nonneg (pos hx).le _))]
    exact add_le_add (mul_le_mul_of_nonneg_left (zmax x hx) (mul_nonneg hσ (Real.rpow_nonneg (pos hx).le _)))
      (mul_le_mul_of_nonneg_right (Wmax x hx) (abs_nonneg _))
  have ai := cdz.abs.intervalIntegrable_of_Icc (μ := volume) hab
  have eint := intervalIntegral.norm_integral_le_of_norm_le hab
    (Filter.Eventually.of_forall fun x hx => eBound x ⟨hx.1.le,hx.2⟩)
    ((wi.mul_const (1/H)).add (ai.const_mul (b^σ)))
  rw [intervalIntegral.integral_add (wi.mul_const (1/H)) (ai.const_mul (b^σ)),
    intervalIntegral.integral_mul_const (1/H) dW, intervalIntegral.integral_const_mul (b^σ) (fun x => |dz x|), wint] at eint
  rw [sub_eq_iff_eq_add.mp fi]
  apply (norm_add_le ..).trans
  have bd := norm_sub_le (B b) (B a)
  have bl := Bmax a (left_mem_Icc.mpr hab)
  have br := Bmax b (right_mem_Icc.mpr hab)
  have vb := mul_le_mul_of_nonneg_left zvar (Real.rpow_nonneg (ha.trans_le hab).le σ)
  have wa : 0 ≤ W a := Real.rpow_nonneg ha.le _
  have wb := mul_le_mul_of_nonneg_right (show W b-W a ≤ b^σ from sub_le_self _ wa) (one_div_nonneg.mpr hH.le)
  simp only [div_eq_mul_inv,one_mul] at bl br vb eint wb ⊢
  linarith only [bd,bl,br,vb,eint,wb]

/-- The bound holds through a stationary point and is uniform in the additive
frequency. The factor X^σ comes from scaling the dyadic interval. -/
private theorem uniform_bound :
    ∀ (X a b σ γ β : ℝ), 0 < X → X ≤ a → a ≤ b → b ≤ 2*X →
      0 ≤ σ → σ ≤ 1 → γ ≠ 0 →
      ‖∫ x in a..b, ((x^(σ-1):ℝ):ℂ) *
        Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)‖ ≤
        X^σ * min 1 ((3+5*Real.pi)/Real.sqrt |γ|) := by
  intro X a b σ γ β hX ha hab hb hσ hσ' hγ
  let l := a/X
  let r := b/X
  have h1 : 1 ≤ l := (one_le_div hX).mpr ha
  have hlr : l ≤ r := div_le_div_of_nonneg_right hab hX.le
  have h2 : r ≤ 2 := (div_le_iff₀ hX).mpr hb
  let z : ℂ := ((X^(σ-1):ℝ):ℂ)*wave (γ*Real.log X)
  have hz : ‖z‖ = X^(σ-1) := by
    simp only [z, norm_mul, wave_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hX.le _)]
  have eqn : (∫ x in l..r, kernel σ β γ (X*x)) = z * (∫ x in l..r, kernel σ (β*X) γ x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hlr] at hx
    exact rescale hX (zero_lt_one.trans_le (h1.trans hx.1)) σ β γ
  have sub := intervalIntegral.integral_comp_mul_left (kernel σ β γ) (a := l) (b := r) hX.ne'
  have hx1 : X*l = a := by dsimp [l]; field_simp
  have hx2 : X*r = b := by dsimp [r]; field_simp
  rw [sub,hx1,hx2] at eqn
  have eqnorm := congrArg norm eqn
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hX), norm_mul, hz] at eqnorm
  have hxpow : X * X^(σ-1) = X^σ := by
    calc
      _ = X^(1:ℝ) * X^(σ-1) := by rw [Real.rpow_one]
      _ = X^(1+(σ-1)) := (Real.rpow_add hX _ _).symm
      _ = _ := by rw [show (1:ℝ)+(σ-1)=σ by ring]
  change ‖∫ x in a..b, kernel σ β γ x‖ ≤ _
  calc
    _ = X*(X^(σ-1) * ‖∫ x in l..r, kernel σ (β*X) γ x‖) := by
      rw [← eqnorm, ← mul_assoc, mul_inv_cancel₀ hX.ne', one_mul]
    _ ≤ X^σ * min 1 ((3+5*Real.pi)/Real.sqrt |γ|) := by
      rw [← mul_assoc, hxpow]
      exact mul_le_mul_of_nonneg_left (dyadic h1 hlr h2 hγ hσ hσ' (β*X)) (Real.rpow_nonneg hX.le _)



/-- A dyadic piece of the additively twisted zero kernel. The curvature bound is
uniform in the frequency, and a lower bound on the absolute phase slope gives
stronger decay when the interval misses the stationary point. -/
theorem per_ordinate :
    ∀ (X a b σ γ β : ℝ), 0 < X → X ≤ a → a ≤ b → b ≤ 2*X → 0 ≤ σ → σ ≤ 1 →
      let K := ∫ x in a..b, ((x^(σ-1):ℝ):ℂ) *
        Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)
      ‖K‖ ≤ X^σ ∧
      (γ ≠ 0 → ‖K‖ ≤ X^σ * ((3+5*Real.pi)/Real.sqrt |γ|)) ∧
      ∀ H : ℝ, 0 < H → (∀ x ∈ Set.Icc a b, H ≤ |β*x+γ|) → ‖K‖ ≤ 5*b^σ/H := by
  intro X a b σ γ β hX ha hab hb hσ hσ' K
  refine ⟨?_, ?_, fun H hH hsep => separated (hX.trans_le ha) hab hσ hH hsep⟩
  · have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := kernel σ β γ)
      (C := X^(σ-1)) (a := a) (b := b) (fun x hx => by
        rw [uIoc_of_le hab] at hx
        have hxx := ha.trans hx.1.le
        rw [kernel,norm_mul,wave_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (hX.le.trans hxx) _)]
        exact Real.rpow_le_rpow_of_nonpos hX hxx (sub_nonpos.mpr hσ'))
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at h
    have hb' : b-a ≤ X := by linarith
    apply h.trans
    calc
      _ ≤ X^(σ-1)*X := mul_le_mul_of_nonneg_left hb' (Real.rpow_nonneg hX.le _)
      _ = _ := by rw [Real.rpow_sub_one hX.ne', div_mul_cancel₀ _ hX.ne']
  · intro hγ
    exact (uniform_bound X a b σ γ β hX ha hab hb hσ hσ' hγ).trans
      (mul_le_mul_of_nonneg_left (min_le_right ..) (Real.rpow_nonneg hX.le _))
end GoldbachOscillation
end


section
/-!
This reduction uses the uniform prime-sum estimate in Friedlander and Goldston,
Sums of Three or More Primes, p. 290, formula (1.15), as an explicit hypothesis.
-/

namespace DeepThreeQuarters

noncomputable def cutoff (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊

noncomputable def width (n : ℕ) : ℕ := 256 * cutoff n * (Nat.log 2 (n+2)) ^ 2

noncomputable def wideArcs (n : ℕ) : Set ℝ := {t | ∃ q a : ℕ,
  1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ a.Coprime q ∧
  |t - (a : ℝ) / q| ≤ (width n : ℝ) / ((q : ℝ) * n)}

noncomputable def B (n q : ℕ) (β : ℝ) : ℝ := max (q : ℝ) ((q : ℝ) * n * |β|)

/-- Dirichlet approximation at the exact real scale `sqrt n`, including the two
endpoint fractions of the unit interval. -/
theorem exists_dirichlet (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    ∃ a q : ℕ, 1 ≤ q ∧ a ≤ q ∧ a.Coprime q ∧ (q : ℝ) ≤ Real.sqrt n ∧
      |t - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * Real.sqrt n) := by
  let K := ⌊Real.sqrt n⌋₊
  have hs : 1 ≤ Real.sqrt n := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast hn)
  have hK : 1 ≤ K := Nat.le_floor (by simpa using hs)
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hfloor : Real.sqrt n ≤ (K : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  obtain ⟨r, happrox, hr⟩ := Real.exists_rat_abs_sub_le_and_den_le t hK
  have hd : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.den_pos
  have hscaled : |t * r.den - r.num| ≤ 1 / ((K : ℝ) + 1) := by
    rw [Rat.cast_def, ← div_div, le_div_iff₀ hd] at happrox
    rwa [← abs_of_pos hd, ← abs_mul, sub_mul, abs_of_pos hd, div_mul_cancel₀ _ hd.ne'] at happrox
  have hnear : |t * r.den - r.num| < 1 := hscaled.trans_lt <| by
    apply (div_lt_iff₀ (by positivity)).2
    linarith
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hnear
  have hreal₀ := mul_nonneg ht.1 hd.le
  have hreal₁ := mul_le_mul_of_nonneg_right ht.2 hd.le
  have hn₀ : -1 < r.num := by exact_mod_cast (show (-1:ℝ) < r.num by linarith)
  have hn₁ : r.num < (r.den : ℤ) + 1 := by
    exact_mod_cast (show (r.num:ℝ) < (r.den:ℝ) + 1 by linarith)
  have habs : (r.num.natAbs : ℤ) = r.num := Int.natAbs_of_nonneg (by omega)
  have ha : r.num.natAbs ≤ r.den := by omega
  refine ⟨r.num.natAbs, r.den, r.den_pos, ha, r.reduced, ?_, ?_⟩
  · exact (Nat.cast_le.mpr hr).trans (Nat.floor_le (Real.sqrt_nonneg _))
  · have hnR : (r.num.natAbs : ℝ) = r.num := by
      rw [Nat.cast_natAbs, abs_of_nonneg (show 0 ≤ r.num by omega)]
    rw [hnR, ← Rat.cast_def]
    apply happrox.trans
    apply one_div_le_one_div_of_le (mul_pos hd (by linarith))
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hfloor hd.le

/-- Effective heights of admissible approximants to points on the deep arcs. -/
theorem height_bounds {n q a : ℕ} {t : ℝ} (hn : 1 ≤ n) (hq : 1 ≤ q) (ha : a ≤ q)
    (hc : a.Coprime q) (hdeep : t ∉ wideArcs n) (hden : (q : ℝ) ≤ Real.sqrt n)
    (happrox : |t - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * Real.sqrt n)) :
    (n : ℝ) ^ (1/3 : ℝ) ≤ B n q (t - (a : ℝ) / q) ∧
      B n q (t - (a : ℝ) / q) ≤ Real.sqrt n := by
  have hq' : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
  constructor
  · by_cases hsmall : q ≤ cutoff n
    · have hout : (width n : ℝ) / ((q : ℝ) * n) < |t - (a : ℝ) / q| := by
        by_contra! hin
        exact hdeep ⟨q, a, hq, hsmall, ha, hc, hin⟩
      have hw : cutoff n + 1 ≤ width n := by
        have hQ : 1 ≤ (Nat.log 2 (n+2)) ^ 2 := by
          have h := Nat.log_pos (b:=2) (n:=n+2) (by decide) (by omega)
          exact Nat.one_le_pow _ _ h
        unfold width
        have := Nat.mul_le_mul_left (256 * cutoff n) hQ
        omega
      have hw' : (cutoff n : ℝ) + 1 ≤ width n := by exact_mod_cast hw
      apply le_trans ((Nat.lt_floor_add_one ((n : ℝ) ^ (1/3 : ℝ))).le.trans hw')
      exact (le_of_lt (by simpa [mul_comm] using (div_lt_iff₀ (mul_pos hq' hn')).mp hout)).trans
        (le_max_right _ _)
    · exact (Nat.lt_of_floor_lt (lt_of_not_ge hsmall)).le.trans (le_max_left _ _)
  · apply max_le hden
    have hmul := (le_div_iff₀ (mul_pos hq' hs)).mp happrox
    have hmul' := mul_le_mul_of_nonneg_right hmul hs.le
    calc
      (q : ℝ) * n * |t - (a : ℝ) / q| =
          (|t - (a : ℝ) / q| * ((q : ℝ) * Real.sqrt n)) * Real.sqrt n := by
        conv_lhs => rw [← Real.sq_sqrt hn'.le]
        ring
      _ ≤ Real.sqrt n := by simpa using hmul'

theorem exists_deep_approximation {n : ℕ} {t : ℝ} (hn : 1 ≤ n) (ht : t ∈ Set.Icc 0 1)
    (hdeep : t ∉ wideArcs n) : ∃ a q : ℕ, 1 ≤ q ∧ a ≤ q ∧ a.Coprime q ∧
      (q : ℝ) ≤ Real.sqrt n ∧ |t - (a : ℝ)/q| ≤ 1/((q : ℝ)*Real.sqrt n) ∧
      (n : ℝ) ^ (1/3 : ℝ) ≤ B n q (t - (a : ℝ)/q) ∧
      B n q (t - (a : ℝ)/q) ≤ Real.sqrt n := by
  obtain ⟨a,q,hq,ha,hc,hd,h⟩ := exists_dirichlet n hn t ht
  exact ⟨a,q,hq,ha,hc,hd,h,height_bounds hn hq ha hc hdeep hd h⟩

end DeepThreeQuarters

namespace DeepThreeQuarters

noncomputable def geometricPhase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

noncomputable def geometricSum (n : ℕ) (β : ℝ) : ℂ :=
  ∑ k ∈ Finset.range n, geometricPhase ((k : ℝ)*β)

noncomputable def positiveGeometricSum (n : ℕ) (β : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 n, geometricPhase ((k : ℝ)*β)

private theorem norm_geometricPhase (x : ℝ) : ‖geometricPhase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem geometricPhase_pow (j : ℕ) (β : ℝ) :
    geometricPhase ((j : ℝ) * β) = geometricPhase β ^ j := by
  unfold geometricPhase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem norm_geometricSum_le (n : ℕ) (β : ℝ) : ‖geometricSum n β‖ ≤ n := by
  calc
    _ ≤ ∑ k ∈ Finset.range n, ‖geometricPhase ((k : ℝ)*β)‖ := norm_sum_le _ _
    _ = n := by simp [norm_geometricPhase]

/-- The chord bound and geometric-series argument specialize the proof of
`goldbach_geometric_sum_le_inv_twice_round_distance` in goldbach-proofs PR
2486 (revision f3613cf846dfb3e7fe7d04fe6ce51c6ee25e7d4f) to the central period.
The multiplicative estimate includes the offset zero. -/
theorem abs_mul_norm_geometricSum_le_half (n : ℕ) {β : ℝ} (hβ : |β| ≤ 1/2) :
    |β| * ‖geometricSum n β‖ ≤ 1/2 := by
  have harg : |Real.pi * β| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos, show Real.pi / 2 = Real.pi * (1 / 2) by ring]
    exact mul_le_mul_of_nonneg_left hβ Real.pi_pos.le
  have hsin : 2 * |β| ≤ |Real.sin (Real.pi * β)| := calc
    _ = 2 / Real.pi * |Real.pi * β| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      field_simp [Real.pi_pos.ne']
    _ ≤ _ := Real.mul_abs_le_abs_sin harg
  have hchord : 4 * |β| ≤ ‖geometricPhase β - 1‖ := by
    unfold geometricPhase
    rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one,
      show (2 * Real.pi * β) / 2 = Real.pi * β by ring, Real.norm_eq_abs, abs_mul]
    norm_num
    linarith
  have hprod : ‖geometricSum n β‖ * ‖geometricPhase β - 1‖ ≤ 2 := by
    unfold geometricSum
    simp_rw [geometricPhase_pow]
    rw [← norm_mul, geom_sum_mul]
    calc
      _ ≤ ‖geometricPhase β ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, norm_geometricPhase]
  linarith only [(mul_le_mul_of_nonneg_left hchord (norm_nonneg (geometricSum n β))).trans hprod]

theorem norm_positiveGeometricSum_eq (n : ℕ) (β : ℝ) :
    ‖positiveGeometricSum n β‖ = ‖geometricSum n β‖ := by
  have hshift : positiveGeometricSum n β = geometricSum n β * geometricPhase β := by
    unfold positiveGeometricSum geometricSum
    rw [Finset.sum_mul]
    symm
    refine Finset.sum_bij (fun j _ => j+1) ?_ ?_ ?_ ?_
    · intro j hj
      have := Finset.mem_range.mp hj
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro i _ j _ hij
      omega
    · intro j hj
      obtain ⟨h₁,h₂⟩ := Finset.mem_Icc.mp hj
      exact ⟨j-1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro j _
      rw [geometricPhase_pow, geometricPhase_pow, pow_succ]
  rw [hshift, norm_mul, show ‖geometricPhase β‖ = 1 from Complex.norm_exp_ofReal_mul_I _, mul_one]

theorem geometricSum_mul_B_le {n q : ℕ} {β : ℝ} (hn : 4 ≤ n) (hq : 1 ≤ q)
    (hβ : |β| ≤ 1 / ((q : ℝ) * Real.sqrt n)) :
    ‖geometricSum n β‖ * B n q β ≤ (n : ℝ) * q := by
  have hs : 2 ≤ Real.sqrt n := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact_mod_cast hn
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hden : 2 ≤ (q : ℝ) * Real.sqrt n := by nlinarith [mul_nonneg (sub_nonneg.mpr hq') (Real.sqrt_nonneg n)]
  have hhalf := abs_mul_norm_geometricSum_le_half n
    (hβ.trans (one_div_le_one_div_of_le (by norm_num) hden))
  rw [B, mul_max_of_nonneg _ _ (norm_nonneg _)]
  refine max_le (mul_le_mul_of_nonneg_right (norm_geometricSum_le n β) (Nat.cast_nonneg q)) ?_
  have h := mul_le_mul_of_nonneg_left (hhalf.trans (by norm_num : (1/2:ℝ) ≤ 1))
    (show 0 ≤ (n:ℝ) * q by positivity)
  linarith only [h]

theorem positiveGeometricSum_mul_B_le {n q : ℕ} {β : ℝ} (hn : 4 ≤ n) (hq : 1 ≤ q)
    (hβ : |β| ≤ 1 / ((q : ℝ) * Real.sqrt n)) :
    ‖positiveGeometricSum n β‖ * B n q β ≤ (n : ℝ) * q := by
  rw [norm_positiveGeometricSum_eq]
  exact geometricSum_mul_B_le hn hq hβ

end DeepThreeQuarters

/-!
# Bounds for the reciprocal totient density

The finite-product argument and logarithmic bound below are the proof of the
private helpers `harm_prod` and `ratio_bound` from the accepted Goldbach Research
PR #1810 (TH-0073), https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/1810/files.
The logarithmic estimate is exposed here for reuse independently of that PR's
energy theorem. The power bounds are consequences for the deep minor arcs.
-/

namespace DeepThreeQuarters

private theorem harm_prod (s : Finset ℕ) :
    (∀ p ∈ s, 2 ≤ p) → ∏ p ∈ s, (p:ℝ) / ((p:ℝ) - 1) ≤ (s.card : ℝ) + 1 := by
  induction s using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s hlt ih =>
    intro h2
    have ha : a ∉ s := fun h => lt_irrefl _ (hlt a h)
    have ha2 : 2 ≤ a := h2 a (Finset.mem_insert_self _ _)
    have ih' := ih (fun p hp => h2 p (Finset.mem_insert_of_mem hp))
    have hsub : s ⊆ Finset.Ico 2 a := by
      intro x hx
      rw [Finset.mem_Ico]
      exact ⟨h2 x (Finset.mem_insert_of_mem hx), hlt x hx⟩
    have hk : s.card ≤ a - 2 := by
      have := Finset.card_le_card hsub
      simpa using this
    have hk' : (s.card : ℝ) + 2 ≤ a := by
      have : s.card + 2 ≤ a := by omega
      exact_mod_cast this
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    push_cast
    have ha' : (2:ℝ) ≤ a := by exact_mod_cast ha2
    have hpos : (0:ℝ) < (a:ℝ) - 1 := by linarith
    have hP : 0 ≤ ∏ p ∈ s, (p:ℝ) / ((p:ℝ) - 1) := by
      apply Finset.prod_nonneg
      intro p hp
      have : (2:ℝ) ≤ p := by exact_mod_cast h2 p (Finset.mem_insert_of_mem hp)
      apply div_nonneg <;> linarith
    have hfrac : (a:ℝ) / ((a:ℝ) - 1) * ((s.card : ℝ) + 1) ≤ (s.card : ℝ) + 1 + 1 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      nlinarith [Nat.cast_nonneg (α := ℝ) s.card]
    calc (a:ℝ) / ((a:ℝ) - 1) * ∏ p ∈ s, (p:ℝ) / ((p:ℝ) - 1)
        ≤ (a:ℝ) / ((a:ℝ) - 1) * ((s.card : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_left ih' (by positivity)
      _ ≤ _ := hfrac

theorem totient_ratio_le_four_log (q : ℕ) (hq : 0 < q) :
    (q:ℝ) / (q.totient : ℝ) ≤ 4 * Real.log ((q + 2 : ℕ) : ℝ) := by
  have hprime : ∀ p ∈ q.primeFactors, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hh := harm_prod q.primeFactors hprime
  have hid := Nat.totient_mul_prod_primeFactors q
  have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hP : (0:ℝ) < ∏ p ∈ q.primeFactors, (p:ℝ) := by
    apply Finset.prod_pos
    intro p hp
    have : (2:ℝ) ≤ p := by exact_mod_cast hprime p hp
    linarith
  have hP1 : (0:ℝ) < ∏ p ∈ q.primeFactors, ((p:ℝ) - 1) := by
    apply Finset.prod_pos
    intro p hp
    have : (2:ℝ) ≤ p := by exact_mod_cast hprime p hp
    linarith
  have hid' : (q.totient : ℝ) * ∏ p ∈ q.primeFactors, (p:ℝ)
      = (q:ℝ) * ∏ p ∈ q.primeFactors, ((p:ℝ) - 1) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) hid
    simp only [Nat.cast_mul, Nat.cast_prod] at this
    rw [this]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]
    simp
  have heq : (q:ℝ) / (q.totient : ℝ) = ∏ p ∈ q.primeFactors, (p:ℝ) / ((p:ℝ) - 1) := by
    rw [Finset.prod_div_distrib, div_eq_div_iff hφ.ne' hP1.ne']
    linarith
  have hpow : 2 ^ q.primeFactors.card ≤ q := by
    calc 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p :=
          Finset.pow_card_le_prod _ _ _ hprime
      _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have hlog2 : (1:ℝ) / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
    norm_num at this
    linarith
  have hk : (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log ((q + 2 : ℕ) : ℝ) := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    have : ((2 ^ q.primeFactors.card : ℕ) : ℝ) ≤ ((q + 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2 ^ q.primeFactors.card ≤ q + 2)
    simpa using this
  have hL : (1:ℝ) / 2 ≤ Real.log ((q + 2 : ℕ) : ℝ) := by
    refine hlog2.trans (Real.log_le_log (by norm_num) ?_)
    exact_mod_cast (by omega : 2 ≤ q + 2)
  have hc : (0:ℝ) ≤ q.primeFactors.card := Nat.cast_nonneg _
  rw [heq]
  have : (q.primeFactors.card : ℝ) * (1 / 2) ≤ q.primeFactors.card * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2 hc
  linarith

/-- A modulus-uniform bound for every positive exponent, with an explicit constant. -/
theorem totient_ratio_le_rpow {ε : ℝ} (hε : 0 < ε) (q : ℕ) (hq : 0 < q) :
    (q : ℝ) / (q.totient : ℝ) ≤ (8 + 4 / ε) * (q : ℝ) ^ ε := by
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpow : 1 ≤ (q : ℝ) ^ ε := Real.one_le_rpow hq₁ hε.le
  have hlog : Real.log ((q + 2 : ℕ) : ℝ) ≤ Real.log 3 + Real.log q := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  have hthree : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)]
  calc
    (q : ℝ) / (q.totient : ℝ) ≤ 4 * Real.log ((q + 2 : ℕ) : ℝ) :=
      totient_ratio_le_four_log q hq
    _ ≤ 8 + 4 * ((q : ℝ) ^ ε / ε) := by
      linarith [Real.log_natCast_le_rpow_div q hε]
    _ ≤ 8 * (q : ℝ) ^ ε + 4 * ((q : ℝ) ^ ε / ε) := by linarith
    _ = (8 + 4 / ε) * (q : ℝ) ^ ε := by ring

end DeepThreeQuarters

namespace DeepThreeQuarters

/-- Convert a geometric-sum estimate at a rational approximation into the
bound for its Möbius-weighted main term. -/
theorem rational_term_le {ε b : ℝ} {n q : ℕ} {z : ℂ} (hε : 0 < ε)
    (hq : 0 < q) (hqn : (q : ℝ) ≤ n) (hb : 0 < b)
    (hz : ‖z‖ * b ≤ (n : ℝ) * q) :
    ‖(ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * z‖ ≤
      (8 + 4/ε) * (n : ℝ) ^ ε * ((n : ℝ) / b) := by
  have hmu : ‖(ArithmeticFunction.moebius q : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q))
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hz' := (le_div_iff₀ hb).mpr hz
  have hratio := (totient_ratio_le_rpow hε q hq).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) hqn hε.le) (by positivity))
  calc
    _ = (‖(ArithmeticFunction.moebius q : ℂ)‖ / (q.totient : ℝ)) * ‖z‖ := by
      rw [norm_mul, norm_div, Complex.norm_natCast]
    _ ≤ (1 / (q.totient : ℝ)) * ((n : ℝ) * q / b) :=
      mul_le_mul (div_le_div_of_nonneg_right hmu hφ.le) hz' (norm_nonneg _) (by positivity)
    _ = ((q : ℝ) / (q.totient : ℝ)) * ((n : ℝ) / b) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hratio (by positivity)

end DeepThreeQuarters

open Filter

namespace DeepThreeQuarters

/-- Combine the rational main term with the error in its approximation. -/
theorem pointwise_budget {x B C ε : ℝ} (hx : 1 ≤ x) (hC : 0 ≤ C)
    (hlo : x ^ (1/3 : ℝ) ≤ B) (hhi : B ≤ Real.sqrt x)
    (P M : ℂ)
    (hmodel : ‖M‖ ≤ C * x ^ ε * (x / B))
    (herror : ‖P - M‖ ≤ C * x ^ ε * (Real.sqrt x * Real.sqrt B)) :
    ‖P‖ ≤ (2 * C) * x ^ (3/4 + ε) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hquarter : x / B ≤ x ^ (3/4 : ℝ) := by
    calc
      _ ≤ x / x ^ (1/3 : ℝ) :=
        div_le_div_of_nonneg_left hx0.le (Real.rpow_pos_of_pos hx0 _) hlo
      _ = x ^ (1 - 1/3 : ℝ) := by rw [Real.rpow_sub hx0, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have he : Real.sqrt x * Real.sqrt B ≤ x ^ (3/4 : ℝ) := by
    calc
      _ ≤ Real.sqrt x * Real.sqrt (Real.sqrt x) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hhi) (Real.sqrt_nonneg _)
      _ = _ := by
        simp only [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
        norm_num
  have hfac : 0 ≤ C * x ^ ε := mul_nonneg hC (Real.rpow_nonneg hx0.le _)
  have htriangle : ‖P‖ ≤ ‖P - M‖ + ‖M‖ := by
    calc
      ‖P‖ = ‖(P - M) + M‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hsum := htriangle.trans (add_le_add
    (herror.trans (mul_le_mul_of_nonneg_left he hfac))
    (hmodel.trans (mul_le_mul_of_nonneg_left hquarter hfac)))
  rw [Real.rpow_add hx0]
  linarith only [hsum]

/-- Absorb every fixed constant into the arbitrarily small power in the
registered conclusion. The threshold is uniform in the point on the arc. -/
theorem eventually_absorb (C η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ (3/4 + η/2) ≤ (n : ℝ) ^ (3/4 + η) := by
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (η/2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < η/2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_ge_atTop C, eventually_ge_atTop 1] with n hpow hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ (n : ℝ) ^ (η/2) * (n : ℝ) ^ (3/4 + η/2) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hn'.le _)
    _ = _ := by rw [← Real.rpow_add hn']; congr 1; ring

end DeepThreeQuarters

namespace DeepThreeQuarters

/-- Absorb the two logarithmic losses in the Friedlander–Goldston (1.15)
error term. The constant is independent of the modulus and frequency. -/
private theorem log_product_bound {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) :
    Real.log x * (Real.log x + 1) ≤ ((2 / ε)^2 + 1 / ε) * x ^ ε := by
  have hx' : 0 < x := zero_lt_one.trans_le hx
  have hlog := Real.log_nonneg hx
  have hhalf := Real.log_le_rpow_div hx'.le (half_pos hε)
  have hsq := mul_self_le_mul_self hlog hhalf
  have hp : x ^ (ε / 2) * x ^ (ε / 2) = x ^ ε := by
    rw [← Real.rpow_add hx', add_halves]
  have hsq' : Real.log x * Real.log x ≤ (2 / ε)^2 * x ^ ε := by
    calc
      _ ≤ (x ^ (ε / 2) / (ε/2)) * (x ^ (ε / 2) / (ε/2)) := hsq
      _ = (2 / ε)^2 * (x ^ (ε / 2) * x ^ (ε / 2)) := by ring
      _ = _ := by rw [hp]
  calc
    _ = Real.log x * Real.log x + Real.log x := by ring
    _ ≤ (2 / ε)^2 * x ^ ε + x ^ ε / ε := add_le_add hsq' (Real.log_le_rpow_div hx'.le hε)
    _ = _ := by ring

/-- Normalization of the numerical error term in Friedlander–Goldston (1.15).
This estimate holds for every frequency offset and modulus as soon as n ≥ 1.
The analytic assertion (1.15) itself is a separate input. -/
theorem friedlanderGoldston_error_normalize {ε : ℝ} (hε : 0 < ε)
    (n q : ℕ) (β : ℝ) (hn : 1 ≤ n) :
    Real.sqrt ((q : ℝ) * n) * Real.log n * (Real.log n + Real.sqrt (n * |β|)) ≤
      ((2 / ε)^2 + 1 / ε) * (n : ℝ)^ε * (Real.sqrt n * Real.sqrt (B n q β)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_nonneg hn'
  have hq : Real.sqrt q ≤ Real.sqrt (B n q β) := Real.sqrt_le_sqrt (le_max_left _ _)
  have hshift : Real.sqrt q * Real.sqrt (n * |β|) ≤ Real.sqrt (B n q β) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg q)]
    apply Real.sqrt_le_sqrt
    rw [← mul_assoc]
    exact le_max_right _ _
  have hsum :
      Real.sqrt q * (Real.log n + Real.sqrt (n * |β|)) ≤
        Real.sqrt (B n q β) * (Real.log n + 1) := by
    simp only [mul_add, mul_one]
    linarith only [mul_le_mul_of_nonneg_right hq hlog, hshift]
  calc
    _ = (Real.sqrt n * Real.log n) * (Real.sqrt q * (Real.log n + Real.sqrt (n * |β|))) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg q)]
      ring
    _ ≤ (Real.sqrt n * Real.log n) * (Real.sqrt (B n q β) * (Real.log n + 1)) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (Real.sqrt_nonneg _) hlog)
    _ = (Real.log n * (Real.log n + 1)) * (Real.sqrt n * Real.sqrt (B n q β)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (log_product_bound hn' hε)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end DeepThreeQuarters

namespace DeepThreeQuarters

noncomputable def primeWeight (k : ℕ) : ℝ := if k.Prime then Real.log k else 0

noncomputable def weightedSum (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (u k : ℂ) *
    Complex.exp (((2 * Real.pi * ((k : ℝ) * t) : ℝ) : ℂ) * Complex.I)

end DeepThreeQuarters

open Filter

namespace DeepThreeQuarters

noncomputable def rationalModel (n q : ℕ) (β : ℝ) : ℂ :=
  (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * positiveGeometricSum n β


end DeepThreeQuarters
end


section
open Set Filter MeasureTheory Complex
open scoped Topology Interval

noncomputable section

namespace GoldbachTwistedMellin

/-- The trapezoid rises on [a,a+1] and falls on [b,b+1]. For integral
endpoints it agrees with the sharp interval (a,b] at every integer. -/
def taper (a b x : ℝ) : ℝ := max 0 (min (x-a) (min 1 (b+1-x)))

def phase (β x : ℝ) : ℂ := Complex.exp (((β*x:ℝ):ℂ)*Complex.I)

def test (a b β x : ℝ) : ℂ := (taper a b x:ℂ)*phase β x

def transform (a b β : ℝ) (s : ℂ) : ℂ := mellin (test a b β) s

theorem taper_left {a b x : ℝ} (h : x ≤ a) : taper a b x = 0 := by
  exact max_eq_left ((min_le_left ..).trans (sub_nonpos.mpr h))

theorem taper_right {a b x : ℝ} (h : b+1 ≤ x) : taper a b x = 0 := by
  exact max_eq_left ((min_le_right ..).trans ((min_le_right ..).trans (sub_nonpos.mpr h)))

theorem taper_rise {a b x : ℝ} (h : a+1 ≤ b) (hx : x ∈ Icc a (a+1)) :
    taper a b x = x-a := by
  rw [taper,min_eq_left (le_min (by linarith [hx.2]) (by linarith [hx.1,hx.2])),
    max_eq_right (sub_nonneg.mpr hx.1)]

theorem taper_flat {a b x : ℝ} (hx : x ∈ Icc (a+1) b) : taper a b x = 1 := by
  rw [taper,min_eq_left (show 1 ≤ b+1-x by linarith [hx.2]),
    min_eq_right (show 1 ≤ x-a by linarith [hx.1]),max_eq_right zero_le_one]

theorem taper_fall {a b x : ℝ} (h : a+1 ≤ b) (hx : x ∈ Icc b (b+1)) :
    taper a b x = b+1-x := by
  rw [taper,min_eq_right (show b+1-x ≤ 1 by linarith [hx.1]),
    min_eq_right (show b+1-x ≤ x-a by linarith [hx.1]),max_eq_right (sub_nonneg.mpr hx.2)]

theorem taper_nat (a b k : ℕ) :
    taper a b k = if k ∈ Finset.Ioc a b then 1 else 0 := by
  split_ifs with h
  · have hx := Finset.mem_Ioc.mp h
    apply taper_flat
    constructor
    · exact_mod_cast hx.1
    · exact_mod_cast hx.2
  · by_cases hk : k ≤ a
    · exact taper_left (by exact_mod_cast hk)
    · apply taper_right
      have hb : b+1 ≤ k := by simp only [Finset.mem_Ioc] at h; omega
      exact_mod_cast hb

theorem continuous_taper (a b : ℝ) : Continuous (taper a b) := by unfold taper; fun_prop

theorem phase_deriv (β x : ℝ) : HasDerivAt (phase β) (phase β x*((β:ℂ)*I)) x := by
  have d := ((((hasDerivAt_id (x:ℂ)).const_mul (β:ℂ)).mul_const I).cexp).comp_ofReal
  change HasDerivAt (fun y : ℝ => Complex.exp (((β*y:ℝ):ℂ)*I)) _ x
  simpa [phase,mul_assoc] using d

theorem continuous_phase (β : ℝ) : Continuous (phase β) :=
  continuous_iff_continuousAt.mpr fun x => (phase_deriv β x).continuousAt

@[simp] theorem norm_phase (β x : ℝ) : ‖phase β x‖ = 1 := by simp [phase,Complex.norm_exp]

theorem continuous_test (a b β : ℝ) : Continuous (test a b β) :=
  (continuous_ofReal.comp (continuous_taper a b)).mul (continuous_phase β)

theorem compact_test (a b β : ℝ) : HasCompactSupport (test a b β) := by
  apply HasCompactSupport.intro' (K := Icc a (b+1)) isCompact_Icc isClosed_Icc
  intro x hx
  rcases not_and_or.mp (show ¬(a ≤ x ∧ x ≤ b+1) from hx) with hl | hr
  · simp [test,taper_left (le_of_not_ge hl)]
  · simp [test,taper_right (le_of_not_ge hr)]

private theorem test_top (a b β p : ℝ) : test a b β =O[atTop] (fun x : ℝ => x^p) := by
  apply Asymptotics.IsBigO.of_bound (c := 0)
  filter_upwards [eventually_ge_atTop (b+1)] with x hx
  simp [test,taper_right hx]

private theorem test_bot {a : ℝ} (ha : 0 < a) (b β p : ℝ) :
    test a b β =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x^p) := by
  apply Asymptotics.IsBigO.of_bound (c := 0)
  filter_upwards [(eventually_lt_nhds ha).filter_mono (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))] with x hx
  simp [test,taper_left hx.le]

theorem analytic_transform {a : ℝ} (ha : 0 < a) (b β : ℝ) :
    Differentiable ℂ (transform a b β) := by
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow (a := s.re+1) (b := s.re-1)
    ((continuous_test a b β).locallyIntegrable.locallyIntegrableOn _)
    (test_top ..) (by linarith) (test_bot ha ..) (by linarith)

/-- The integral against the trapezoid is a difference of unit averages of
any primitive. This identity is used for both stationary and nonstationary phases. -/
theorem window_primitive {a b : ℝ} (hab : a+1 ≤ b) (f P : ℝ → ℂ)
    (hc : ContinuousOn f (Icc a (b+1))) (hd : ∀ x ∈ Icc a (b+1), HasDerivAt P (f x) x) :
    (∫ x in a..b+1, (taper a b x:ℂ)*f x) =
      (∫ x in b..b+1, P x) - ∫ x in a..a+1, P x := by
  have ab : a ≤ b := by linarith
  have a1 : a ≤ a+1 := by linarith
  have b1 : b ≤ b+1 := by linarith
  have hP : ContinuousOn P (Icc a (b+1)) := fun x hx =>
    (hd x hx).continuousAt.continuousWithinAt
  have iW {l r : ℝ} (hl : a ≤ l) (hr : r ≤ b+1) (hlr : l ≤ r) :
      IntervalIntegrable (fun x => (taper a b x:ℂ)*f x) volume l r :=
    ((continuous_ofReal.comp (continuous_taper a b)).continuousOn.mul
      (hc.mono (Icc_subset_Icc hl hr))).intervalIntegrable_of_Icc hlr
  have ip {l r : ℝ} (hl : a ≤ l) (hr : r ≤ b+1) (hlr : l ≤ r)
      (u : ℝ → ℂ) (v : ℂ) (hu : ∀ x, HasDerivAt u v x) :
      (∫ x in l..r, u x*f x) = u r*P r-u l*P l-(∫ x in l..r, v*P x) := by
    apply intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    · exact (continuous_iff_continuousAt.mpr fun x => (hu x).continuousAt).continuousOn
    · rw [uIcc_of_le hlr]
      exact hP.mono (Icc_subset_Icc hl hr)
    · exact fun x _ => hu x
    · intro x hx
      rw [min_eq_left hlr,max_eq_right hlr] at hx
      exact hd x ⟨hl.trans hx.1.le,hx.2.le.trans hr⟩
    · exact intervalIntegrable_const
    · exact (hc.mono (Icc_subset_Icc hl hr)).intervalIntegrable_of_Icc hlr
  have rise : (∫ x in a..a+1, (taper a b x:ℂ)*f x) = P (a+1) - ∫ x in a..a+1, P x := by
    let u := fun x : ℝ => (x:ℂ)-a
    have hu (x : ℝ) : HasDerivAt u 1 x := by
      simpa [u] using ((hasDerivAt_id (x:ℂ)).sub_const (a:ℂ)).comp_ofReal
    rw [intervalIntegral.integral_congr (g := fun x => u x*f x) (fun x hx => by
      rw [uIcc_of_le a1] at hx
      simp only [u,taper_rise hab hx,ofReal_sub]),ip le_rfl (by linarith) a1 u 1 hu]
    simp [u]
  have mid : (∫ x in a+1..b, (taper a b x:ℂ)*f x) = P b-P (a+1) := by
    rw [intervalIntegral.integral_congr (g := fun x => f x) (fun x hx => by
      rw [uIcc_of_le hab] at hx
      simp [taper_flat hx])]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hd x ((Icc_subset_Icc a1 b1) ((uIcc_of_le hab) ▸ hx)))
      ((hc.mono (Icc_subset_Icc a1 b1)).intervalIntegrable_of_Icc hab)
  have fall : (∫ x in b..b+1, (taper a b x:ℂ)*f x) = -P b + ∫ x in b..b+1, P x := by
    let u := fun x : ℝ => (b:ℂ)+1-x
    have hu (x : ℝ) : HasDerivAt u (-1) x := by
      simpa [u] using ((hasDerivAt_id (x:ℂ)).const_sub ((b:ℂ)+1)).comp_ofReal
    rw [intervalIntegral.integral_congr (g := fun x => u x*f x) (fun x hx => by
      rw [uIcc_of_le b1] at hx
      simp only [u,taper_fall hab hx,ofReal_sub,ofReal_add,ofReal_one]),ip ab le_rfl b1 u (-1) hu]
    simp [u,intervalIntegral.integral_neg]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (iW le_rfl b1 ab) (iW ab le_rfl b1),
    ← intervalIntegral.integral_add_adjacent_intervals (iW le_rfl (by linarith) a1) (iW a1 b1 hab),
    rise,mid,fall]
  abel

def density (β : ℝ) (s : ℂ) (x : ℝ) : ℂ := phase β x*(x:ℂ)^(s-1)

theorem continuousAt_density (β : ℝ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (density β s) x :=
  (continuous_phase β).continuousAt.mul
    (differentiableAt_id.ofReal_cpow_const (s-1) hx.ne').continuousAt

theorem integral_density {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (β : ℝ) (s : ℂ) :
    IntervalIntegrable (density β s) volume a b :=
  (show ContinuousOn (density β s) (Icc a b) from fun _ hx =>
    (continuousAt_density β s (ha.trans_le hx.1)).continuousWithinAt).intervalIntegrable_of_Icc hab

theorem transform_eq_taper_integral {a b : ℝ} (ha : 0 < a) (hab : a+1 ≤ b) (β : ℝ) (s : ℂ) :
    transform a b β s = ∫ x in a..b+1, (taper a b x:ℂ)*density β s x := by
  rw [transform,mellin,intervalIntegral.integral_of_le (show a ≤ b+1 by linarith)]
  simp only [smul_eq_mul]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Ioc a (b+1)) (t := Ioi (0:ℝ)) measurableSet_Ioi
    (fun x hx => ha.trans hx.1) (fun x hx => by
      rcases le_or_gt x a with hl | hl
      · simp [test,taper_left hl]
      · have hr : b+1 ≤ x := le_of_not_ge fun h => hx.2 ⟨hl,h⟩
        simp [test,taper_right hr])]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x _
  unfold test density
  ring

/-- The integer-exact trapezoid is the average of translated sharp intervals.
The identity keeps the oscillatory phase, not just its absolute value. -/
theorem transform_eq_average {a b : ℝ} (ha : 0 < a) (hab : a+1 ≤ b) (β : ℝ) (s : ℂ) :
    transform a b β s = ∫ u in (0:ℝ)..1, ∫ x in (a+u)..(b+u), density β s x := by
  let f := density β s
  let P (v : ℝ) := ∫ x in a..v, f x
  have ab : a ≤ b := by linarith
  have hd (x : ℝ) (hx : x ∈ Icc a (b+1)) : HasDerivAt P (f x) x := by
    apply intervalIntegral.integral_hasDerivAt_right (integral_density ha hx.1 β s)
    · exact ContinuousAt.stronglyMeasurableAtFilter (s := Ioi (0:ℝ)) isOpen_Ioi
        (fun y hy => continuousAt_density β s hy) x (ha.trans_le hx.1)
    · exact continuousAt_density β s (ha.trans_le hx.1)
  have hc : ContinuousOn f (Icc a (b+1)) := fun x hx =>
    (continuousAt_density β s (ha.trans_le hx.1)).continuousWithinAt
  have pc : ContinuousOn P (Icc a (b+1)) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have shift (l : ℝ) (hl : a ≤ l) (hl' : l ≤ b) :
      IntervalIntegrable (fun u => P (l+u)) volume 0 1 := by
    have hmap : MapsTo (fun u : ℝ => l+u) (Icc 0 1) (Icc a (b+1)) :=
      fun u hu => ⟨by linarith [hu.1],by linarith [hu.2]⟩
    exact (pc.comp (continuous_const.add continuous_id).continuousOn hmap).intervalIntegrable_of_Icc zero_le_one
  rw [transform_eq_taper_integral ha hab,window_primitive hab f P hc hd]
  have he : (∫ u in (0:ℝ)..1, ∫ x in (a+u)..(b+u), f x) =
      ∫ u in (0:ℝ)..1, (P (b+u)-P (a+u)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le zero_le_one] at hu
    exact eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals
      (integral_density ha (by linarith [hu.1]: a ≤ a+u) β s)
      (integral_density (by linarith [hu.1] : 0 < a+u) (by linarith : a+u ≤ b+u) β s))
  change _ = ∫ u in (0:ℝ)..1, ∫ x in (a+u)..(b+u), f x
  rw [he,intervalIntegral.integral_sub (shift b ab le_rfl) (shift a le_rfl ab),
    intervalIntegral.integral_comp_add_left,intervalIntegral.integral_comp_add_left]
  simp

theorem density_eq {x : ℝ} (hx : 0 < x) (β : ℝ) (s : ℂ) :
    density β s x = ((x^(s.re-1):ℝ):ℂ)*
      Complex.exp (((β*x+s.im*Real.log x:ℝ):ℂ)*I) := by
  rw [density,phase,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le,Real.rpow_def_of_pos hx,Complex.ofReal_exp,
    ← Complex.exp_add,← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp
  ring

/-- Any uniform bound for sharp subinterval integrals bounds the transform
of the exact integer window with the same constant. -/
theorem norm_transform_le {X a b D : ℝ} (hX : 0 < X) (ha : X ≤ a) (hab : a+1 ≤ b)
    (hb : b+1 ≤ 2*X) (β : ℝ) (s : ℂ)
    (hd : ∀ l r : ℝ, X ≤ l → l ≤ r → r ≤ 2*X → ‖∫ x in l..r, density β s x‖ ≤ D) :
    ‖transform a b β s‖ ≤ D := by
  rw [transform_eq_average (hX.trans_le ha) hab]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := D)
    (f := fun u : ℝ => ∫ x in (a+u)..(b+u), density β s x) (fun u hu => by
      rw [uIoc_of_le zero_le_one] at hu
      exact hd _ _ (by linarith [hu.1]) (by linarith) (by linarith [hu.2]))
  simpa using h

theorem norm_window_modes {X a b : ℝ} (hX : 0 < X) (ha : X ≤ a) (hab : a+1 ≤ b)
    (hb : b+1 ≤ 2*X) (β : ℝ) (s : ℂ) (hσ : 0 ≤ s.re) (hσ' : s.re ≤ 1) :
    ‖transform a b β s‖ ≤ X^s.re ∧
      (s.im ≠ 0 → ‖transform a b β s‖ ≤ X^s.re*((3+5*Real.pi)/Real.sqrt |s.im|)) ∧
      (0 < |s.im| → 4*|β| * X ≤ |s.im| →
        ‖transform a b β s‖ ≤ 20*X^s.re/|s.im|) := by
  have bounds (l r : ℝ) (hl : X ≤ l) (hlr : l ≤ r) (hr : r ≤ 2*X) :
      let K := ∫ x in l..r, density β s x
      ‖K‖ ≤ X^s.re ∧ (s.im ≠ 0 → ‖K‖ ≤ X^s.re*((3+5*Real.pi)/Real.sqrt |s.im|)) ∧
        ∀ H : ℝ, 0 < H → (∀ x ∈ Icc l r, H ≤ |β*x+s.im|) → ‖K‖ ≤ 5*r^s.re/H := by
    have he := intervalIntegral.integral_congr (μ := volume) (f := density β s)
      (a := l) (b := r) (fun x hx => density_eq ((hX.trans_le hl).trans_le (((uIcc_of_le hlr) ▸ hx).1)) β s)
    dsimp only
    rw [he]
    exact GoldbachOscillation.per_ordinate X l r s.re s.im β hX hl hlr hr hσ hσ'
  refine ⟨norm_transform_le hX ha hab hb β s (fun l r hl hm hr => (bounds l r hl hm hr).1),?_,?_⟩
  · intro ht
    exact norm_transform_le hX ha hab hb β s (fun l r hl hm hr => (bounds l r hl hm hr).2.1 ht)
  · intro ht hcut
    apply norm_transform_le hX ha hab hb β s
    intro l r hl hlr hr
    have hsep (x : ℝ) (hx : x ∈ Icc l r) : |s.im|/2 ≤ |β*x+s.im| := by
      have h := abs_add_le (β*x+s.im) (-(β*x))
      rw [show β*x+s.im+ -(β*x) = s.im by ring,abs_neg,abs_mul,abs_of_nonneg (hX.le.trans (hl.trans hx.1))] at h
      have hj := mul_le_mul_of_nonneg_left (hx.2.trans hr) (abs_nonneg β)
      linarith only [h,hcut,hj]
    have hpow : r^s.re ≤ 2*X^s.re := calc
      _ ≤ (2*X)^s.re := Real.rpow_le_rpow (hX.le.trans (hl.trans hlr)) hr hσ
      _ = (2:ℝ)^s.re * X^s.re := Real.mul_rpow (by norm_num) hX.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        simpa using Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num) hσ')
        (Real.rpow_nonneg hX.le _)
    apply ((bounds l r hl hlr hr).2.2 _ (half_pos ht) hsep).trans
    rw [div_div_eq_mul_div]
    exact (div_le_div_iff_of_pos_right ht).mpr (by linarith only [hpow])

end GoldbachTwistedMellin
end
end


section
open Set MeasureTheory Complex
open scoped Interval

noncomputable section
namespace GoldbachTwistedMellin

private def freq (β : ℝ) : ℂ := (β:ℂ)*I
private theorem norm_freq (β : ℝ) : ‖freq β‖ = |β| := by simp [freq,Real.norm_eq_abs]

theorem density_succ (β : ℝ) (s : ℂ) (x : ℝ) :
    density β (s+1) x = phase β x*(x:ℂ)^s := by simp [density]

private theorem pow_deriv {s : ℂ} (hs : 0 < s.re) (β : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (density β (s+1)) (s*density β s x+freq β*density β (s+1) x) x := by
  have sn : s ≠ 0 := fun h => by simp [h] at hs
  have he := (phase_deriv β x).mul (hasDerivAt_ofReal_cpow_const hx.ne' sn)
  rw [show density β (s+1) = fun y : ℝ => phase β y*(y:ℂ)^s from funext (density_succ β s)]
  convert he using 1
  unfold density freq
  ring

private theorem pow_ibp {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    s*(∫ x in l..r, density β s x) = density β (s+1) r - density β (s+1) l -
      freq β*(∫ x in l..r, density β (s+1) x) := by
  have hder := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := density β (s+1)) (a := l) (b := r)
    (fun x hx => pow_deriv hs β (hl.trans_le (((uIcc_of_le hlr) ▸ hx).1)))
    (((integral_density hl hlr β s).const_mul s).add ((integral_density hl hlr β (s+1)).const_mul (freq β)))
  rw [intervalIntegral.integral_add ((integral_density hl hlr β s).const_mul s)
    ((integral_density hl hlr β (s+1)).const_mul (freq β)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hder
  exact eq_sub_of_add_eq hder

/-- Integration by parts for the whole piecewise linear window. The first
derivative contains two unit end intervals and the derivative of the twist. -/
theorem transform_recurrence {a b : ℝ} (ha : 0 < a) (hab : a+1 ≤ b) (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    s*transform a b β s = (∫ x in b..b+1, density β (s+1) x) -
      (∫ x in a..a+1, density β (s+1) x) - freq β*transform a b β (s+1) := by
  have hL : a ≤ b+1 := by linarith
  have cont (z : ℂ) : ContinuousOn (density β z) (Icc a (b+1)) :=
    fun x hx => (continuousAt_density β z (ha.trans_le hx.1)).continuousWithinAt
  have wcont (z : ℂ) : ContinuousOn (fun x => (taper a b x:ℂ)*density β z x) (Icc a (b+1)) :=
    (continuous_ofReal.comp (continuous_taper a b)).continuousOn.mul (cont z)
  have wp := window_primitive hab
    (fun x => s*density β s x+freq β*density β (s+1) x) (density β (s+1))
    (((cont s).const_mul _).add ((cont (s+1)).const_mul _))
    (fun x hx => pow_deriv hs β (ha.trans_le hx.1))
  have point (x : ℝ) : (taper a b x:ℂ)*(s*density β s x+freq β*density β (s+1) x) =
      s*((taper a b x:ℂ)*density β s x)+freq β*((taper a b x:ℂ)*density β (s+1) x) := by ring
  simp_rw [point] at wp
  rw [intervalIntegral.integral_add (((wcont s).intervalIntegrable_of_Icc hL).const_mul s)
    (((wcont (s+1)).intervalIntegrable_of_Icc hL).const_mul (freq β)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    ← transform_eq_taper_integral ha hab,← transform_eq_taper_integral ha hab] at wp
  exact eq_sub_of_add_eq wp

/-- The derivative of the smooth phase is bounded for |β|≤1. One integration
by parts gives a common first-order bound for the integrals in the recurrence. -/
private theorem endpoint_bound {X l r β : ℝ} (hX : 1 ≤ X) (hl : X ≤ l) (hlr : l ≤ r)
    (hr : r ≤ 2*X) (hβ : |β| ≤ 1) {s : ℂ} (hs : 0 < s.re) (hs' : s.re ≤ 2)
    (hn : 0 < ‖s+1‖) :
    ‖∫ x in l..r, density β (s+1) x‖ ≤ 32*X^4/‖s+1‖ := by
  have xl : 0 < l := zero_lt_one.trans_le (hX.trans hl)
  have bnd (x : ℝ) (hx : x ∈ Icc l r) : ‖density β ((s+1)+1) x‖ ≤ (2*X)^3 := by
    rw [density_succ,norm_mul,norm_phase,one_mul,norm_cpow_eq_rpow_re_of_pos (xl.trans_le hx.1)]
    rw [add_re,one_re]
    calc
      x^(s.re+1) ≤ (2*X)^(s.re+1) :=
        Real.rpow_le_rpow (xl.le.trans hx.1) (hx.2.trans hr) (by linarith)
      _ ≤ (2*X)^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = _ := by norm_num
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := l) (b := r)
    (fun x hx => bnd x (by rw [uIoc_of_le hlr] at hx; exact ⟨hx.1.le,hx.2⟩))
  rw [abs_of_nonneg (sub_nonneg.mpr hlr)] at hb
  have e := pow_ibp xl hlr β (s := s+1) (by simp only [add_re,one_re]; linarith)
  have he := (norm_sub_le .. : ‖(density β ((s+1)+1) r - density β ((s+1)+1) l) -
      freq β*(∫ x in l..r, density β ((s+1)+1) x)‖ ≤ _)
  rw [← e,norm_mul,norm_mul,norm_freq] at he
  apply (le_div_iff₀ hn).mpr
  rw [mul_comm]
  have coeff := mul_le_of_le_one_left (norm_nonneg (∫ x in l..r, density β ((s+1)+1) x)) hβ
  have len : r-l ≤ 2*X := by linarith
  have hlen := mul_le_mul_of_nonneg_left len (by positivity : 0 ≤ (2*X)^3)
  have x3 : X^3 ≤ X^4 := by
    simpa only [pow_succ] using (le_mul_of_one_le_right (by positivity : 0 ≤ X^3) hX)
  linarith only [he,norm_sub_le (density β ((s+1)+1) r) (density β ((s+1)+1) l),
    bnd r (right_mem_Icc.mpr hlr),bnd l (left_mem_Icc.mpr hlr),coeff,hb,hlen,x3]

/-- Uniform quadratic decay throughout the contour strip, including the
unit-width transition regions. This bound is only used beyond polynomial height. -/
theorem norm_transform_tail {X a b β : ℝ} (hX : 1 ≤ X) (ha : X ≤ a) (hab : a+1 ≤ b)
    (hb : b+1 ≤ 2*X) (hβ : |β| ≤ 1) (s : ℂ) (hs : 0 < s.re) (hs' : s.re ≤ 2)
    (ht : 0 < |s.im|) : ‖transform a b β s‖ ≤ 96*X^4/|s.im|^2 := by
  have lt0 : 0 < X := zero_lt_one.trans_le hX
  have t1 : |s.im| ≤ ‖s+1‖ := by simpa using abs_im_le_norm (s+1)
  have t0 := abs_im_le_norm s
  have ext (l r : ℝ) (hl : X ≤ l) (hlr : l ≤ r) (hr : r ≤ 2*X) :=
    endpoint_bound hX hl hlr hr hβ hs hs' (ht.trans_le t1)
  have hB := ext b (b+1) (by linarith) (by linarith) hb
  have hA := ext a (a+1) ha (by linarith) (by linarith)
  have hG := norm_transform_le lt0 ha hab hb β (s+1) ext
  have he := transform_recurrence (lt0.trans_le ha) hab β hs
  have triangle := norm_sub_le ((∫ x in b..b+1, density β (s+1) x)-(∫ x in a..a+1, density β (s+1) x))
    (freq β*transform a b β (s+1))
  rw [← he,norm_mul,norm_mul,norm_freq] at triangle
  have part := norm_sub_le (∫ x in b..b+1, density β (s+1) x) (∫ x in a..a+1, density β (s+1) x)
  have coeff := mul_le_of_le_one_left (norm_nonneg (transform a b β (s+1))) hβ
  have total : ‖s‖ * ‖transform a b β s‖ ≤ 96*X^4/‖s+1‖ := by
    simp only [div_eq_mul_inv] at hA hB hG ⊢
    linarith only [triangle,part,coeff,hA,hB,hG]
  have htprod := (le_div_iff₀ (ht.trans_le t1)).mp total
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  calc
    _ = |s.im| * ‖transform a b β s‖*|s.im| := by ring
    _ ≤ _ := (mul_le_mul (mul_le_mul_of_nonneg_right t0 (norm_nonneg _)) t1 ht.le (by positivity)).trans htprod

end GoldbachTwistedMellin
end
end


section
open Set Filter MeasureTheory Complex
open scoped Topology Interval

noncomputable section
namespace GoldbachTwistedMellin

/-- Integrate a height profile with a bounded central interval, a curvature
range, a nonstationary range, and a quadratic-decay tail after the log loss. -/
theorem integrate_profile (g : ℝ → ℂ) (hm : AEStronglyMeasurable g volume)
    {J T U V W Z : ℝ} (hJ : 1 ≤ J) (hJT : J ≤ T) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hW : 0 ≤ W) (hZ : 0 ≤ Z)
    (h0 : ∀ t, |t| ≤ 1 → ‖g t‖ ≤ U)
    (h1 : ∀ t, 1 ≤ |t| → |t| ≤ J → ‖g t‖ ≤ V*|t|^(-(1/2):ℝ))
    (h2 : ∀ t, J ≤ |t| → |t| ≤ T → ‖g t‖ ≤ W*|t|⁻¹)
    (h3 : ∀ t, T < |t| → ‖g t‖ ≤ Z*|t|^(-(3/2):ℝ)) :
    Integrable g ∧ (∫ t : ℝ, ‖g t‖) ≤ 2*(U+2*V*Real.sqrt J+W*Real.log T+2*Z/Real.sqrt T) := by
  let f0 := (Icc (0:ℝ) 1).indicator (fun _ => U)
  let f1 := (Icc 1 J).indicator (fun t : ℝ => V*t^(-(1/2):ℝ))
  let f2 := (Icc 1 T).indicator (fun t : ℝ => W*t⁻¹)
  let f3 := (Ioi T).indicator (fun t : ℝ => Z*t^(-(3/2):ℝ))
  let f (t : ℝ) := f0 t + f1 t + f2 t + f3 t
  have hT := hJ.trans hJT
  have Tpos : 0 < T := zero_lt_one.trans_le hT
  have i0 : Integrable f0 := ((continuous_const : Continuous (fun _ : ℝ => U)).continuousOn.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have c1 : ContinuousOn (fun t : ℝ => V*t^(-(1/2):ℝ)) (Icc 1 J) :=
    (continuousOn_id.rpow_const (fun x (hx : x ∈ Icc (1:ℝ) J) => Or.inl (zero_lt_one.trans_le hx.1).ne')).const_mul _
  have c2 : ContinuousOn (fun t : ℝ => W*t⁻¹) (Icc 1 T) :=
    (continuousOn_id.inv₀ (fun x (hx : x ∈ Icc (1:ℝ) T) => (zero_lt_one.trans_le hx.1).ne')).const_mul _
  have i1 : Integrable f1 := c1.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have i2 : Integrable f2 := c2.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have i3 : Integrable f3 :=
    (integrable_indicator_iff measurableSet_Ioi).mpr ((integrableOn_Ioi_rpow_of_lt (by norm_num : -(3/2:ℝ) < -1) Tpos).const_mul Z)
  have iz : Integrable f := ((i0.add i1).add i2).add i3
  have n0 (t : ℝ) : 0 ≤ f0 t := indicator_nonneg (fun _ _ => hU) _
  have n1 (t : ℝ) : 0 ≤ f1 t := indicator_nonneg (s := Icc 1 J) (fun _ hx => mul_nonneg hV (Real.rpow_nonneg (zero_le_one.trans hx.1) _)) _
  have n2 (t : ℝ) : 0 ≤ f2 t := indicator_nonneg (s := Icc 1 T) (fun _ hx => mul_nonneg hW (inv_nonneg.mpr (zero_le_one.trans hx.1))) _
  have n3 (t : ℝ) : 0 ≤ f3 t := indicator_nonneg (s := Ioi T) (fun _ hx => mul_nonneg hZ (Real.rpow_nonneg (Tpos.le.trans (le_of_lt hx)) _)) _
  have nf (t : ℝ) : 0 ≤ f t := by dsimp [f]; linarith only [n0 t,n1 t,n2 t,n3 t]
  have per (t : ℝ) : ‖g t‖ ≤ f |t| := by
    let y := |t|
    change _ ≤ f0 y+f1 y+f2 y+f3 y
    by_cases hlo : y ≤ 1
    · have e : f0 y = U := indicator_of_mem (s := Icc 0 1) ⟨abs_nonneg _,hlo⟩ _
      linarith only [h0 t hlo,e,n1 y,n2 y,n3 y]
    have hy : 1 ≤ y := le_of_not_ge hlo
    by_cases hj : y ≤ J
    · have e : f1 y = V*y^(-(1/2):ℝ) := indicator_of_mem (s := Icc 1 J) ⟨hy,hj⟩ _
      linarith only [h1 t hy hj,e,n0 y,n2 y,n3 y]
    by_cases ht : y ≤ T
    · have e : f2 y = W*y⁻¹ := indicator_of_mem (s := Icc 1 T) ⟨hy,ht⟩ _
      linarith only [h2 t (le_of_not_ge hj) ht,e,n0 y,n1 y,n3 y]
    · have e : f3 y = Z*y^(-(3/2):ℝ) := indicator_of_mem (lt_of_not_ge ht) _
      linarith only [h3 t (lt_of_not_ge ht),e,n0 y,n1 y,n2 y]
  have major (t : ℝ) : ‖g t‖ ≤ f t+f (-t) := by
    rcases le_total 0 t with ht | ht
    · exact (per t).trans (by rw [abs_of_nonneg ht]; linarith only [nf (-t)])
    · exact (per t).trans (by rw [abs_of_nonpos ht]; linarith only [nf t])
  have ie : Integrable (fun t => f t+f (-t)) := iz.add iz.comp_neg
  have ig := ie.mono' hm (Eventually.of_forall major)
  refine ⟨ig,?_⟩
  have v0 : (∫ t, f0 t) = U := by
    rw [show (∫ t, f0 t) = ∫ t in Icc (0:ℝ) 1, U from integral_indicator measurableSet_Icc]
    simp
  have v1 : (∫ t, f1 t) ≤ 2*V*Real.sqrt J := by
    rw [show (∫ t, f1 t) = ∫ t in Icc 1 J, V*t^(-(1/2):ℝ) from integral_indicator measurableSet_Icc,
      integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hJ,intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1/2)))]
    rw [show (-(1/2):ℝ)+1=1/2 by norm_num,← Real.sqrt_eq_rpow,Real.one_rpow]
    linarith only [hV]
  have v2 : (∫ t, f2 t) = W*Real.log T := by
    rw [show (∫ t, f2 t) = ∫ t in Icc 1 T, W*t⁻¹ from integral_indicator measurableSet_Icc,
      integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hT,intervalIntegral.integral_const_mul,
      integral_inv (by rw [uIcc_of_le hT]; simp),div_one]
  have v3 : (∫ t, f3 t) = 2*Z/Real.sqrt T := by
    rw [show (∫ t, f3 t) = ∫ t in Ioi T, Z*t^(-(3/2):ℝ) from integral_indicator measurableSet_Ioi,
      integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num : -(3/2:ℝ) < -1) Tpos,
      show (-(3/2):ℝ)+1= -(1/2) by norm_num,Real.rpow_neg Tpos.le,← Real.sqrt_eq_rpow]
    ring
  apply (integral_mono ig.norm ie major).trans
  rw [integral_add iz iz.comp_neg,integral_neg_eq_self]
  have tot : (∫ t, f t) = (∫ t, f0 t)+(∫ t, f1 t)+(∫ t, f2 t)+(∫ t, f3 t) := by
    change (∫ t, (((f0+f1)+f2)+f3) t) = _
    rw [integral_add' ((i0.add i1).add i2) i3,integral_add' (i0.add i1) i2,integral_add' i0 i1]
  rw [tot,v0,v2,v3]
  linarith only [v1]

end GoldbachTwistedMellin
end
end


section
open Set Filter MeasureTheory Complex
open scoped Topology Interval

noncomputable section
namespace GoldbachTwistedMellin

def heightCut (X : ℝ) : ℝ := (2*X)^8
def logBudget (q : ℕ) (X : ℝ) : ℝ := 1+Goldbach.logHeight q (heightCut X)

theorem heightCut_ge {X : ℝ} (hX : 1 ≤ X) : 1+4*X ≤ heightCut X := by
  have hpow : X ≤ X^8 := by simpa using pow_le_pow_right₀ hX (show 1 ≤ 8 by decide)
  dsimp [heightCut]
  rw [mul_pow]
  norm_num
  linarith

private theorem log_small (q : ℕ) [NeZero q] {X t : ℝ} (hX : 1 ≤ X) (ht : |t| ≤ heightCut X) :
    Goldbach.logHeight q t ≤ logBudget q X := by
  have hp := heightCut_ge hX
  have hp' : 0 ≤ heightCut X := by linarith
  have qpos : 0 < (q:ℝ) := by exact_mod_cast NeZero.pos q
  have h := Real.log_le_log (by positivity : 0 < 2*(q:ℝ)*(2+|t|))
    (mul_le_mul_of_nonneg_left (by linarith : 2+|t| ≤ 2+heightCut X) (by positivity))
  simp only [Goldbach.logHeight,logBudget,abs_of_nonneg hp']
  linarith only [h]

private theorem log_large (q : ℕ) [NeZero q] {X t : ℝ} (hX : 1 ≤ X) (ht : heightCut X < |t|) :
    Goldbach.logHeight q t ≤ 3*logBudget q X*Real.sqrt |t| := by
  have hp := heightCut_ge hX
  have hT : 1 ≤ heightCut X := by linarith
  have hy : 1 ≤ |t| := hT.trans ht.le
  have yp : 0 < |t| := zero_lt_one.trans_le hy
  have qpos : 0 < (q:ℝ) := by exact_mod_cast NeZero.pos q
  have hmul : 2+|t| ≤ (2+heightCut X)*|t| := by
    nlinarith only [hy,show 0 ≤ heightCut X*|t| from mul_nonneg (zero_le_one.trans hT) yp.le,
      mul_le_mul_of_nonneg_right hT yp.le]
  have arg : 0 < 2*(q:ℝ)*(2+heightCut X) := by positivity
  have h := Real.log_le_log (by positivity : 0 < 2*(q:ℝ)*(2+|t|))
    (mul_le_mul_of_nonneg_left hmul (by positivity : 0 ≤ 2*(q:ℝ)))
  rw [← mul_assoc,Real.log_mul arg.ne' yp.ne'] at h
  have hl := Real.log_le_rpow_div yp.le (by norm_num : (0:ℝ) < 1/2)
  rw [← Real.sqrt_eq_rpow] at hl
  have hs : 1 ≤ Real.sqrt |t| := by simpa using Real.sqrt_le_sqrt hy
  have hL : 1 ≤ logBudget q X := by
    dsimp [logBudget]
    linarith only [Goldbach.logHeight_ge_one q (heightCut X)]
  have hsL := mul_le_mul_of_nonneg_right hL (Real.sqrt_nonneg |t|)
  have hLs := mul_le_mul_of_nonneg_left hs (zero_le_one.trans hL)
  change Real.log (2*(q:ℝ)*(2+|t|)) ≤ _
  have he : Real.log (2*(q:ℝ)*(2+heightCut X)) = logBudget q X-1 := by
    simp [logBudget,Goldbach.logHeight,abs_of_nonneg (zero_le_one.trans hT)]
  rw [he] at h
  linarith only [h,hl,hsL,hLs]

/-- The Mellin L¹ bound, including the logarithmic height factor supplied by
a Dirichlet logarithmic derivative. The frequency loss is square-root. -/
theorem weighted_vertical {X a b β σ A : ℝ} (q : ℕ) [NeZero q]
    (hX : 1 ≤ X) (ha : X ≤ a) (hab : a+1 ≤ b) (hb : b+1 ≤ 2*X)
    (hβ : |β| ≤ 1) (hs : 0 < σ) (hs' : σ ≤ 1) (hA : 0 ≤ A)
    (v : ℝ → ℂ) (hm : AEStronglyMeasurable v volume)
    (hv : ∀ t, ‖v t‖ ≤ A*Goldbach.logHeight q t) :
    let g := fun t : ℝ => v t*transform a b β ((σ:ℂ)+(t:ℂ)*I)
    Integrable g ∧ (∫ t : ℝ, ‖g t‖) ≤ 500*A*X^σ*logBudget q X*
      (1+Real.sqrt (1+4*|β| * X)+Real.log (heightCut X)) := by
  intro g
  let T := heightCut X
  let J := 1+4*|β| * X
  let L := logBudget q X
  let B := A*L*X^σ
  have xp := zero_lt_one.trans_le hX
  have XL := Real.one_le_rpow hX hs.le
  have L1 : 1 ≤ L := by dsimp [L,logBudget]; linarith only [Goldbach.logHeight_ge_one q (heightCut X)]
  have L0 : 0 ≤ L := zero_le_one.trans L1
  have B0 : 0 ≤ B := by dsimp [B]; positivity
  have hJ : 1 ≤ J := by dsimp [J]; linarith only [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (abs_nonneg β)) xp.le]
  have hJT : J ≤ T := by
    have hex := mul_le_mul_of_nonneg_right hβ xp.le
    dsimp [J,T]
    linarith only [heightCut_ge hX,hex]
  have Tpos := xp.trans_le (show X ≤ T by dsimp [T]; linarith [heightCut_ge hX])
  let z (t : ℝ) : ℂ := (σ:ℂ)+(t:ℂ)*I
  have zr (t : ℝ) : (z t).re = σ := by simp [z]
  have zi (t : ℝ) : (z t).im = t := by simp [z]
  let mode (t : ℝ) := norm_window_modes xp ha hab hb β (z t)
    (by rw [zr]; exact hs.le) (by rw [zr]; exact hs')
  have small (t : ℝ) (ht : |t| ≤ T) : ‖v t‖ ≤ A*L :=
    (hv t).trans (mul_le_mul_of_nonneg_left (log_small q hX ht) hA)
  have hg : AEStronglyMeasurable g volume := hm.mul
    (((analytic_transform (xp.trans_le ha) b β).continuous.comp
      (continuous_const.add (continuous_ofReal.mul continuous_const))).aestronglyMeasurable)
  have main := integrate_profile g hg (J := J) (T := T) hJ hJT
    (U := B) (V := B*(3+5*Real.pi)) (W := 20*B) (Z := 288*A*L*X^4)
    B0 (by positivity) (by positivity) (by positivity)
    (fun t ht => by
      change ‖v t*transform a b β (z t)‖ ≤ _
      rw [norm_mul]
      apply mul_le_mul (small t (ht.trans (hJ.trans hJT))) _ (norm_nonneg _) (mul_nonneg hA L0)
      simpa only [zr] using (mode t).1)
    (fun t ht hj => by
      change ‖v t*transform a b β (z t)‖ ≤ _
      have h := (mode t).2.1 (by rw [zi]; exact abs_pos.mp (zero_lt_one.trans_le ht))
      rw [zi,zr] at h
      rw [norm_mul]
      apply (mul_le_mul (small t (hj.trans hJT)) h (norm_nonneg _) (mul_nonneg hA L0)).trans_eq
      rw [Real.rpow_neg (abs_nonneg _),← Real.sqrt_eq_rpow]
      dsimp [B]
      ring)
    (fun t hj ht => by
      have h := (mode t).2.2 (by rw [zi]; exact zero_lt_one.trans_le (hJ.trans hj))
        (by rw [zi]; dsimp [J] at hj; linarith)
      rw [zi,zr] at h
      change ‖v t*transform a b β (z t)‖ ≤ _
      rw [norm_mul]
      apply (mul_le_mul (small t ht) h (norm_nonneg _) (mul_nonneg hA L0)).trans_eq
      dsimp [B]
      ring)
    (fun t ht => by
      have yp := Tpos.trans ht
      have tail := norm_transform_tail hX ha hab hb hβ (z t) (by rw [zr]; exact hs)
        (by rw [zr]; linarith) (by rwa [zi])
      rw [zi] at tail
      have vl := (hv t).trans (mul_le_mul_of_nonneg_left (log_large q hX ht) hA)
      change ‖v t*transform a b β (z t)‖ ≤ _
      rw [norm_mul]
      apply (mul_le_mul vl tail (norm_nonneg _) (by positivity)).trans_eq
      have hp : Real.sqrt |t| / |t|^2 = |t|^(-(3/2):ℝ) := by
        rw [Real.sqrt_eq_rpow,show |t|^2 = |t|^(2:ℝ) by norm_num,← Real.rpow_sub yp]
        norm_num
      dsimp [L] at *
      linear_combination (288*A*logBudget q X*X^4)*hp)
  refine ⟨main.1,main.2.trans ?_⟩
  have sqT : Real.sqrt T = (2*X)^4 := by
    dsimp [T,heightCut]
    rw [show (2*X)^8=((2*X)^4)^2 by ring,Real.sqrt_sq (by positivity)]
  have ht : 2*(288*A*L*X^4)/Real.sqrt T = 36*A*L := by
    rw [sqT]
    field_simp
    ring
  rw [ht]
  have aln : 0 ≤ Real.log T := Real.log_nonneg (hJ.trans hJT)
  have rt := Real.sqrt_nonneg J
  have hb1 : A*L ≤ B := by
    dsimp [B]
    exact le_mul_of_one_le_right (mul_nonneg hA L0) XL
  have piB := mul_le_mul_of_nonneg_right (le_of_lt Real.pi_lt_four) (mul_nonneg B0 rt)
  change _ ≤ 500*A*X^σ*L*(1+Real.sqrt J+Real.log T)
  rw [show 500*A*X^σ*L = 500*B by dsimp [B]; ring]
  nlinarith only [hb1,piB,B0,mul_nonneg B0 rt,mul_nonneg B0 aln]

end GoldbachTwistedMellin
end
end


section
open Set Filter MeasureTheory Complex
open scoped Topology Interval

noncomputable section
namespace GoldbachTwistedMellin

theorem integrable_transform {X a b β σ : ℝ} (hX : 1 ≤ X) (ha : X ≤ a) (hab : a+1 ≤ b)
    (hb : b+1 ≤ 2*X) (hβ : |β| ≤ 1) (hs : 0 < σ) (hs' : σ ≤ 2) :
    Integrable (fun t : ℝ => transform a b β ((σ:ℂ)+(t:ℂ)*I)) := by
  let g := fun t : ℝ => transform a b β ((σ:ℂ)+(t:ℂ)*I)
  have hc : Continuous g := (analytic_transform (zero_lt_one.trans_le (hX.trans ha)) b β).continuous.comp
    (continuous_const.add (continuous_ofReal.mul continuous_const))
  obtain ⟨M,hM⟩ := (isCompact_Icc (α := ℝ) (a := -1) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  let C := 2*(max 0 M+96*X^4)
  refine (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable ?_
  filter_upwards with t
  change ‖g t‖ ≤ C*(1+t^2)⁻¹
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).mpr
  by_cases ht : |t| ≤ 1
  · have h := hM t (abs_le.mp ht)
    have ht2 : t^2 ≤ 1 := by
      have hprod := mul_nonneg (sub_nonneg.mpr ht) (show 0 ≤ 1+|t| by positivity)
      nlinarith only [hprod,sq_abs t]
    have hm : ‖g t‖*(1+t^2) ≤ (max 0 M)*2 :=
      mul_le_mul (h.trans (le_max_right ..)) (by linarith) (by positivity) (le_max_left ..)
    dsimp [C]
    nlinarith only [hm,show 0 ≤ X^4 by positivity]
  · have ht' : 0 < |t| := by linarith only [lt_of_not_ge ht]
    have hbound := norm_transform_tail hX ha hab hb hβ ((σ:ℂ)+(t:ℂ)*I)
      (by simpa using hs) (by simpa using hs') (by simpa using ht')
    have hn : ‖g t‖*|t|^2 ≤ 96*X^4 := (le_div_iff₀ (by positivity)).mp (by simpa [g] using hbound)
    have hsq : 1 ≤ |t|^2 := by nlinarith only [lt_of_not_ge ht,sq_nonneg (|t|-1)]
    have hmul := mul_le_mul_of_nonneg_left (by nlinarith only [hsq,sq_abs t] : 1+t^2 ≤ 2*|t|^2) (norm_nonneg (g t))
    dsimp [C]
    nlinarith only [hmul,hn,le_max_left 0 M]

theorem mellinInv_transform {X a b β σ y : ℝ} (hX : 1 ≤ X) (ha : X ≤ a) (hab : a+1 ≤ b)
    (hb : b+1 ≤ 2*X) (hβ : |β| ≤ 1) (hs : 0 < σ) (hs' : σ ≤ 2) (hy : 0 < y) :
    mellinInv σ (transform a b β) y = test a b β y := by
  have ha0 := zero_lt_one.trans_le (hX.trans ha)
  have hm : MellinConvergent (test a b β) (σ:ℂ) := by
    apply mellinConvergent_of_isBigO_rpow (a := σ+1) (b := σ-1)
      ((continuous_test a b β).locallyIntegrable.locallyIntegrableOn _)
    · apply Asymptotics.IsBigO.of_bound (c := 0)
      filter_upwards [eventually_ge_atTop (b+1)] with x hx
      simp [test,taper_right hx]
    · simp
    · apply Asymptotics.IsBigO.of_bound (c := 0)
      filter_upwards [(eventually_lt_nhds ha0).filter_mono (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))] with x hx
      simp [test,taper_left hx.le]
    · simp
  exact mellinInv_mellin_eq σ _ hy hm (integrable_transform hX ha hab hb hβ hs hs') (continuous_test a b β).continuousAt

-- The Dirichlet-series interchange follows the smoothing proof of PR #2486.
private theorem term_norm_vertical (a : ℕ → ℂ) (σ t : ℝ) (n : ℕ) :
    ‖LSeries.term a ((σ : ℂ) + (t : ℂ) * I) n‖ = ‖LSeries.term a (σ : ℂ) n‖ := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp only [LSeries.term_of_ne_zero hn, norm_div,
      norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), add_re, ofReal_re, mul_I_re, ofReal_im,
      neg_zero, add_zero]

private theorem term_continuous_vertical (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ => LSeries.term a ((σ : ℂ) + (t : ℂ) * I) n) := by
  by_cases hn : n = 0
  · subst n
    simpa only [LSeries.term_zero] using (continuous_const : Continuous fun _ : ℝ => (0 : ℂ))
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hline : Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) :=
      continuous_const.add (continuous_ofReal.mul continuous_const)
    simp_rw [LSeries.term_of_ne_zero hn, cpow_def_of_ne_zero hnC]
    exact continuous_const.div (continuous_exp.comp (continuous_const.mul hline))
      (fun _ => exp_ne_zero _)


theorem integrable_series_transform (a : ℕ → ℂ) (K : ℂ → ℂ) {σ : ℝ}
    (hK : Integrable (fun t : ℝ => K ((σ:ℂ)+(t:ℂ)*I)))
    (hAbs : Summable fun n => ‖LSeries.term a (σ : ℂ) n‖) :
    Integrable (fun t : ℝ => LSeries a ((σ : ℂ) + (t : ℂ) * I) *
      K ((σ : ℂ) + (t : ℂ) * I)) := by
  let z (t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hc : Continuous (fun t : ℝ => LSeries a (z t)) := by
    exact continuous_tsum (term_continuous_vertical a σ) hAbs
      (fun n t => le_of_eq (term_norm_vertical a σ t n))
  refine (hK.norm.const_mul (∑' n, ‖LSeries.term a (σ : ℂ) n‖)).mono'
    (hc.aestronglyMeasurable.mul hK.aestronglyMeasurable) ?_
  filter_upwards with t
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hS : Summable (fun n => ‖LSeries.term a (z t) n‖) :=
    hAbs.congr (fun n => (term_norm_vertical a σ t n).symm)
  exact (norm_tsum_le_tsum_norm hS).trans_eq (tsum_congr (term_norm_vertical a σ t))

/-- Mellin inversion with an absolutely convergent Dirichlet series. -/
theorem series_transform_inversion (a : ℕ → ℂ) (ha0 : a 0 = 0) (f : ℝ → ℂ) (K : ℂ → ℂ) {σ : ℝ}
    (hK : Integrable (fun t : ℝ => K ((σ:ℂ)+(t:ℂ)*I)))
    (hInvK : ∀ y : ℝ, 0 < y → mellinInv σ K y = f y)
    (hAbs : Summable fun n => ‖LSeries.term a (σ : ℂ) n‖) :
    (∑' n, a n * f n) =
      (1 / (2 * Real.pi)) • (∫ t : ℝ,
        LSeries a ((σ : ℂ) + (t : ℂ) * I) * K ((σ : ℂ) + (t : ℂ) * I)) := by
  let z (t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I
  let F (n : ℕ) (t : ℝ) : ℂ := LSeries.term a (z t) n * K (z t)
  have hN (n : ℕ) (t : ℝ) : ‖F n t‖ =
      ‖LSeries.term a (σ : ℂ) n‖ * ‖K (z t)‖ := by
    dsimp only [F]
    rw [norm_mul, term_norm_vertical]
  have hF (n : ℕ) : Integrable (F n) := by
    refine (hK.norm.const_mul ‖LSeries.term a (σ : ℂ) n‖).mono' ?_ ?_
    · exact (term_continuous_vertical a σ n).aestronglyMeasurable.mul hK.aestronglyMeasurable
    · filter_upwards with t
      exact le_of_eq (hN n t)
  have hFsum : Summable fun n => ∫ t : ℝ, ‖F n t‖ := by
    simp_rw [hN, integral_const_mul]
    exact hAbs.mul_right _
  have hInv (n : ℕ) : a n * f n =
      (1 / (2 * Real.pi)) • (∫ t : ℝ, F n t) := by
    by_cases hn : n = 0
    · subst n
      simp [F, ha0]
    have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [← hInvK n hnR]
    unfold mellinInv
    simp only [F, z, LSeries.term_def₀ ha0, ofReal_natCast, smul_eq_mul, mul_assoc]
    rw [integral_const_mul]
    simp only [Algebra.smul_def]
    ring
  calc
    _ = ∑' n, (1 / (2 * Real.pi)) • (∫ t : ℝ, F n t) := tsum_congr hInv
    _ = (1 / (2 * Real.pi)) • (∑' n, ∫ t : ℝ, F n t) := tsum_const_smul'' _
    _ = (1 / (2 * Real.pi)) • (∫ t : ℝ, ∑' n, F n t) :=
      congrArg ((1 / (2 * Real.pi)) • ·) (integral_tsum_of_summable_integral_norm hF hFsum)
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      simp only [F, z, LSeries, tsum_mul_right]


open GoldbachSmoothing DirichletCharacter

theorem character_sum_eq_vertical {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a b : ℕ} {X β : ℝ} (hX : 1 ≤ X) (ha : X ≤ (a:ℝ)) (hab : (a:ℝ)+1 ≤ b)
    (hb : (b:ℝ)+1 ≤ 2*X) (hβ : |β| ≤ 1) :
    (∑ n ∈ Finset.Ioc a b, twistedCoefficient χ n * phase β n) =
      (1/(2*Real.pi)) • ∫ t : ℝ, (-logDeriv (LFunction χ) (2+(t:ℂ)*I)) *
        transform a b β (2+(t:ℂ)*I) := by
  have hAbs : Summable fun n => ‖LSeries.term (twistedCoefficient χ) (2:ℂ) n‖ :=
    summable_norm_iff.mpr (χ.LSeriesSummable_twist_vonMangoldt (by norm_num))
  have hEq (t : ℝ) : LSeries (twistedCoefficient χ) (2+(t:ℂ)*I) =
      -logDeriv (LFunction χ) (2+(t:ℂ)*I) := LSeries_twistedCoefficient_eq χ (by norm_num)
  have h := series_transform_inversion (twistedCoefficient χ) (twistedCoefficient_zero χ)
    (test a b β) (transform a b β) (σ := 2) (integrable_transform hX ha hab hb hβ (by norm_num) le_rfl)
    (fun _ hy => mellinInv_transform hX ha hab hb hβ (by norm_num) le_rfl hy) (by simpa using hAbs)
  simp only [ofReal_ofNat,hEq] at h
  rw [← h, tsum_eq_sum (s := Finset.Ioc a b)]
  · apply Finset.sum_congr rfl
    intro n hn
    simp [test,taper_nat,hn]
  · intro n hn
    simp [test,taper_nat,hn]

end GoldbachTwistedMellin
end
end


section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter
open scoped Topology Interval

noncomputable section
namespace GoldbachTwistedMellin

def line (σ t : ℝ) : ℂ := (σ:ℂ)+(t:ℂ)*I

@[simp] theorem re_line (σ t : ℝ) : (line σ t).re = σ := by simp [line]
@[simp] theorem im_line (σ t : ℝ) : (line σ t).im = t := by simp [line]

theorem continuous_line (σ : ℝ) : Continuous (line σ) :=
  continuous_const.add (continuous_ofReal.mul continuous_const)

theorem strip_nonzero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hG : GRH) {z : ℂ} (hz : 1/2 < z.re) : regularizedL χ z ≠ 0 := by
  intro h
  linarith only [regularizedL_zero_line χ hG (by linarith : 0 < z.re) h,hz]

theorem continuous_contour {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hG : GRH) {σ : ℝ} (hs : 1/2 < σ) (hs1 : σ ≠ 1) :
    Continuous (fun t : ℝ => contourLog χ (line σ t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let z := line σ t
  have hF := analytic_regularizedL χ z (Set.mem_univ _)
  have hlog : AnalyticAt ℂ (logDeriv (regularizedL χ)) z := by
    simpa only [logDeriv,Pi.div_apply] using hF.deriv.div hF (strip_nonzero χ hG (by simpa [z] using hs))
  have h1 : z-1 ≠ 0 := sub_ne_zero.mpr (fun h => hs1 (by simpa [z] using congrArg Complex.re h))
  have hden : AnalyticAt ℂ (fun w : ℂ => w-1) z := analyticAt_id.sub analyticAt_const
  have hflag : AnalyticAt ℂ (fun _ : ℂ => principalFlag χ) z := analyticAt_const
  have hc : AnalyticAt ℂ (contourLog χ) z := hlog.neg.add (hflag.div hden h1)
  exact ContinuousAt.comp (f := line σ) (g := contourLog χ) (x := t) hc.continuousAt (continuous_line σ).continuousAt

/-- The distance to every zero is uniform to the right of the critical line.
The additional distance condition excludes the pole at one on contour edges. -/
theorem log_control_right (hG : GRH) {d : ℝ} (hd : 0 < d) :
    ∃ A : ℝ, 0 < A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t : ℝ),
      1/2+d ≤ σ → σ ≤ 2 → 1/4 ≤ ‖line σ t-1‖ →
      ‖contourLog χ (line σ t)‖ ≤ A*logHeight q t := by
  obtain ⟨C,hC,hbound⟩ := uniform_dirichlet_log_control
  refine ⟨C*(1+d⁻¹)+4,by positivity,?_⟩
  intro q _ χ σ t hσ hσ' hp
  have hdist (ρ : ℂ) (hρ : 0 < ρ.re) (hz : regularizedL χ ρ = 0) : d ≤ ‖line σ t-ρ‖ := by
    have hre := regularizedL_zero_line χ hG hρ hz
    calc
      d ≤ (line σ t-ρ).re := by simp only [sub_re,re_line,hre]; linarith
      _ ≤ _ := re_le_norm _
  have h := hbound q χ σ t d ⟨by linarith,hσ'⟩ hd hdist
  have hflag : ‖principalFlag χ‖ ≤ 1 := by by_cases hc : χ = 1 <;> simp [principalFlag,hc]
  have hquot : ‖principalFlag χ / (line σ t-1)‖ ≤ 4 := by
    rw [norm_div]
    apply (div_le_iff₀ (by linarith : 0 < ‖line σ t-1‖)).mpr
    linarith
  have hlog := logHeight_ge_one q t
  unfold contourLog
  refine (norm_add_le ..).trans ?_
  rw [norm_neg]
  change ‖logDeriv (regularizedL χ) (line σ t)‖ ≤ _ at h
  nlinarith only [h,hquot,hlog]

theorem left_pole_dist {σ : ℝ} (hs : σ ≤ 3/4) (t : ℝ) : 1/4 ≤ ‖line σ t-1‖ := by
  have h := neg_le_abs (line σ t-1).re
  have h' := abs_re_le_norm (line σ t-1)
  simp only [sub_re,re_line,one_re] at h h'
  linarith

theorem horizontal_pole_dist {t : ℝ} (ht : 1 ≤ |t|) (σ : ℝ) : 1/4 ≤ ‖line σ t-1‖ := by
  have h := abs_im_le_norm (line σ t-1)
  simp only [sub_im,im_line,one_im,sub_zero] at h
  linarith

theorem contour_right (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    contourLog χ (line 2 t) = -logDeriv (LFunction χ) (line 2 t) := by
  have hn : line 2 t ≠ 1 := by intro h; have := congrArg Complex.re h; simp at this
  have hL := LFunction_ne_zero_of_one_le_re χ (Or.inr hn) (by simp)
  rw [contourLog,logDeriv_regularizedL_eq χ hn hL]
  ring

end GoldbachTwistedMellin
end
end


section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter
open scoped Topology Interval

noncomputable section
namespace GoldbachTwistedMellin

/-- The horizontal edges tend to zero, with an elementary O(1/T) bound. -/
theorem horizontal_limit {X a b β d A : ℝ} {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hX : 1 ≤ X) (ha : X ≤ a) (hab : a+1 ≤ b)
    (hb : b+1 ≤ 2*X) (hβ : |β| ≤ 1) (hd : 0 < d) (hd' : d ≤ 1/4) (hA : 0 ≤ A)
    (hlog : ∀ σ t : ℝ, 1/2+d ≤ σ → σ ≤ 2 → 1/4 ≤ ‖line σ t-1‖ →
      ‖contourLog χ (line σ t)‖ ≤ A*logHeight q t)
    {u : ℝ → ℝ} (hu : ∀ T : ℝ, 1 ≤ T → |u T| = T) :
    Tendsto (fun T => ∫ σ : ℝ in (1/2+d)..2,
      contourLog χ (line σ (u T)) * transform a b β (line σ (u T))) atTop (𝓝 0) := by
  let C := A*(6*(q:ℝ))*(96*X^4)*|2-(1/2+d)|
  have lim : Tendsto (fun T : ℝ => C/T) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using (tendsto_const_nhds (x := C)).mul tendsto_inv_atTop_zero
  refine squeeze_zero_norm' ?_ lim
  filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
  have Tpos : 0 < T := zero_lt_one.trans_le hT
  have uq : 0 < (q:ℝ) := by exact_mod_cast NeZero.pos q
  have huT := hu T hT
  have hl : logHeight q (u T) ≤ (6*(q:ℝ))*T := by
    unfold logHeight
    rw [huT]
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 2*(q:ℝ)*(2+T))
    nlinarith only [h,mul_le_mul_of_nonneg_left hT uq.le]
  have hpoint (σ : ℝ) (hσ : σ ∈ Ι (1/2+d) 2) :
      ‖contourLog χ (line σ (u T))*transform a b β (line σ (u T))‖ ≤ A*(6*(q:ℝ))*(96*X^4)/T := by
    rw [uIoc_of_le (by linarith)] at hσ
    have h₁ := hlog σ (u T) hσ.1.le hσ.2 (horizontal_pole_dist (huT.symm ▸ hT) σ)
    have h₂ := norm_transform_tail hX ha hab hb hβ (line σ (u T)) (by simp; linarith [hσ.1]) (by simpa using hσ.2)
      (by rw [im_line,huT]; exact Tpos)
    rw [im_line,huT] at h₂
    rw [norm_mul]
    calc
      _ ≤ (A*((6*(q:ℝ))*T))*(96*X^4/T^2) :=
        mul_le_mul (h₁.trans (mul_le_mul_of_nonneg_left hl hA)) h₂ (norm_nonneg _) (by positivity)
      _ = _ := by field_simp
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  exact h.trans_eq (by dsimp [C]; ring)

theorem contour_shift {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hG : GRH)
    {σ : ℝ} (hs : 1/2 < σ) (hs1 : σ < 1) {K : ℂ → ℂ} (hK : Differentiable ℂ K)
    (hiL : Integrable fun t : ℝ => contourLog χ (line σ t)*K (line σ t))
    (hiR : Integrable fun t : ℝ => contourLog χ (line 2 t)*K (line 2 t))
    (lo : Tendsto (fun T : ℝ => ∫ x : ℝ in σ..2, contourLog χ (line x (-T))*K (line x (-T))) atTop (𝓝 0))
    (up : Tendsto (fun T : ℝ => ∫ x : ℝ in σ..2, contourLog χ (line x T)*K (line x T)) atTop (𝓝 0)) :
    (∫ t : ℝ, contourLog χ (line 2 t)*K (line 2 t)) =
      (∫ t : ℝ, contourLog χ (line σ t)*K (line σ t)) + (2*(Real.pi:ℂ))*(principalFlag χ*K 1) := by
  let G := fun z : ℂ => contourLog χ z*K z
  let P := (2*(Real.pi:ℂ))*(principalFlag χ*K 1)
  let D := fun T : ℝ => I*((∫ x : ℝ in σ..2, G (line x (-T))) - ∫ x : ℝ in σ..2, G (line x T))
  have hd : Tendsto D atTop (𝓝 0) := by simpa only [D,G,sub_zero,mul_zero] using (tendsto_const_nhds (x := I)).mul (lo.sub up)
  have hl := intervalIntegral_tendsto_integral hiL (tendsto_neg_atTop_atBot (G := ℝ)) (tendsto_id (α := ℝ) (x := atTop))
  have hr := intervalIntegral_tendsto_integral hiR (tendsto_neg_atTop_atBot (G := ℝ)) (tendsto_id (α := ℝ) (x := atTop))
  have heq : (fun T : ℝ => (∫ t : ℝ in (-T)..T, G (line σ t))+P+D T) =ᶠ[atTop]
      (fun T : ℝ => ∫ t : ℝ in (-T)..T, G (line 2 t)) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    let U := Icc σ 2 ×ℂ Icc (-T) T
    have hF : AnalyticOnNhd ℂ (regularizedL χ) U := (analytic_regularizedL χ).mono (subset_univ _)
    have hKa : AnalyticOnNhd ℂ K U := fun z _ => hK.analyticAt z
    have hz (z : ℂ) (hzU : z ∈ U) : regularizedL χ z = 0 ↔ z ∈ (∅ : Finset ℂ) := by
      simp only [Finset.notMem_empty,iff_false]
      exact strip_nonzero χ hG (hs.trans_le hzU.1.1)
    have hrect := rectBoundaryIntegral_neg_logDeriv_add_pole_mul (regularizedL χ) K (∅ : Finset ℂ) (principalFlag χ)
      hs1 (by norm_num : (1:ℝ) < 2) (neg_lt_zero.mpr hT) hT hF hKa hz (by simp) (by simp) (regularizedL_ne_zero_at_one χ)
    have hr' := right_vertical_integral_of_rect hrect
    simpa [G,D,P,line,contourLog] using hr'.symm
  have hlim := ((hl.add (tendsto_const_nhds (x := P))).add hd).congr' heq
  simpa [P] using tendsto_nhds_unique hr hlim

end GoldbachTwistedMellin
end
end


section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter GoldbachSmoothing
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

/-- Exact dyadic twisted Mangoldt sums, after shifting the Mellin contour
to the right of the critical line. The only residue is the principal pole. -/
theorem dyadic_twist_under_GRH (hG : GRH) {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (a b : ℕ) (X β : ℝ), 1 ≤ X → X ≤ (a:ℝ) → (a:ℝ)+1 ≤ b → (b:ℝ)+1 ≤ 2*X → |β| ≤ 1 →
      ‖(∑ k ∈ Finset.Ioc a b, twistedCoefficient χ k * phase β k) -
        principalFlag χ*transform a b β 1‖ ≤
        C*X^(1/2+d)*logBudget q X*(1+Real.sqrt (1+4*|β| * X)+Real.log (heightCut X)) := by
  obtain ⟨A,hA,hlog⟩ := log_control_right hG hd
  let c := 1/(2*Real.pi)
  have hpi := Real.pi_pos
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c*(500*A),by positivity,?_⟩
  intro q _ χ a b X β hX ha hab hb hβ
  let σ : ℝ := 1/2+d
  let K := transform a b β
  let v := fun t : ℝ => contourLog χ (line σ t)
  have hs : 1/2 < σ := by dsimp [σ]; linarith
  have hσ : σ ≤ 3/4 := by dsimp [σ]; linarith
  have hσ' : σ < 1 := by linarith
  have hleft := weighted_vertical q hX ha hab hb hβ (by linarith : 0 < σ) hσ'.le hA.le v
    (continuous_contour χ hG hs hσ'.ne).aestronglyMeasurable
    (fun t => hlog q χ σ t le_rfl (by linarith) (left_pole_dist hσ t))
  have hAbs : Summable fun n => ‖LSeries.term (twistedCoefficient χ) (2:ℂ) n‖ :=
    summable_norm_iff.mpr (χ.LSeriesSummable_twist_vonMangoldt (by norm_num))
  have hright (t : ℝ) : LSeries (twistedCoefficient χ) (line 2 t) = contourLog χ (line 2 t) := by
    rw [contour_right]; exact LSeries_twistedCoefficient_eq χ (by simp)
  have hiR : Integrable fun t : ℝ => contourLog χ (line 2 t)*K (line 2 t) := by
    simp_rw [← hright]
    exact integrable_series_transform (twistedCoefficient χ) K (σ := 2)
      (integrable_transform hX ha hab hb hβ (by norm_num) le_rfl) (by simpa using hAbs)
  have horiz := @horizontal_limit X (a:ℝ) (b:ℝ) β d A q _ χ hX ha hab hb hβ hd hd' hA.le (hlog q χ)
  have shift := contour_shift χ hG hs hσ'
    (analytic_transform (zero_lt_one.trans_le (hX.trans ha)) b β) hleft.1 hiR
    (horiz (fun T hT => by simpa using abs_of_nonneg (zero_le_one.trans hT)))
    (horiz (fun T hT => abs_of_nonneg (zero_le_one.trans hT)))
  have inv := character_sum_eq_vertical χ hX ha hab hb hβ
  have rline (t : ℝ) : -logDeriv (LFunction χ) (2+(t:ℂ)*I) = contourLog χ (line 2 t) := by
    simpa [line] using (contour_right q χ t).symm
  simp_rw [rline] at inv
  change _ = c • (∫ t : ℝ, contourLog χ (line 2 t)*K (line 2 t)) at inv
  rw [inv,shift,smul_add]
  have hcancel (z : ℂ) : c • ((2*(Real.pi:ℂ))*z) = z := by
    rw [Complex.real_smul]
    simp [c,Complex.ofReal_mul,Real.pi_ne_zero,mul_assoc]
  rw [hcancel,add_sub_cancel_right,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
  have hbnd := (norm_integral_le_integral_norm (fun t : ℝ => v t*K (line σ t))).trans hleft.2
  exact (mul_le_mul_of_nonneg_left hbnd hc.le).trans_eq (by dsimp [σ]; ring)

end GoldbachTwistedMellin
end
end


section
open Finset Complex GoldbachGRHWindow
noncomputable section
namespace GoldbachTwistedMellin

variable {q : ℕ} [NeZero q]
local instance : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _

-- Generalize the finite Parseval argument of PR #2486 to a complex principal term.
private noncomputable def residueSum (I : Finset ℕ) (w : ℕ → ℂ) (r : ZMod q) : ℂ :=
  ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r), w k

private noncomputable def residueError (M : ℂ) (I : Finset ℕ) (w : ℕ → ℂ) (r : ZMod q) : ℂ :=
  residueSum I w r - if IsUnit r then M / (q.totient : ℂ) else 0

private theorem sum_residueSum_mul (I : Finset ℕ) (w : ℕ → ℂ) (K : ZMod q → ℂ) :
    (∑ r : ZMod q, residueSum I w r * K r) =
      ∑ k ∈ I, w k * K (k : ZMod q) := by
  calc
    _ = ∑ r : ZMod q, ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r),
        w k * K (k : ZMod q) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [residueSum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [(Finset.mem_filter.mp hk).2]
    _ = _ := Finset.sum_fiberwise I (fun k => (k : ZMod q)) _

private theorem sum_if_isUnit (F : ZMod q → ℂ) :
    (∑ r : ZMod q, if IsUnit r then F r else 0) = ∑ u : (ZMod q)ˣ, F (u : ZMod q) := by
  classical
  rw [← Finset.sum_filter]
  have hs : (univ : Finset (ZMod q)).filter IsUnit =
      (univ : Finset (ZMod q)ˣ).map ⟨(↑), Units.val_injective⟩ := by
    ext r
    simp [IsUnit]
  rw [hs, Finset.sum_map]
  rfl

private theorem residueError_character (M : ℂ) (I : Finset ℕ) (w : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) :
    (∑ r : ZMod q, residueError M I w r * χ r) =
      (∑ k ∈ I, w k * χ (k : ZMod q)) - (if χ = 1 then M else 0) := by
  classical
  unfold residueError
  simp only [sub_mul, Finset.sum_sub_distrib, sum_residueSum_mul]
  congr 1
  have hs : (∑ r : ZMod q, (if IsUnit r then M / (q.totient : ℂ) else 0) * χ r) =
      (M / (q.totient : ℂ)) * (∑ r : ZMod q, χ r) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hr : IsUnit r
    · simp [hr]
    · simp [hr, MulChar.map_nonunit χ hr]
  rw [hs]
  by_cases hχ : χ = 1
  · subst χ
    rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient, ite_eq_left rfl]
    exact div_mul_cancel₀ _ (by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne')
  · rw [MulChar.sum_eq_zero_of_ne_one hχ, mul_zero, ite_eq_right hχ]

private theorem residueError_additive (M : ℂ) (I : Finset ℕ) (w : ℕ → ℂ) (a : ZMod q) :
    (∑ r : ZMod q, residueError M I w r * ZMod.stdAddChar (a * r)) =
      (∑ k ∈ I, w k * ZMod.stdAddChar (a * (k : ZMod q))) - M * additiveModel q a := by
  classical
  simp only [residueError, sub_mul, Finset.sum_sub_distrib, sum_residueSum_mul]
  congr 1
  calc
    _ = (M / (q.totient : ℂ)) *
        (∑ r : ZMod q, if IsUnit r then ZMod.stdAddChar (a * r) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : IsUnit r <;> simp [hr]
    _ = _ := by
      rw [sum_if_isUnit]
      unfold additiveModel
      simp only [div_eq_mul_inv]
      ring

/-- Squared short-window error at all additive numerators, from uniform
    individual character bounds and an absolute mass bound at nonunits. -/
theorem sum_additive_centered_sq_le (M : ℂ) (I : Finset ℕ) (w : ℕ → ℂ)
    (B P : ℝ) (_hB : 0 ≤ B) (_hP : 0 ≤ P)
    (hχ : ∀ χ : DirichletCharacter ℂ q,
      ‖(∑ k ∈ I, w k * χ (k : ZMod q)) - (if χ = 1 then M else 0)‖ ≤ B)
    (hnon : (∑ k ∈ I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q)), ‖w k‖) ≤ P) :
    (∑ a : ZMod q,
      ‖(∑ k ∈ I, w k * ZMod.stdAddChar (a * (k : ZMod q))) - M * additiveModel q a‖ ^ 2) ≤
      (q : ℝ) * (B ^ 2 + P ^ 2) := by
  classical
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hCard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hUnit : (∑ r ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖residueError M I w r‖ ^ 2) ≤
      B ^ 2 := by
    apply le_of_mul_le_mul_left _ hφ
    rw [← multiplicative_energy]
    calc
      _ ≤ ∑ χ : DirichletCharacter ℂ q, B ^ 2 := by
        refine Finset.sum_le_sum fun χ _ => ?_
        rw [residueError_character]
        exact pow_le_pow_left₀ (norm_nonneg _) (hχ χ) 2
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hCard]
  let V : Finset (ZMod q) := univ.filter (fun r => ¬ IsUnit r)
  have hV : (∑ r ∈ V, ‖residueError M I w r‖) ≤ P := by
    calc
      _ ≤ ∑ r ∈ V, ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r), ‖w k‖ := by
        refine Finset.sum_le_sum fun r hr => ?_
        have hr' : ¬ IsUnit r := (Finset.mem_filter.mp hr).2
        simpa [residueError, hr', residueSum] using
          norm_sum_le (I.filter (fun k : ℕ => (k : ZMod q) = r)) w
      _ = ∑ k ∈ I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q)), ‖w k‖ := by
        rw [Finset.sum_fiberwise_eq_sum_filter]
        simp [V]
      _ ≤ _ := hnon
  have hNonUnit : (∑ r ∈ V, ‖residueError M I w r‖ ^ 2) ≤ P ^ 2 :=
    (Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)).trans
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hV 2)
  simp_rw [← residueError_additive]
  rw [additive_energy]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := (univ : Finset (ZMod q))) (p := IsUnit)]
  exact add_le_add hUnit hNonUnit


theorem centered_additive_le (M : ℂ) (I : Finset ℕ) (w : ℕ → ℂ)
    (B P : ℝ) (hB : 0 ≤ B) (hP : 0 ≤ P)
    (hχ : ∀ χ : DirichletCharacter ℂ q,
      ‖(∑ k ∈ I, w k * χ (k : ZMod q)) - (if χ = 1 then M else 0)‖ ≤ B)
    (hnon : (∑ k ∈ I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q)), ‖w k‖) ≤ P)
    (a : ZMod q) :
    ‖(∑ k ∈ I, w k * ZMod.stdAddChar (a * (k : ZMod q))) - M*additiveModel q a‖ ≤
      Real.sqrt q*(B+P) := by
  let e := fun a : ZMod q => ‖(∑ k ∈ I, w k * ZMod.stdAddChar (a * (k : ZMod q))) - M*additiveModel q a‖
  have he : e a ^ 2 ≤ (q:ℝ)*(B^2+P^2) :=
    (Finset.single_le_sum (f := fun z : ZMod q => e z ^ 2) (fun _ _ => sq_nonneg _) (mem_univ a)).trans
      (sum_additive_centered_sq_le M I w B P hB hP hχ hnon)
  have hbig : (q:ℝ)*(B^2+P^2) ≤ (Real.sqrt q*(B+P))^2 := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg q)]
    exact mul_le_mul_of_nonneg_left (by nlinarith only [mul_nonneg hB hP]) (Nat.cast_nonneg q)
  exact le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (by positivity) (he.trans hbig)

end GoldbachTwistedMellin
end
end


section
open Set Filter MeasureTheory Complex
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

theorem phase_dist (β x y : ℝ) : ‖phase β x-phase β y‖ ≤ |β| * |x-y| := by
  exact (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (phase_deriv β z).hasDerivWithinAt)
    (fun z _ => by simp [Real.norm_eq_abs]) (mem_univ y) (mem_univ x)

theorem phase_cell {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (β : ℝ) (k : ℕ) :
    ‖(∫ x : ℝ in ((k:ℝ)+u)..((k:ℝ)+1+u), phase β x) - phase β ((k:ℝ)+1)‖ ≤ |β| := by
  have hi := (continuous_phase β).intervalIntegrable ((k:ℝ)+u) ((k:ℝ)+1+u) (μ := volume)
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (k:ℝ)+u) (b := (k:ℝ)+1+u)
    (f := fun x => phase β x-phase β ((k:ℝ)+1)) (C := |β|) (fun x hx => by
      rw [uIoc_of_le (by linarith)] at hx
      have h := phase_dist β x ((k:ℝ)+1)
      exact h.trans (by
        conv_rhs => rw [← mul_one |β|]
        exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [hu.1,hx.1],by linarith [hu.2,hx.2]⟩) (abs_nonneg _)))
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const,intervalIntegral.integral_const] at hh
  simpa [show (k:ℝ)+1+u-((k:ℝ)+u) = 1 by ring] using hh

theorem phase_cells {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (β : ℝ) (a b : ℕ) (hab : a ≤ b) :
    ‖(∫ x : ℝ in ((a:ℝ)+u)..((b:ℝ)+u), phase β x) - ∑ k ∈ Finset.Ioc a b, phase β k‖ ≤
      ((b:ℝ)-a)*|β| := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hI : Finset.Ioc a (b+1) = insert (b+1) (Finset.Ioc a b) := by
      ext k; simp only [Finset.mem_Ioc,Finset.mem_insert]; omega
    have hk : b+1 ∉ Finset.Ioc a b := by simp
    rw [hI,Finset.sum_insert hk,Nat.cast_succ,← intervalIntegral.integral_add_adjacent_intervals
      ((continuous_phase β).intervalIntegrable _ ((b:ℝ)+u)) ((continuous_phase β).intervalIntegrable _ _)]
    have h := norm_add_le ((∫ x : ℝ in ((a:ℝ)+u)..((b:ℝ)+u), phase β x) - ∑ k ∈ Finset.Ioc a b, phase β k)
      ((∫ x : ℝ in ((b:ℝ)+u)..((b:ℝ)+1+u), phase β x) - phase β ((b:ℝ)+1))
    rw [show ∀ A B C D : ℂ, A+B-(D+C) = (A-C)+(B-D) by intros; ring]
    exact h.trans ((add_le_add ih (phase_cell hu β b)).trans_eq (by ring))

theorem principal_approx {a b : ℕ} (ha : 0 < a) (hab : a+1 ≤ b) (β : ℝ) :
    ‖transform a b β 1 - ∑ k ∈ Finset.Ioc a b, phase β k‖ ≤ ((b:ℝ)-a)*|β| := by
  let S := ∑ k ∈ Finset.Ioc a b, phase β k
  let H := fun u : ℝ => ∫ x : ℝ in ((a:ℝ)+u)..((b:ℝ)+u), phase β x
  have hi (x y : ℝ) := (continuous_phase β).intervalIntegrable x y (μ := volume)
  have hc : Continuous H := by
    let P := fun v : ℝ => ∫ x : ℝ in (0:ℝ)..v, phase β x
    have cp : Continuous P := intervalIntegral.continuous_primitive hi 0
    have eqH : H = fun u => P ((b:ℝ)+u)-P ((a:ℝ)+u) := by
      funext u
      exact (eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals (hi 0 ((a:ℝ)+u)) (hi ((a:ℝ)+u) ((b:ℝ)+u))))
    rw [eqH]
    exact (cp.comp (continuous_const.add continuous_id)).sub (cp.comp (continuous_const.add continuous_id))
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (f := fun u => H u-S) (C := ((b:ℝ)-a)*|β|) (fun u hu => by
      rw [uIoc_of_le zero_le_one] at hu
      exact phase_cells ⟨hu.1.le,hu.2⟩ β a b (by omega))
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const] at h
  rw [transform_eq_average (by exact_mod_cast ha) (by exact_mod_cast hab)]
  simpa [H,S,density] using h

end GoldbachTwistedMellin
end
end


section
open Finset Set Filter MeasureTheory Complex GoldbachGRHWindow GoldbachSmoothing Goldbach
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

private theorem nonprime_mass (n : ℕ) :
    (∑ k ∈ range (n+1), if k.Prime then 0 else ArithmeticFunction.vonMangoldt k) =
      Chebyshev.psi n - Chebyshev.theta n := by
  rw [Chebyshev.psi_eq_sum_Icc,Chebyshev.theta_eq_sum_Icc,Nat.floor_natCast,
    sum_filter,←sum_sub_distrib,Nat.range_succ_eq_Icc_zero]
  apply sum_congr rfl
  intro k _
  by_cases hk : k.Prime <;> simp [hk,ArithmeticFunction.vonMangoldt_apply_prime]

theorem prime_removal {q : ℕ} (χ : DirichletCharacter ℂ q) (a b n : ℕ)
    (hb : b ≤ n) (hn : 1 ≤ n) (β : ℝ) :
    ‖(∑ k ∈ Finset.Ioc a b, (primeLog k*phase β k)*χ (k:ZMod q)) -
      (∑ k ∈ Finset.Ioc a b, twistedCoefficient χ k*phase β k)‖ ≤
      2*Real.sqrt n*Real.log n := by
  rw [← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ k ∈ Finset.Ioc a b, if k.Prime then 0 else ArithmeticFunction.vonMangoldt k := by
      apply sum_le_sum
      intro k _
      by_cases hk : k.Prime
      · simp [primeLog,twistedCoefficient,hk,ArithmeticFunction.vonMangoldt_apply_prime hk,mul_comm,mul_left_comm,mul_assoc]
      · simp only [primeLog,ite_eq_right hk,ofReal_zero,zero_mul,zero_sub,norm_neg,
          twistedCoefficient,Pi.mul_apply,norm_mul,norm_phase,mul_one,Complex.norm_real,
          Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact (mul_le_mul_of_nonneg_right (χ.norm_le_one _) ArithmeticFunction.vonMangoldt_nonneg).trans_eq (one_mul _)
    _ ≤ ∑ k ∈ range (n+1), if k.Prime then 0 else ArithmeticFunction.vonMangoldt k := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk; have := (mem_Ioc.mp hk).2; apply Finset.mem_range.mpr; omega
      · intro k _ _; split_ifs <;> positivity
    _ ≤ _ := by rw [nonprime_mass]; exact Chebyshev.psi_sub_theta_le (by exact_mod_cast hn)

theorem dyadic_prime_error {q : ℕ} [NeZero q] {a b n : ℕ} {β B : ℝ}
    (hb : b ≤ n) (hn : 1 ≤ n) (ha : 0 < a) (hab : a+1 ≤ b) (hB : 0 ≤ B)
    (hchr : ∀ χ : DirichletCharacter ℂ q, ‖(∑ k ∈ Finset.Ioc a b, twistedCoefficient χ k*phase β k) -
      principalFlag χ*transform a b β 1‖ ≤ B) (r : ZMod q) :
    ‖(∑ k ∈ Finset.Ioc a b, (primeLog k*phase β k)*ZMod.stdAddChar (r*(k:ZMod q))) -
      (∑ k ∈ Finset.Ioc a b, phase β k)*additiveModel q r‖ ≤
      Real.sqrt q*(2*Real.sqrt n*Real.log n+B+((b:ℝ)-a)*|β|+Real.log q) := by
  classical
  let S := ∑ k ∈ Finset.Ioc a b, phase β k
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have habR : (a:ℝ) ≤ b := by exact_mod_cast (show a ≤ b by omega)
  have hqR : 1 ≤ (q:ℝ) := by exact_mod_cast (NeZero.pos q)
  refine centered_additive_le S (Finset.Ioc a b) (fun k => primeLog k*phase β k) _
    (Real.log q) (by have := Real.log_nonneg hnR; have := sub_nonneg.mpr habR; positivity)
    (Real.log_nonneg hqR) ?_ ?_ r
  · intro χ
    let P := ∑ k ∈ Finset.Ioc a b, (primeLog k*phase β k)*χ (k:ZMod q)
    let L := ∑ k ∈ Finset.Ioc a b, twistedCoefficient χ k*phase β k
    let M := principalFlag χ*transform a b β 1
    have hm : ‖M-(if χ=1 then S else 0)‖ ≤ ((b:ℝ)-a)*|β| := by
      by_cases h : χ=1
      · simpa [M,S,principalFlag,h] using principal_approx ha hab β
      · simpa [M,principalFlag,h] using mul_nonneg (sub_nonneg.mpr habR) (abs_nonneg β)
    have ht : P-(if χ=1 then S else 0) = (P-L)+(L-M)+(M-(if χ=1 then S else 0)) := by abel
    have result : ‖P-(if χ=1 then S else 0)‖ ≤ 2*Real.sqrt n*Real.log n+B+((b:ℝ)-a)*|β| := by
      rw [ht]
      exact (norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add
        (prime_removal χ a b n hb hn β) (hchr χ))) hm)
    by_cases h : χ = 1 <;> simpa [P,h] using result
  · simpa only [norm_mul,norm_phase,mul_one] using primeLog_nonunit_mass_le (q := q) (Finset.Ioc a b)

end GoldbachTwistedMellin
end
end


section
open Finset Complex GoldbachGRHWindow
noncomputable section
namespace GoldbachTwistedMellin

/-- Repeatedly halve n-2. This makes the integer endpoints of every block
compatible with both one-unit shoulders of the Mellin window. -/
theorem dyadic_prefix (f : ℕ → ℂ) (n : ℕ) (hn : 2 ≤ n) (D : ℝ) (_hD : 0 ≤ D)
    (hbase : ∀ j : ℕ, j ≤ 3 → ‖∑ k ∈ Finset.Ioc 0 j, f k‖ ≤ D)
    (hblock : ∀ a b : ℕ, 1 ≤ a → a+1 ≤ b → b+1 ≤ 2*a → b ≤ n →
      ‖∑ k ∈ Finset.Ioc a b, f k‖ ≤ D) :
    ‖∑ k ∈ Finset.Ioc 0 n, f k‖ ≤ ((Nat.log 2 (n-2):ℝ)+1)*D := by
  have h (m : ℕ) : m+2 ≤ n → ‖∑ k ∈ Finset.Ioc 0 (m+2), f k‖ ≤ ((Nat.log 2 m:ℝ)+1)*D := by
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro hm
      by_cases hsmall : m < 2
      · exact (hbase _ (by omega)).trans (by
          rw [Nat.log_of_lt hsmall]
          simp)
      · have hm2 : 2 ≤ m := by omega
        have hhalf : m/2 < m := Nat.div_lt_self (by omega) (by decide)
        let a := m/2+2
        have hal : a ≤ m+2 := by dsimp [a]; omega
        rw [← Finset.sum_Ioc_consecutive f (Nat.zero_le a) hal]
        have h₁ := ih (m/2) hhalf (hal.trans hm)
        have h₂ := hblock a (m+2) (by dsimp [a]; omega) (by dsimp [a]; omega) (by dsimp [a]; omega) hm
        have hsum := (norm_add_le ..).trans (add_le_add h₁ h₂)
        exact hsum.trans_eq (by rw [Nat.log_of_one_lt_of_le (by decide : 1 < 2) hm2]; push_cast; ring)
  simpa [Nat.sub_add_cancel hn] using h (n-2) (by omega)

def primeError {q : ℕ} [NeZero q] (r : ZMod q) (β : ℝ) (k : ℕ) : ℂ :=
  (primeLog k*phase β k)*ZMod.stdAddChar (r*(k:ZMod q)) - phase β k*additiveModel q r

theorem sum_primeError {q : ℕ} [NeZero q] (r : ZMod q) (β : ℝ) (a b : ℕ) :
    (∑ k ∈ Finset.Ioc a b, primeError r β k) =
    (∑ k ∈ Finset.Ioc a b, (primeLog k*phase β k)*ZMod.stdAddChar (r*(k:ZMod q))) -
      (∑ k ∈ Finset.Ioc a b, phase β k)*additiveModel q r := by
  simp only [primeError,sum_sub_distrib,sum_mul]

theorem norm_unit_model {q : ℕ} [NeZero q] (r : ZMod q) : ‖additiveModel q r‖ ≤ 1 := by
  have hphi : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  rw [additiveModel,norm_div,Complex.norm_natCast,div_le_iff₀ hphi,one_mul]
  refine (norm_sum_le ..).trans ?_
  simp [ZMod.stdAddChar_apply,ZMod.card_units_eq_totient]

theorem primeError_small {q : ℕ} [NeZero q] (r : ZMod q) (β : ℝ) (j : ℕ) (hj : j ≤ 3) :
    ‖∑ k ∈ Finset.Ioc 0 j, primeError r β k‖ ≤ 12 := by
  refine (norm_sum_le ..).trans ?_
  calc
    _ ≤ ∑ _k ∈ Finset.Ioc 0 j, (4:ℝ) := by
      refine sum_le_sum fun k hk => ?_
      have hpos : 0 < k := (mem_Ioc.mp hk).1
      have hle : k ≤ 3 := (mem_Ioc.mp hk).2.trans hj
      have hposR : 1 ≤ (k:ℝ) := by exact_mod_cast hpos
      have hleR : (k:ℝ) ≤ 3 := by exact_mod_cast hle
      have hp : ‖primeLog k‖ ≤ 3 := by
        unfold primeLog
        by_cases h : k.Prime
        · simp only [ite_eq_left h,Complex.norm_real,Real.norm_of_nonneg (Real.log_nonneg hposR)]
          linarith only [Real.log_le_sub_one_of_pos (by linarith : 0 < (k:ℝ)),hleR]
        · simp [h]
      unfold primeError
      refine (norm_sub_le ..).trans ?_
      simpa [norm_mul,ZMod.stdAddChar_apply] using (add_le_add hp (norm_unit_model r)).trans_eq (by norm_num : (3:ℝ)+1=4)
    _ ≤ _ := by simp; exact_mod_cast (show j*4 ≤ 12 by omega)

end GoldbachTwistedMellin
end
end


section
open Set Real Goldbach
noncomputable section
namespace GoldbachTwistedMellin

def logScale (x : ℝ) := 1+Real.log (2*x)
theorem logScale_one {x : ℝ} (hx : 1 ≤ x) : 1 ≤ logScale x := by
  dsimp [logScale]
  linarith only [Real.log_nonneg (by linarith : 1 ≤ 2*x)]
theorem log_le_scale {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ logScale x := by
  dsimp [logScale]
  linarith only [Real.log_le_log (by linarith : 0 < x) (by linarith : x ≤ 2*x)]

theorem log_window_scale {X x : ℝ} {q : ℕ} [NeZero q] (hX : 1 ≤ X) (hXx : X ≤ x)
    (hq : (q:ℝ) ≤ x) : logBudget q X ≤ 10*logScale x ∧ Real.log (heightCut X) ≤ 8*logScale x := by
  have hx := hX.trans hXx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hT : 1 ≤ heightCut X := by dsimp [heightCut]; exact one_le_pow₀ (by linarith)
  have hT0 := zero_lt_one.trans_le hT
  have qpos : 0 < (q:ℝ) := by exact_mod_cast NeZero.pos q
  have ht : Real.log (heightCut X) ≤ 8*Real.log (2*x) := by
    rw [heightCut,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith)) (by norm_num)
  have ht' : 2+heightCut X ≤ 3*heightCut X := by linarith
  have hlog := Real.log_le_log (by linarith : 0 < 2+heightCut X) ht'
  rw [Real.log_mul (by norm_num) hT0.ne'] at hlog
  have hqlog := Real.log_le_log (by positivity : 0 < 2*(q:ℝ)) (by linarith : 2*(q:ℝ) ≤ 2*x)
  have hln3 := Real.log_le_sub_one_of_pos (by norm_num : 0<(3:ℝ))
  have hln := Real.log_nonneg (by linarith : 1 ≤ 2*x)
  dsimp only [logScale,logBudget,logHeight]
  rw [abs_of_pos hT0,Real.log_mul (by positivity) (by linarith : 2+heightCut X ≠ 0)]
  constructor <;> linarith

theorem sqrt_q_budget {x X γ : ℝ} {q : ℕ} [NeZero q]
    (hX : 1 ≤ X) (hXx : X ≤ x) (hq : (q:ℝ) ≤ Real.sqrt x)
    (hγ : (q:ℝ)*|γ| * x ≤ 8*Real.sqrt x) :
    Real.sqrt q ≤ x^(1/4:ℝ) ∧
    Real.sqrt q*(1+Real.sqrt (1+4*|γ| * X)+Real.log (heightCut X)) ≤ 17*logScale x*x^(1/4:ℝ) := by
  have hx := hX.trans hXx
  have hx0 := (zero_lt_one.trans_le hx).le
  have hq' : (q:ℝ) ≤ x := hq.trans (Real.sqrt_le_self_iff.mpr (Or.inr hx))
  have hQ : Real.sqrt (Real.sqrt x) = x^(1/4:ℝ) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul hx0]
    norm_num
  have hq₁ := (Real.sqrt_le_sqrt hq).trans_eq hQ
  have hq₂ : Real.sqrt q*Real.sqrt (1+4*|γ| * X) ≤ 8*x^(1/4:ℝ) := by
    have hqq := mul_le_mul_of_nonneg_left hXx (mul_nonneg (Nat.cast_nonneg q) (abs_nonneg γ))
    have hcmp : (q:ℝ)*(1+4*|γ| * X) ≤ 64*Real.sqrt x := by
      nlinarith only [hγ,hq,hqq,Real.sqrt_nonneg x]
    rw [← Real.sqrt_mul (Nat.cast_nonneg q),← hQ]
    exact (Real.sqrt_le_sqrt hcmp).trans_eq (by rw [Real.sqrt_mul (by norm_num : 0 ≤ (64:ℝ))]; norm_num)
  have hlog := (log_window_scale hX hXx hq').2
  have hT : 1 ≤ heightCut X := by dsimp [heightCut]; exact one_le_pow₀ (by linarith)
  have hsqlog := mul_le_mul hq₁ hlog (Real.log_nonneg hT) (Real.rpow_nonneg hx0 _)
  have hL := mul_le_mul_of_nonneg_right (logScale_one hx) (Real.rpow_nonneg hx0 (1/4:ℝ))
  exact ⟨hq₁,by nlinarith only [hq₁,hq₂,hsqlog,hL]⟩

end GoldbachTwistedMellin
end
end


section
open Set Real Complex Goldbach
noncomputable section
namespace GoldbachTwistedMellin

theorem block_budget {x X γ C d : ℝ} {q : ℕ} [NeZero q] (hX : 1 ≤ X) (hXx : X ≤ x)
    (hd : 0 ≤ d) (hC : 0 ≤ C) (hq : (q:ℝ) ≤ Real.sqrt x) (hγ : (q:ℝ)*|γ| * x ≤ 8*Real.sqrt x) :
    Real.sqrt q*(2*Real.sqrt x*Real.log x +
      C*X^(1/2+d)*logBudget q X*(1+Real.sqrt (1+4*|γ| * X)+Real.log (heightCut X)) +
      x*|γ| + Real.log q) ≤ (12+170*C)*x^(3/4+d)*logScale x^2 := by
  let L := logScale x
  let Q := x^(1/4:ℝ)
  let S := x^(1/2+d)
  let U := x^(3/4+d)
  have hx := hX.trans hXx
  have hx0 := zero_lt_one.trans_le hx
  have hL : 1 ≤ L := logScale_one hx
  have hL0 : 0 ≤ L := by linarith
  have hLL : L ≤ L^2 := by nlinarith only [hL,sq_nonneg (L-1)]
  have hL2 : 1 ≤ L^2 := hL.trans hLL
  have hqpos : 1 ≤ (q:ℝ) := by exact_mod_cast NeZero.pos q
  have hqx := hq.trans (Real.sqrt_le_self_iff.mpr (Or.inr hx))
  have hlogq := (Real.log_le_log (by linarith : 0 < (q:ℝ)) hqx).trans (log_le_scale hx)
  have hS : Real.sqrt x ≤ S := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hXS : X^(1/2+d) ≤ S := Real.rpow_le_rpow (zero_le_one.trans hX) hXx (by linarith)
  have hQS : Q*S = U := by
    dsimp [Q,S,U]; rw [←Real.rpow_add hx0]; congr 1; ring
  have hBudget := (log_window_scale hX hXx hqx).1
  have ⟨hQ,hWindow⟩ := sqrt_q_budget hX hXx hq hγ
  let W := 1+Real.sqrt (1+4*|γ| * X)+Real.log (heightCut X)
  have hT : 1 ≤ heightCut X := by dsimp [heightCut]; exact one_le_pow₀ (by linarith)
  have hW : 0 ≤ W := by dsimp [W]; linarith only [Real.sqrt_nonneg (1+4*|γ| * X),Real.log_nonneg hT]
  have hBL : 0 ≤ logBudget q X := by
    dsimp [logBudget]; linarith only [logHeight_ge_one q (heightCut X)]
  have hmain : Real.sqrt q*(C*X^(1/2+d)*logBudget q X*W) ≤ 170*C*U*L^2 := by
    calc
      _ = C*(X^(1/2+d)*logBudget q X)*(Real.sqrt q*W) := by ring
      _ ≤ C*(S*(10*L))*(17*L*Q) := mul_le_mul
        (mul_le_mul_of_nonneg_left (mul_le_mul hXS hBudget hBL (Real.rpow_nonneg hx0.le _)) hC)
        hWindow (mul_nonneg (Real.sqrt_nonneg _) hW)
        (mul_nonneg hC (mul_nonneg (Real.rpow_nonneg hx0.le _) (by positivity)))
      _ = _ := by rw [←hQS]; ring
  have hQS' : Real.sqrt q*Real.sqrt x ≤ U :=
    (mul_le_mul hQ hS (Real.sqrt_nonneg _) (Real.rpow_nonneg hx0.le _)).trans_eq hQS
  have hU0 : 0 ≤ U := Real.rpow_nonneg hx0.le _
  have hpsi : Real.sqrt q*(2*Real.sqrt x*Real.log x) ≤ 2*U*L^2 := by
    have sl := mul_le_mul hQS' ((log_le_scale hx).trans hLL) (Real.log_nonneg hx) hU0
    linarith only [show 2*(Real.sqrt q*Real.sqrt x*Real.log x) ≤ 2*(U*L^2) by linarith only [sl],
      show Real.sqrt q*(2*Real.sqrt x*Real.log x) = 2*(Real.sqrt q*Real.sqrt x*Real.log x) by ring,
      show 2*(U*L^2) = 2*U*L^2 by ring]
  have hg : x*|γ| ≤ 8*Real.sqrt x := by
    nlinarith only [hγ,mul_le_mul_of_nonneg_right hqpos (mul_nonneg (abs_nonneg γ) hx0.le)]
  have herr : Real.sqrt q*(x*|γ|) ≤ 8*U*L^2 := by
    have A := mul_le_mul_of_nonneg_left hg (Real.sqrt_nonneg q)
    have B := mul_le_mul_of_nonneg_left hL2 hU0
    nlinarith only [A,B,hQS']
  have hqU : Real.sqrt q ≤ U := (le_mul_of_one_le_right (Real.sqrt_nonneg _) (by simpa using Real.sqrt_le_sqrt hx : 1 ≤ Real.sqrt x)).trans hQS'
  have hqlog := mul_le_mul hqU (hlogq.trans hLL) (Real.log_nonneg hqpos) hU0
  change Real.sqrt q*(2*Real.sqrt x*Real.log x + C*X^(1/2+d)*logBudget q X*W+x*|γ|+Real.log q) ≤ (12+170*C)*U*L^2
  nlinarith only [hmain,hpsi,herr,hqlog,mul_nonneg hU0 (sq_nonneg L)]

end GoldbachTwistedMellin
end
end


section
open Finset Complex Real Goldbach GoldbachGRHWindow DeepThreeQuarters
noncomputable section
namespace GoldbachTwistedMellin

theorem rational_phase {q : ℕ} [NeZero q] (a k : ℕ) (β : ℝ) :
    phase (2*Real.pi*β) k*ZMod.stdAddChar ((a:ZMod q)*(k:ZMod q)) =
      geometricPhase ((k:ℝ)*((a:ℝ)/q+β)) := by
  have hc (m : ℕ) : ZMod.stdAddChar ((m:ℕ):ZMod q) = Complex.exp (2*(Real.pi:ℂ)*I*(m:ℂ)/(q:ℂ)) := by
    simpa only [Int.cast_natCast] using ZMod.stdAddChar_coe (N := q) (m:ℤ)
  rw [← Nat.cast_mul,hc,phase,geometricPhase,←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem primeError_prefix_eq {q : ℕ} [NeZero q] (a n : ℕ) (ha : a.Coprime q) (β : ℝ) :
    (∑ k ∈ Finset.Ioc 0 n, primeError (a:ZMod q) (2*Real.pi*β) k) =
        weightedSum n primeWeight ((a:ℝ)/q+β) - rationalModel n q β := by
  rw [sum_primeError]
  have hI : Finset.Ioc 0 n = Finset.Icc 1 n := by ext k; simp [Nat.lt_iff_add_one_le]
  have hR : range (n+1) = insert 0 (Finset.Ioc 0 n) := by
    ext k; simp only [mem_range,mem_insert,mem_Ioc]; omega
  apply congrArg₂ (fun x y : ℂ => x-y)
  · rw [weightedSum,hR,Finset.sum_insert (by simp)]
    simp only [primeWeight,Nat.not_prime_zero,ite_false,ofReal_zero,zero_mul,zero_add]
    apply sum_congr rfl
    intro k _
    rw [mul_assoc,rational_phase]
    rfl
  · rw [rationalModel,additiveModel_eq_moebius _ ((ZMod.isUnit_iff_coprime ..).mpr ha),mul_comm,hI]
    apply congrArg (fun z : ℂ => (ArithmeticFunction.moebius q:ℂ)/(q.totient:ℂ)*z)
    apply sum_congr rfl
    intro k _
    unfold phase geometricPhase
    congr 1
    push_cast
    ring

theorem angular_range {n q : ℕ} {β : ℝ} (hn : 64 ≤ n) (hq : 1 ≤ q)
    (hβ : |β| ≤ 1/((q:ℝ)*Real.sqrt n)) :
    |2*Real.pi*β| ≤ 1 ∧ (q:ℝ)*|2*Real.pi*β| * (n:ℝ) ≤ 8*Real.sqrt n := by
  have hnR : (64:ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hs : (8:ℝ) ≤ Real.sqrt n := by
    calc
      _ = Real.sqrt 64 := by norm_num
      _ ≤ _ := Real.sqrt_le_sqrt hnR
  have ht := (le_div_iff₀ (by positivity : 0 < (q:ℝ)*Real.sqrt n)).mp hβ
  have hπ := Real.pi_lt_four
  have hh := mul_le_mul_of_nonneg_left ht (show 0 ≤ 2*Real.pi by positivity)
  rw [abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]
  have hD : 8 ≤ (q:ℝ)*Real.sqrt n :=
    hs.trans ((one_mul _).symm.trans_le (mul_le_mul_of_nonneg_right hqR (Real.sqrt_nonneg _)))
  constructor
  · by_contra! h
    nlinarith only [hh,hπ,mul_lt_mul_of_pos_right h (show 0 < (q:ℝ)*Real.sqrt n by positivity),hD]
  · have hh' : (q:ℝ)*(2*Real.pi*|β|)*Real.sqrt n ≤ 8 := by nlinarith only [hh,hπ]
    calc
      _ = ((q:ℝ)*(2*Real.pi*|β|)*Real.sqrt n)*Real.sqrt n := by
        rw [mul_assoc _ (Real.sqrt n),←sq,Real.sq_sqrt (Nat.cast_nonneg n)]
      _ ≤ _ := mul_le_mul_of_nonneg_right hh' (Real.sqrt_nonneg n)

theorem dyadic_count_le {n : ℕ} (hn : 4 ≤ n) : (Nat.log 2 (n-2):ℝ)+1 ≤ 3*logScale n := by
  have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hpos : 0 < ((n-2:ℕ):ℝ) := by exact_mod_cast (show 0 < n-2 by omega)
  have hle : ((n-2:ℕ):ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 2
  have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have h := Real.natLog_le_logb (n-2) 2
  rw [Real.logb, Nat.cast_ofNat,le_div_iff₀ (by positivity)] at h
  have h' := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg (Nat.log 2 (n-2)) (α := ℝ))
  linarith only [h,h',Real.log_le_log hpos hle,log_le_scale hn',logScale_one hn']

end GoldbachTwistedMellin
end
end


section
open Finset Real Complex Goldbach GoldbachGRHWindow DeepThreeQuarters
noncomputable section
namespace GoldbachTwistedMellin

/-- Uniform rational approximation throughout the Dirichlet approximation range.
The estimate has an arbitrarily small power loss, sufficient for the frozen
three-quarters target. The phase parameter here uses the 2π convention. -/
theorem prefix_rational_error (hG : GRH) {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1/4) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 64 ≤ n → ∀ a q : ℕ, 1 ≤ q → a.Coprime q →
      (q:ℝ) ≤ Real.sqrt n → ∀ β : ℝ, |β| ≤ 1/((q:ℝ)*Real.sqrt n) →
      ‖weightedSum n primeWeight ((a:ℝ)/q+β) - rationalModel n q β‖ ≤
        K*(n:ℝ)^(3/4+d)*logScale n^3 := by
  obtain ⟨C,hC,hchr⟩ := dyadic_twist_under_GRH hG hd hd'
  refine ⟨3*(12+170*C),by positivity,?_⟩
  intro n hn a q hq hc hqs β hβ
  let : NeZero q := ⟨by omega⟩
  let γ := 2*Real.pi*β
  let D := (12+170*C)*(n:ℝ)^(3/4+d)*logScale n^2
  have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hL := logScale_one hn'
  have hpow : (1:ℝ) ≤ (n:ℝ)^(3/4+d) := Real.one_le_rpow hn' (by linarith)
  have hL2 : 1 ≤ logScale n^2 := one_le_pow₀ hL
  have hD : 12 ≤ D := by
    dsimp [D]
    calc
      (12:ℝ) ≤ (12+170*C)*1*1 := by linarith
      _ ≤ _ := by gcongr
  have hD0 : 0 ≤ D := by linarith
  have ⟨hγ,hγq⟩ := angular_range hn hq hβ
  have hpre := dyadic_prefix (primeError (a:ZMod q) γ) n (by omega) D hD0
    (fun j hj => (primeError_small _ _ _ hj).trans hD) (fun l r hl hlr hr hrn => by
      have hlR : 1 ≤ (l:ℝ) := by exact_mod_cast hl
      have hlrR : (l:ℝ)+1 ≤ r := by exact_mod_cast hlr
      have hss : (l:ℝ) ≤ n := by exact_mod_cast (show l ≤ n by omega)
      let W := 1+Real.sqrt (1+4*|γ| * l)+Real.log (heightCut l)
      let B := C*(l:ℝ)^(1/2+d)*logBudget q l*W
      have hT : 1 ≤ heightCut l := by dsimp [heightCut]; exact one_le_pow₀ (by linarith)
      have hW : 0 ≤ W := by dsimp [W]; linarith only [Real.sqrt_nonneg (1+4*|γ| * l),Real.log_nonneg hT]
      have hlog : 0 ≤ logBudget q l := by dsimp [logBudget]; linarith only [logHeight_ge_one q (heightCut l)]
      have hB : 0 ≤ B := by dsimp [B]; positivity
      have m := dyadic_prime_error (q := q) (a := l) (b := r) (n := n) (β := γ) (B := B) hrn (by omega) hl hlr hB
        (fun χ => hchr q χ l r l γ hlR le_rfl hlrR (by exact_mod_cast hr) hγ) (a:ZMod q)
      rw [sum_primeError]
      have hbnd := block_budget (X := (l:ℝ)) (x := (n:ℝ)) (q := q) (γ := γ) hlR hss hd.le hC.le hqs hγq
      refine m.trans (le_trans ?_ hbnd)
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg q)
      have hrR : (r:ℝ) ≤ n := by exact_mod_cast hrn
      have he := mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) l] : (r:ℝ)-l ≤ n) (abs_nonneg γ)
      dsimp only [B,W]
      linarith only [he])
  change ‖∑ k ∈ Finset.Ioc 0 n, primeError (a:ZMod q) (2*Real.pi*β) k‖ ≤ _ at hpre
  rw [primeError_prefix_eq a n hc β] at hpre
  exact hpre.trans ((mul_le_mul_of_nonneg_right (dyadic_count_le (by omega : 4 ≤ n)) hD0).trans_eq (by dsimp [D]; ring))

end GoldbachTwistedMellin
end
end


section
open Finset Real Complex Goldbach DeepThreeQuarters Filter
noncomputable section
namespace GoldbachTwistedMellin

theorem cubic_log_scale {e : ℝ} (he : 0 < e) :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 1 ≤ x → logScale x^3 ≤ D*x^e := by
  let u := e/3
  have hu : 0 < u := by dsimp [u]; positivity
  let c := 1+Real.log 2+1/u
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c^3,by positivity,?_⟩
  intro x hx
  have hx0 := zero_lt_one.trans_le hx
  have hXu := Real.one_le_rpow hx hu.le
  have hlog := Real.log_le_rpow_div hx0.le hu
  have h : logScale x ≤ c*x^u := by
    rw [logScale,Real.log_mul (by norm_num) hx0.ne']
    dsimp [c]
    rw [one_div]
    rw [div_eq_mul_inv] at hlog
    nlinarith only [hlog,mul_le_mul_of_nonneg_left hXu (by linarith : 0 ≤ 1+Real.log 2)]
  refine (pow_le_pow_left₀ (zero_le_one.trans (logScale_one hx)) h 3).trans_eq ?_
  rw [mul_pow,←Real.rpow_mul_natCast hx0.le]
  have hu3 : u*(3:ℕ) = e := by dsimp [u]; ring
  rw [hu3]

/-- The exact frozen pointwise deep-arc conclusion from Dirichlet GRH. -/
theorem deep_three_quarters_of_dirichlet_GRH (hG : GRH) :
    ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0:ℝ) 1,
      t ∉ wideArcs n → ‖weightedSum n primeWeight t‖ ≤ (n:ℝ)^(3/4+η) := by
  intro η hη
  let d := min (η/4) (1/4)
  have hd : 0 < d := lt_min (by positivity) (by norm_num)
  have hdq : d ≤ 1/4 := min_le_right ..
  have hde : d ≤ η/4 := min_le_left ..
  obtain ⟨K,hK,hest⟩ := prefix_rational_error hG hd hdq
  obtain ⟨D,hD,hlog⟩ := cubic_log_scale (show 0 < η/4 by positivity)
  let A := 8+4/(η/2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨N,hN⟩ := eventually_atTop.1 (eventually_absorb (K*D+A) η hη)
  refine ⟨max 64 N,?_⟩
  intro n hn t ht hdeep
  have hn64 := (le_max_left 64 N).trans hn
  have hn4 : 4 ≤ n := by omega
  have hx : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hx0 := zero_lt_one.trans_le hx
  obtain ⟨a,q,hq,_,hc,hqs,hβ,hlo,_⟩ := exists_deep_approximation (by omega : 1 ≤ n) ht hdeep
  let β := t-(a:ℝ)/q
  have hB : 0 < B n q β := (Real.rpow_pos_of_pos hx0 _).trans_le hlo
  have hm := rational_term_le (half_pos hη) hq (hqs.trans (Real.sqrt_le_self_iff.mpr (Or.inr hx)))
    hB (positiveGeometricSum_mul_B_le hn4 hq hβ)
  change ‖rationalModel n q β‖ ≤ A*(n:ℝ)^(η/2)*((n:ℝ)/B n q β) at hm
  have hsize : (n:ℝ)/B n q β ≤ (n:ℝ)^(3/4:ℝ) := by
    calc
      _ ≤ (n:ℝ)/(n:ℝ)^(1/3:ℝ) := div_le_div_of_nonneg_left hx0.le (Real.rpow_pos_of_pos hx0 _) hlo
      _ = (n:ℝ)^(1-1/3:ℝ) := by rw [Real.rpow_sub hx0,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hmodel : ‖rationalModel n q β‖ ≤ A*(n:ℝ)^(3/4+η/2) := by
    refine hm.trans ((mul_le_mul_of_nonneg_left hsize (by positivity)).trans_eq ?_)
    rw [mul_assoc,←Real.rpow_add hx0]
    congr 2
    ring
  have he := hest n hn64 a q hq hc hqs β hβ
  rw [show (a:ℝ)/q+β = t by dsimp [β]; ring] at he
  have herr : ‖weightedSum n primeWeight t-rationalModel n q β‖ ≤ (K*D)*(n:ℝ)^(3/4+η/2) := by
    refine he.trans ((mul_le_mul_of_nonneg_left (hlog n hx) (by positivity)).trans ?_)
    calc
      _ = (K*D)*(n:ℝ)^(3/4+d+η/4) := by rw [Real.rpow_add hx0 (3/4+d) (η/4)]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) (by positivity)
  have tri := norm_add_le (weightedSum n primeWeight t-rationalModel n q β) (rationalModel n q β)
  rw [sub_add_cancel] at tri
  exact (tri.trans ((add_le_add herr hmodel).trans_eq (by ring))).trans (hN n ((le_max_right ..).trans hn))

end GoldbachTwistedMellin
end
end


theorem PEqualNP.Outside.L_goldbach_deep_three_quarters_from_dirichlet_grh : (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1/2) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ wideArcs n → ‖S n w t‖ ≤ (n : ℝ) ^ (3 / 4 + η)) := by
  intro h
  exact GoldbachTwistedMellin.deep_three_quarters_of_dirichlet_GRH h
