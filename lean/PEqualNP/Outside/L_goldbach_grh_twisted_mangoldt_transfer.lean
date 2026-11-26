import Mathlib


/-! The Dirichlet zero count is adapted from DNZJSJ, goldbach-proofs PR #2486,
commit f3613cf846dfb3e7fe7d04fe6ce51c6ee25e7d4f, Apache-2.0. -/

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
end Goldbach
end
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
private theorem per_ordinate :
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

-- Bin zero contributes the trivial bound, bins 1 through J the curvature
-- estimate, and larger bins the reciprocal first-derivative estimate.
private noncomputable def profile (J j : ℕ) : ℝ :=
  if j = 0 then 1 else if j ≤ J then (3+5*Real.pi)/Real.sqrt j else 20/j

private lemma profile_nonneg (J j : ℕ) : 0 ≤ profile J j := by
  unfold profile
  split_ifs <;> positivity

private theorem sqrt_step (j : ℕ) :
    1 / Real.sqrt (j+1:ℝ) ≤ 2*(Real.sqrt (j+1:ℝ)-Real.sqrt j) := by
  have hp : 0 < Real.sqrt (j+1:ℝ) := by positivity
  have hle := Real.sqrt_le_sqrt (show (j:ℝ) ≤ j+1 by linarith)
  have hs1 := Real.sq_sqrt (show 0 ≤ (j+1:ℝ) by positivity)
  have hs0 := Real.sq_sqrt (show 0 ≤ (j:ℝ) by positivity)
  apply (div_le_iff₀ hp).mpr
  nlinarith only [sq_nonneg (Real.sqrt (j+1:ℝ)-Real.sqrt j), hs1, hs0]

private theorem profile_sum (J N : ℕ) :
    (∑ j ∈ Finset.range (N+1), profile J j) ≤
      1+2*(3+5*Real.pi)*Real.sqrt J + 20*(1+Real.log (N+1:ℝ)) := by
  have bound (n : ℕ) :
      (∑ j ∈ Finset.range (n+1), profile J j) ≤
        1+2*(3+5*Real.pi)*Real.sqrt (min n J) + 20*(harmonic n:ℝ) := by
    induction n with
    | zero => simp [profile, harmonic]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [show profile J (n+1) = (if n+1 ≤ J then (3+5*Real.pi)/Real.sqrt (n+1:ℝ) else 20/(n+1:ℝ)) by simp [profile]]
      rw [harmonic_succ]
      push_cast
      split_ifs with h
      · rw [min_eq_left (show (n:ℝ)+1 ≤ J by exact_mod_cast h)]
        rw [min_eq_left (show (n:ℝ) ≤ J by exact_mod_cast Nat.le_trans (Nat.le_succ n) h)] at ih
        have hs := mul_le_mul_of_nonneg_left (sqrt_step n) (show 0 ≤ 3+5*Real.pi by positivity)
        have hr : 0 ≤ ((n:ℝ)+1)⁻¹ := by positivity
        simp only [div_eq_mul_inv, one_mul] at hs ⊢
        linarith only [ih,hs,hr]
      · have hn : J ≤ n := by omega
        rw [min_eq_right (show (J:ℝ) ≤ n by exact_mod_cast hn)] at ih
        rw [min_eq_right (show (J:ℝ) ≤ n+1 by exact_mod_cast hn.trans (Nat.le_succ _))]
        simp only [div_eq_mul_inv]
        linarith only [ih]
  have hs := Real.sqrt_le_sqrt (show min (N:ℝ) J ≤ J by exact min_le_right _ _)
  have hs' := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*(3+5*Real.pi) by positivity)
  have hn := harmonic_le_one_add_log (N+1)
  have hh : (harmonic N : ℝ) ≤ harmonic (N+1) := by
    rw [harmonic_succ]
    push_cast
    have h : 0 ≤ ((N:ℝ)+1)⁻¹ := by positivity
    linarith
  push_cast at hn
  linarith only [bound N,hs',hn,hh]

end GoldbachOscillation

open GoldbachOscillation
open scoped ComplexConjugate

set_option maxHeartbeats 1200000 in
/-- Dyadic kernel estimates and their sum over a finite indexed family with a unit-height occupancy bound. -/
theorem PEqualNP.Outside.L_goldbach_zero_additive_twist_dyadic :
    ∀ (X a b σ β : ℝ), 0 < X → X ≤ a → a ≤ b → b ≤ 2*X → 0 ≤ σ → σ ≤ 1 →
      let K := fun γ : ℝ => ∫ x in a..b, ((x^(σ-1):ℝ):ℂ) *
        Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)
      (∀ γ : ℝ, ‖K γ‖ ≤ X^σ ∧
        (γ ≠ 0 → ‖K γ‖ ≤ X^σ*((3+5*Real.pi)/Real.sqrt |γ|)) ∧
        ∀ H : ℝ, 0 < H → (∀ x ∈ Set.Icc a b, H ≤ |β*x+γ|) → ‖K γ‖ ≤ 5*b^σ/H) ∧
      ∀ (I : Finset ℕ) (g : ℕ → ℝ) (J N : ℕ) (M : ℝ),
        0 ≤ M → 4*|β| * X ≤ J → (∀ i ∈ I, |g i| < (N:ℝ)+1) →
        (∀ j ≤ N, (((I.filter (fun i => ⌊|g i|⌋₊ = j)).card : ℕ) : ℝ) ≤ M) →
        (∑ i ∈ I, ‖K (g i)‖) ≤
          X^σ*M*(1 + 2*(3+5*Real.pi)*Real.sqrt J + 20*(1+Real.log (N+1:ℝ))) := by
  intro X a b σ β hX ha hab hb hσ hσ' K
  have single (γ : ℝ) : ‖K γ‖ ≤ X^σ ∧
      (γ ≠ 0 → ‖K γ‖ ≤ X^σ*((3+5*Real.pi)/Real.sqrt |γ|)) ∧
      ∀ H : ℝ, 0 < H → (∀ x ∈ Set.Icc a b, H ≤ |β*x+γ|) → ‖K γ‖ ≤ 5*b^σ/H :=
    per_ordinate X a b σ γ β hX ha hab hb hσ hσ'
  refine ⟨single, ?_⟩
  intro I g J N M hM hJ hN hcount
  let bin := fun i : ℕ => ⌊|g i|⌋₊
  have hscale := Real.rpow_pos_of_pos hX σ
  have hpow : b^σ ≤ 2*X^σ := by
    calc
      b^σ ≤ (2*X)^σ := Real.rpow_le_rpow (hX.le.trans (ha.trans hab)) hb hσ
      _ = (2:ℝ)^σ * X^σ := Real.mul_rpow (by norm_num) hX.le
      _ ≤ 2*X^σ := by
        apply mul_le_mul_of_nonneg_right _ hscale.le
        simpa using Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num) hσ'
  have per (i : ℕ) : ‖K (g i)‖ ≤ X^σ * profile J (bin i) := by
    have hfloor : ((bin i):ℝ) ≤ |g i| := Nat.floor_le (abs_nonneg _)
    unfold profile
    split_ifs with hz hj
    · simpa using (single (g i)).1
    · have hbin : 0 < ((bin i):ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hz
      have hg : g i ≠ 0 := abs_pos.mp (hbin.trans_le hfloor)
      apply ((single (g i)).2.1 hg).trans
      apply mul_le_mul_of_nonneg_left _ hscale.le
      exact div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hbin)
        (Real.sqrt_le_sqrt hfloor)
    · have hbin : 0 < ((bin i):ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hz
      have hcut : (J:ℝ) ≤ bin i := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hj))
      have sep (x : ℝ) (hx : x ∈ Icc a b) : (bin i:ℝ)/2 ≤ |β*x+g i| := by
        have hxx : 0 ≤ x := hX.le.trans (ha.trans hx.1)
        have ht := abs_add_le (β*x+g i) (-(β*x))
        rw [show β*x+g i+ -(β*x) = g i by ring, abs_neg, abs_mul, abs_of_nonneg hxx] at ht
        have hbβ := mul_le_mul_of_nonneg_left (hx.2.trans hb) (abs_nonneg β)
        linarith only [ht,hbβ,hJ,hcut,hfloor]
      have hhalf : 0 < (bin i:ℝ)/2 := by positivity
      apply ((single (g i)).2.2 _ hhalf sep).trans
      apply (div_le_iff₀ hhalf).mpr
      calc
        5*b^σ ≤ 5*(2*X^σ) := by linarith only [hpow]
        _ = X^σ*(20/(bin i:ℝ))*((bin i:ℝ)/2) := by field_simp; norm_num
  have maps : ∀ i ∈ I, bin i ∈ Finset.range (N+1) := by
    intro i hi
    apply Finset.mem_range.mpr
    exact (Nat.floor_lt (abs_nonneg _)).mpr (by simpa using hN i hi)
  calc
    _ ≤ ∑ i ∈ I, X^σ*profile J (bin i) := Finset.sum_le_sum fun i _ => per i
    _ = ∑ j ∈ Finset.range (N+1), ∑ i ∈ I.filter (fun i => bin i = j),
          X^σ*profile J (bin i) := (Finset.sum_fiberwise_of_maps_to maps _).symm
    _ ≤ ∑ j ∈ Finset.range (N+1), M*(X^σ*profile J j) := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        _ = ∑ i ∈ I.filter (fun i => bin i = j), X^σ*profile J j := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [(Finset.mem_filter.mp hi).2]
        _ = ((I.filter (fun i => bin i = j)).card:ℝ)*(X^σ*profile J j) := by
          simp [nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (hcount j (by have := Finset.mem_range.mp hj; omega))
          (mul_nonneg hscale.le (profile_nonneg J j))
    _ = X^σ*M*(∑ j ∈ Finset.range (N+1), profile J j) := by
      simp_rw [← mul_assoc, mul_comm M (X^σ)]
      exact (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (profile_sum J N) (mul_nonneg hscale.le hM)
end


section
open Set MeasureTheory

namespace TwistedZeroApplication

/-- Label every occurrence of an ordinate by a distinct natural number.
The identity holds for every real-valued test function, including bin indicators. -/
private theorem enumerate_occurrences {α : Type*} (Z : Finset α) (g : α → ℝ) (m : α → ℕ) :
    ∃ (I : Finset ℕ) (h : ℕ → ℝ), (∀ k ∈ I, ∃ z ∈ Z, h k = g z) ∧
      ∀ f : ℝ → ℝ, (∑ k ∈ I, f (h k)) = ∑ z ∈ Z, (m z:ℝ)*f (g z) := by
  classical
  let A := (z : Z) × Fin (m z.val)
  let e : A ↪ ℕ := (Fintype.equivFin A).toEmbedding.trans Fin.valEmbedding
  let I := Finset.univ.map e
  let h (k : ℕ) : ℝ := if hk : ∃ u : A, e u = k then g (Classical.choose hk).1.val else 0
  have he (u : A) : h (e u) = g u.1.val := by
    have hx : ∃ v : A, e v = e u := ⟨u,rfl⟩
    simp only [h, dite_eq_left hx, e.injective (Classical.choose_spec hx)]
  refine ⟨I,h,?_,?_⟩
  · intro k hk
    obtain ⟨u,_,rfl⟩ := Finset.mem_map.mp hk
    exact ⟨u.1.val,u.1.property,he u⟩
  · intro f
    change ∑ k ∈ Finset.univ.map e, f (h k) = _
    rw [Finset.sum_map]
    simp only [he]
    change (∑ u : (z : Z) × Fin (m z.val), f (g u.1.val)) = _
    rw [Fintype.sum_sigma]
    simp [nsmul_eq_mul]
    exact Finset.sum_attach Z (fun z => (m z:ℝ)*f (g z))

private theorem bin_cover {f : ℂ → ℂ} {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1)
    (hz : f z = 0) :
    z ∈ Goldbach.criticalZeroSlice f ⌊|z.im|⌋₊ ∪ Goldbach.criticalZeroSlice f (- (⌊|z.im|⌋₊:ℝ)) := by
  have hlo := Nat.floor_le (abs_nonneg z.im)
  have hhi := Nat.lt_floor_add_one |z.im|
  rcases le_total 0 z.im with hp | hn
  · left
    refine ⟨h0,h1,?_,hz⟩
    simp only [abs_of_nonneg hp] at *
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · right
    refine ⟨h0,h1,?_,hz⟩
    simp only [abs_of_nonpos hn] at *
    exact abs_le.mpr ⟨by linarith,by linarith⟩

private theorem sum_slice {f : ℂ → ℂ} (Z : Finset ℂ) (t : ℝ)
    (hf : (Goldbach.criticalZeroSlice f t).Finite) :
    (∑ z ∈ Z, (Goldbach.criticalZeroSlice f t).indicator (fun z => (analyticOrderNatAt f z:ℝ)) z) ≤
      ∑ᶠ z : ℂ, (Goldbach.criticalZeroSlice f t).indicator (fun z => (analyticOrderNatAt f z:ℝ)) z := by
  classical
  let S := Goldbach.criticalZeroSlice f t
  let v := S.indicator (fun z => (analyticOrderNatAt f z:ℝ))
  have supp : Function.support v ⊆ (hf.toFinset : Set ℂ) := by
    simpa only [Set.Finite.coe_toFinset] using Set.support_indicator_subset (s := S) (f := fun z => (analyticOrderNatAt f z:ℝ))
  change ∑ z ∈ Z, v z ≤ ∑ᶠ z : ℂ, v z
  rw [finsum_eq_sum_of_support_subset _ supp]
  calc
    _ = ∑ z ∈ Z ∩ hf.toFinset, v z := by
      symm
      apply Finset.sum_subset (Finset.inter_subset_left)
      intro z hz hn
      have hnot : z ∉ hf.toFinset := fun h => hn (Finset.mem_inter.mpr ⟨hz,h⟩)
      exact not_ne_iff.mp (fun h => hnot (supp h))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun z _ _ => Set.indicator_nonneg (fun _ _ => by positivity) _)

/-- Assuming GRH, the zero-counting input of the twisted-kernel theorem follows
from the uniform Jensen slice estimate for regularized Dirichlet L-functions.
The finite set contains all critical-strip zeros below the absolute height cutoff,
and the sum counts each zero with its analytic multiplicity. -/
theorem dirichlet_zero_sum (hGRH : Goldbach.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (N J : ℕ)
      (X a b β : ℝ), 0 < X → X ≤ a → a ≤ b → b ≤ 2*X → 4*|β| * X ≤ J →
      let f := Goldbach.regularizedL χ
      let K := fun γ : ℝ => ∫ x in a..b, ((x^((1/2:ℝ)-1):ℝ):ℂ) *
        Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)
      ∃ Z : Finset ℂ, (∀ z : ℂ, z ∈ Z ↔ 0 < z.re ∧ z.re < 1 ∧ |z.im| < (N:ℝ)+1 ∧ f z=0) ∧
        (∑ z ∈ Z, (analyticOrderNatAt f z:ℝ)*‖K z.im‖) ≤
          Real.sqrt X*(2*C*Real.log (2*(q:ℝ)*(2+N)))*
            (1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (N+1:ℝ))) := by
  classical
  obtain ⟨C,hC,count⟩ := Goldbach.uniform_dirichlet_zero_slice hGRH
  refine ⟨C,hC,?_⟩
  intro q _ χ N J X a b β hX ha hab hb hJ f K
  let W : Set ℂ := {z | 0 < z.re ∧ z.re < 1 ∧ |z.im| < (N:ℝ)+1 ∧ f z=0}
  let S := Goldbach.criticalZeroSlice f
  let m (z : ℂ) := analyticOrderNatAt f z
  let w (z : ℂ) := (m z:ℝ)
  have cover : W ⊆ ⋃ j ∈ Finset.range (N+1), (S (j:ℝ) ∪ S (-(j:ℝ))) := by
    intro z hz
    have hj : ⌊|z.im|⌋₊ ∈ Finset.range (N+1) := Finset.mem_range.mpr
      ((Nat.floor_lt (abs_nonneg _)).mpr (by simpa using hz.2.2.1))
    exact Set.mem_iUnion.mpr ⟨_,Set.mem_iUnion.mpr ⟨hj,bin_cover hz.1 hz.2.1 hz.2.2.2⟩⟩
  have hfin : W.Finite := ((Finset.range (N+1)).finite_toSet.biUnion
    (fun j _ => ((count q χ (j:ℝ)).1.union (count q χ (-(j:ℝ))).1))).subset cover
  let Z := hfin.toFinset
  have mem (z : ℂ) : z ∈ Z ↔ z ∈ W := hfin.mem_toFinset
  refine ⟨Z,mem,?_⟩
  obtain ⟨I,g,hg,henum⟩ := enumerate_occurrences Z Complex.im m
  let B := C*Real.log (2*(q:ℝ)*(2+N))
  have qpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq : (1:ℝ) ≤ q := by exact_mod_cast qpos
  have arg : (1:ℝ) ≤ 2*(q:ℝ)*(2+N) := by nlinarith only [hq, Nat.cast_nonneg (α := ℝ) N, mul_nonneg (by positivity : 0 ≤ (q:ℝ)) (Nat.cast_nonneg (α := ℝ) N)]
  have hB : 0 ≤ B := mul_nonneg hC.le (Real.log_nonneg arg)
  have rangeG (i : ℕ) (hi : i ∈ I) : |g i| < (N:ℝ)+1 := by
    obtain ⟨z,hz,he⟩ := hg i hi
    rw [he]
    exact ((mem z).mp hz).2.2.1
  have slice (t : ℝ) (ht : |t| ≤ N) : (∑ z ∈ Z, (S t).indicator w z) ≤ B := by
    apply (sum_slice Z t (count q χ t).1).trans
    apply (count q χ t).2.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have occupancy (j : ℕ) (hj : j ≤ N) :
      (((I.filter (fun i => ⌊|g i|⌋₊ = j)).card:ℕ):ℝ) ≤ 2*B := by
    let F (t : ℝ) : ℝ := if ⌊|t|⌋₊ = j then 1 else 0
    have eqn := henum F
    have hc : (∑ i ∈ I, F (g i)) = ((I.filter (fun i => ⌊|g i|⌋₊ = j)).card:ℝ) := by
      simp [F]
    rw [← hc,eqn]
    calc
      _ ≤ ∑ z ∈ Z, ((S (j:ℝ)).indicator w z + (S (-(j:ℝ))).indicator w z) := by
        apply Finset.sum_le_sum
        intro z hz
        have wz : 0 ≤ w z := Nat.cast_nonneg _
        have hplus := Set.indicator_nonneg (s := S (j:ℝ)) (f := w) (fun _ _ => Nat.cast_nonneg _) z
        have hminus := Set.indicator_nonneg (s := S (-(j:ℝ))) (f := w) (fun _ _ => Nat.cast_nonneg _) z
        by_cases h : ⌊|z.im|⌋₊ = j
        · simp only [F,h,ite_true,mul_one]
          have hw := (mem z).mp hz
          have hc' := bin_cover hw.1 hw.2.1 hw.2.2.2
          rw [h] at hc'
          rcases hc' with hp | hn
          · rw [Set.indicator_of_mem hp]
            exact le_add_of_nonneg_right hminus
          · rw [Set.indicator_of_mem hn]
            exact le_add_of_nonneg_left hplus
        · simp only [F,h,ite_false,mul_zero]
          exact add_nonneg hplus hminus
      _ ≤ _ := by
        rw [Finset.sum_add_distrib]
        have hj' : (j:ℝ) ≤ N := by exact_mod_cast hj
        have hp := slice j (by simpa only [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) j)] using hj')
        have hn := slice (-(j:ℝ)) (by simpa only [abs_neg,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) j)] using hj')
        linarith only [hp,hn]
  have bound := (PEqualNP.Outside.L_goldbach_zero_additive_twist_dyadic X a b (1/2) β hX ha hab hb
    (by norm_num) (by norm_num)).2 I g J N (2*B) (by positivity) hJ rangeG occupancy
  have eqn := henum (fun t => ‖K t‖)
  change (∑ i ∈ I, ‖K (g i)‖) ≤ _ at bound
  rw [eqn] at bound
  simpa only [← Real.sqrt_eq_rpow, B, mul_assoc] using bound

/-- Glue dyadic bounds on [v/2,v] into a bound for the full interval. The geometric
series for the square-root scale costs a factor of at most three. -/
private theorem dyadic_to_prefix {α : Type*} (Z : Finset α) (w : α → ℝ) (u : α → ℝ → ℂ)
    (Y D : ℝ) (hY : 1 ≤ Y) (hD : 0 ≤ D) (hw : ∀ z, 0 ≤ w z)
    (hc : ∀ z, ContinuousOn (u z) (Ici 1))
    (hd : ∀ X v : ℝ, 1 ≤ X → X ≤ v → v ≤ 2*X → v ≤ Y →
      (∑ z ∈ Z, w z * ‖∫ x in X..v, u z x‖) ≤ Real.sqrt X*D) :
    (∑ z ∈ Z, w z * ‖∫ x in (1:ℝ)..Y, u z x‖) ≤ 3*Real.sqrt Y*D := by
  have stepBound (n : ℕ) (v : ℝ) (hv : 1 ≤ v) (hvY : v ≤ Y) (hp : v ≤ 2^n) :
      (∑ z ∈ Z, w z * ‖∫ x in (1:ℝ)..v, u z x‖) ≤ 3*Real.sqrt v*D := by
    induction n generalizing v with
    | zero =>
      have h : v = 1 := le_antisymm (by simpa using hp) hv
      simp [h,hD]
    | succ n ih =>
      by_cases small : v ≤ 2
      · apply (hd 1 v le_rfl hv (by linarith) hvY).trans
        apply mul_le_mul_of_nonneg_right _ hD
        have hs := Real.sqrt_le_sqrt hv
        rw [Real.sqrt_one] at *
        linarith
      · have half : 1 ≤ v/2 := by linarith
        have hvpos : 0 ≤ v := by linarith
        have hmv : v/2 ≤ v := by linarith
        have hleft := ih (v/2) half (hmv.trans hvY)
          (by rw [pow_succ] at hp; linarith)
        have hright := hd (v/2) v half hmv (by linarith) hvY
        calc
          _ ≤ ∑ z ∈ Z, (w z*‖∫ x in (1:ℝ)..(v/2), u z x‖ +
              w z*‖∫ x in (v/2)..v, u z x‖) := by
            apply Finset.sum_le_sum
            intro z _
            have hint {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
                IntervalIntegrable (u z) volume a b :=
              ((hc z).mono (fun x (hx : x ∈ Icc a b) => ha.trans hx.1)).intervalIntegrable_of_Icc hab
            have he := intervalIntegral.integral_add_adjacent_intervals
              (hint (by rfl) half) (hint half hmv)
            rw [← he, ← mul_add]
            exact mul_le_mul_of_nonneg_left (norm_add_le ..) (hw z)
          _ ≤ (3*Real.sqrt (v/2) + Real.sqrt (v/2))*D := by
            rw [Finset.sum_add_distrib, add_mul]
            exact add_le_add hleft hright
          _ ≤ _ := by
            apply mul_le_mul_of_nonneg_right _ hD
            apply (sq_le_sq₀ (by positivity) (by positivity)).mp
            nlinarith only [Real.sq_sqrt (show 0 ≤ v/2 by positivity),Real.sq_sqrt hvpos,hvpos]
  obtain ⟨n,_,hn⟩ := exists_nat_pow_near hY (by norm_num : (1:ℝ) < 2)
  exact stepBound (n+1) Y hY le_rfl hn.le

end TwistedZeroApplication

open TwistedZeroApplication

/-- A single truncated Dirichlet zero sum across the entire interval [1,Y].
The exponent in each integral is the real part of that zero. The constant is
uniform in the character, conductor parameter, truncation height and twist. -/
theorem TwistedZeroApplication.full_interval_bound (hGRH : Goldbach.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (N : ℕ) (Y β : ℝ), 1 ≤ Y →
      let f := Goldbach.regularizedL χ
      let J := ⌈4*|β| * Y⌉₊
      ∃ Z : Finset ℂ, (∀ z : ℂ, z ∈ Z ↔ 0 < z.re ∧ z.re < 1 ∧ |z.im| < (N:ℝ)+1 ∧ f z=0) ∧
        (∑ z ∈ Z, (analyticOrderNatAt f z:ℝ)*
          ‖∫ x in (1:ℝ)..Y, ((x^(z.re-1):ℝ):ℂ)*
            Complex.exp (((β*x+z.im*Real.log x:ℝ):ℂ)*Complex.I)‖) ≤
          C*Real.sqrt Y*Real.log (2*(q:ℝ)*(2+N))*
            (1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (N+1:ℝ))) := by
  classical
  obtain ⟨C,hC,dyadic⟩ := dirichlet_zero_sum hGRH
  refine ⟨6*C,by positivity,?_⟩
  intro q _ χ N Y β hY f J
  let u (z : ℂ) (x : ℝ) : ℂ :=
    ((x^(z.re-1):ℝ):ℂ)*Complex.exp (((β*x+z.im*Real.log x:ℝ):ℂ)*Complex.I)
  let D := (2*C*Real.log (2*(q:ℝ)*(2+N)))*
    (1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (N+1:ℝ)))
  have hcut {X : ℝ} (h : X ≤ Y) : 4*|β| * X ≤ J :=
    (mul_le_mul_of_nonneg_left h (by positivity)).trans (Nat.le_ceil _)
  obtain ⟨Z,hZ,_⟩ := dyadic q χ N J 1 1 1 β (by norm_num) le_rfl le_rfl (by norm_num) (hcut hY)
  refine ⟨Z,hZ,?_⟩
  have q1 : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hl : 0 ≤ Real.log (2*(q:ℝ)*(2+N)) := by
    apply Real.log_nonneg
    nlinarith only [q1, mul_nonneg (Nat.cast_nonneg (α := ℝ) q) (Nat.cast_nonneg (α := ℝ) N)]
  have hn : 0 ≤ Real.log (N+1:ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have posD : 0 ≤ D := by dsimp [D]; positivity
  have cont (z : ℂ) : ContinuousOn (u z) (Ici 1) := by
    have hpos {x : ℝ} (hx : x ∈ Ici (1:ℝ)) : 0 < x := zero_lt_one.trans_le hx
    have cp : ContinuousOn (fun x : ℝ => x^(z.re-1)) (Ici 1) :=
      continuousOn_id.rpow_const (fun _ hx => Or.inl (hpos hx).ne')
    have cl : ContinuousOn Real.log (Ici (1:ℝ)) := Real.continuousOn_log.mono (fun x hx => (hpos hx).ne')
    unfold u
    exact (Complex.continuous_ofReal.comp_continuousOn cp).mul
      (Complex.continuous_exp.comp_continuousOn
        ((Complex.continuous_ofReal.comp_continuousOn
          ((continuous_const.mul continuous_id).continuousOn.add (cl.const_mul _))).mul continuousOn_const))
  have bound := dyadic_to_prefix Z (fun z => (analyticOrderNatAt f z:ℝ)) u Y D hY posD
    (fun _ => Nat.cast_nonneg _) cont (by
      intro X v hX hxv hv2 hvY
      obtain ⟨Z',hZ',hb⟩ := dyadic q χ N J X X v β (zero_lt_one.trans_le hX) le_rfl hxv hv2
        (hcut (hxv.trans hvY))
      have same : Z' = Z := Finset.ext (fun z => (hZ' z).trans (hZ z).symm)
      subst Z'
      calc
        _ = ∑ z ∈ Z, (analyticOrderNatAt f z:ℝ)*
            ‖∫ x in X..v, ((x^((1/2:ℝ)-1):ℝ):ℂ)*
              Complex.exp (((β*x+z.im*Real.log x:ℝ):ℂ)*Complex.I)‖ := by
          apply Finset.sum_congr rfl
          intro z hz
          have hm := (hZ z).mp hz
          have line := Goldbach.regularizedL_zero_line χ hGRH hm.1 hm.2.2.2
          simp only [u,line]
        _ ≤ _ := by simpa only [D,mul_assoc] using hb)
  change (∑ z ∈ Z, (analyticOrderNatAt f z:ℝ)*‖∫ x in (1:ℝ)..Y, u z x‖) ≤ _
  apply bound.trans_eq
  dsimp [D]
  ring
end


section
open Set MeasureTheory

namespace TwistedZeroApplication

noncomputable def wave (β x : ℝ) : ℂ := Complex.exp (((β*x:ℝ):ℂ)*Complex.I)

private theorem wave_deriv (β x : ℝ) :
    HasDerivAt (wave β) (wave β x*((β:ℂ)*Complex.I)) x := by
  have d := ((((hasDerivAt_id (x:ℂ)).const_mul (β:ℂ)).mul_const Complex.I).cexp).comp_ofReal
  change HasDerivAt (fun y : ℝ => Complex.exp (((β*y:ℝ):ℂ)*Complex.I)) _ x
  simpa [wave, mul_assoc] using d

private theorem wave_norm (β x : ℝ) : ‖wave β x‖ = 1 := by simp [wave,Complex.norm_exp]

/-- Abel transfer from an untwisted summatory model to its additively twisted
derivative. Both endpoint discrepancies and the integrated remainder are retained. -/
private theorem twist_discrepancy (c : ℕ → ℂ) (B V : ℝ → ℂ) (Y β E : ℝ) (hY : 1 ≤ Y)
    (hBV : ∀ x ∈ Icc 1 Y, HasDerivAt B (V x) x) (hV : ContinuousOn V (Icc 1 Y))
    (hE : ∀ x ∈ Icc (1:ℝ) Y, ‖(∑ k ∈ Finset.Icc 0 ⌊x⌋₊, c k)-B x‖ ≤ E) :
    ‖(∑ k ∈ Finset.Ioc 1 ⌊Y⌋₊, wave β k * c k) - ∫ x in (1:ℝ)..Y, wave β x*V x‖ ≤
      E*(2+|β| * (Y-1)) := by
  let A (x : ℝ) := ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, c k
  let F := wave β
  let d (x : ℝ) := F x*((β:ℂ)*Complex.I)
  have hd (x : ℝ) : HasDerivAt F (d x) x := wave_deriv β x
  have cF : Continuous F := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have cd : Continuous d := cF.mul continuous_const
  have cb : ContinuousOn B (Icc 1 Y) := fun x hx => (hBV x hx).continuousAt.continuousWithinAt
  have hi : IntegrableOn d (Icc 1 Y) := cd.continuousOn.integrableOn_Icc
  have hder : deriv F = d := funext (fun x => (hd x).deriv)
  have ab := sum_mul_eq_sub_sub_integral_mul (f := F) c (a := 1) (by norm_num) hY
    (fun t _ => (hd t).differentiableAt) (hder ▸ hi)
  rw [← intervalIntegral.integral_of_le hY, hder] at ab
  change (∑ k ∈ Finset.Ioc ⌊(1:ℝ)⌋₊ ⌊Y⌋₊, F k*c k) = F Y*A Y-F 1*A 1-∫ x in (1:ℝ)..Y, d x*A x at ab
  rw [Nat.floor_one] at ab
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := F) (v := B) (a := 1) (b := Y) cF.continuousOn ((uIcc_of_le hY).symm ▸ cb)
    (fun t _ => hd t) (fun t ht => hBV t (by simpa only [Set.mem_Icc,min_eq_left hY,max_eq_right hY] using (show min 1 Y ≤ t ∧ t ≤ max 1 Y from ⟨ht.1.le,ht.2.le⟩)))
    (cd.intervalIntegrable 1 Y) (hV.intervalIntegrable_of_Icc hY)
  have hda : IntervalIntegrable (fun x => d x*A x) volume 1 Y :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hY).mpr (integrableOn_mul_sum_Icc c (by norm_num) hi)
  have hdb : IntervalIntegrable (fun x => d x*B x) volume 1 Y := (cd.continuousOn.mul cb).intervalIntegrable_of_Icc (μ := volume) hY
  have eqn : (∑ k ∈ Finset.Ioc 1 ⌊Y⌋₊, F k*c k) - (∫ x in (1:ℝ)..Y, F x*V x) =
      (F Y*(A Y-B Y) - F 1*(A 1-B 1)) - ∫ x in (1:ℝ)..Y, (d x*A x-d x*B x) := by
    rw [ab,ibp,intervalIntegral.integral_sub hda hdb]
    ring
  have endpoint (x : ℝ) (hx : x ∈ Icc 1 Y) : ‖F x*(A x-B x)‖ ≤ E := by
    simpa only [F,norm_mul,wave_norm,one_mul] using hE x hx
  have ib := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := Y) (C := |β| * E)
    (f := fun x => d x*A x-d x*B x) (fun x hx => by
      rw [uIoc_of_le hY] at hx
      rw [← mul_sub,norm_mul,show ‖d x‖ = |β| by simp [d,F,wave_norm,Real.norm_eq_abs]]
      exact mul_le_mul_of_nonneg_left (hE x ⟨hx.1.le,hx.2⟩) (abs_nonneg β))
  rw [abs_of_nonneg (sub_nonneg.mpr hY)] at ib
  change ‖(∑ k ∈ Finset.Ioc 1 ⌊Y⌋₊, F k*c k) - (∫ x in (1:ℝ)..Y, F x*V x)‖ ≤ _
  rw [eqn]
  apply (norm_sub_le ..).trans
  have he := norm_sub_le (F Y*(A Y-B Y)) (F 1*(A 1-B 1))
  linarith only [he,endpoint Y (right_mem_Icc.mpr hY),endpoint 1 (left_mem_Icc.mpr hY),ib]

/-- Separate the real amplitude from the phase of a zero contribution on a
positive real interval. -/
private theorem wave_cpow {x : ℝ} (hx : 0 < x) (β : ℝ) (z : ℂ) :
    wave β x*(x:ℂ)^(z-1) = ((x^(z.re-1):ℝ):ℂ)*
      Complex.exp (((β*x+z.im*Real.log x:ℝ):ℂ)*Complex.I) := by
  rw [wave,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le,Real.rpow_def_of_pos hx,Complex.ofReal_exp,
    ← Complex.exp_add,← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp
  ring

/-- Given a uniform remainder for the sharp, untwisted summatory function,
bound the twisted sum by its principal integral, the individual twisted zero
integrals, and an explicit remainder. The uniform remainder is an input. -/
theorem sharp_formula_transfer (c : ℕ → ℂ) (d : ℂ) (Z : Finset ℂ) (m : ℂ → ℕ)
    (Y β E : ℝ) (hY : 1 ≤ Y) (hz : ∀ z ∈ Z, z ≠ 0)
    (hE : ∀ x ∈ Icc (1:ℝ) Y, ‖(∑ k ∈ Finset.Icc 0 ⌊x⌋₊, c k) -
      (d*x - ∑ z ∈ Z, (m z:ℂ)*((x:ℂ)^z/z))‖ ≤ E) :
    ‖(∑ k ∈ Finset.Ioc 1 ⌊Y⌋₊, wave β k*c k) - d*(∫ x in (1:ℝ)..Y, wave β x)‖ ≤
      E*(2+|β| * (Y-1)) + ∑ z ∈ Z, (m z:ℝ)*
        ‖∫ x in (1:ℝ)..Y, ((x^(z.re-1):ℝ):ℂ)*
          Complex.exp (((β*x+z.im*Real.log x:ℝ):ℂ)*Complex.I)‖ := by
  classical
  let B (x : ℝ) := d*x - ∑ z ∈ Z, (m z:ℂ)*((x:ℂ)^z/z)
  let V (x : ℝ) := d - ∑ z ∈ Z, (m z:ℂ)*(x:ℂ)^(z-1)
  have pos {x : ℝ} (hx : x ∈ Icc 1 Y) : 0 < x := zero_lt_one.trans_le hx.1
  have deriv (x : ℝ) (hx : x ∈ Icc 1 Y) : HasDerivAt B (V x) x := by
    have hz' (z : ℂ) (h : z ∈ Z) :
        HasDerivAt (fun t : ℝ => (m z:ℂ)*((t:ℂ)^z/z)) ((m z:ℂ)*(x:ℂ)^(z-1)) x := by
      have e := (hasDerivAt_ofReal_cpow_const (pos hx).ne' (hz z h)).div_const z
      simpa only [mul_div_cancel_left₀ _ (hz z h)] using e.const_mul (m z:ℂ)
    have hd : HasDerivAt (fun t : ℝ => d*(t:ℂ)) d x := by
      simpa using ((hasDerivAt_id (x:ℂ)).const_mul d).comp_ofReal
    exact hd.sub (HasDerivAt.fun_sum hz')
  have cp (z : ℂ) : ContinuousOn (fun x : ℝ => (x:ℂ)^(z-1)) (Icc 1 Y) := by
    intro x hx
    exact (differentiableAt_id.ofReal_cpow_const (z-1) (pos hx).ne').continuousAt.continuousWithinAt
  have cv : ContinuousOn V (Icc 1 Y) :=
    continuousOn_const.sub (continuousOn_finsetSum _ fun z _ => (cp z).const_mul _)
  have ab := twist_discrepancy c B V Y β E hY deriv cv hE
  let K (z : ℂ) := ∫ x in (1:ℝ)..Y, ((x^(z.re-1):ℝ):ℂ)*
    Complex.exp (((β*x+z.im*Real.log x:ℝ):ℂ)*Complex.I)
  have cw : Continuous (wave β) := continuous_iff_continuousAt.mpr fun x => (wave_deriv β x).continuousAt
  have ki (z : ℂ) : IntervalIntegrable (fun x => wave β x*(x:ℂ)^(z-1)) volume 1 Y :=
    (cw.continuousOn.mul (cp z)).intervalIntegrable_of_Icc hY
  have exchange : (∫ x in (1:ℝ)..Y, wave β x*V x) =
      d*(∫ x in (1:ℝ)..Y, wave β x) - ∑ z ∈ Z, (m z:ℂ)*K z := by
    have ex (x : ℝ) : wave β x*V x =
        d*wave β x - ∑ z ∈ Z, (m z:ℂ)*(wave β x*(x:ℂ)^(z-1)) := by
      simp only [V,mul_sub,Finset.mul_sum]
      rw [mul_comm (wave β x) d]
      congr 1
      apply Finset.sum_congr rfl
      intro z _
      ring
    simp_rw [ex]
    rw [intervalIntegral.integral_sub ((cw.intervalIntegrable _ _).const_mul d)
      (show IntervalIntegrable (fun x => ∑ z ∈ Z, (m z:ℂ)*(wave β x*(x:ℂ)^(z-1))) volume 1 Y from
        (continuousOn_finsetSum Z (fun z _ => (cw.continuousOn.mul (cp z)).const_mul _)).intervalIntegrable_of_Icc hY),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_finsetSum (fun z _ => (ki z).const_mul _)]
    congr 1
    apply Finset.sum_congr rfl
    intro z _
    rw [intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hY] at hx
    exact wave_cpow (pos hx) β z
  rw [exchange] at ab
  let W := (∑ k ∈ Finset.Ioc 1 ⌊Y⌋₊, wave β k*c k) - d*(∫ x in (1:ℝ)..Y, wave β x)
  let err := ∑ z ∈ Z, (m z:ℂ)*K z
  have he : ‖err‖ ≤ ∑ z ∈ Z, (m z:ℝ)*‖K z‖ := by
    apply (norm_sum_le ..).trans
    exact Finset.sum_le_sum fun z _ => by simp
  have hb : ‖W+err‖ ≤ E*(2+|β| * (Y-1)) := by simpa only [W,err,sub_sub_eq_add_sub,sub_add_eq_add_sub,add_comm,add_left_comm,add_assoc,sub_eq_add_neg,neg_add_rev,neg_neg] using ab
  change ‖W‖ ≤ _ + ∑ z ∈ Z, (m z:ℝ)*‖K z‖
  calc
    _ = ‖(W+err)-err‖ := by rw [add_sub_cancel_right]
    _ ≤ _ := (norm_sub_le ..).trans (add_le_add hb he)

end TwistedZeroApplication

open TwistedZeroApplication

/-- Transfer a sharp untwisted explicit-formula remainder for the character
Mangoldt sum to an additive twist. GRH supplies the zero-counting input.
The size of the sharp untwisted remainder E remains an explicit assumption. -/
theorem TwistedZeroApplication.transfer_bound :
    Goldbach.GRH → ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (N : ℕ) (Y β : ℝ), 1 ≤ Y →
      let f := Goldbach.regularizedL χ
      let c := fun k : ℕ => χ (k : ZMod q)*(ArithmeticFunction.vonMangoldt k:ℂ)
      let d : ℂ := @ite ℂ (χ=1) (Classical.propDecidable _) 1 0
      let F := fun x : ℝ => Complex.exp (((β*x:ℝ):ℂ)*Complex.I)
      let J := ⌈4*|β| * Y⌉₊
      ∃ Z : Finset ℂ, (∀ z : ℂ, z ∈ Z ↔ 0 < z.re ∧ z.re < 1 ∧ |z.im| < (N:ℝ)+1 ∧ f z=0) ∧
        ∀ E : ℝ, (∀ x ∈ Set.Icc (1:ℝ) Y, ‖(∑ k ∈ Finset.Icc 0 ⌊x⌋₊, c k) -
          (d*x - ∑ z ∈ Z, (analyticOrderNatAt f z:ℂ)*((x:ℂ)^z/z))‖ ≤ E) →
        ‖(∑ k ∈ Finset.Ioc 1 ⌊Y⌋₊, F k*c k) - d*(∫ x in (1:ℝ)..Y, F x)‖ ≤
          E*(2+|β| * (Y-1)) + C*Real.sqrt Y*Real.log (2*(q:ℝ)*(2+N))*
            (1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (N+1:ℝ))) := by
  intro hGRH
  obtain ⟨C,hC,prefixBound⟩ := TwistedZeroApplication.full_interval_bound hGRH
  refine ⟨C,hC,?_⟩
  intro q _ χ N Y β hY f c d F J
  obtain ⟨Z,hZ,hSum⟩ := prefixBound q χ N Y β hY
  refine ⟨Z,hZ,?_⟩
  intro E hE
  have nz (z : ℂ) (hz : z ∈ Z) : z ≠ 0 := by
    have hp := ((hZ z).mp hz).1
    intro h
    simp [h] at hp
  exact (sharp_formula_transfer c d Z (analyticOrderNatAt f) Y β E hY nz hE).trans
    (add_le_add le_rfl hSum)


theorem PEqualNP.Outside.L_goldbach_grh_twisted_mangoldt_transfer : (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1/2) → ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (N : ℕ) (Y β : ℝ), 1 ≤ Y →
      let f := @ite (ℂ → ℂ) (χ = 1) (Classical.propDecidable _) (DirichletCharacter.LFunctionTrivChar₁ q) (DirichletCharacter.LFunction χ)
      let c := fun k : ℕ => χ (k : ZMod q)*(ArithmeticFunction.vonMangoldt k:ℂ)
      let d : ℂ := @ite ℂ (χ=1) (Classical.propDecidable _) 1 0
      let F := fun x : ℝ => Complex.exp (((β*x:ℝ):ℂ)*Complex.I)
      let J := ⌈4*|β| * Y⌉₊
      ∃ Z : Finset ℂ, (∀ z : ℂ, z ∈ Z ↔ 0 < z.re ∧ z.re < 1 ∧ |z.im| < (N:ℝ)+1 ∧ f z=0) ∧
        ∀ E : ℝ, (∀ x ∈ Set.Icc (1:ℝ) Y, ‖(∑ k ∈ Finset.Icc 0 ⌊x⌋₊, c k) -
          (d*x - ∑ z ∈ Z, (analyticOrderNatAt f z:ℂ)*((x:ℂ)^z/z))‖ ≤ E) →
        ‖(∑ k ∈ Finset.Ioc 1 ⌊Y⌋₊, F k*c k) - d*(∫ x in (1:ℝ)..Y, F x)‖ ≤
          E*(2+|β| * (Y-1)) + C*Real.sqrt Y*Real.log (2*(q:ℝ)*(2+N))*
            (1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (N+1:ℝ))) := by
  classical
  intro hGRH
  obtain ⟨C, hC, bound⟩ := TwistedZeroApplication.transfer_bound hGRH
  refine ⟨C, hC, ?_⟩
  intro q inst χ
  by_cases hχ : χ = 1
  · simpa only [Goldbach.regularizedL, ite_eq_left hχ] using bound q χ
  · simpa only [Goldbach.regularizedL, ite_eq_right hχ] using bound q χ
end

