import Mathlib

/-!
Finite explicit formula for an additively twisted Dirichlet character sum.
No hypothesis on the real parts of the zeros is used. The formula keeps the
signed multiplicities of the enclosed zeros and the truncated left edge.
The right tail and both horizontal integrals have uniform quantitative bounds.

The analytic growth, Jensen disk, logarithmic derivative and rectangle
residue estimates are adapted from DNZJSJ, goldbach-proofs PR #2486,
commit f3613cf846dfb3e7fe7d04fe6ce51c6ee25e7d4f (Apache-2.0).
The Mellin window and inversion use the same integer endpoints as the
conditional three-quarters proof. The right-half count, shared edge
selection and two-sided truncation estimate below do not use Dirichlet GRH.
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

/-- A unit interval contains a height separated by `1 / (2 * (1 + S.card))`
from all ordinates in a finite family. -/
theorem exists_goodHeight {α : Type*} (S : Finset α) (ordinate : α → ℝ) (T : ℝ) :
    ∃ u ∈ Set.Icc T (T + 1),
      ∀ a ∈ S, (1 : ℝ) / (2 * (1 + (S.card : ℝ))) ≤ |u - ordinate a| := by
  classical
  let den : ℝ := 1 + (S.card : ℝ)
  let gap : ℝ := 1 / (2 * den)
  let grid (j : Fin (S.card + 1)) : ℝ := T + (j.val : ℝ) / den
  have hDen : 0 < den := by dsimp [den]; positivity
  have hGrid (j : Fin (S.card + 1)) : grid j ∈ Set.Icc T (T + 1) := by
    have hj : (j.val : ℝ) ≤ S.card := by exact_mod_cast Nat.le_of_lt_succ j.isLt
    have hLower : 0 ≤ (j.val : ℝ) / den := div_nonneg (by positivity) hDen.le
    have hUpper : (j.val : ℝ) / den ≤ 1 := by
      apply (div_le_one hDen).mpr
      dsimp [den]
      linarith only [hj]
    exact ⟨by dsimp [grid]; linarith only [hLower], add_le_add le_rfl hUpper⟩
  have hGridGap {j k : Fin (S.card + 1)} (hjk : j ≠ k) :
      gap + gap ≤ |grid j - grid k| := by
    have hNat : j.val ≠ k.val := fun heq ↦ hjk (Fin.ext heq)
    have hInt : (j.val : ℤ) ≠ (k.val : ℤ) := by exact_mod_cast hNat
    have hAbsInt : (1 : ℤ) ≤ |(j.val : ℤ) - (k.val : ℤ)| :=
      Int.one_le_abs (sub_ne_zero.mpr hInt)
    have hAbs : (1 : ℝ) ≤ |(j.val : ℝ) - (k.val : ℝ)| := by exact_mod_cast hAbsInt
    have hGridSub : grid j - grid k = ((j.val : ℝ) - (k.val : ℝ)) / den := by
      dsimp [grid]
      ring
    calc
      gap + gap = 1 / den := by
        dsimp [gap]
        field_simp [hDen.ne']
        norm_num
      _ ≤ |(j.val : ℝ) - (k.val : ℝ)| / den := div_le_div_of_nonneg_right hAbs hDen.le
      _ = |grid j - grid k| := by rw [hGridSub, abs_div, abs_of_pos hDen]
  by_contra hNoGood
  have hBad (j : Fin (S.card + 1)) : ∃ a : S, |grid j - ordinate a| < gap := by
    by_contra hNoBad
    apply hNoGood
    refine ⟨grid j, hGrid j, ?_⟩
    intro a ha
    exact le_of_not_gt (fun h ↦ hNoBad ⟨⟨a, ha⟩, h⟩)
  let badAt (j : Fin (S.card + 1)) : S := (hBad j).choose
  have hBadAt (j : Fin (S.card + 1)) : |grid j - ordinate (badAt j)| < gap :=
    (hBad j).choose_spec
  have hInjective : Function.Injective badAt := by
    intro j k hEqual
    by_contra hDifferent
    have hPair : |grid j - ordinate (badAt j)| + |grid k - ordinate (badAt j)| < gap + gap :=
      (add_lt_add (hBadAt j) (by simpa only [hEqual] using hBadAt k))
    have hTri : |grid j - grid k| ≤
        |grid j - ordinate (badAt j)| + |grid k - ordinate (badAt j)| := by
      simpa only [abs_sub_comm (ordinate (badAt j)) (grid k)] using
        abs_sub_le (grid j) (ordinate (badAt j)) (grid k)
    exact not_lt_of_ge (hGridGap hDifferent) (hTri.trans_lt hPair)
  have hCard : S.card + 1 ≤ S.card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_le_of_injective badAt hInjective
  omega
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

/-- The anchor gives finite order of the regularized L-function at every complex point. -/
theorem regularizedL_analyticOrder_ne_top {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (z : ℂ) : analyticOrderAt (regularizedL χ) z ≠ ⊤ := by
  let c : ℂ := ⟨2, 0⟩
  have hC : regularizedL χ c ≠ 0 := norm_pos_iff.mp
    ((by norm_num : (0 : ℝ) < 1 / 4).trans_le (norm_regularizedL_anchor χ 0))
  have hOrderC : analyticOrderAt (regularizedL χ) c ≠ ⊤ := by
    rw [((analytic_regularizedL χ) c (mem_univ c)).analyticOrderAt_eq_zero.mpr hC]
    exact ENat.zero_ne_top
  exact (analytic_regularizedL χ).analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ c) (mem_univ z) hOrderC

theorem regularizedL_analyticOrderNatAt_pos_iff {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (z : ℂ) :
    0 < analyticOrderNatAt (regularizedL χ) z ↔ regularizedL χ z = 0 := by
  constructor
  · intro h
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero h.ne'
  · intro h
    apply Nat.pos_of_ne_zero
    intro hzero
    apply ((analytic_regularizedL χ) z (mem_univ z)).analyticOrderAt_ne_zero.mpr h
    rw [← Nat.cast_analyticOrderNatAt (regularizedL_analyticOrder_ne_top χ z), hzero, Nat.cast_zero]

theorem regularizedL_divisor_apply {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {U : Set ℂ} {z : ℂ} (hz : z ∈ U) :
    divisor (regularizedL χ) U z = (analyticOrderNatAt (regularizedL χ) z : ℤ) := by
  rw [((analytic_regularizedL χ).mono (subset_univ U)).divisor_apply hz,
    ← Nat.cast_analyticOrderNatAt (regularizedL_analyticOrder_ne_top χ z),
    ENat.map_natCast, WithTop.untop₀_coe]
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
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter MeromorphicOn
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

/-- Every zero on a compact rectangle has finite multiplicity and the set is finite.
The rectangle may cross the critical line. -/
theorem finite_box_zeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a b c d : ℝ) :
    {z : ℂ | z ∈ Icc a b ×ℂ Icc c d ∧ regularizedL χ z = 0}.Finite := by
  let U := Icc a b ×ℂ Icc c d
  have hcompact : IsCompact U := isCompact_Icc.reProdIm isCompact_Icc
  apply ((divisor (regularizedL χ) U).finiteSupport hcompact).subset
  intro z hz
  change divisor (regularizedL χ) U z ≠ 0
  rw [regularizedL_divisor_apply χ hz.1]
  exact_mod_cast ((regularizedL_analyticOrderNatAt_pos_iff χ z).mpr hz.2).ne'

noncomputable def boxZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b c d : ℝ) : Finset ℂ := (finite_box_zeros χ a b c d).toFinset

theorem mem_boxZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a b c d : ℝ) (z : ℂ) :
    z ∈ boxZeros χ a b c d ↔ z ∈ Icc a b ×ℂ Icc c d ∧ regularizedL χ z = 0 :=
  (finite_box_zeros χ a b c d).mem_toFinset

theorem regularizedL_ne_zero_right {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {z : ℂ} (hz : 1 < z.re) : regularizedL χ z ≠ 0 := by
  have hz1 : z ≠ 1 := by intro h; simp [h] at hz
  have hn := LFunction_ne_zero_of_one_le_re χ (Or.inr hz1) hz.le
  by_cases hχ : χ = 1
  · subst χ
    simpa only [regularizedL, ite_true, LFunctionTrivChar₁, Function.update_of_ne hz1] using
      mul_ne_zero (sub_ne_zero.mpr hz1) hn
  · simpa only [regularizedL, ite_eq_right hχ] using hn

/-- The same vertical side and symmetric truncation heights work for every
character of a fixed conductor parameter. The choices can be made in
arbitrarily short prescribed open intervals. -/
theorem common_box_sides (q : ℕ) [NeZero q] {u v B D : ℝ}
    (huv : u < v) (hB : 0 < B) (hBD : B < D) :
    ∃ σ ∈ Ioo u v, ∃ T ∈ Ioo B D, ∀ χ : DirichletCharacter ℂ q,
      ∀ z ∈ boxZeros χ σ 2 (-T) T, σ < z.re ∧ z.re < 2 ∧ -T < z.im ∧ z.im < T := by
  classical
  let allZeros : Finset ℂ := Finset.univ.biUnion fun χ : DirichletCharacter ℂ q => boxZeros χ u 2 (-D) D
  obtain ⟨σ,hσ,avoidR⟩ := (Ioo_infinite huv).exists_notMem_finset (allZeros.image Complex.re)
  obtain ⟨T,hT,avoidI⟩ := (Ioo_infinite hBD).exists_notMem_finset (allZeros.image fun z => |z.im|)
  refine ⟨σ,hσ,T,hT,?_⟩
  intro χ z hz
  have hz' := (mem_boxZeros χ σ 2 (-T) T z).mp hz
  have hb := mem_reProdIm.mp hz'.1
  have hzall : z ∈ allZeros := by
    refine Finset.mem_biUnion.mpr ⟨χ,Finset.mem_univ _,(mem_boxZeros χ u 2 (-D) D z).mpr ⟨?_,hz'.2⟩⟩
    exact mem_reProdIm.mpr ⟨⟨hσ.1.le.trans hb.1.1,hb.1.2⟩,⟨(neg_le_neg hT.2.le).trans hb.2.1,hb.2.2.trans hT.2.le⟩⟩
  have hT0 : 0 < T := hB.trans hT.1
  have hleft : σ ≠ z.re := fun h => avoidR (Finset.mem_image.mpr ⟨z,hzall,h.symm⟩)
  have habs : |z.im| ≠ T := fun h => avoidI (Finset.mem_image.mpr ⟨z,hzall,h⟩)
  refine ⟨lt_of_le_of_ne hb.1.1 hleft,lt_of_le_of_ne hb.1.2 ?_,lt_of_le_of_ne hb.2.1 ?_,lt_of_le_of_ne hb.2.2 ?_⟩
  · intro h
    exact regularizedL_ne_zero_right χ (by rw [h]; norm_num) hz'.2
  · intro h
    apply habs
    rw [← h,abs_neg,abs_of_pos hT0]
  · intro h
    exact habs (by rw [h,abs_of_pos hT0])

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter GoldbachSmoothing
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

noncomputable def integrand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a b β : ℝ) (z : ℂ) : ℂ :=
  contourLog χ z * transform a b β z

/-- Signed, multiplicity-weighted residues of the additively twisted Mellin window. -/
noncomputable def zeroContribution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b β σ T : ℝ) : ℂ :=
  ∑ z ∈ boxZeros χ σ 2 (-T) T, (analyticOrderNatAt (regularizedL χ) z : ℂ) * transform a b β z

noncomputable def contourRemainder {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b β σ T : ℝ) : ℂ :=
  let F := integrand χ a b β
  (1/(2*Real.pi)) • ((∫ t : ℝ in (-T)..T, F (line σ t)) +
    I * ((∫ x : ℝ in σ..2, F (line x (-T))) - ∫ x : ℝ in σ..2, F (line x T)))

noncomputable def truncationRemainder {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b β T : ℝ) : ℂ :=
  let F := integrand χ a b β
  (1/(2*Real.pi)) • ((∫ t : ℝ, F (line 2 t)) - ∫ t : ℝ in (-T)..T, F (line 2 t))

theorem exact_twisted_box {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a b : ℕ} {X β σ T : ℝ} (hX : 1 ≤ X) (ha : X ≤ (a:ℝ)) (hab : (a:ℝ)+1 ≤ b)
    (hb : (b:ℝ)+1 ≤ 2*X) (hβ : |β| ≤ 1) (hs : σ < 1) (hT : 0 < T)
    (hinterior : ∀ z ∈ boxZeros χ σ 2 (-T) T, σ < z.re ∧ z.re < 2 ∧ -T < z.im ∧ z.im < T) :
    (∑ n ∈ Finset.Ioc a b, twistedCoefficient χ n * phase β n) =
      principalFlag χ * transform a b β 1 - zeroContribution χ a b β σ T +
        contourRemainder χ a b β σ T + truncationRemainder χ a b β T := by
  let K := transform a b β
  let S := boxZeros χ σ 2 (-T) T
  let F := integrand χ a b β
  let c : ℝ := 1/(2*Real.pi)
  have hK := analytic_transform (zero_lt_one.trans_le (hX.trans ha)) (b:ℝ) β
  have hr := rectBoundaryIntegral_neg_logDeriv_add_pole_mul (regularizedL χ) K S (principalFlag χ)
    hs (by norm_num : (1:ℝ) < 2) (neg_lt_zero.mpr hT) hT
    ((analytic_regularizedL χ).mono (subset_univ _)) (fun z _ => hK.analyticAt z)
    (fun z hz => by simp only [S,mem_boxZeros,and_iff_right hz]) hinterior
    (fun z _ => regularizedL_analyticOrder_ne_top χ z) (regularizedL_ne_zero_at_one χ)
  have vertical := right_vertical_integral_of_rect hr
  change (∫ y : ℝ in (-T)..T, F (line 2 y)) =
    (∫ y : ℝ in (-T)..T, F (line σ y)) +
      (2*(Real.pi:ℂ))*(principalFlag χ * K 1-zeroContribution χ a b β σ T) +
      I*((∫ x : ℝ in σ..2, F (line x (-T))) - ∫ x : ℝ in σ..2, F (line x T)) at vertical
  have inv := character_sum_eq_vertical χ hX ha hab hb hβ
  have rline (t : ℝ) : -logDeriv (LFunction χ) (2+(t:ℂ)*I) = contourLog χ (line 2 t) := by
    simpa [line] using (contour_right q χ t).symm
  simp_rw [rline] at inv
  change _ = c • ∫ t : ℝ, F (line 2 t) at inv
  have cancel (z : ℂ) : c • ((2*(Real.pi:ℂ))*z) = z := by
    rw [Complex.real_smul]
    simp [c,Complex.ofReal_mul,Real.pi_ne_zero,mul_assoc]
  have scaled := congrArg (fun z : ℂ => c • z) vertical
  simp only [smul_add,cancel] at scaled
  rw [inv]
  change _ = _ + c • (_ + _) + c • (_ - _)
  rw [smul_add,smul_sub,scaled]
  abel

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter GoldbachSmoothing
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

/-- A single absolute convergent series bounds the logarithmic derivatives on
the right edge, for all characters and all imaginary heights. -/
theorem uniform_right_log_bound : ∃ A : ℝ, 0 < A ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ), ‖contourLog χ (line 2 t)‖ ≤ A := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have hsum : Summable fun n => ‖LSeries.term f (2:ℂ) n‖ :=
    summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num))
  let M := ∑' n, ‖LSeries.term f (2:ℂ) n‖
  have hM : 0 ≤ M := tsum_nonneg fun n => norm_nonneg _
  refine ⟨M+1,by positivity,?_⟩
  intro q _ χ t
  rw [contour_right, ← LSeries_twistedCoefficient_eq χ (by simp)]
  have h (n : ℕ) : ‖LSeries.term (twistedCoefficient χ) (line 2 t) n‖ ≤ ‖LSeries.term f (2:ℂ) n‖ := by
    have hs : ‖LSeries.term f (line 2 t) n‖ = ‖LSeries.term f (2:ℂ) n‖ := by simp [LSeries.norm_term_eq]
    rw [← hs]
    apply LSeries.norm_term_le
    change ‖χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)‖ ≤ ‖(ArithmeticFunction.vonMangoldt n:ℂ)‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  have ht := hsum.of_nonneg_of_le (fun _ => norm_nonneg _) h
  exact ((norm_tsum_le_tsum_norm ht).trans (ht.tsum_le_tsum h hsum)).trans (by dsimp [M]; linarith)

/-- Removing both infinite tails of a vertical integral loses at most 2M/T
when the pointwise norm beyond height T is at most M/t². -/
theorem tails_bound {f : ℝ → ℂ} (hi : Integrable f) {T M : ℝ} (hT : 0 < T) (_hM : 0 ≤ M)
    (hb : ∀ t : ℝ, T < |t| → ‖f t‖ ≤ M / t^2) :
    ‖(∫ t : ℝ, f t) - (∫ t : ℝ in (-T)..T, f t)‖ ≤ 2*M/T := by
  have ht : -T ≤ T := by linarith
  have hcut := intervalIntegral.integral_Iic_add_Ioi (b := T) (μ := volume) hi.integrableOn hi.integrableOn
  have hsplit : (∫ t in Iic T, f t) =
      (∫ t in Iic (-T), f t) + ∫ t in Ioc (-T) T, f t := by
    rw [← setIntegral_union (Iic_disjoint_Ioc (le_refl (-T))) measurableSet_Ioc hi.integrableOn hi.integrableOn,
      Iic_union_Ioc_eq_Iic ht]
  have htail (g : ℝ → ℂ) (hg : IntegrableOn g (Ioi T)) (hg' : ∀ t ∈ Ioi T, ‖g t‖ ≤ M/t^2) :
      ‖∫ t in Ioi T, g t‖ ≤ M/T := by
    have hr (t : ℝ) (h : t ∈ Ioi T) : t^(-2:ℝ) = (t^2)⁻¹ := by
      rw [Real.rpow_neg (hT.trans h).le,Real.rpow_two]
    have hm := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hT).const_mul M
    calc
      ‖∫ t in Ioi T, g t‖ ≤ ∫ t in Ioi T, ‖g t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioi T, M*t^(-2:ℝ) := by
        apply setIntegral_mono_on hg.norm hm measurableSet_Ioi
        intro t ht'
        simpa only [hr t ht',div_eq_mul_inv] using hg' t ht'
      _ = M/T := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hT]
        norm_num [Real.rpow_neg hT.le,div_eq_mul_inv]
  have hpos := htail f hi.integrableOn (fun t ht' => hb t (by rwa [abs_of_pos (hT.trans ht')]))
  have hneg := htail (fun t => f (-t)) hi.comp_neg.integrableOn (fun t ht' => by
    simpa only [neg_sq] using hb (-t) (by rwa [abs_neg,abs_of_pos (hT.trans ht')]))
  rw [integral_comp_neg_Ioi] at hneg
  rw [← hcut, hsplit, intervalIntegral.integral_of_le ht]
  have cancel (l m r : ℂ) : l+m+r-m = l+r := by abel
  rw [cancel]
  exact (norm_add_le _ _).trans ((add_le_add hneg hpos).trans_eq (by ring))

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter GoldbachSmoothing
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

theorem truncation_bound : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b : ℕ) (X β T : ℝ), 1 ≤ X → X ≤ (a:ℝ) → (a:ℝ)+1 ≤ b → (b:ℝ)+1 ≤ 2*X →
      |β| ≤ 1 → 0 < T → ‖truncationRemainder χ a b β T‖ ≤ C*X^4/T := by
  obtain ⟨A,hA,logbound⟩ := uniform_right_log_bound
  let c : ℝ := 1/(2*Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c*(2*A*96),by positivity,?_⟩
  intro q _ χ a b X β T hX ha hab hb hβ hT
  let F := integrand χ a b β
  have hr (t : ℝ) : LSeries (twistedCoefficient χ) (line 2 t) = contourLog χ (line 2 t) := by
    rw [contour_right]
    exact LSeries_twistedCoefficient_eq χ (by simp)
  have hAbs : Summable fun n => ‖LSeries.term (twistedCoefficient χ) (2:ℂ) n‖ :=
    summable_norm_iff.mpr (χ.LSeriesSummable_twist_vonMangoldt (by norm_num))
  have hi : Integrable fun t : ℝ => F (line 2 t) := by
    dsimp [F,integrand]
    simp_rw [← hr]
    exact integrable_series_transform (twistedCoefficient χ) (transform a b β) (σ := 2)
      (integrable_transform hX ha hab hb hβ (by norm_num) le_rfl) (by simpa using hAbs)
  have hbnd (t : ℝ) (ht : T < |t|) : ‖F (line 2 t)‖ ≤ (A*96*X^4)/t^2 := by
    have h := norm_transform_tail hX ha hab hb hβ (line 2 t) (by simp) (by simp) (by simpa using hT.trans ht)
    rw [im_line, sq_abs] at h
    change ‖contourLog χ (line 2 t) * _‖ ≤ _
    rw [norm_mul]
    exact (mul_le_mul (logbound q χ t) h (norm_nonneg _) hA.le).trans_eq (by ring)
  have ht := tails_bound hi hT (by positivity : 0 ≤ A*96*X^4) hbnd
  change ‖c • _‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hc]
  exact (mul_le_mul_of_nonneg_left ht hc.le).trans_eq (by ring)

/-- A finite-height explicit formula for every character with a common modulus.
The sides are selected before the character, frequency or dyadic interval.
All zeros in the rectangle occur with their true analytic multiplicities. -/
theorem finite_twisted_explicit_formula :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (u v B D : ℝ), u < v → v < 1 → 0 < B → B < D →
      ∃ σ ∈ Ioo u v, ∃ T ∈ Ioo B D, ∀ (χ : DirichletCharacter ℂ q) (a b : ℕ) (X β : ℝ),
        1 ≤ X → X ≤ (a:ℝ) → (a:ℝ)+1 ≤ b → (b:ℝ)+1 ≤ 2*X → |β| ≤ 1 →
        ‖(∑ n ∈ Finset.Ioc a b, twistedCoefficient χ n * phase β n) -
          (principalFlag χ*transform a b β 1 - zeroContribution χ a b β σ T +
            contourRemainder χ a b β σ T)‖ ≤ C*X^4/T := by
  obtain ⟨C,hC,tail⟩ := truncation_bound
  refine ⟨C,hC,?_⟩
  intro q _ u v B D huv hv hB hBD
  obtain ⟨σ,hσ,T,hT,edges⟩ := common_box_sides q huv hB hBD
  refine ⟨σ,hσ,T,hT,?_⟩
  intro χ a b X β hX ha hab hb hβ
  rw [exact_twisted_box χ hX ha hab hb hβ (hσ.2.trans hv) (hB.trans hT.1) (edges χ),add_sub_cancel_left]
  exact tail q χ a b X β T hX ha hab hb hβ (hB.trans hT.1)

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter MeromorphicOn Metric
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

/-- Every zero to the right of the critical line whose ordinate differs from t
by at most one lies in the same Jensen disk. -/
theorem mem_right_jensen_disk {z : ℂ} {t : ℝ}
    (hl : 1/2 ≤ z.re) (hr : z.re ≤ 2) (hi : |z.im-t| ≤ 1) :
    z ∈ closedBall (⟨2,t⟩:ℂ) (29/16) := by
  rw [mem_closedBall,dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 29/16)).mp
  have hrabs : |z.re-2| ≤ 3/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have h1 := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 3/2)).mpr hrabs
  have h2 := (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr hi
  rw [sq_abs] at h1 h2
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re,Complex.sub_im]
  nlinarith only [h1,h2]

/-- The unit-height bound counts multiplicities throughout the right half of
the critical strip. It requires no hypothesis on the real part of other zeros. -/
theorem unconditional_right_slice_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) (Z : Finset ℂ),
      (∀ z ∈ Z, 1/2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im-t| ≤ 1) →
      (∑ z ∈ Z, (analyticOrderNatAt (regularizedL χ) z:ℝ)) ≤ C*logHeight q t := by
  classical
  obtain ⟨C,hC,jensen⟩ := jensen_diskDivisor_bound (A:=25) (b:=1/4) (by norm_num) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro q _ χ t Z hZ
  let U := closedBall (⟨2,t⟩:ℂ) (29/16)
  let D := divisor (regularizedL χ) U
  have hfin := D.finiteSupport (isCompact_closedBall _ _)
  let W := Z ∪ hfin.toFinset
  have hsup : Function.support D ⊆ (W:Set ℂ) := fun _ hz => Finset.mem_union_right _ (hfin.mem_toFinset.mpr hz)
  have hbound := jensen q (regularizedL χ) t (NeZero.pos q)
    ((analytic_regularizedL χ).mono (subset_univ _))
    (fun s hs => by
      have hg := GoldbachGrhGrowth.norm_regularizedLFunction_le χ hs
      by_cases hχ : χ = 1
      · simpa only [regularizedL,hχ,ite_true] using hg
      · simpa only [regularizedL,hχ,ite_false] using hg) (norm_regularizedL_anchor χ t)
  have hmul (z : ℂ) (hz : z ∈ Z) : (analyticOrderNatAt (regularizedL χ) z : ℤ) = D z :=
    (regularizedL_divisor_apply χ (mem_right_jensen_disk (hZ z hz).1 (hZ z hz).2.1 (hZ z hz).2.2)).symm
  have hD : ∀ z, 0 ≤ D z := ((analytic_regularizedL χ).mono (subset_univ U)).divisor_nonneg
  have hsum : (∑ z ∈ Z,(analyticOrderNatAt (regularizedL χ) z:ℤ)) ≤ ∑ᶠ z, D z := by
    rw [finsum_eq_sum_of_support_subset _ hsup,Finset.sum_congr rfl hmul]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun z _ _ => hD z)
  exact (show (∑ z ∈ Z,(analyticOrderNatAt (regularizedL χ) z:ℝ)) ≤ ((∑ᶠ z, D z : ℤ):ℝ) by exact_mod_cast hsum).trans hbound

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

/-- The number of distinct right-hand zeros in a horizontal band is at most
the Jensen bound for their total multiplicity. -/
theorem right_box_card :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
      ((boxZeros χ (1/2) 2 (t-1) (t+1)).card:ℝ) ≤ C*logHeight q t := by
  obtain ⟨C,hC,count⟩ := unconditional_right_slice_count
  refine ⟨C,hC,?_⟩
  intro q _ χ t
  let Z := boxZeros χ (1/2) 2 (t-1) (t+1)
  have hz (z : ℂ) (h : z ∈ Z) := (mem_boxZeros χ _ _ _ _ z).mp h
  have bounds (z : ℂ) (h : z ∈ Z) : 1/2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im-t| ≤ 1 := by
    have b := mem_reProdIm.mp (hz z h).1
    exact ⟨b.1.1,b.1.2,abs_le.mpr ⟨by linarith [b.2.1],by linarith [b.2.2]⟩⟩
  have one (z : ℂ) (h : z ∈ Z) : (1:ℝ) ≤ analyticOrderNatAt (regularizedL χ) z := by
    exact_mod_cast (regularizedL_analyticOrderNatAt_pos_iff χ z).mpr (hz z h).2
  exact (show (Z.card:ℝ) ≤ ∑ z ∈ Z, (analyticOrderNatAt (regularizedL χ) z:ℝ) by
    simpa using Finset.sum_le_sum one).trans (count q χ t Z bounds)

/-- A height in each unit interval avoids the ordinates of zeros near both the
upper and lower edge. The width of the forbidden neighborhoods is inverse
logarithmic in the modulus and height. -/
theorem good_symmetric_height :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (B : ℝ), 2 ≤ B →
      ∃ T ∈ Icc B (B+1), ∀ z : ℂ, 1/2 ≤ z.re → regularizedL χ z = 0 →
        (C*logHeight q (B+1/2))⁻¹ ≤ abs (T - |z.im|) := by
  obtain ⟨C,hC,count⟩ := right_box_card
  refine ⟨4*(1+2*C),by positivity,?_⟩
  intro q _ χ B hB
  let t := B+1/2
  let P := boxZeros χ (1/2) 2 (t-1) (t+1)
  let N := boxZeros χ (1/2) 2 (-t-1) (-t+1)
  let S := P ∪ N
  let L := logHeight q t
  have hL : 1 ≤ L := logHeight_ge_one q t
  have hLn : logHeight q (-t) = L := by simp [L,logHeight]
  have hs : (S.card:ℝ) ≤ 2*C*L := by
    have hp := count q χ t
    have hn := count q χ (-t)
    rw [hLn] at hn
    have hu : (S.card:ℝ) ≤ (P.card:ℝ)+(N.card:ℝ) := by exact_mod_cast Finset.card_union_le P N
    dsimp only [P,N] at hu
    linarith [hp,hn]
  obtain ⟨v,hv,sep⟩ := exists_goodHeight S (fun z => 2*|z.im|) (2*B+1/2)
  let T := v/2
  have hT : B+1/4 ≤ T ∧ T ≤ B+3/4 := by dsimp [T]; constructor <;> linarith [hv.1,hv.2]
  let g := (4*(1+2*C)*L)⁻¹
  have hden : 4*(1+(S.card:ℝ)) ≤ 4*(1+2*C)*L := by linarith only [hs,hL]
  have hg : g ≤ 1/(4*(1+(S.card:ℝ))) := by
    rw [one_div];exact inv_anti₀ (by positivity) hden
  have hg' : g ≤ 1/4 := hg.trans ((one_div_le_one_div_of_le (by norm_num : (0:ℝ)<4) (by linarith [Nat.cast_nonneg (α:=ℝ) S.card] : (4:ℝ) ≤ 4*(1+(S.card:ℝ)))))
  refine ⟨T,⟨by linarith [hT.1],by linarith [hT.2]⟩,?_⟩
  intro z hz hzero
  change g ≤ _
  by_contra! hclose
  have hnear := abs_lt.mp (hclose.trans_le hg')
  have hr : z.re ≤ 2 := by by_contra! h; exact regularizedL_ne_zero_right χ (by linarith) hzero
  have hzS : z ∈ S := by
    by_cases hi : 0 ≤ z.im
    · rw [abs_of_nonneg hi] at hnear
      apply Finset.mem_union_left
      apply (mem_boxZeros χ _ _ _ _ z).mpr
      exact ⟨mem_reProdIm.mpr ⟨⟨hz,hr⟩,⟨by dsimp [t];linarith [hT.1,hnear.2],by dsimp [t];linarith [hT.2,hnear.1]⟩⟩,hzero⟩
    · rw [abs_of_neg (lt_of_not_ge hi)] at hnear
      apply Finset.mem_union_right
      apply (mem_boxZeros χ _ _ _ _ z).mpr
      exact ⟨mem_reProdIm.mpr ⟨⟨hz,hr⟩,⟨by dsimp [t];linarith [hT.2,hnear.1],by dsimp [t];linarith [hT.1,hnear.2]⟩⟩,hzero⟩
  have hsep := sep z hzS
  rw [show v-2*|z.im|=2*(T-|z.im|) by dsimp [T];ring,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hsep
  have heq : 1/(2*(1+(S.card:ℝ))) = 2*(1/(4*(1+(S.card:ℝ)))) := by field_simp; ring
  linarith only [heq,hsep,hg,hclose]

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

theorem logHeight_mono_abs (q : ℕ) [NeZero q] {s t : ℝ} (h : |s| ≤ |t|) :
    logHeight q s ≤ logHeight q t := by
  have hq : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  apply Real.log_le_log (by positivity)
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- A uniform logarithmic-derivative bound holds on both horizontal edges. The
height can depend on the character; every point of each edge is covered. -/
theorem unconditional_horizontal_log {d : ℝ} (hd : 0 < d) :
    ∃ A : ℝ, 0 < A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (B : ℝ), 2 ≤ B →
      ∃ T ∈ Icc B (B+1), (∀ z : ℂ, 1/2 ≤ z.re → regularizedL χ z = 0 → |z.im| ≠ T) ∧
        ∀ σ t : ℝ, 1/2+d ≤ σ → σ ≤ 2 → |t| = T →
        ‖contourLog χ (line σ t)‖ ≤ A*(logHeight q (B+1))^2 := by
  obtain ⟨C,hC,good⟩ := good_symmetric_height
  obtain ⟨K,hK,bound⟩ := uniform_dirichlet_log_control
  refine ⟨K*(1+d⁻¹+C)+4,by positivity,?_⟩
  intro q _ χ B hB
  obtain ⟨T,hT,avoid⟩ := good q χ B hB
  let L := logHeight q (B+1)
  have hL : 1 ≤ L := logHeight_ge_one q _
  have hc := logHeight_ge_one q (B+1/2)
  have hmid : logHeight q (B+1/2) ≤ L := by
    apply logHeight_mono_abs
    rw [abs_of_nonneg (by linarith : 0 ≤ B+1/2),abs_of_nonneg (by linarith : 0 ≤ B+1)]
    linarith
  let r := min d (C*logHeight q (B+1/2))⁻¹
  have hr : 0 < r := lt_min hd (by positivity)
  have hr' : r⁻¹ ≤ d⁻¹+C*L := by
    dsimp [r]
    rcases le_total d (C*logHeight q (B+1/2))⁻¹ with h|h
    · rw [min_eq_left h]; nlinarith only [hC,hL,mul_pos hC (by linarith : 0 < L)]
    · rw [min_eq_right h,inv_inv]; linarith only [mul_le_mul_of_nonneg_left hmid hC.le,inv_pos.mpr hd]
  refine ⟨T,hT,?_,?_⟩
  · intro z hz hz0 heq
    have gap := avoid z hz hz0
    rw [heq,sub_self,abs_zero] at gap
    exact (not_le_of_gt (by positivity)) gap
  intro σ t hσ hσ' ht
  have hdist (z : ℂ) (_hz : 0 < z.re) (hz0 : regularizedL χ z = 0) : r ≤ ‖line σ t - z‖ := by
    by_cases hz : 1/2 ≤ z.re
    · have h := avoid z hz hz0
      have h' := abs_norm_sub_norm_le t z.im
      simp only [Real.norm_eq_abs,ht] at h'
      exact ((min_le_right ..).trans (h.trans h')).trans (by simpa using abs_im_le_norm (line σ t-z))
    · exact (min_le_left ..).trans ((show d ≤ (line σ t-z).re by simp only [sub_re,re_line];linarith).trans (re_le_norm _))
  have raw := bound q χ σ t r ⟨by linarith,hσ'⟩ hr hdist
  have htlog : logHeight q t ≤ L := by apply logHeight_mono_abs;rw [ht,abs_of_nonneg (by linarith : 0≤B+1)];exact hT.2
  have hsep := horizontal_pole_dist (by rw [ht];linarith [hT.1] : 1 ≤ |t|) σ
  have hflag : ‖principalFlag χ‖ ≤ 1 := by by_cases h : χ = 1 <;> simp [principalFlag,h]
  have hpole : ‖principalFlag χ/(line σ t-1)‖ ≤ 4 := by
    rw [norm_div];apply (div_le_iff₀ (by linarith : 0 < ‖line σ t-1‖)).mpr;linarith
  rw [mul_right_comm K] at raw
  change ‖logDeriv (regularizedL χ) (line σ t)‖ ≤ K*(1+r⁻¹)*logHeight q t at raw
  have hfactor : 1+r⁻¹ ≤ (1+d⁻¹+C)*L := by
    nlinarith only [hr',hL,mul_le_mul_of_nonneg_left hL (inv_pos.mpr hd).le]
  have hm := mul_le_mul (mul_le_mul_of_nonneg_left hfactor hK.le) htlog
    (by linarith [logHeight_ge_one q t]) (by positivity)
  have hsq : 1 ≤ L^2 := one_le_pow₀ hL
  calc
    ‖contourLog χ (line σ t)‖ ≤ ‖logDeriv (regularizedL χ) (line σ t)‖ + ‖principalFlag χ/(line σ t-1)‖ := by
      simpa only [contourLog,norm_neg] using norm_add_le (-logDeriv (regularizedL χ) (line σ t)) (principalFlag χ/(line σ t-1))
    _ ≤ (K*(1+d⁻¹+C)+4)*L^2 := by nlinarith only [raw.trans hm,hpole,hsq]

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter GoldbachSmoothing
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

noncomputable def leftVertical {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b β σ T : ℝ) : ℂ :=
  (1/(2*Real.pi)) • ∫ t : ℝ in (-T)..T, integrand χ a b β (line σ t)

/-- Along either horizontal side the window decays quadratically in height.
The loss from the logarithmic derivative is at most quadratic in log height. -/
theorem horizontal_edge_bound {d σ T B A X β : ℝ} {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a b : ℕ} (hX : 1 ≤ X) (ha : X ≤ (a:ℝ)) (hab : (a:ℝ)+1 ≤ b)
    (hb : (b:ℝ)+1 ≤ 2*X) (hβ : |β| ≤ 1) (hd : 0 < d)
    (hs : 1/2+d ≤ σ) (hs' : σ < 1) (hT : 0 < T) (hA : 0 ≤ A)
    (hlog : ∀ x t : ℝ, 1/2+d ≤ x → x ≤ 2 → |t| = T →
      ‖contourLog χ (line x t)‖ ≤ A*(logHeight q (B+1))^2) {t : ℝ} (ht : |t| = T) :
    ‖∫ x : ℝ in σ..2, integrand χ a b β (line x t)‖ ≤
      (2*A*96)*X^4*(logHeight q (B+1))^2/T^2 := by
  let L := logHeight q (B+1)
  have hpos : 0 < σ := by linarith
  have pt (x : ℝ) (hx : x ∈ Ι σ 2) : ‖integrand χ a b β (line x t)‖ ≤ (A*L^2)*(96*X^4/T^2) := by
    rw [uIoc_of_le (by linarith)] at hx
    have hw := norm_transform_tail hX ha hab hb hβ (line x t) (by simp;linarith [hx.1])
      (by simpa using hx.2) (by simpa [ht] using hT)
    rw [im_line,ht] at hw
    rw [integrand,norm_mul]
    exact mul_le_mul (hlog x t (hs.trans hx.1.le) hx.2 ht) hw (norm_nonneg _) (by positivity)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const pt
  have hlen : |2-σ| ≤ 2 := by rw [abs_of_nonneg (by linarith)];linarith
  exact hi.trans ((mul_le_mul_of_nonneg_left hlen (by positivity)).trans_eq (by dsimp [L];ring))

theorem finite_formula_left_vertical {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1/8) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (B : ℝ), 2 ≤ B →
      ∃ T ∈ Icc B (B+1), ∃ σ ∈ Ioo (1/2+d) (1/2+2*d),
        ∀ (a b : ℕ) (X β : ℝ), 1 ≤ X → X ≤ (a:ℝ) → (a:ℝ)+1 ≤ b → (b:ℝ)+1 ≤ 2*X → |β| ≤ 1 →
        ‖(∑ n ∈ Finset.Ioc a b, twistedCoefficient χ n * phase β n) -
          (principalFlag χ*transform a b β 1 - zeroContribution χ a b β σ T +
            leftVertical χ a b β σ T)‖ ≤ C*X^4*(T⁻¹+(logHeight q (B+1))^2/T^2) := by
  classical
  obtain ⟨A,hA,horiz⟩ := unconditional_horizontal_log hd
  obtain ⟨K,hK,tail⟩ := truncation_bound
  let c : ℝ := 1/(2*Real.pi)
  have hc : 0 < c := by dsimp [c];positivity
  let M := c*(2*(2*A*96))
  have hM : 0 < M := by dsimp [M];positivity
  refine ⟨max K M,hK.trans_le (le_max_left ..),?_⟩
  intro q _ χ B hB
  obtain ⟨T,hTB,avoid,hlog⟩ := horiz q χ B hB
  have hT : 0 < T := by linarith [hTB.1]
  let Z := boxZeros χ (1/2+d) 2 (-T) T
  obtain ⟨σ,hσ,avoidR⟩ := (Ioo_infinite (by linarith : 1/2+d < 1/2+2*d)).exists_notMem_finset (Z.image Complex.re)
  have hs : σ < 1 := by linarith [hσ.2]
  have inner (z : ℂ) (hz : z ∈ boxZeros χ σ 2 (-T) T) : σ < z.re ∧ z.re < 2 ∧ -T < z.im ∧ z.im < T := by
    obtain ⟨h,z0⟩ := (mem_boxZeros χ _ _ _ _ z).mp hz
    have hb := mem_reProdIm.mp h
    have hzZ : z ∈ Z := (mem_boxZeros χ _ _ _ _ z).mpr
      ⟨mem_reProdIm.mpr ⟨⟨hσ.1.le.trans hb.1.1,hb.1.2⟩,hb.2⟩,z0⟩
    have him := avoid z (by linarith [hσ.1,hb.1.1]) z0
    refine ⟨lt_of_le_of_ne hb.1.1 (fun e => avoidR (Finset.mem_image.mpr ⟨z,hzZ,e.symm⟩)),
      lt_of_le_of_ne hb.1.2 ?_,lt_of_le_of_ne hb.2.1 ?_,lt_of_le_of_ne hb.2.2 ?_⟩
    · intro e;exact regularizedL_ne_zero_right χ (by rw [e];norm_num) z0
    · intro e;exact him (by rw [←e,abs_neg,abs_of_pos hT])
    · intro e;exact him (by rw [e,abs_of_pos hT])
  refine ⟨T,hTB,σ,hσ,?_⟩
  intro a b X β hX ha hab hb hβ
  let F := integrand χ a b β
  let H (t : ℝ) := ∫ x : ℝ in σ..2, F (line x t)
  let R := truncationRemainder χ a b β T
  have hH := @horizontal_edge_bound d σ T B A X β q _ χ a b hX ha hab hb hβ hd hσ.1.le hs hT hA.le hlog
  have hlo := hH (t := -T) (by simp [abs_of_pos hT])
  have hhi := hH (t := T) (abs_of_pos hT)
  have hR := tail q χ a b X β T hX ha hab hb hβ hT
  have hEq := exact_twisted_box χ hX ha hab hb hβ hs hT inner
  rw [hEq]
  unfold contourRemainder leftVertical
  change ‖_ + c • (_ + I*(H (-T) - H T)) + R - (_ + c • _)‖ ≤ _
  rw [smul_add]
  have cancel (p l h r : ℂ) : p+(l+h)+r-(p+l)=h+r := by abel
  rw [cancel]
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_mul,norm_I,one_mul,Real.norm_eq_abs,abs_of_pos hc]
  let L := logHeight q (B+1)
  have hedge : c*‖H (-T)-H T‖ ≤ M*X^4*(L^2/T^2) :=
    (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add hlo hhi)) hc.le).trans_eq (by dsimp [M,L];ring)
  calc
    _ ≤ M*X^4*(L^2/T^2)+K*X^4/T := add_le_add hedge hR
    _ ≤ max K M*X^4*(L^2/T^2)+max K M*X^4/T := by
      gcongr
      · exact le_max_right ..
      · exact le_max_left ..
    _ = _ := by dsimp [L];ring

end GoldbachTwistedMellin
end
end

open Set Complex Goldbach GoldbachTwistedMellin
open scoped Topology Interval

theorem PEqualNP.Outside.L_goldbach_twisted_explicit_formula_right_zeros :
    let W := fun (a b : ℕ) (β : ℝ) (s : ℂ) =>
      mellin (fun x : ℝ => ((max 0 (min (x - (a:ℝ)) (min 1 ((b:ℝ)+1-x))) : ℝ) : ℂ) *
        Complex.exp (((β*x:ℝ):ℂ)*Complex.I)) s
    let line := fun x t : ℝ => (x:ℂ)+(t:ℂ)*Complex.I
    ∀ d : ℝ, 0 < d → d ≤ 1/8 → ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (B : ℝ), 2 ≤ B →
      let f := @ite (ℂ → ℂ) (χ = 1) (Classical.propDecidable _) (DirichletCharacter.LFunctionTrivChar₁ q) (DirichletCharacter.LFunction χ)
      let p := @ite ℂ (χ = 1) (Classical.propDecidable _) 1 0
      ∃ T ∈ Set.Icc B (B+1), ∃ σ ∈ Set.Ioo (1/2+d) (1/2+2*d), ∃ Z : Finset ℂ,
        (∀ z : ℂ, z ∈ Z ↔ (σ ≤ z.re ∧ z.re ≤ 2) ∧ (-T ≤ z.im ∧ z.im ≤ T) ∧ f z = 0) ∧
        ∀ (a b : ℕ) (X β : ℝ), 1 ≤ X → X ≤ (a:ℝ) → (a:ℝ)+1 ≤ b → (b:ℝ)+1 ≤ 2*X → |β| ≤ 1 →
        ‖(∑ n ∈ Finset.Ioc a b, χ (n:ZMod q) * (ArithmeticFunction.vonMangoldt n:ℂ) *
            Complex.exp (((β*(n:ℝ):ℝ):ℂ)*Complex.I)) -
          (p*W a b β 1 - (∑ z ∈ Z, (analyticOrderNatAt f z:ℂ)*W a b β z) +
            (1/(2*Real.pi):ℝ) • ∫ t : ℝ in (-T)..T,
              (-logDeriv f (line σ t) + p/(line σ t-1))*W a b β (line σ t))‖ ≤
          C*X^4*(T⁻¹+(Real.log (2*(q:ℝ)*(2+|B+1|)))^2/T^2) := by
  classical
  intro W ℓ d hd hd'
  obtain ⟨C,hC,h⟩ := finite_formula_left_vertical hd hd'
  refine ⟨C,hC,?_⟩
  intro q _ χ B hB f p
  obtain ⟨T,hT,σ,hσ,bound⟩ := h q χ B hB
  let Z := boxZeros χ σ 2 (-T) T
  have hf : f = regularizedL χ := by
    by_cases hχ : χ = 1 <;> simp [f,regularizedL,hχ]
  have hp : p = principalFlag χ := by
    by_cases hχ : χ = 1 <;> simp [p,principalFlag,hχ]
  refine ⟨T,hT,σ,hσ,Z,?_,?_⟩
  · intro z
    rw [hf,mem_boxZeros]
    constructor
    · rintro ⟨hbox,hz⟩
      have hh := mem_reProdIm.mp hbox
      exact ⟨hh.1,hh.2,hz⟩
    · rintro ⟨hre,him,hz⟩
      exact ⟨mem_reProdIm.mpr ⟨hre,him⟩,hz⟩
  · intro a b X β hX ha hab hb hβ
    rw [hf,hp]
    exact bound a b X β hX ha hab hb hβ
