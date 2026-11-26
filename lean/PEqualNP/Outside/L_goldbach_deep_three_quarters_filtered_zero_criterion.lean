import Mathlib

/-!
Primitive-character and dyadic real-part criterion for the pointwise three-quarters bound.
The real-part, ordinate and phase tests are evaluated at each inducing conductor.
The phase derivative is tested over the entire dyadic interval.
The signed residue sum is evaluated only at the primitive levels. Its exact inverse
has squared Möbius coefficients; uniform upper bounds transfer at a cost of q/φ(q).
The Mellin estimate also discards the zeros below the block-dependent threshold
X^Re(z) sqrt(q) sqrt(1+8 pi |beta| X) <= n^(3/4).
The primitive-conductor projection cancels before taking absolute values.
Every conductor at most q/n^(1/4) contributes within the pointwise budget.
No hypothesis on the real parts of the zeros is used. The formula keeps the
signed multiplicities of the enclosed zeros. An average over contour abscissae
bounds the left edge using local zero counts and an integrable product kernel.
At polynomial height the entire error is bounded at the oscillatory window scale.
Local Jensen bounds then fix the cutoff at the critical line, strictly excluding
zeros on the line itself. Finite character inversion recovers the prime sum.

The analytic growth, Jensen disk, logarithmic derivative and rectangle
residue estimates are adapted from DNZJSJ, goldbach-proofs PR #2486,
commit f3613cf846dfb3e7fe7d04fe6ce51c6ee25e7d4f (Apache-2.0).
The Mellin window and inversion use the same integer endpoints as the
conditional three-quarters proof. The right-half count, shared edge
selection and two-sided truncation estimate below do not use Dirichlet GRH.
The per-ordinate oscillatory bounds are from 34245621, PR #2511, at
cba708bd00210b8e17a7f7f9d5e48b74599f48c5. The rational-approximation and main-term estimates
are adapted from Esythium, PR #2512 at 9117b0e8465c7323ed09c4673b5ceac9a7ef8118.
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


end GoldbachTwistedMellin
end
end

section
open Set MeasureTheory
open scoped Interval Topology
noncomputable section
namespace GoldbachTwistedMellin

def rootKernel (x : ℝ) := |x|^(-(1/2):ℝ)

theorem rootKernel_nonneg (x : ℝ) : 0 ≤ rootKernel x := Real.rpow_nonneg (abs_nonneg _) _

theorem integrable_rootKernel (a b r : ℝ) : IntervalIntegrable (fun x => rootKernel (x-r)) volume a b := by
  have hpow (u v : ℝ) : IntervalIntegrable (fun x : ℝ => x^(-(1/2):ℝ)) volume u v :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hpos : IntervalIntegrable (fun x : ℝ => (x-r)^(-(1/2):ℝ)) volume a b :=
    by simpa using (hpow (a-r) (b-r)).comp_sub_right r
  have hneg : IntervalIntegrable (fun x : ℝ => (r-x)^(-(1/2):ℝ)) volume a b :=
    by simpa using (hpow (r-a) (r-b)).comp_sub_left r
  rw [intervalIntegrable_iff] at hpos hneg ⊢
  have h := Integrable.piecewise (μ:=volume.restrict (Ι a b)) (s:=Iio r) measurableSet_Iio.nullMeasurableSet
    (Integrable.integrableOn hneg) (Integrable.integrableOn hpos)
  apply h.congr
  filter_upwards with x
  by_cases hx : x < r
  · simp [Set.piecewise,hx,rootKernel,abs_of_neg (sub_neg.mpr hx),neg_sub]
  · simp [Set.piecewise,hx,rootKernel,abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hx))]

theorem integral_rootKernel_right {a b r : ℝ} (ha : r ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, rootKernel (x-r)) = 2*(Real.sqrt (b-r)-Real.sqrt (a-r)) := by
  have h : (∫ x in a..b, rootKernel (x-r)) = ∫ x in a..b, (x-r)^(-(1/2):ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    simp [rootKernel,abs_of_nonneg (sub_nonneg.mpr (ha.trans hx.1))]
  rw [h,intervalIntegral.integral_comp_sub_right (fun x : ℝ => x^(-(1/2):ℝ)) r,
    integral_rpow (Or.inl (by norm_num))]
  norm_num [← Real.sqrt_eq_rpow]
  ring

theorem integral_rootKernel_left {a b r : ℝ} (hb : b ≤ r) (hab : a ≤ b) :
    (∫ x in a..b, rootKernel (x-r)) = 2*(Real.sqrt (r-a)-Real.sqrt (r-b)) := by
  have h : (∫ x in a..b, rootKernel (x-r)) = ∫ x in a..b, (r-x)^(-(1/2):ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    simp [rootKernel,abs_of_nonpos (sub_nonpos.mpr (hx.2.trans hb)),neg_sub]
  rw [h,intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^(-(1/2):ℝ)) r,
    integral_rpow (Or.inl (by norm_num))]
  norm_num [← Real.sqrt_eq_rpow]
  ring

theorem integral_rootKernel_le {a b : ℝ} (hab : a ≤ b) (r : ℝ) :
    (∫ x in a..b, rootKernel (x-r)) ≤ 4*Real.sqrt (b-a) := by
  have diffBound (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      Real.sqrt (x+y)-Real.sqrt x ≤ Real.sqrt y := by
    apply sub_le_iff_le_add.mpr
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    nlinarith only [Real.sq_sqrt (add_nonneg hx hy),Real.sq_sqrt hx,Real.sq_sqrt hy,
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  rcases le_total r a with h|h
  · rw [integral_rootKernel_right h hab]
    have he : b-r = a-r+(b-a) := by ring
    rw [he]
    linarith [diffBound (a-r) (b-a) (by linarith) (by linarith),Real.sqrt_nonneg (b-a)]
  rcases le_total b r with h'|h'
  · rw [integral_rootKernel_left h' hab]
    have he : r-a = r-b+(b-a) := by ring
    rw [he]
    linarith [diffBound (r-b) (b-a) (by linarith) (by linarith),Real.sqrt_nonneg (b-a)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (integrable_rootKernel a r r) (integrable_rootKernel r b r),
    integral_rootKernel_left (le_refl r) h,integral_rootKernel_right (le_refl r) h',sub_self,Real.sqrt_zero]
  linarith [Real.sqrt_le_sqrt (by linarith : r-a ≤ b-a),Real.sqrt_le_sqrt (by linarith : b-r ≤ b-a)]

end GoldbachTwistedMellin
end
end

section
open Set MeasureTheory
open scoped Interval Topology
noncomputable section
namespace GoldbachTwistedMellin

/-- A vertical side avoiding any prescribed finite set can be chosen with
controlled total square-root singularity at all real coordinates. -/
theorem exists_weighted_rootKernel_bound {ι : Type*} (S : Finset ι) (w y : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (bad : Finset ℝ) {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Ioo a b, x ∉ bad ∧
      (∑ i ∈ S, w i*rootKernel (x-y i)) ≤ (4/Real.sqrt (b-a))*(∑ i ∈ S,w i) := by
  classical
  let I := Ioc a b
  let μ := volume.restrict I
  have len : 0 < b-a := sub_pos.mpr hab
  have hreal : μ.real univ = b-a := by
    simp [μ,I,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal len.le]
  have hn : μ ≠ 0 := by
    intro h
    have hp : 0 < μ.real univ := hreal.symm ▸ len
    simp [h] at hp
  let : IsFiniteMeasure μ := ⟨by simp [μ,I,Real.volume_Ioc]⟩
  let g := fun x : ℝ => ∑ i ∈ S, w i*rootKernel (x-y i)
  have int (i : ι) : Integrable (fun x => w i*rootKernel (x-y i)) μ :=
    ((integrable_rootKernel a b (y i)).1.const_mul (w i))
  have hi : Integrable g μ := integrable_finsetSum S (fun i _ => int i)
  have avg : (⨍ x, g x ∂μ) ≤ (4/Real.sqrt (b-a))*(∑ i ∈ S,w i) := by
    rw [average_eq,hreal,smul_eq_mul]
    have hi' : (∫ x, g x ∂μ) ≤ 4*Real.sqrt (b-a)*(∑ i ∈ S,w i) := by
      unfold g
      rw [integral_finsetSum S (fun i _ => int i),Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      rw [integral_const_mul]
      have hbound := integral_rootKernel_le hab.le (y i)
      rw [intervalIntegral.integral_of_le hab.le] at hbound
      exact (mul_le_mul_of_nonneg_left hbound (hw i hi)).trans_eq (by ring)
    apply (mul_le_mul_of_nonneg_left hi' (inv_nonneg.mpr len.le)).trans_eq
    have hs := Real.sq_sqrt len.le
    have hp := Real.sqrt_pos.mpr len
    field_simp
    rw [hs]
  let N : Set ℝ := Iᶜ ∪ (↑(insert b bad) : Set ℝ)
  have hN : μ N = 0 := by
    apply measure_union_null
    · simp [μ,I,Measure.restrict_apply,measurableSet_Ioc.compl]
    · exact (insert b bad).measure_zero μ
  obtain ⟨x,hx,hgx⟩ := exists_notMem_null_le_average hn hi hN
  have h' : x ∈ I := by by_contra hh;exact hx (Or.inl hh)
  have hbad : x ∉ insert b bad := fun h => hx (Or.inr h)
  exact ⟨x,⟨h'.1,lt_of_le_of_ne h'.2 (fun h => hbad (Finset.mem_insert.mpr (.inl h)))⟩,
    fun h => hbad (Finset.mem_insert.mpr (.inr h)),hgx.trans avg⟩

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

theorem inv_distance_le_root_product (s z : ℂ) (hx : s.re ≠ z.re) (hy : s.im ≠ z.im) :
    ‖s-z‖⁻¹ ≤ rootKernel (s.re-z.re)*rootKernel (s.im-z.im) := by
  let x := |s.re-z.re|
  let y := |s.im-z.im|
  have hxp : 0 < x := abs_pos.mpr (sub_ne_zero.mpr hx)
  have hyp : 0 < y := abs_pos.mpr (sub_ne_zero.mpr hy)
  have h1 : x ≤ ‖s-z‖ := abs_re_le_norm _
  have h2 : y ≤ ‖s-z‖ := abs_im_le_norm _
  have hsq : Real.sqrt x*Real.sqrt y ≤ ‖s-z‖ := by
    rw [← Real.sqrt_mul hxp.le]
    exact (Real.sqrt_le_iff).mpr ⟨norm_nonneg _,by simpa only [pow_two] using mul_le_mul h1 h2 hyp.le (norm_nonneg _)⟩
  change _ ≤ x^(-(1/2):ℝ)*y^(-(1/2):ℝ)
  rw [Real.rpow_neg hxp.le,Real.rpow_neg hyp.le,←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow,← mul_inv]
  exact inv_anti₀ (mul_pos (Real.sqrt_pos.mpr hxp) (Real.sqrt_pos.mpr hyp)) hsq

/-- Only zeros within one vertical unit and to the right of one half may
contribute a singular term. A product of two locally integrable kernels
majorizes each such term at almost every height. -/
noncomputable def localZeroPotential (Z : Finset ℂ) (σ t : ℝ) : ℝ :=
  ∑ z ∈ Z, if |t-z.im| ≤ 1 then rootKernel (σ-z.re)*rootKernel (t-z.im) else 0

theorem localPotential_nonneg (Z : Finset ℂ) (σ t : ℝ) : 0 ≤ localZeroPotential Z σ t :=
  Finset.sum_nonneg fun z _ => by split <;> first | exact mul_nonneg (rootKernel_nonneg _) (rootKernel_nonneg _) | exact le_rfl

theorem localPotential_term {Z : Finset ℂ} {z : ℂ} (hz : z ∈ Z) (σ t : ℝ) (h : |t-z.im| ≤ 1) :
    rootKernel (σ-z.re)*rootKernel (t-z.im) ≤ localZeroPotential Z σ t := by
  classical
  let w := fun z : ℂ => if |t-z.im| ≤ 1 then rootKernel (σ-z.re)*rootKernel (t-z.im) else 0
  have hn (z : ℂ) (_ : z ∈ Z) : 0 ≤ w z := by dsimp [w];split <;> first | exact mul_nonneg (rootKernel_nonneg _) (rootKernel_nonneg _) | exact le_rfl
  simpa only [w,localZeroPotential,ite_eq_left h] using Finset.single_le_sum hn hz

theorem log_control_via_potential {d : ℝ} (hd : 0 < d) :
    ∃ A : ℝ, 0 < A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t T : ℝ),
      1/2+d ≤ σ → σ ≤ 3/4 → |t| ≤ T →
      let Z := boxZeros χ (1/2) 2 (-T-1) (T+1)
      (∀ z ∈ Z, σ ≠ z.re) → (∀ z ∈ Z, t ≠ z.im) →
      ‖contourLog χ (line σ t)‖ ≤ A*logHeight q t*(1+localZeroPotential Z σ t) := by
  obtain ⟨C,hC,bound⟩ := uniform_dirichlet_log_control
  refine ⟨C*(2+d⁻¹)+4,by positivity,?_⟩
  intro q _ χ σ t T hs hs' ht Z xr yi
  let P := localZeroPotential Z σ t
  have hP : 0 ≤ P := localPotential_nonneg _ _ _
  let D := 1+d⁻¹+P
  have hD : 0 < D := by dsimp [D];positivity
  have sep (z : ℂ) (_ : 0 < z.re) (hz : regularizedL χ z = 0) : D⁻¹ ≤ ‖line σ t-z‖ := by
    by_cases hreal : z.re < 1/2
    · have hsep : d ≤ ‖line σ t-z‖ := (show d ≤ (line σ t-z).re by simp only [sub_re,re_line];linarith).trans (re_le_norm _)
      exact (show D⁻¹ ≤ d by simpa using inv_anti₀ (inv_pos.mpr hd) (by dsimp [D];linarith : d⁻¹ ≤ D)).trans hsep
    by_cases him : |t-z.im| ≤ 1
    · have hZ : z ∈ Z := by
        apply (mem_boxZeros χ _ _ _ _ z).mpr
        have hright : z.re ≤ 2 := by by_contra! h;exact regularizedL_ne_zero_right χ (by linarith) hz
        have htt := abs_le.mp ht
        have hii := abs_le.mp him
        exact ⟨mem_reProdIm.mpr ⟨⟨le_of_not_gt hreal,hright⟩,⟨by linarith [htt.1,hii.2],by linarith [htt.2,hii.1]⟩⟩,hz⟩
      have hdis := inv_distance_le_root_product (line σ t) z (by simpa using xr z hZ) (by simpa using yi z hZ)
      simp only [re_line,im_line] at hdis
      have hle := hdis.trans (localPotential_term hZ σ t him)
      have hp : 0 < ‖line σ t-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun he => xr z hZ (by simpa using congrArg Complex.re he)))
      exact (inv_le_comm₀ hD hp).mpr (by dsimp [D];linarith only [hle,inv_pos.mpr hd])
    · have hi : 1 ≤ ‖line σ t-z‖ := (le_of_not_ge him).trans (by simpa using abs_im_le_norm (line σ t-z))
      exact (show D⁻¹ ≤ 1 by simpa using inv_anti₀ zero_lt_one (by dsimp [D];linarith only [hP,inv_pos.mpr hd] : 1 ≤ D)).trans hi
  have raw := bound q χ σ t D⁻¹ ⟨by linarith,by linarith⟩ (inv_pos.mpr hD) sep
  rw [inv_inv] at raw
  have hL := logHeight_ge_one q t
  have hp := left_pole_dist hs' t
  have hf : ‖principalFlag χ‖ ≤ 1 := by by_cases h : χ=1 <;> simp [principalFlag,h]
  have hflag : ‖principalFlag χ/(line σ t-1)‖ ≤ 4 := by
    rw [norm_div];apply (div_le_iff₀ (by linarith : 0<‖line σ t-1‖)).mpr;linarith
  calc
    ‖contourLog χ (line σ t)‖ ≤ ‖logDeriv (regularizedL χ) (line σ t)‖ + ‖principalFlag χ/(line σ t-1)‖ := by
      simpa only [contourLog,norm_neg] using norm_add_le (-logDeriv (regularizedL χ) (line σ t)) (principalFlag χ/(line σ t-1))
    _ ≤ (C*(2+d⁻¹)+4)*logHeight q t*(1+P) := by
      change ‖logDeriv (regularizedL χ) (line σ t)‖ ≤ C*logHeight q t*(1+D) at raw
      have hfac : 1+D ≤ (2+d⁻¹)*(1+P) := by dsimp [D];nlinarith only [hP,mul_nonneg (inv_pos.mpr hd).le hP]
      have hh := mul_le_mul_of_nonneg_left hfac (mul_nonneg hC.le (by linarith : 0≤logHeight q t))
      nlinarith only [raw.trans hh,hflag,hL,mul_nonneg (by linarith : 0≤logHeight q t) hP]

end GoldbachTwistedMellin
end
end

section
open Set MeasureTheory
open scoped Interval Topology
noncomputable section
namespace GoldbachTwistedMellin

theorem exists_cluster_average {ι : Type*} (I : Finset ι) (Z : ι → Finset ℂ) (w : ι → ℝ)
    (hw : ∀ i ∈ I, 0 ≤ w i) (bad : Finset ℝ) {a b M : ℝ} (hab : a < b)
    (hM : ∀ i ∈ I, ((Z i).card:ℝ) ≤ M) :
    ∃ σ ∈ Ioo a b, σ ∉ bad ∧
      (∑ i ∈ I, w i*(1+4*∑ z ∈ Z i,rootKernel (σ-z.re))) ≤
        (1+16*M/Real.sqrt (b-a))*(∑ i ∈ I,w i) := by
  classical
  let S := I.sigma Z
  let weight := fun p : Σ _ : ι, ℂ => w p.1
  obtain ⟨x,hx,hbad,avg⟩ := exists_weighted_rootKernel_bound S weight (fun p => p.2.re)
    (fun p hp => hw p.1 (Finset.mem_sigma.mp hp).1) bad hab
  simp only [S,weight,Finset.sum_sigma] at avg
  refine ⟨x,hx,hbad,?_⟩
  have sumWeight : (∑ i ∈ I,∑ _ ∈ Z i,w i) ≤ M*∑ i ∈ I,w i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => by
      simpa only [Finset.sum_const,nsmul_eq_mul] using mul_le_mul_of_nonneg_right (hM i hi) (hw i hi)
  have hg := avg.trans (mul_le_mul_of_nonneg_left sumWeight (by positivity))
  have eq : (∑ i ∈ I,w i*(1+4*∑ z ∈ Z i,rootKernel (x-z.re))) =
      (∑ i ∈ I,w i)+4*(∑ i ∈ I,∑ z ∈ Z i,w i*rootKernel (x-z.re)) := by
    simp only [Finset.mul_sum,Finset.sum_add_distrib,mul_add,mul_one]
    simp only [mul_left_comm (w _)]
  rw [eq]
  calc
    _ ≤ (∑ i ∈ I,w i) + 4*((4/Real.sqrt (b-a))*(M*∑ i ∈ I,w i)) := by gcongr
    _ = (1+16*M/Real.sqrt (b-a))*(∑ i ∈ I,w i) := by ring

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

theorem potential_localize {Z S : Finset ℂ} (σ t : ℝ)
    (hs : ∀ z ∈ Z, |t-z.im| ≤ 1 → z ∈ S) :
    localZeroPotential Z σ t ≤ ∑ z ∈ S, rootKernel (σ-z.re)*rootKernel (t-z.im) := by
  classical
  rw [localZeroPotential,← Finset.sum_filter]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => hs z (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz).2)
    (fun z _ _ => mul_nonneg (rootKernel_nonneg _) (rootKernel_nonneg _))

theorem band_integral_majorant (S : Finset ℂ) (σ l H : ℝ) (hH : 0 ≤ H)
    (f : ℝ → ℝ) (hi : IntervalIntegrable f volume l (l+1))
    (hf : ∀ᵐ t ∂volume.restrict (Icc l (l+1)), f t ≤
      H*(1+∑ z ∈ S,rootKernel (σ-z.re)*rootKernel (t-z.im))) :
    (∫ t in l..l+1, f t) ≤ H*(1+4*∑ z ∈ S,rootKernel (σ-z.re)) := by
  let g (z : ℂ) (t : ℝ) := rootKernel (σ-z.re)*rootKernel (t-z.im)
  have ig (z : ℂ) : IntervalIntegrable (g z) volume l (l+1) :=
    (integrable_rootKernel l (l+1) z.im).const_mul _
  have isum : IntervalIntegrable (fun t => ∑ z ∈ S,g z t) volume l (l+1) :=
    ⟨integrable_finsetSum S (fun z _ => (ig z).1),integrable_finsetSum S (fun z _ => (ig z).2)⟩
  have hb := intervalIntegral.integral_mono_ae_restrict (by linarith : l ≤ l+1) hi
    ((intervalIntegrable_const.add isum).const_mul H) hf
  apply hb.trans
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add intervalIntegrable_const isum,
    intervalIntegral.integral_const,intervalIntegral.integral_finsetSum (fun z _ => ig z),Finset.mul_sum]
  simp only [add_sub_cancel_left,one_smul]
  apply mul_le_mul_of_nonneg_left _ hH
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro z hz
  rw [show (∫ t in l..l+1, g z t) = rootKernel (σ-z.re) * (∫ t in l..l+1,rootKernel (t-z.im)) from
    intervalIntegral.integral_const_mul ..]
  have hk := integral_rootKernel_le (by linarith : l ≤ l+1) z.im
  simp only [add_sub_cancel_left,Real.sqrt_one,mul_one] at hk
  exact (mul_le_mul_of_nonneg_left hk (rootKernel_nonneg _)).trans_eq (mul_comm ..)

theorem integrable_box_line {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ M : ℝ}
    (hs : 1/2 ≤ σ) (hs' : σ ≤ 3/4) {a b β : ℝ} (ha : 0 < a)
    (avoid : ∀ z ∈ boxZeros χ (1/2) 2 (-M-1) (M+1), σ ≠ z.re) :
    ContinuousOn (fun t : ℝ => integrand χ a b β (line σ t)) (Icc (-M) M) := by
  intro t ht
  let z := line σ t
  have hz : regularizedL χ z ≠ 0 := by
    intro hz
    have hm : z ∈ boxZeros χ (1/2) 2 (-M-1) (M+1) := by
      apply (mem_boxZeros χ _ _ _ _ z).mpr
      exact ⟨mem_reProdIm.mpr ⟨⟨by simpa [z] using hs,by dsimp [z];simp;linarith⟩,⟨by dsimp [z];simp;linarith [ht.1],by dsimp [z];simp;linarith [ht.2]⟩⟩,hz⟩
    exact avoid z hm (by simp [z])
  have hF := analytic_regularizedL χ z (mem_univ _)
  have hlog : AnalyticAt ℂ (logDeriv (regularizedL χ)) z := by
    simpa only [logDeriv,Pi.div_apply] using hF.deriv.div hF hz
  have hz1 : z-1 ≠ 0 := sub_ne_zero.mpr fun h => (by have he := congrArg Complex.re h; simp [z] at he;linarith)
  have hden : AnalyticAt ℂ (fun w : ℂ => w-1) z := analyticAt_id.sub analyticAt_const
  have hflag : AnalyticAt ℂ (fun _ : ℂ => principalFlag χ) z := analyticAt_const
  have hc : AnalyticAt ℂ (contourLog χ) z := hlog.neg.add (hflag.div hden hz1)
  have hi : AnalyticAt ℂ (integrand χ a b β) z := hc.mul ((analytic_transform ha b β).analyticAt z)
  exact (ContinuousAt.comp (f := line σ) (g := integrand χ a b β) (x := t) hi.continuousAt
    (continuous_line σ).continuousAt).continuousWithinAt

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

/-- The three-unit interval contains all zeros within vertical distance one
of a point of the integration interval [l,l+1]. -/
noncomputable def bandZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (l : ℝ) :=
  boxZeros χ (1/2) 2 (l-1) (l+2)

theorem bandZeros_card :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (l M : ℝ),
      |l| ≤ M → ((bandZeros χ l).card:ℝ) ≤ C*logHeight q (M+2) := by
  obtain ⟨C,hC,bound⟩ := right_box_card
  refine ⟨2*C,by positivity,?_⟩
  intro q _ χ l M hm
  let P := boxZeros χ (1/2) 2 (l-1) (l+1)
  let N := boxZeros χ (1/2) 2 ((l+1)-1) ((l+1)+1)
  have hsub : bandZeros χ l ⊆ P ∪ N := by
    intro z hz
    obtain ⟨hb,hz0⟩ := (mem_boxZeros χ _ _ _ _ z).mp hz
    have h := mem_reProdIm.mp hb
    by_cases h' : z.im ≤ l+1
    · exact Finset.mem_union_left _ ((mem_boxZeros χ _ _ _ _ z).mpr ⟨mem_reProdIm.mpr ⟨h.1,h.2.1,h'⟩,hz0⟩)
    · exact Finset.mem_union_right _ ((mem_boxZeros χ _ _ _ _ z).mpr ⟨mem_reProdIm.mpr ⟨h.1,by linarith,by linarith [h.2.2]⟩,hz0⟩)
  have hn : (0:ℝ) ≤ M := (abs_nonneg _).trans hm
  have hp := (bound q χ l).trans (mul_le_mul_of_nonneg_left
    (logHeight_mono_abs q (by rw [abs_of_nonneg (by linarith : 0 ≤ M+2)];linarith : |l| ≤ |M+2|)) hC.le)
  have hh : |l+1| ≤ |M+2| := by
    rw [abs_of_nonneg (by linarith : 0 ≤ M+2)]
    linarith [abs_add_le l 1,abs_one (α:=ℝ)]
  have hN := (bound q χ (l+1)).trans (mul_le_mul_of_nonneg_left (logHeight_mono_abs q hh) hC.le)
  exact (show ((bandZeros χ l).card:ℝ) ≤ (P.card:ℝ)+(N.card:ℝ) by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le P N)).trans ((add_le_add hp hN).trans_eq (by ring))

theorem near_zero_in_band {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (l t M : ℝ)
    (ht : t ∈ Icc l (l+1)) {z : ℂ} (hz : z ∈ boxZeros χ (1/2) 2 (-M-1) (M+1))
    (h : |t-z.im|≤1) : z ∈ bandZeros χ l := by
  obtain ⟨hb,hz0⟩ := (mem_boxZeros χ _ _ _ _ z).mp hz
  have hi := abs_le.mp h
  exact (mem_boxZeros χ _ _ _ _ z).mpr ⟨mem_reProdIm.mpr ⟨(mem_reProdIm.mp hb).1,
    by linarith [ht.1,hi.2],by linarith [ht.2,hi.1]⟩,hz0⟩

end GoldbachTwistedMellin
end
end

section
open Set MeasureTheory Finset
open scoped Interval Topology
noncomputable section
namespace GoldbachTwistedMellin

def grid (M : ℕ) : Finset (Bool × ℕ) := Finset.univ ×ˢ Finset.range M

def gridStart (p : Bool × ℕ) : ℝ := if p.1 then (p.2:ℝ) else -((p.2:ℝ)+1)

theorem grid_geometry {M : ℕ} {p : Bool × ℕ} (hp : p ∈ grid M) :
    |gridStart p| ≤ M ∧ ∀ t ∈ Icc (gridStart p) (gridStart p+1), (p.2:ℝ) ≤ |t| ∧ |t| ≤ M := by
  have hj := Finset.mem_range.mp (Finset.mem_product.mp hp).2
  have hle : (p.2:ℝ)+1 ≤ M := by exact_mod_cast hj
  have hn : (0:ℝ) ≤ p.2 := by positivity
  cases he : p.1 <;> simp only [gridStart,he,Bool.false_eq_true,ite_false,ite_true,abs_neg,
    abs_of_nonneg hn,abs_of_nonneg (by linarith : 0≤(p.2:ℝ)+1)]
  · refine ⟨hle,?_⟩; intro t ht
    rw [abs_of_nonpos (by linarith [ht.2])]
    constructor <;> linarith [ht.1,ht.2]
  · refine ⟨by linarith,?_⟩;intro t ht
    rw [abs_of_nonneg (by linarith [ht.1])]
    exact ⟨ht.1,ht.2.trans hle⟩

theorem sum_grid_weight (M : ℕ) (w : ℕ → ℝ) :
    (∑ p ∈ grid M, w p.2) = 2*∑ j ∈ Finset.range M,w j := by
  simp [grid,Finset.sum_product,two_mul]

theorem sum_grid_integrals {M : ℕ} (f : ℝ → ℝ)
    (hi : ∀ p ∈ grid M, IntervalIntegrable f volume (gridStart p) (gridStart p+1)) :
    (∫ t in -(M:ℝ)..(M:ℝ), f t) = ∑ p ∈ grid M, ∫ t in gridStart p..gridStart p+1, f t := by
  have ip (j : ℕ) (hj : j < M) : IntervalIntegrable f volume (j:ℝ) ((j+1:ℕ):ℝ) := by
    simpa [gridStart,Nat.cast_add] using hi (true,j) (by simp [grid,hj])
  have im (j : ℕ) (hj : j < M) : IntervalIntegrable f volume (-(j:ℝ)) (-((j+1:ℕ):ℝ)) := by
    have h := (hi (false,j) (by simp [grid,hj])).symm
    simpa [gridStart,Nat.cast_add,neg_add_rev] using h
  have hp := intervalIntegral.sum_integral_adjacent_intervals (a:=fun k : ℕ => (k:ℝ)) ip
  have hm := intervalIntegral.sum_integral_adjacent_intervals (a:=fun k : ℕ => -(k:ℝ)) im
  have hip := IntervalIntegrable.trans_iterate ip
  have him := IntervalIntegrable.trans_iterate im
  simp only [Nat.cast_zero,neg_zero] at hp hm hip him
  have hneg := congrArg Neg.neg hm
  rw [← Finset.sum_neg_distrib,←intervalIntegral.integral_symm] at hneg
  simp_rw [← intervalIntegral.integral_symm] at hneg
  rw [← intervalIntegral.integral_add_adjacent_intervals him.symm hip,←hneg,←hp]
  simp [grid,gridStart,Finset.sum_product,Nat.cast_add,neg_add_rev,add_comm]

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Finset
open scoped Topology
noncomputable section
namespace GoldbachTwistedMellin

/-- Average the dyadic window over unit height intervals using the oscillatory
estimates of the earlier zero-integral proof. -/

noncomputable def profile (J j : ℕ) : ℝ :=
  if j = 0 then 1 else if j ≤ J then (3+5*Real.pi)/Real.sqrt j else 20/j

theorem profile_nonneg (J j : ℕ) : 0 ≤ profile J j := by
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

theorem profile_sum (J N : ℕ) :
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

theorem window_bin_bound {X a b β V σ t : ℝ} (hX : 1 ≤ X) (ha : X ≤ a) (hab : a+1 ≤ b)
    (hb : b+1 ≤ 2*X) (hs : 0 ≤ σ) (hs' : σ ≤ 1) (hV : σ ≤ V) {j J : ℕ}
    (ht : (j:ℝ) ≤ |t|) (hJ : 4 * |β| * X ≤ (J:ℝ)) :
    ‖transform a b β (line σ t)‖ ≤ X^V * profile J j := by
  obtain ⟨triv,curv,far⟩ := norm_window_modes (zero_lt_one.trans_le hX) ha hab hb β (line σ t)
    (by simpa using hs) (by simpa using hs')
  simp only [re_line,im_line] at triv curv far
  have hpow := Real.rpow_le_rpow_of_exponent_le hX hV
  apply le_trans _ (mul_le_mul_of_nonneg_right hpow (profile_nonneg J j))
  by_cases h0 : j=0
  · simpa [profile,h0] using triv
  have hj : 0 < (j:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
  have htpos := hj.trans_le ht
  by_cases hjJ : j ≤ J
  · rw [profile,ite_eq_right h0,ite_eq_left hjJ]
    apply (curv (abs_pos.mp htpos)).trans
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hj)
      (Real.sqrt_le_sqrt ht)) (Real.rpow_nonneg (by linarith) _)
  · rw [profile,ite_eq_right h0,ite_eq_right hjJ]
    have hfar := far htpos (hJ.trans ((by exact_mod_cast (Nat.le_of_not_ge hjJ) : (J:ℝ) ≤ j).trans ht))
    exact hfar.trans ((div_le_div_of_nonneg_left (by positivity) hj ht).trans_eq (by ring))

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

theorem local_band_norm {d A X a b β V σ M l : ℝ} {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (j J : ℕ) (hd : 0 < d) (hA : 0 ≤ A)
    (hX : 1 ≤ X) (ha : X ≤ a) (hab : a+1 ≤ b) (hb : b+1 ≤ 2*X)
    (hs : 1/2+d ≤ σ) (hs' : σ ≤ 3/4) (hV : σ ≤ V) (hJ : 4 * |β| * X ≤ (J:ℝ))
    (hgrid : ∀ t ∈ Icc l (l+1), (j:ℝ) ≤ |t| ∧ |t| ≤ M)
    (avoid : ∀ z ∈ boxZeros χ (1/2) 2 (-M-1) (M+1), σ ≠ z.re)
    (hlog : ∀ t : ℝ, |t| ≤ M → (∀ z ∈ boxZeros χ (1/2) 2 (-M-1) (M+1), t ≠ z.im) →
      ‖contourLog χ (line σ t)‖ ≤ A*logHeight q t*(1+localZeroPotential (boxZeros χ (1/2) 2 (-M-1) (M+1)) σ t)) :
    (∫ t in l..l+1, ‖integrand χ a b β (line σ t)‖) ≤
      (A*logHeight q (M+2)*X^V)*profile J j *
      (1+4*∑ z ∈ bandZeros χ l,rootKernel (σ-z.re)) := by
  classical
  let Z := boxZeros χ (1/2) 2 (-M-1) (M+1)
  let S := bandZeros χ l
  let G (t : ℝ) := integrand χ a b β (line σ t)
  have hM : 0 ≤ M := (abs_nonneg _).trans (hgrid l ⟨le_rfl,by linarith⟩).2
  have hL := logHeight_ge_one q (M+2)
  have hpow : 0 ≤ X^V := Real.rpow_nonneg (by linarith) _
  have hprof := profile_nonneg J j
  have H : 0 ≤ (A*logHeight q (M+2)*X^V)*profile J j := by positivity
  have hc := integrable_box_line (a:=a) (b:=b) (β:=β) χ (by linarith : 1/2 ≤ σ) hs' (zero_lt_one.trans_le (hX.trans ha)) avoid
  have hcont : ContinuousOn G (Icc l (l+1)) := hc.mono (fun t ht => abs_le.mp (hgrid t ht).2)
  have hi : IntervalIntegrable (fun t => ‖G t‖) volume l (l+1) :=
    hcont.norm.intervalIntegrable_of_Icc (by linarith)
  apply band_integral_majorant S σ l _ H _ hi
  let μ := volume.restrict (Icc l (l+1))
  have hnull : μ (↑(Z.image Complex.im):Set ℝ) = 0 := (Z.image Complex.im).measure_zero μ
  filter_upwards [ae_restrict_mem measurableSet_Icc,measure_eq_zero_iff_ae_notMem.mp hnull] with t ht him
  have yt : ∀ z ∈ Z, t ≠ z.im := fun z hz e => him (Finset.mem_image.mpr ⟨z,hz,e.symm⟩)
  have hh := hlog t (hgrid t ht).2 yt
  have hl : logHeight q t ≤ logHeight q (M+2) := by
    apply logHeight_mono_abs
    rw [abs_of_nonneg (by linarith : 0 ≤ M+2)]
    linarith [(hgrid t ht).2]
  have hloc := potential_localize (Z:=Z) (S:=S) σ t (fun z hz h => near_zero_in_band χ l t M ht hz h)
  have hw := window_bin_bound hX ha hab hb (by linarith : 0 ≤ σ) (by linarith : σ ≤ 1) hV (hgrid t ht).1 hJ
  have hsum := localPotential_nonneg Z σ t
  have h1 := (mul_le_mul (mul_le_mul_of_nonneg_left hl hA) (add_le_add_right hloc 1)
    (by linarith : 0 ≤ 1+localZeroPotential Z σ t) (by positivity)).trans' hh
  change ‖contourLog χ (line σ t)*transform a b β (line σ t)‖ ≤ _
  rw [norm_mul]
  have wn : 0 ≤ ∑ z ∈ S,rootKernel (σ-z.re)*rootKernel (t-z.im) :=
    Finset.sum_nonneg fun z _ => mul_nonneg (rootKernel_nonneg _) (rootKernel_nonneg _)
  exact (mul_le_mul h1 hw (norm_nonneg _) (by positivity)).trans_eq (by ring)

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter Finset
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

theorem averaged_vertical {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1/8) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M J : ℕ)
      (a b X β : ℝ), 1 ≤ X → X ≤ a → a+1 ≤ b → b+1 ≤ 2*X → 4 * |β| * X ≤ J →
      ∃ σ ∈ Ioo (1/2+d) (1/2+2*d), (∀ z ∈ boxZeros χ (1/2) 2 (-(M:ℝ)-1) ((M:ℝ)+1), σ ≠ z.re) ∧
        (∫ t : ℝ in -(M:ℝ)..(M:ℝ), ‖integrand χ a b β (line σ t)‖) ≤
          C*X^(1/2+2*d)*(logHeight q ((M:ℝ)+2))^2*
            (1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (M+1:ℝ))) := by
  classical
  obtain ⟨A,hA,logbound⟩ := log_control_via_potential hd
  obtain ⟨K,hK,cardbound⟩ := bandZeros_card
  let D := Real.sqrt d
  have hD : 0 < D := Real.sqrt_pos.mpr hd
  let C := 2*A*(1+16*K/D)
  have hC : 0 < C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  intro q _ χ M J a b X β hX ha hab hb hJ
  let u : ℝ := 1/2+d
  let v : ℝ := 1/2+2*d
  let L := logHeight q ((M:ℝ)+2)
  have hL : 1 ≤ L := logHeight_ge_one q _
  let Z := boxZeros χ (1/2) 2 (-(M:ℝ)-1) ((M:ℝ)+1)
  let S := fun p : Bool × ℕ => bandZeros χ (gridStart p)
  let w := fun p : Bool × ℕ => profile J p.2
  have hw (p : Bool × ℕ) (_ : p ∈ grid M) : 0 ≤ w p := profile_nonneg _ _
  have card (p : Bool × ℕ) (hp : p ∈ grid M) : ((S p).card:ℝ) ≤ K*L :=
    cardbound q χ (gridStart p) M (grid_geometry hp).1
  obtain ⟨σ,hσ,bad,avg⟩ := exists_cluster_average (grid M) S w hw (Z.image Complex.re)
    (by dsimp [u,v];linarith : u<v) card
  have hdiff : v-u=d := by dsimp [u,v];ring
  rw [hdiff] at avg
  have avoid (z : ℂ) (hz : z ∈ Z) : σ ≠ z.re := fun he => bad (Finset.mem_image.mpr ⟨z,hz,he.symm⟩)
  refine ⟨σ,hσ,avoid,?_⟩
  let V (t : ℝ) := ‖integrand χ a b β (line σ t)‖
  have hlo : 1/2+d ≤ σ := hσ.1.le
  have hup : σ ≤ 3/4 := by dsimp [v] at hσ;linarith [hσ.2]
  have cont := (integrable_box_line (a:=a) (b:=b) (β:=β) χ (by linarith : 1/2 ≤ σ) hup
    (zero_lt_one.trans_le (hX.trans ha)) avoid).norm
  have int (p : Bool × ℕ) (hp : p ∈ grid M) : IntervalIntegrable V volume (gridStart p) (gridStart p+1) :=
    (cont.mono fun t ht => abs_le.mp ((grid_geometry hp).2 t ht).2).intervalIntegrable_of_Icc (by linarith)
  have hlocal (p : Bool × ℕ) (hp : p ∈ grid M) :
      (∫ t in gridStart p..gridStart p+1,V t) ≤ (A*L*X^v)*
        (w p*(1+4*∑ z ∈ S p,rootKernel (σ-z.re))) := by
    have h := local_band_norm χ p.2 J hd hA.le hX ha hab hb hlo hup hσ.2.le hJ (grid_geometry hp).2
      avoid (fun t ht yt => logbound q χ σ t M hlo hup ht avoid yt)
    exact h.trans_eq (by dsimp [w,L,S];ring)
  have profileBound := profile_sum J M
  have prof : (∑ j ∈ range M,profile J j) ≤ 1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (M+1:ℝ)) :=
    (sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_succ M)) (fun i _ _ => profile_nonneg _ _)).trans profileBound
  have wsum : (∑ p ∈ grid M,w p) = 2*∑ j ∈ range M,profile J j := sum_grid_weight M (profile J)
  rw [wsum] at avg
  have hn := Finset.sum_nonneg (s:=range M) (fun i _ => profile_nonneg J i)
  have hvX : 0 ≤ X^v := Real.rpow_nonneg (by linarith) _
  have factor : 1+16*(K*L)/Real.sqrt d ≤ (1+16*K/D)*L := by dsimp [D]; simp only [div_eq_mul_inv]; nlinarith only [hL]
  have bound' := avg.trans (mul_le_mul factor (mul_le_mul_of_nonneg_left prof (by norm_num : (0:ℝ)≤2))
    (by positivity) (by positivity))
  change (∫ t in -(M:ℝ)..(M:ℝ), V t) ≤ _
  rw [sum_grid_integrals V int]
  have total := Finset.sum_le_sum hlocal
  rw [←Finset.mul_sum] at total
  exact (total.trans (mul_le_mul_of_nonneg_left bound' (by positivity))).trans_eq (by dsimp [C,v,L];ring)

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter GoldbachSmoothing
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

/-- With a suitable contour the signed zero residues account for every term larger
than the square-root window error and the finite-height truncation error. -/
theorem unconditional_zero_model {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1/8) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (B : ℝ)
      (M J a b : ℕ) (X β : ℝ), 2 ≤ B → B+1 ≤ (M:ℝ) →
      1 ≤ X → X ≤ (a:ℝ) → (a:ℝ)+1 ≤ b → (b:ℝ)+1 ≤ 2*X → |β| ≤ 1 → 4*|β| *X ≤ J →
      ∃ T ∈ Icc B (B+1), ∃ σ ∈ Ioo (1/2+d) (1/2+2*d),
        ‖(∑ n ∈ Finset.Ioc a b, twistedCoefficient χ n * phase β n) -
          (principalFlag χ*transform a b β 1 - zeroContribution χ a b β σ T)‖ ≤
        C*(X^(1/2+2*d)*(logHeight q ((M:ℝ)+2))^2*
           (1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (M+1:ℝ))) +
           X^4*(T⁻¹ + (logHeight q ((M:ℝ)+2))^2/T^2)) := by
  classical
  obtain ⟨A,hA,horiz⟩ := unconditional_horizontal_log hd
  obtain ⟨K,hK,tail⟩ := truncation_bound
  obtain ⟨D,hD,vertical⟩ := averaged_vertical hd hd'
  let c : ℝ := 1/(2*Real.pi)
  have hc : 0 < c := by dsimp [c];positivity
  let C := max (c*D) (max K (c*(2*(2*A*96))))
  have cv : c*D ≤ C := le_max_left ..
  have ct : K ≤ C := (le_max_left ..).trans (le_max_right ..)
  have ch : c*(2*(2*A*96)) ≤ C := (le_max_right ..).trans (le_max_right ..)
  refine ⟨C,hK.trans_le ct,?_⟩
  intro q _ χ B M J a b X β hB hBM hX ha hab hb hβ hJ
  obtain ⟨T,hTB,avoid,hlog⟩ := horiz q χ B hB
  obtain ⟨σ,hσ,avoidR,hV⟩ := vertical q χ M J a b X β hX ha hab hb hJ
  have hT : 0 < T := by linarith [hTB.1]
  have hTM : T ≤ (M:ℝ) := hTB.2.trans hBM
  have hs : σ < 1 := by linarith [hσ.2]
  have inner (z : ℂ) (hz : z ∈ boxZeros χ σ 2 (-T) T) : σ < z.re ∧ z.re < 2 ∧ -T < z.im ∧ z.im < T := by
    obtain ⟨h,z0⟩ := (mem_boxZeros χ _ _ _ _ z).mp hz
    obtain ⟨⟨hr,hr'⟩,hi,hi'⟩ := mem_reProdIm.mp h
    have hzZ : z ∈ boxZeros χ (1/2) 2 (-(M:ℝ)-1) ((M:ℝ)+1) := (mem_boxZeros χ _ _ _ _ z).mpr
      ⟨mem_reProdIm.mpr ⟨⟨by linarith [hσ.1],hr'⟩,by constructor <;> linarith⟩,z0⟩
    have him := avoid z (by linarith [hσ.1]) z0
    refine ⟨lt_of_le_of_ne hr (avoidR z hzZ),lt_of_le_of_ne hr' ?_,lt_of_le_of_ne hi ?_,lt_of_le_of_ne hi' ?_⟩
    · intro e;exact regularizedL_ne_zero_right χ (by rw [e];norm_num) z0
    · intro e;exact him (by rw [←e,abs_neg,abs_of_pos hT])
    · intro e;exact him (by rw [e,abs_of_pos hT])
  refine ⟨T,hTB,σ,hσ,?_⟩
  let F := integrand χ a b β
  let H (t : ℝ) := ∫ x : ℝ in σ..2, F (line x t)
  let V := ∫ t : ℝ in (-T)..T, F (line σ t)
  let R := truncationRemainder χ a b β T
  let L := logHeight q ((M:ℝ)+2)
  let P := 1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (M+1:ℝ))
  let U := X^(1/2+2*d)*L^2*P
  have logpos : 0 ≤ Real.log (M+1:ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) M])
  have hU : 0 ≤ U := by dsimp [U,P];positivity
  have hcomp : logHeight q (B+1) ≤ L := by
    apply logHeight_mono_abs
    rw [abs_of_nonneg (by linarith : 0≤B+1),abs_of_nonneg (by positivity : 0≤(M:ℝ)+2)]
    linarith
  have hH := @horizontal_edge_bound d σ T B A X β q _ χ a b hX ha hab hb hβ hd hσ.1.le hs hT hA.le hlog
  have ho (t : ℝ) (ht : |t|=T) : ‖H t‖ ≤ (2*A*96)*X^4*L^2/T^2 := by
    apply (hH ht).trans
    gcongr
    exact (zero_le_one.trans (logHeight_ge_one q (B+1)))
  have hlo := ho (-T) (by simp [abs_of_pos hT])
  have hhi := ho T (abs_of_pos hT)
  have hR := tail q χ a b X β T hX ha hab hb hβ hT
  have hi := (integrable_box_line (a:=(a:ℝ)) (b:=(b:ℝ)) (β:=β) χ (by linarith [hσ.1] : 1/2 ≤ σ)
    (by linarith [hσ.2] : σ ≤ 3/4) (zero_lt_one.trans_le (hX.trans ha)) avoidR).norm
  have hsmall : ‖V‖ ≤ ∫ t in (-T)..T, ‖F (line σ t)‖ := by
    dsimp only [V]
    rw [intervalIntegral.integral_of_le (by linarith : -T≤T),intervalIntegral.integral_of_le (by linarith : -T≤T)]
    exact norm_integral_le_integral_norm _
  have hlarge : (∫ t in (-T)..T, ‖F (line σ t)‖) ≤ ∫ t in -(M:ℝ)..(M:ℝ), ‖F (line σ t)‖ := intervalIntegral.integral_mono_interval (neg_le_neg hTM) (by linarith : -T≤T) hTM
    (ae_of_all _ (fun t => norm_nonneg (F (line σ t)))) (hi.intervalIntegrable_of_Icc (by linarith))
  have hvert : c*‖V‖ ≤ C*U := by
    calc
      _ ≤ c*(D*U) := mul_le_mul_of_nonneg_left ((hsmall.trans hlarge).trans (hV.trans_eq (by dsimp [U,P,L];ring))) hc.le
      _ ≤ C*U := by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right cv hU
  have hedge : c*‖H (-T)-H T‖ ≤ C*(X^4*(L^2/T^2)) := by
    calc
      _ ≤ c*(((2*A*96)*X^4*L^2/T^2)+((2*A*96)*X^4*L^2/T^2)) :=
        mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add hlo hhi)) hc.le
      _ = (c*(2*(2*A*96)))*(X^4*(L^2/T^2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ch (by positivity)
  have htrunc : ‖R‖ ≤ C*(X^4*T⁻¹) := by
    apply hR.trans
    calc
      _ = K*(X^4*T⁻¹) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ct (by positivity)
  rw [exact_twisted_box χ hX ha hab hb hβ hs hT inner]
  unfold contourRemainder
  change ‖_ + c • (V + I*(H (-T) - H T)) + R - _‖ ≤ _
  have cancel (p l r : ℂ) : p+l+r-p=l+r := by abel
  rw [cancel,smul_add]
  apply (norm_add_le _ _).trans
  apply (add_le_add_left (norm_add_le _ _) _).trans
  rw [norm_smul,norm_smul,norm_mul,norm_I,one_mul,Real.norm_eq_abs,abs_of_pos hc]
  exact (add_le_add (add_le_add hvert hedge) htrunc).trans_eq (by dsimp [U,P,L];ring)
end GoldbachTwistedMellin
end
end

section
open Set Complex Goldbach DirichletCharacter GoldbachSmoothing
noncomputable section
namespace GoldbachTwistedMellin

/-- At a polynomial height the two tails are absorbed by the oscillatory window bound. -/
theorem dyadic_zero_model {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1/8) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (a b : ℕ) (X β : ℝ), 1 ≤ X → X ≤ (a:ℝ) → (a:ℝ)+1 ≤ b → (b:ℝ)+1 ≤ 2*X → |β| ≤ 1 →
      ∃ T ∈ Icc (heightCut X) (heightCut X+1), ∃ σ ∈ Ioo (1/2+d) (1/2+2*d),
        ‖(∑ n ∈ Finset.Ioc a b, twistedCoefficient χ n * phase β n) -
          (principalFlag χ*transform a b β 1 - zeroContribution χ a b β σ T)‖ ≤
        C*X^(1/2+2*d)*(logBudget q X)^2*
           (1+Real.sqrt (1+4*|β| *X)+Real.log (heightCut X)) := by
  obtain ⟨C,hC,model⟩ := unconditional_zero_model hd hd'
  refine ⟨1000*C,by positivity,?_⟩
  intro q _ χ a b X β hX ha hab hb hβ
  let B := heightCut X
  let M := ⌈B+1⌉₊
  let J := ⌈4*|β| *X⌉₊
  have hB : 2 ≤ B := by dsimp [B];linarith [heightCut_ge hX]
  have hB0 : 0 < B := by linarith
  have hM : B+1 ≤ (M:ℝ) := Nat.le_ceil _
  have hJ : 4*|β| *X ≤ (J:ℝ) := Nat.le_ceil _
  have hM' : (M:ℝ) < B+1+1 := Nat.ceil_lt_add_one (by linarith)
  have hJ' : (J:ℝ) < 4*|β| *X+1 := Nat.ceil_lt_add_one (by positivity)
  obtain ⟨T,hT,σ,hσ,err⟩ := model q χ B M J a b X β hB hM hX ha hab hb hβ hJ
  refine ⟨T,hT,σ,hσ,err.trans ?_⟩
  let L := logBudget q X
  let W := 1+Real.sqrt (1+4*|β| *X)+Real.log B
  let S := X^(1/2+2*d)
  have hS : 1 ≤ S := Real.one_le_rpow hX (by linarith)
  have hL : 1 ≤ L := by dsimp [L,logBudget];linarith [logHeight_ge_one q (heightCut X)]
  have hln := Real.log_nonneg (by linarith : 1≤B)
  have hW : 1 ≤ W := by dsimp [W];linarith [Real.sqrt_nonneg (1+4*|β| *X)]
  have hq : 0 < (q:ℝ) := by exact_mod_cast NeZero.pos q
  have h3 := Real.log_le_sub_one_of_pos (by norm_num : 0<(3:ℝ))
  have hlogM : Real.log (M+1:ℝ) ≤ 2+Real.log B := by
    have h := Real.log_le_log (by positivity : 0 < (M:ℝ)+1) (by linarith : (M:ℝ)+1 ≤ 3*B)
    rw [Real.log_mul (by norm_num) hB0.ne'] at h
    linarith
  have hlogL : logHeight q ((M:ℝ)+2) ≤ 3*L := by
    have h : Real.log (2*(q:ℝ)*(2+((M:ℝ)+2))) ≤ Real.log (3*(2*(q:ℝ)*(2+B))) :=
      Real.log_le_log (by positivity) (by nlinarith only [mul_le_mul_of_nonneg_left (by linarith : 2+((M:ℝ)+2) ≤ 3*(2+B)) (by positivity : 0 ≤ 2*(q:ℝ))])
    rw [Real.log_mul (by norm_num : (3:ℝ)≠0) (by positivity)] at h
    change Real.log (2*(q:ℝ)*(2+|(M:ℝ)+2|)) ≤ 3*(1+Real.log (2*(q:ℝ)*(2+|B|)))
    rw [abs_of_nonneg (by positivity : 0≤(M:ℝ)+2),abs_of_pos hB0]
    have hl := logHeight_ge_one q B
    change 1 ≤ Real.log (2*(q:ℝ)*(2+|B|)) at hl
    rw [abs_of_pos hB0] at hl
    linarith
  have hlsq : (logHeight q ((M:ℝ)+2))^2 ≤ 9*L^2 :=
    (pow_le_pow_left₀ (zero_le_one.trans (logHeight_ge_one q _)) hlogL 2).trans_eq (by ring)
  have hroot : Real.sqrt J ≤ Real.sqrt (1+4*|β| *X) := Real.sqrt_le_sqrt (by linarith)
  have hp : (1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (M+1:ℝ))) ≤ 100*W := by
    dsimp [W]
    nlinarith only [hlogM,hln,hroot,Real.sqrt_nonneg (1+4*|β| *X),
      mul_le_mul_of_nonneg_right Real.pi_lt_four.le (Real.sqrt_nonneg (J:ℝ))]
  have hp0 : 0 ≤ 1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (M+1:ℝ)) := by
    have := Real.log_nonneg (show 1≤(M:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) M])
    positivity
  have hvert := mul_le_mul (mul_le_mul_of_nonneg_left hlsq (zero_le_one.trans hS)) hp hp0 (by positivity : 0 ≤ S*(9*L^2))
  have hXT : X^4 ≤ T := by
    have hx := pow_le_pow_right₀ hX (show 4 ≤ 8 by decide)
    have h : X^8 ≤ B := by dsimp [B,heightCut];rw [mul_pow];norm_num;linarith [pow_nonneg (by linarith : 0≤X) 8]
    exact hx.trans (h.trans hT.1)
  have hT1 : 1 ≤ T := by linarith [hT.1]
  have hT0 : 0 < T := by linarith
  have ht₁ : X^4*T⁻¹ ≤ 1 := by rw [←div_eq_mul_inv];exact (div_le_one hT0).mpr hXT
  have ht₂ : X^4/T^2 ≤ 1 := (div_le_one (sq_pos_of_pos hT0)).mpr (hXT.trans (le_self_pow₀ hT1 (by decide)))
  have htail : X^4*(T⁻¹+(logHeight q ((M:ℝ)+2))^2/T^2) ≤ 1+9*L^2 := by
    calc
      _ = X^4*T⁻¹+(X^4/T^2)*(logHeight q ((M:ℝ)+2))^2 := by ring
      _ ≤ 1+1*(9*L^2) := add_le_add ht₁ (mul_le_mul ht₂ hlsq (sq_nonneg _) zero_le_one)
      _ = _ := by ring
  have hL₂ : 1 ≤ L^2 := one_le_pow₀ hL
  have hprod : L^2 ≤ S*L^2*W := (le_mul_of_one_le_left (sq_nonneg L) hS).trans
    (le_mul_of_one_le_right (by positivity) hW)
  have hall : S*(logHeight q ((M:ℝ)+2))^2*(1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (M+1:ℝ)))+
      X^4*(T⁻¹+(logHeight q ((M:ℝ)+2))^2/T^2) ≤ 1000*(S*L^2*W) := by
    nlinarith only [hvert,htail,hL₂,hprod]
  exact (mul_le_mul_of_nonneg_left hall hC.le).trans_eq (by dsimp [S,L,W,B];ring)
end GoldbachTwistedMellin
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


end GoldbachTwistedMellin
end
end

section
open Finset Complex GoldbachGRHWindow
noncomputable section
namespace GoldbachTwistedMellin

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
open Finset Complex GoldbachGRHWindow
open scoped ComplexConjugate
noncomputable section
namespace GoldbachTwistedMellin
variable {q : ℕ} [NeZero q]

/-- Fourier coefficient of the additive phase on the group of units. -/
noncomputable def additiveWeight (a : ZMod q) (χ : DirichletCharacter ℂ q) : ℂ :=
  conj (∑ r : ZMod q, conj (ZMod.stdAddChar (a*r))*χ r) / (q.totient:ℂ)

theorem weight_expansion (a : ZMod q) (χ : DirichletCharacter ℂ q) :
    additiveWeight a χ = (∑ r : ZMod q, ZMod.stdAddChar (a*r)*conj (χ r))/(q.totient:ℂ) := by
  simp [additiveWeight,map_sum]

private theorem units_filter (F : ZMod q → ℂ) :
    (∑ r : ZMod q, if IsUnit r then F r else 0) = ∑ u : (ZMod q)ˣ, F u := by
  classical
  rw [← Finset.sum_filter]
  have hs : (univ : Finset (ZMod q)).filter IsUnit = (univ : Finset (ZMod q)ˣ).map ⟨(↑), Units.val_injective⟩ := by
    ext r
    simp [IsUnit]
  rw [hs, Finset.sum_map]
  rfl

theorem additiveWeight_one (a : ZMod q) : additiveWeight a 1 = additiveModel q a := by
  classical
  rw [weight_expansion,additiveModel]
  congr 1
  rw [← units_filter (fun r : ZMod q => ZMod.stdAddChar (a*r))]
  refine sum_congr rfl fun r _ => ?_
  by_cases hr : IsUnit r
  · simp [MulChar.one_apply,hr]
  · simp [MulChar.map_nonunit _ hr,hr]

theorem additiveWeight_inversion (a s : ZMod q) :
    (∑ χ : DirichletCharacter ℂ q, additiveWeight a χ * χ s) =
      (if IsUnit s then ZMod.stdAddChar (a*s) else 0) := by
  classical
  have orth (r : ZMod q) : (∑ χ : DirichletCharacter ℂ q, conj (χ r)*χ s) =
      if r=s ∧ IsUnit s then (q.totient:ℂ) else 0 := by
    by_cases hr : IsUnit r
    · have inv (χ : DirichletCharacter ℂ q) : conj (χ r) = χ r⁻¹ := by
        have hχr : χ r ≠ 0 := (hr.map χ).ne_zero
        have hi : χ r⁻¹ = (χ r)⁻¹ := by
          calc
            _ = χ r⁻¹ * (χ r * (χ r)⁻¹) := by rw [mul_inv_cancel₀ hχr,mul_one]
            _ = _ := by rw [←mul_assoc,←map_mul,ZMod.inv_mul_of_unit r hr,map_one,one_mul]
        exact (MulChar.star_apply' χ r).trans ((MulChar.inv_apply_eq_inv' χ r).trans hi.symm)
      simp_rw [inv]
      rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hr s]
      by_cases h : r=s
      · subst s;simp [hr]
      · simp [h]
    · simp only [MulChar.map_nonunit _ hr,map_zero,zero_mul,sum_const_zero]
      split_ifs with h
      · exact False.elim (hr (h.1.symm ▸ h.2))
      · rfl
  have hφ : (q.totient:ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  calc
    _ = (∑ r : ZMod q, ZMod.stdAddChar (a*r)*(∑ χ : DirichletCharacter ℂ q, conj (χ r)*χ s))/(q.totient:ℂ) := by
      simp_rw [weight_expansion,div_mul_eq_mul_div,Finset.sum_mul,Finset.mul_sum,mul_assoc]
      rw [←Finset.sum_div,Finset.sum_comm]
    _ = _ := by
      simp_rw [orth]
      by_cases hs : IsUnit s
      · simp [hs,mul_ite,hφ]
      · simp [hs]

theorem sum_norm_additiveWeight_le (a : ZMod q) :
    (∑ χ : DirichletCharacter ℂ q, ‖additiveWeight a χ‖) ≤ Real.sqrt q := by
  classical
  let V : Finset (ZMod q) := univ.filter IsUnit
  have hφ : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have card : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [←Nat.card_eq_fintype_card];exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have cV : (V.card:ℝ) ≤ q := by
    exact_mod_cast (V.card_le_univ.trans_eq (ZMod.card q))
  have energy : (∑ χ : DirichletCharacter ℂ q, ‖additiveWeight a χ‖^2) = (V.card:ℝ)/(q.totient:ℝ) := by
    simp only [additiveWeight,norm_div,norm_conj,Complex.norm_natCast,div_pow,←Finset.sum_div]
    rw [multiplicative_energy]
    simp only [norm_conj,ZMod.stdAddChar_apply,Circle.norm_coe,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one]
    change (q.totient:ℝ)*(V.card:ℝ)/(q.totient:ℝ)^2 = _
    field_simp
  have raw := sq_sum_le_card_mul_sum_sq (s:=(univ:Finset (DirichletCharacter ℂ q))) (f:=fun χ => ‖additiveWeight a χ‖)
  rw [Finset.card_univ,card,energy] at raw
  have count : (q.totient:ℝ)*((V.card:ℝ)/(q.totient:ℝ)) = V.card := by field_simp
  rw [count] at raw
  exact (Real.le_sqrt (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Nat.cast_nonneg q)).mpr (raw.trans cV)
end GoldbachTwistedMellin
end
end

section
open Finset Complex Goldbach GoldbachSmoothing GoldbachGRHWindow
noncomputable section
namespace GoldbachTwistedMellin
variable {q : ℕ} [NeZero q]

/-- Inverting the unit characters leaves exactly the nonunit terms. -/
theorem sum_character_transfer (I : Finset ℕ) (w : ℕ → ℂ) (a : ZMod q) :
    (∑ k ∈ I, w k*ZMod.stdAddChar (a*(k:ZMod q))) =
      (∑ χ : DirichletCharacter ℂ q, additiveWeight a χ*(∑ k ∈ I,w k*χ (k:ZMod q))) +
      ∑ k ∈ I.filter (fun k : ℕ => ¬IsUnit (k:ZMod q)), w k*ZMod.stdAddChar (a*(k:ZMod q)) := by
  classical
  rw [Finset.sum_filter]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm,←Finset.sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  have h := congrArg (w k * ·) (additiveWeight_inversion a (k:ZMod q))
  simp only [Finset.mul_sum] at h
  simp_rw [mul_left_comm (additiveWeight a _) (w k)]
  rw [h]
  by_cases hk : IsUnit (k:ZMod q) <;> simp [hk]

theorem signed_dyadic_transfer (r : ZMod q) {a b n : ℕ} {β B : ℝ}
    (hb : b ≤ n) (hn : 1 ≤ n) (ha : 0 < a) (hab : a+1≤b) (hB : 0≤B)
    (Z : DirichletCharacter ℂ q → ℂ)
    (hchr : ∀ χ : DirichletCharacter ℂ q,
      ‖(∑ k ∈ Finset.Ioc a b,twistedCoefficient χ k*phase β k) -
        (principalFlag χ*transform a b β 1 - Z χ)‖ ≤ B) :
    ‖(∑ k ∈ Finset.Ioc a b,primeError r β k) + ∑ χ : DirichletCharacter ℂ q,additiveWeight r χ*Z χ‖ ≤
      Real.sqrt q*(2*Real.sqrt n*Real.log n+B+((b:ℝ)-a)*|β|+Real.log q) := by
  classical
  let I := Finset.Ioc a b
  let w := fun k : ℕ => primeLog k*phase β k
  let S := ∑ k ∈ I,phase β k
  let P := fun χ : DirichletCharacter ℂ q => ∑ k ∈ I,w k*χ (k:ZMod q)
  let e := fun χ : DirichletCharacter ℂ q => P χ - (if χ=1 then S else 0) + Z χ
  let E := 2*Real.sqrt n*Real.log n+B+((b:ℝ)-a)*|β|
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have habR : (a:ℝ) ≤ b := by exact_mod_cast (show a≤b by omega)
  have hE : 0 ≤ E := by dsimp [E];have := Real.log_nonneg hnR;have := sub_nonneg.mpr habR;positivity
  have hev (χ : DirichletCharacter ℂ q) : ‖e χ‖ ≤ E := by
    let L := ∑ k ∈ I, twistedCoefficient χ k * phase β k
    let M := principalFlag χ * transform a b β 1
    have hm : ‖M-(if χ=1 then S else 0)‖ ≤ ((b:ℝ)-a)*|β| := by
      by_cases h : χ=1
      · simpa [M,S,I,principalFlag,h] using principal_approx ha hab β
      · simpa [M,principalFlag,h] using mul_nonneg (sub_nonneg.mpr habR) (abs_nonneg β)
    have he : e χ = ((P χ-L)+(L-(M-Z χ)))+(M-(if χ=1 then S else 0)) := by dsimp [e];abel
    rw [he]
    exact (norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans
      (add_le_add (prime_removal χ a b n hb hn β) (hchr χ))) hm)
  let D := ∑ k ∈ I.filter (fun k : ℕ => ¬IsUnit (k:ZMod q)), w k*ZMod.stdAddChar (r*(k:ZMod q))
  have hnunit : ‖D‖ ≤ Real.log q := by
    apply (norm_sum_le ..).trans
    simpa [I,w,norm_mul,norm_phase,ZMod.stdAddChar_apply] using primeLog_nonunit_mass_le (q:=q) I
  have hsingle : (∑ χ : DirichletCharacter ℂ q, additiveWeight r χ*(if χ=1 then S else 0)) = S*additiveModel q r := by
    simp [mul_ite,additiveWeight_one,mul_comm]
  have heq : (∑ k ∈ I,primeError r β k) + ∑ χ : DirichletCharacter ℂ q,additiveWeight r χ*Z χ =
      (∑ χ : DirichletCharacter ℂ q, additiveWeight r χ*e χ)+D := by
    dsimp only [I]
    rw [sum_primeError,sum_character_transfer]
    simp only [e,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,hsingle]
    dsimp [I,P,S,D,w]
    abel
  change ‖(∑ k ∈ I,primeError r β k)+_‖ ≤ _
  rw [heq]
  have hsum : ‖∑ χ : DirichletCharacter ℂ q, additiveWeight r χ*e χ‖ ≤ Real.sqrt q*E := by
    apply (norm_sum_le ..).trans
    simp only [norm_mul]
    calc
      _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖additiveWeight r χ‖*E := by
        apply sum_le_sum;intro χ _;exact mul_le_mul_of_nonneg_left (hev χ) (norm_nonneg _)
      _ ≤ _ := by rw [←Finset.sum_mul];exact mul_le_mul_of_nonneg_right (sum_norm_additiveWeight_le r) hE
  have hq : 1 ≤ (q:ℝ) := by exact_mod_cast NeZero.pos q
  have hs : 1 ≤ Real.sqrt q := by simpa using Real.sqrt_le_sqrt hq
  apply (norm_add_le ..).trans
  exact (add_le_add hsum hnunit).trans (by
    change Real.sqrt q*E+Real.log q ≤ Real.sqrt q*(E+Real.log q)
    calc
      _ ≤ Real.sqrt q*E + Real.sqrt q*Real.log q := add_le_add le_rfl (le_mul_of_one_le_left (Real.log_nonneg hq) hs)
      _ = _ := by ring)
end GoldbachTwistedMellin
end
end

section
open Finset
noncomputable section
namespace GoldbachTwistedMellin

/-- The ordered disjoint blocks covering the integers up to m+2 after the base interval. The first at most
three integers are left in the base estimate. -/
def prefixBlocks (m : ℕ) : List (ℕ × ℕ) :=
  if h : m < 2 then [] else (m/2+2,m+2)::prefixBlocks (m/2)
termination_by m
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem prefixBlocks_valid {m : ℕ} {p : ℕ × ℕ} (hp : p ∈ prefixBlocks m) :
    1 ≤ p.1 ∧ p.1+1 ≤ p.2 ∧ p.2+1 ≤ 2*p.1 ∧ p.2 ≤ m+2 := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    rw [prefixBlocks] at hp
    split_ifs at hp with h
    · simp at hp
    rcases List.mem_cons.mp hp with h|h
    · subst p;dsimp;omega
    · obtain ⟨a,b,c,e⟩ := ih (m/2) (Nat.div_lt_self (by omega) (by decide)) h
      exact ⟨a,b,c,by omega⟩

/-- Attach a complex correction to each block before estimating the full sum. -/
theorem dyadic_prefix_corrected (f : ℕ → ℂ) (z : ℕ × ℕ → ℂ) (n : ℕ) (hn : 2 ≤ n) (D : ℝ)
    (base : ∀ k : ℕ, k ≤ 3 → ‖∑ j ∈ Finset.Ioc 0 k,f j‖ ≤ D)
    (block : ∀ p ∈ prefixBlocks (n-2), ‖(∑ k ∈ Finset.Ioc p.1 p.2,f k)+z p‖ ≤ D) :
    ‖(∑ k ∈ Finset.Ioc 0 n,f k) + ((prefixBlocks (n-2)).map z).sum‖ ≤ ((Nat.log 2 (n-2):ℝ)+1)*D := by
  have h (m : ℕ) (sub : ∀ p ∈ prefixBlocks m,p ∈ prefixBlocks (n-2)) :
      ‖(∑ k ∈ Finset.Ioc 0 (m+2),f k) + ((prefixBlocks m).map z).sum‖ ≤ ((Nat.log 2 m:ℝ)+1)*D := by
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      by_cases hsmall : m<2
      · rw [prefixBlocks,dite_eq_left hsmall,Nat.log_of_lt hsmall]
        simpa using base (m+2) (by omega)
      · have hpos : 2 ≤ m := by omega
        let p := (m/2+2,m+2)
        have eqs : prefixBlocks m = p::prefixBlocks (m/2) := by rw [prefixBlocks,dite_eq_right hsmall]
        have hsm := ih (m/2) (Nat.div_lt_self (by omega) (by decide)) (fun i hi => sub i (by rw [eqs];exact List.mem_cons_of_mem _ hi))
        have hlg := block p (sub p (by rw [eqs];exact List.mem_cons_self))
        rw [eqs,List.map_cons,List.sum_cons,←Finset.sum_Ioc_consecutive f (Nat.zero_le (m/2+2)) (by omega : m/2+2 ≤ m+2)]
        have a : ∀ x y u v : ℂ, x+y+(u+v) = (x+v)+(y+u) := by intros;abel
        rw [a]
        exact (norm_add_le ..).trans ((add_le_add hsm hlg).trans_eq (by
          rw [Nat.log_of_one_lt_of_le (by decide : 1<2) hpos];push_cast;ring))
  simpa [Nat.sub_add_cancel hn] using h (n-2) (fun _ hp => hp)
end GoldbachTwistedMellin
end
end

section
open Finset Complex Goldbach GoldbachSmoothing GoldbachGRHWindow DeepThreeQuarters
noncomputable section
namespace GoldbachTwistedMellin

/-- The extra logarithm in the unconditional contour bound costs one extra
logarithm on the rational arc, uniformly in its denominator and numerator. -/
theorem signed_block_budget {n l r q : ℕ} [NeZero q] (v : ZMod q) {d C γ : ℝ}
    (hn : 1 ≤ n) (hl : 1 ≤ l) (hlr : l+1≤r) (hrn : r≤n)
    (hd : 0≤d) (hC : 0≤C) (hqs : (q:ℝ)≤Real.sqrt n)
    (hγq : (q:ℝ)*|γ| *(n:ℝ) ≤ 8*Real.sqrt n)
    (Z : DirichletCharacter ℂ q → ℂ)
    (model : ∀ χ : DirichletCharacter ℂ q,
      ‖(∑ k ∈ Finset.Ioc l r,twistedCoefficient χ k*phase γ k) -
        (principalFlag χ*transform l r γ 1 - Z χ)‖ ≤
      C*(l:ℝ)^(1/2+d)*(logBudget q l)^2*(1+Real.sqrt (1+4*|γ| *l)+Real.log (heightCut l))) :
    ‖(∑ k ∈ Finset.Ioc l r,primeError v γ k) + ∑ χ : DirichletCharacter ℂ q,additiveWeight v χ*Z χ‖ ≤
      (12+1700*C)*(n:ℝ)^(3/4+d)*logScale n^3 := by
  let L := logScale n
  let S := (n:ℝ)^(3/4+d)
  let W := 1+Real.sqrt (1+4*|γ| *l)+Real.log (heightCut l)
  have hx : 1 ≤ (l:ℝ) := by exact_mod_cast hl
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hxn : (l:ℝ) ≤ n := by exact_mod_cast (show l≤n by omega)
  have hL : 1 ≤ L := logScale_one hnR
  have hp : 0 ≤ (l:ℝ)^(1/2+d) := Real.rpow_nonneg (by positivity) _
  have hT : 1 ≤ heightCut l := by linarith [heightCut_ge hx]
  have hW : 0 ≤ W := by dsimp [W];linarith only [Real.sqrt_nonneg (1+4*|γ| *l),Real.log_nonneg hT]
  have hbudget : 0≤logBudget q l := by dsimp [logBudget];linarith only [logHeight_ge_one q (heightCut l)]
  have hB := (log_window_scale hx hxn (hqs.trans (Real.sqrt_le_self_iff.mpr (Or.inr hnR)))).1
  let C' := 10*C*L
  have hC' : 0 ≤ C' := by dsimp [C'];positivity
  let R := C'*(l:ℝ)^(1/2+d)*logBudget q l*W
  have hR : 0 ≤ R := by dsimp [R];positivity
  have hres (χ : DirichletCharacter ℂ q) := (model χ).trans (show _ ≤ R from by
    calc
      C*(l:ℝ)^(1/2+d)*(logBudget q l)^2*W =
        (C*(l:ℝ)^(1/2+d)*logBudget q l*W)*logBudget q l := by ring
      _ ≤ (C*(l:ℝ)^(1/2+d)*logBudget q l*W)*(10*L) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = R := by dsimp [R,C'];ring)
  have m := signed_dyadic_transfer v hrn hn hl hlr hR Z hres
  have raw := block_budget hx hxn hd hC' hqs hγq
  have he := mul_le_mul_of_nonneg_right (by linarith [show (r:ℝ)≤n by exact_mod_cast hrn, Nat.cast_nonneg (α:=ℝ) l] : (r:ℝ)-l ≤ n) (abs_nonneg γ)
  have comp : Real.sqrt q*(2*Real.sqrt n*Real.log n+R+((r:ℝ)-l)*|γ|+Real.log q) ≤
        (12+170*C')*S*L^2 := by
    apply le_trans _ raw
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg q)
    dsimp only [R,W];linarith only [he]
  have hS : 0≤S := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have mul := mul_le_mul_of_nonneg_right hL (mul_nonneg hS (sq_nonneg L))
  exact (m.trans comp).trans (by dsimp only [C',S,L] at *;nlinarith only [mul])
end GoldbachTwistedMellin
end
end

section
open Set Finset Complex Goldbach DirichletCharacter
noncomputable section
namespace GoldbachTwistedMellin

private def zeroBin (t : ℝ) : Bool × ℕ := (decide (0≤t),⌊|t|⌋₊)
private def binCenter (p : Bool × ℕ) : ℝ := if p.1 then (p.2:ℝ) else -(p.2:ℝ)

private theorem bin_properties (t : ℝ) :
    ((zeroBin t).2:ℝ) ≤ |t| ∧ |t-binCenter (zeroBin t)| ≤ 1 := by
  have h := Nat.floor_le (abs_nonneg t)
  have h' := Nat.lt_floor_add_one |t|
  refine ⟨h,?_⟩
  by_cases ht : 0≤t
  · simp only [abs_of_nonneg ht] at h h'
    simp [binCenter,zeroBin,ht,abs_of_nonneg ht,abs_le];constructor <;> linarith
  · have hn := le_of_not_ge ht
    simp only [abs_of_nonpos hn] at h h'
    simp [binCenter,zeroBin,ht,abs_of_nonpos hn,abs_le];constructor <;> linarith

private theorem binCenter_abs (p : Bool × ℕ) : |binCenter p|=(p.2:ℝ) := by
  dsimp [binCenter];split <;> simp

/-- Sum the Mellin transform over a narrow real-part strip, counting analytic
multiplicities. Uniform local Jensen bounds apply to every height bin. -/
theorem near_line_residues :
    ∃ C : ℝ, 0<C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Z : Finset ℂ)
    (a b X β B V : ℝ), 1≤X → X≤a → a+1≤b → b+1≤2*X →
    2≤B → V≤1 → (∀ z∈Z, 1/2≤z.re ∧ z.re≤V ∧ |z.im|≤B) →
    (∑ z ∈ Z, (analyticOrderNatAt (regularizedL χ) z:ℝ)*‖transform a b β z‖) ≤
      C*X^V*logHeight q B*(1+Real.sqrt (1+4*|β| *X)+Real.log B) := by
  classical
  obtain ⟨K,hK,slice⟩ := unconditional_right_slice_count
  refine ⟨200*K,by positivity,?_⟩
  intro q _ χ Z a b X β B V hX ha hab hb hB hV geom
  let J := ⌈4*|β| *X⌉₊
  let M := ⌊B⌋₊
  let y := fun z : ℂ => zeroBin z.im
  let mult := fun z : ℂ => (analyticOrderNatAt (regularizedL χ) z:ℝ)
  let W := 1+Real.sqrt (1+4*|β| *X)+Real.log B
  have hJ : 4*|β| * X ≤ (J:ℝ) := Nat.le_ceil _
  have hJ' : (J:ℝ) < 4*|β| *X+1 := Nat.ceil_lt_add_one (by positivity)
  have hM : (M:ℝ) ≤ B := Nat.floor_le (by linarith)
  have hgrid (z : ℂ) (hz : z∈Z) : y z ∈ grid (M+1) := by
    apply Finset.mem_product.mpr
    exact ⟨mem_univ _,mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (geom z hz).2.2))⟩
  have per (p : Bool×ℕ) (hp : p∈grid (M+1)) :
      (∑ z ∈ Z.filter (fun z => y z=p), mult z*‖transform a b β z‖) ≤
        (K*logHeight q B*X^V)*profile J p.2 := by
    let Y := Z.filter (fun z => y z=p)
    have hwlt (z : ℂ) (hz : z∈Y) : ‖transform a b β z‖ ≤ X^V*profile J p.2 := by
      obtain ⟨hzZ,he⟩ := mem_filter.mp hz
      obtain ⟨hl,hr,_⟩ := geom z hzZ
      have h := window_bin_bound hX ha hab hb (by linarith : 0≤z.re) (hr.trans hV) hr (bin_properties z.im).1 hJ
      have heq : line z.re z.im = z := by apply Complex.ext <;> simp
      rw [heq] at h
      simpa only [←he,y] using h
    have hcount := slice q χ (binCenter p) Y (fun z hz => by
      obtain ⟨hzZ,he⟩ := mem_filter.mp hz
      obtain ⟨hl,hr,_⟩ := geom z hzZ
      exact ⟨hl,by linarith,by simpa only [←he,y] using (bin_properties z.im).2⟩)
    have hj : p.2 ≤ M := Nat.lt_succ_iff.mp (mem_range.mp (mem_product.mp hp).2)
    have hlog : logHeight q (binCenter p) ≤ logHeight q B := by
      apply logHeight_mono_abs;rw [binCenter_abs,abs_of_nonneg (by linarith : 0≤B)]
      exact (show (p.2:ℝ) ≤ M by exact_mod_cast hj).trans hM
    have hm : (∑ z ∈ Y,mult z) ≤ K*logHeight q B := hcount.trans (mul_le_mul_of_nonneg_left hlog hK.le)
    calc
      _ ≤ ∑ z ∈ Y,mult z*(X^V*profile J p.2) := sum_le_sum fun z hz =>
        mul_le_mul_of_nonneg_left (hwlt z hz) (Nat.cast_nonneg _)
      _ = (∑ z ∈ Y,mult z)*(X^V*profile J p.2) := (Finset.sum_mul ..).symm
      _ ≤ (K*logHeight q B)*(X^V*profile J p.2) :=
        mul_le_mul_of_nonneg_right hm (mul_nonneg (Real.rpow_nonneg (by linarith) _) (profile_nonneg ..))
      _ = _ := by ring
  have hlogB := Real.log_nonneg (by linarith : 1≤B)
  have hln : Real.log (M+1:ℝ) ≤ 1+Real.log B := by
    have hy := Real.log_le_log (by positivity : 0<(M:ℝ)+1) (by linarith : (M:ℝ)+1 ≤ 2*B)
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (by linarith)] at hy
    linarith only [hy,Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))]
  have hsqrt : Real.sqrt J ≤ Real.sqrt (1+4*|β| *X) := Real.sqrt_le_sqrt (by linarith)
  have hprof : (∑ j ∈ range (M+1),profile J j) ≤ 100*W := by
    apply (profile_sum J M).trans;dsimp [W]
    nlinarith only [hln,hlogB,hsqrt,Real.sqrt_nonneg (1+4*|β| *X),
      mul_le_mul_of_nonneg_right Real.pi_lt_four.le (Real.sqrt_nonneg (J:ℝ))]
  have tot := sum_le_sum per
  rw [Finset.sum_fiberwise_of_maps_to hgrid,←Finset.mul_sum,sum_grid_weight] at tot
  have hL : 0 ≤ logHeight q B := zero_le_one.trans (logHeight_ge_one q B)
  exact (tot.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprof (by norm_num : (0:ℝ)≤2))
    (by positivity))).trans_eq (by dsimp [W,mult];ring)
end GoldbachTwistedMellin
end
end

section
open Set Finset Complex Goldbach DirichletCharacter
noncomputable section
namespace GoldbachTwistedMellin

theorem high_edge_residues :
    ∃ C : ℝ, 0<C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Z : Finset ℂ)
    (a b X β B : ℝ), 1≤X → X≤a → a+1≤b → b+1≤2*X → |β|≤1 → 2≤B → X^4≤B^2 →
    (∀ z∈Z, 1/2≤z.re ∧ z.re≤2 ∧ B≤|z.im| ∧ |z.im|≤B+1) →
    (∑ z ∈ Z,(analyticOrderNatAt (regularizedL χ) z:ℝ)*‖transform a b β z‖) ≤ C*logHeight q B := by
  classical
  obtain ⟨K,hK,slice⟩ := unconditional_right_slice_count
  refine ⟨192*K,by positivity,?_⟩
  intro q _ χ Z a b X β B hX ha hab hb hβ hB hBX geom
  let m := fun z : ℂ => (analyticOrderNatAt (regularizedL χ) z:ℝ)
  let pos := fun z : ℂ => 0≤z.im
  have top := slice q χ B (Z.filter pos) (fun z hz => by
    obtain ⟨hzZ,hp⟩ := mem_filter.mp hz
    obtain ⟨hr,hr',hi,hi'⟩ := geom z hzZ
    rw [abs_of_nonneg hp] at hi hi'
    exact ⟨hr,hr',abs_le.mpr ⟨by linarith,by linarith⟩⟩)
  have bot := slice q χ (-B) (Z.filter fun z => ¬pos z) (fun z hz => by
    obtain ⟨hzZ,hn⟩ := mem_filter.mp hz
    obtain ⟨hr,hr',hi,hi'⟩ := geom z hzZ
    rw [abs_of_nonpos (le_of_not_ge hn)] at hi hi'
    exact ⟨hr,hr',abs_le.mpr ⟨by linarith,by linarith⟩⟩)
  rw [show logHeight q (-B)=logHeight q B by simp [logHeight]] at bot
  have cnt : (∑ z ∈ Z,m z) ≤ 2*K*logHeight q B := by
    rw [←Finset.sum_filter_add_sum_filter_not Z pos m]
    exact (add_le_add top bot).trans_eq (by ring)
  have hwin (z : ℂ) (hz : z∈Z) : ‖transform a b β z‖ ≤ 96 := by
    obtain ⟨hr,hr',hi,_⟩ := geom z hz
    apply (norm_transform_tail hX ha hab hb hβ z (by linarith) hr' (by linarith)).trans
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < |z.im|))).mpr
    exact mul_le_mul_of_nonneg_left (hBX.trans (pow_le_pow_left₀ (by linarith) hi _)) (by norm_num)
  calc
    _ ≤ ∑ z ∈ Z,m z*96 := sum_le_sum fun z hz => mul_le_mul_of_nonneg_left (hwin z hz) (Nat.cast_nonneg _)
    _ = (∑ z ∈ Z,m z)*96 := (Finset.sum_mul ..).symm
    _ ≤ (2*K*logHeight q B)*96 := mul_le_mul_of_nonneg_right cnt (by norm_num)
    _ = _ := by ring
end GoldbachTwistedMellin
end
end

section
open Set Finset Complex Goldbach DirichletCharacter GoldbachSmoothing
noncomputable section
namespace GoldbachTwistedMellin

/-- Every zero strictly right of one half and of ordinate at most B in modulus. -/
noncomputable def exceptionalZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (B : ℝ) : Finset ℂ :=
  (boxZeros χ (1/2) 2 (-B) B).filter (fun z => 1/2 < z.re)

theorem mem_exceptionalZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (B : ℝ) (z : ℂ) :
    z ∈ exceptionalZeros χ B ↔ 1/2 < z.re ∧ |z.im| ≤ B ∧ regularizedL χ z = 0 := by
  classical
  rw [exceptionalZeros,mem_filter,mem_boxZeros,mem_reProdIm]
  constructor
  · rintro ⟨⟨⟨_,hi⟩,hz⟩,hl⟩
    exact ⟨hl,abs_le.mpr hi,hz⟩
  · rintro ⟨hl,hi,hz⟩
    have hr : z.re ≤ 2 := by by_contra! h;exact regularizedL_ne_zero_right χ (by linarith) hz
    exact ⟨⟨⟨⟨hl.le,hr⟩,abs_le.mp hi⟩,hz⟩,hl⟩

noncomputable def fixedZeroTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a b X β : ℝ) : ℂ :=
  ∑ z ∈ exceptionalZeros χ (heightCut X), (analyticOrderNatAt (regularizedL χ) z:ℂ)*transform a b β z

/-- Remove contour choices from the explicit formula. Zeros between the two
abscissae are bounded at the window scale, and the two top slices have small tails. -/
theorem fixed_dyadic_model {d : ℝ} (hd : 0<d) (hd' : d≤1/8) :
    ∃ C : ℝ, 0<C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (a b : ℕ) (X β : ℝ),
      1≤X → X≤(a:ℝ) → (a:ℝ)+1≤b → (b:ℝ)+1≤2*X → |β|≤1 →
      ‖(∑ k ∈ Finset.Ioc a b,twistedCoefficient χ k*phase β k) -
        (principalFlag χ*transform a b β 1 - fixedZeroTerm χ a b X β)‖ ≤
      C*X^(1/2+2*d)*(logBudget q X)^2*(1+Real.sqrt (1+4*|β| *X)+Real.log (heightCut X)) := by
  classical
  obtain ⟨C,hC,model⟩ := dyadic_zero_model hd hd'
  obtain ⟨K,hK,narrow⟩ := near_line_residues
  obtain ⟨A,hA,high⟩ := high_edge_residues
  refine ⟨C+K+A,by positivity,?_⟩
  intro q _ χ a b X β hX ha hab hb hβ
  let B := heightCut X
  obtain ⟨T,hT,σ,hσ,e⟩ := model q χ a b X β hX ha hab hb hβ
  let V := 1/2+2*d
  let Z := exceptionalZeros χ B
  let Y := boxZeros χ σ 2 (-T) T
  let F := fun z : ℂ => (analyticOrderNatAt (regularizedL χ) z:ℂ)*transform a b β z
  let S := X^V
  let L := logBudget q X
  let W := 1+Real.sqrt (1+4*|β| *X)+Real.log B
  have hV : V≤1 := by dsimp [V];linarith
  have hS : 1 ≤ S := Real.one_le_rpow hX (by dsimp [V];linarith)
  have hB : 2≤B := by linarith [heightCut_ge hX]
  have hLB : 1≤logHeight q B := logHeight_ge_one _ _
  have hL : 1≤L := by dsimp [L,logBudget,B] at *;linarith only [hLB]
  have hW : 1≤W := by dsimp [W];linarith only [Real.sqrt_nonneg (1+4*|β| *X),Real.log_nonneg (by linarith : 1≤B)]
  have hLSq : logHeight q B ≤ L^2 := by
    have h' : logHeight q B ≤ L := by dsimp [L,logBudget,B];linarith
    exact h'.trans (le_self_pow₀ hL (by decide))
  have lowGeom (z : ℂ) (hz : z∈ Z \ Y) : 1/2≤z.re ∧ z.re≤V ∧ |z.im|≤B := by
    obtain ⟨hzZ,hn⟩ := mem_sdiff.mp hz
    obtain ⟨hr,hi,hzero⟩ := (mem_exceptionalZeros χ B z).mp hzZ
    have hright : z.re≤2 := by by_contra! h;exact regularizedL_ne_zero_right χ (by linarith) hzero
    refine ⟨hr.le,?_,hi⟩
    by_contra! h
    apply hn
    exact (mem_boxZeros χ _ _ _ _ z).mpr ⟨mem_reProdIm.mpr
      ⟨⟨hσ.2.le.trans (by exact h.le),hright⟩,abs_le.mp (hi.trans hT.1)⟩,hzero⟩
  have highGeom (z : ℂ) (hz : z∈ Y \ Z) : 1/2≤z.re ∧ z.re≤2 ∧ B ≤ |z.im| ∧ |z.im|≤B+1 := by
    obtain ⟨hzY,hn⟩ := mem_sdiff.mp hz
    obtain ⟨h,hzero⟩ := (mem_boxZeros χ _ _ _ _ z).mp hzY
    obtain ⟨hr,hi⟩ := mem_reProdIm.mp h
    have hstrict : 1/2<z.re := by linarith [hσ.1,hr.1]
    refine ⟨hstrict.le,hr.2,?_,(abs_le.mpr hi).trans hT.2⟩
    by_contra! h
    exact hn ((mem_exceptionalZeros χ B z).mpr ⟨hstrict,h.le,hzero⟩)
  have hpow : X^4 ≤ B^2 := by
    have h8 := pow_le_pow_right₀ hX (show 4≤8 by decide)
    have h : X^8≤B := by dsimp [B,heightCut];rw [mul_pow];norm_num;linarith [pow_nonneg (by linarith : 0≤X) 8]
    exact (h8.trans h).trans (le_self_pow₀ (by linarith : 1≤B) (by decide))
  have low := narrow q χ (Z \ Y) a b X β B V hX ha hab hb hB hV lowGeom
  have hi := high q χ (Y \ Z) a b X β B hX ha hab hb hβ hB hpow highGeom
  have nf (z : ℂ) : ‖F z‖ = (analyticOrderNatAt (regularizedL χ) z:ℝ)*‖transform a b β z‖ := by simp [F]
  have small : ‖(∑ z ∈ Z,F z)-(∑ z ∈ Y,F z)‖ ≤ (K+A)*S*L^2*W := by
    rw [←Finset.sum_sdiff_sub_sum_sdiff]
    apply (norm_sub_le ..).trans
    apply (add_le_add (norm_sum_le ..) (norm_sum_le ..)).trans
    simp_rw [nf]
    have low' : K*S*logHeight q B*W ≤ K*S*L^2*W := by gcongr
    have hh := (mul_le_mul_of_nonneg_left hLSq hA.le).trans (show A*L^2 ≤ A*S*L^2*W from by
      have h := le_mul_of_one_le_left (sq_nonneg L) hS
      have h' := le_mul_of_one_le_right (show 0≤S*L^2 by positivity) hW
      nlinarith only [mul_le_mul_of_nonneg_left (h.trans h') hA.le])
    exact (add_le_add (low.trans low') (hi.trans hh)).trans_eq (by ring)
  let P := ∑ k ∈ Finset.Ioc a b,twistedCoefficient χ k*phase β k
  let M := principalFlag χ*transform a b β 1
  change ‖P-(M-∑ z ∈ Z,F z)‖ ≤ _
  change ‖P-(M-∑ z ∈ Y,F z)‖ ≤ C*S*L^2*W at e
  have eq' : P-(M-∑ z ∈ Z,F z) = (P-(M-∑ z ∈ Y,F z))+((∑ z ∈ Z,F z)-(∑ z ∈ Y,F z)) := by abel
  rw [eq']
  exact (norm_add_le ..).trans ((add_le_add e small).trans_eq (by dsimp [S,L,W,V,B];ring))
end GoldbachTwistedMellin
end
end

section
open Set Complex Goldbach GoldbachSmoothing GoldbachGRHWindow DeepThreeQuarters
noncomputable section
namespace GoldbachTwistedMellin

/-- Signed sum of the exceptional Dirichlet zeros with a deterministic height
on each dyadic block and the finite Fourier weights of the rational phase. -/
noncomputable def canonicalCorrection {q : ℕ} [NeZero q] (n : ℕ) (v : ZMod q) (β : ℝ) : ℂ :=
  ((prefixBlocks (n-2)).map fun p => ∑ χ : DirichletCharacter ℂ q,additiveWeight v χ *
    fixedZeroTerm χ p.1 p.2 p.1 (2*Real.pi*β)).sum

/-- Uniform rational approximation with an explicit signed zero correction.
The correction uses only the zeros strictly to the right of the critical line. -/
theorem rational_canonical_model {d : ℝ} (hd : 0<d) (hd' : d≤1/8) :
    ∃ K : ℝ, 0<K ∧ ∀ n : ℕ, 64≤n → ∀ (a q : ℕ) [NeZero q], a.Coprime q →
      (q:ℝ) ≤ Real.sqrt n → ∀ β : ℝ, |β| ≤ 1/((q:ℝ)*Real.sqrt n) →
      ‖weightedSum n primeWeight ((a:ℝ)/q+β) - rationalModel n q β + canonicalCorrection n (a:ZMod q) β‖ ≤
        K*(n:ℝ)^(3/4+2*d)*logScale n^4 := by
  classical
  obtain ⟨C,hC,model⟩ := fixed_dyadic_model hd hd'
  refine ⟨3*(12+1700*C),by positivity,?_⟩
  intro n hn a q _ hc hqs β hβ
  have hn1 : 1 ≤ n := by omega
  have hq : 1 ≤ q := NeZero.pos q
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn1
  let γ := 2*Real.pi*β
  obtain ⟨hγ,hγq⟩ := angular_range hn hq hβ
  let pairs := prefixBlocks (n-2)
  let S := (n:ℝ)^(3/4+2*d)
  let L := logScale n
  let D := (12+1700*C)*S*L^3
  have hL : 1 ≤ L := logScale_one hnR
  have hS : 1 ≤ S := Real.one_le_rpow hnR (by linarith)
  have hD : 12 ≤ D := by
    dsimp [D]
    calc
      (12:ℝ) ≤ (12+1700*C)*1*1 := by linarith
      _ ≤ _ := by gcongr;exact one_le_pow₀ hL
  have geom (p : ℕ×ℕ) (hp : p ∈ pairs) : 1≤p.1 ∧ p.1+1≤p.2 ∧ p.2+1≤2*p.1 ∧ p.2≤n := by
    have := prefixBlocks_valid hp
    simpa [Nat.sub_add_cancel (show 2≤n by omega)] using this
  let z := fun p : ℕ×ℕ => ∑ χ : DirichletCharacter ℂ q, additiveWeight (a:ZMod q) χ *
    fixedZeroTerm χ p.1 p.2 p.1 γ
  have pre := dyadic_prefix_corrected (primeError (a:ZMod q) γ) z n (by omega) D
    (fun j hj => (primeError_small _ _ _ hj).trans hD) (fun p hp => by
      obtain ⟨hl,hlr,hr,hrn⟩ := geom p hp
      exact signed_block_budget (a:ZMod q) hn1 hl hlr hrn (by linarith : 0≤2*d) hC.le hqs hγq
        (fun χ => fixedZeroTerm χ p.1 p.2 p.1 γ) (fun χ =>
          model q χ p.1 p.2 p.1 γ (by exact_mod_cast hl) le_rfl (by exact_mod_cast hlr) (by exact_mod_cast hr) hγ))
  change ‖(∑ k ∈ Finset.Ioc 0 n,primeError (a:ZMod q) (2*Real.pi*β) k) + canonicalCorrection n (a:ZMod q) β‖ ≤ _ at pre
  rw [primeError_prefix_eq a n hc β] at pre
  exact pre.trans ((mul_le_mul_of_nonneg_right (dyadic_count_le (by omega : 4≤n)) (by linarith : 0≤D)).trans_eq
    (by dsimp [D,S,L];ring))
end GoldbachTwistedMellin
end
end

section
open Finset Real Complex Goldbach DeepThreeQuarters Filter
noncomputable section
namespace GoldbachTwistedMellin

theorem quartic_log_scale {e : ℝ} (he : 0 < e) :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 1 ≤ x → logScale x^4 ≤ D*x^e := by
  let u := e/4
  have hu : 0 < u := by dsimp [u]; positivity
  let c := 1+Real.log 2+1/u
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c^4,by positivity,?_⟩
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
  refine (pow_le_pow_left₀ (zero_le_one.trans (logScale_one hx)) h 4).trans_eq ?_
  rw [mul_pow,←Real.rpow_mul_natCast hx0.le]
  have hu3 : u*(4:ℕ) = e := by dsimp [u]; ring
  rw [hu3]

/-- On every deep arc the prime exponential sum plus a signed average
of finite zero residues has the full three-quarters saving. -/
theorem deep_canonical_three_quarters :
    ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0:ℝ) 1,
      t ∉ wideArcs n → ∀ (a q : ℕ) [NeZero q], a ≤ q → a.Coprime q → (q:ℝ) ≤ Real.sqrt n →
      |t-(a:ℝ)/q| ≤ 1/((q:ℝ)*Real.sqrt n) →
      ‖weightedSum n primeWeight t + canonicalCorrection n (a:ZMod q) (t-(a:ℝ)/q)‖ ≤ (n:ℝ)^(3/4+η) := by
  intro η hη
  let d := min (η/8) (1/8)
  have hd : 0 < d := lt_min (by positivity) (by norm_num)
  have hdq : d ≤ 1/8 := min_le_right ..
  have hde : d ≤ η/8 := min_le_left ..
  obtain ⟨K,hK,hest⟩ := rational_canonical_model hd hdq
  obtain ⟨D,hD,hlog⟩ := quartic_log_scale (show 0 < η/4 by positivity)
  let A := 8+4/(η/2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨N,hN⟩ := eventually_atTop.1 (eventually_absorb (K*D+A) η hη)
  refine ⟨max 64 N,?_⟩
  intro n hn t _ht hdeep a q _ haq hc hqs hβ
  have hn64 := (le_max_left 64 N).trans hn
  have hn4 : 4 ≤ n := by omega
  have hx : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hx0 := zero_lt_one.trans_le hx
  have hq := NeZero.pos q
  have hlo := (height_bounds (by omega : 1≤n) hq haq hc hdeep hqs hβ).1
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
  have he := hest n hn64 a q hc hqs β hβ
  let Z := canonicalCorrection n (a:ZMod q) β
  rw [show (a:ℝ)/q+β = t by dsimp [β]; ring] at he
  have herr : ‖weightedSum n primeWeight t-rationalModel n q β + Z‖ ≤ (K*D)*(n:ℝ)^(3/4+η/2) := by
    refine he.trans ((mul_le_mul_of_nonneg_left (hlog n hx) (by positivity)).trans ?_)
    calc
      _ = (K*D)*(n:ℝ)^(3/4+2*d+η/4) := by rw [Real.rpow_add hx0 (3/4+2*d) (η/4)]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) (by positivity)
  have tri := norm_add_le (weightedSum n primeWeight t-rationalModel n q β + Z) (rationalModel n q β)
  rw [show weightedSum n primeWeight t-rationalModel n q β+Z+rationalModel n q β = weightedSum n primeWeight t+Z by abel] at tri
  exact (tri.trans ((add_le_add herr hmodel).trans_eq (by ring))).trans (hN n ((le_max_right ..).trans hn))

end GoldbachTwistedMellin
end
end

section
open Set Complex Goldbach DeepThreeQuarters Filter
noncomputable section
namespace GoldbachTwistedMellin

/-- The exact deep-arc target is equivalent to cancellation in the fixed signed zero sum.
The zero criterion quantifies over every reduced Dirichlet approximant. -/
theorem deep_iff_exceptional_cancellation :
    (∀ η : ℝ, 0<η → ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ t ∈ Icc (0:ℝ) 1, t ∉ wideArcs n →
      ‖weightedSum n primeWeight t‖ ≤ (n:ℝ)^(3/4+η)) ↔
    (∀ η : ℝ, 0<η → ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ t ∈ Icc (0:ℝ) 1, t ∉ wideArcs n →
      ∀ (a q : ℕ) [NeZero q], a≤q → a.Coprime q → (q:ℝ)≤Real.sqrt n →
      |t-(a:ℝ)/q| ≤ 1/((q:ℝ)*Real.sqrt n) →
      ‖canonicalCorrection n (a:ZMod q) (t-(a:ℝ)/q)‖ ≤ (n:ℝ)^(3/4+η)) := by
  constructor
  · intro target η hη
    obtain ⟨N,hN⟩ := target (η/2) (half_pos hη)
    obtain ⟨M,hM⟩ := deep_canonical_three_quarters (η/2) (half_pos hη)
    obtain ⟨P,hP⟩ := eventually_atTop.1 (eventually_absorb 2 η hη)
    refine ⟨max N (max M P),?_⟩
    intro n hn t ht hdeep a q _ ha hc hq hβ
    have h₁ := hN n (by omega) t ht hdeep
    have h₂ := hM n (by omega) t ht hdeep a q ha hc hq hβ
    let S := weightedSum n primeWeight t
    let Z := canonicalCorrection n (a:ZMod q) (t-(a:ℝ)/q)
    change ‖Z‖ ≤ _
    have h : Z = (S+Z)-S := by abel
    rw [h]
    exact (norm_sub_le ..).trans ((add_le_add h₂ h₁).trans ((le_of_eq (by ring)).trans (hP n (by omega))))
  · intro zeros η hη
    obtain ⟨N,hN⟩ := zeros (η/2) (half_pos hη)
    obtain ⟨M,hM⟩ := deep_canonical_three_quarters (η/2) (half_pos hη)
    obtain ⟨P,hP⟩ := eventually_atTop.1 (eventually_absorb 2 η hη)
    refine ⟨max 1 (max N (max M P)),?_⟩
    intro n hn t ht hdeep
    obtain ⟨a,q,hq,ha,hc,hden,hβ⟩ := exists_dirichlet n (by omega) t ht
    let : NeZero q := ⟨by omega⟩
    have h₁ := hN n (by omega) t ht hdeep a q ha hc hden hβ
    have h₂ := hM n (by omega) t ht hdeep a q ha hc hden hβ
    let S := weightedSum n primeWeight t
    let Z := canonicalCorrection n (a:ZMod q) (t-(a:ℝ)/q)
    change ‖S‖ ≤ _
    have h : S = (S+Z)-Z := by abel
    rw [h]
    exact (norm_sub_le ..).trans ((add_le_add h₂ h₁).trans ((le_of_eq (by ring)).trans (hP n (by omega))))
end GoldbachTwistedMellin
end
end

section
open Complex Finset GoldbachGRHWindow
open scoped ComplexConjugate BigOperators
noncomputable section
namespace GoldbachTwistedMellin
variable {q : ℕ} [NeZero q]

theorem additiveWeight_gauss (a : ZMod q) (χ : DirichletCharacter ℂ q) :
    additiveWeight a χ = gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift a) / (q.totient : ℂ) := by
  rw [weight_expansion, gaussSum]
  congr 1
  apply sum_congr rfl
  intro r _
  rw [AddChar.mulShift_apply, mul_comm]
  exact congrArg (fun z => z * _) (MulChar.star_apply' χ r)

theorem additiveWeight_unit (a : (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) :
    additiveWeight a χ = χ a * additiveWeight 1 χ := by
  simp only [additiveWeight_gauss, gaussSum_mulShift_eq, inv_inv, AddChar.mulShift_one, mul_div_assoc]

theorem norm_primitive_weight (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖additiveWeight 1 χ‖ = Real.sqrt q / q.totient := by
  simp only [additiveWeight_gauss, AddChar.mulShift_one, norm_div,
    DirichletCharacter.norm_gaussSum_stdAddChar hχ.inv, Complex.norm_natCast]

noncomputable def characterZeroSum (n : ℕ) (χ : DirichletCharacter ℂ q) (β : ℝ) : ℂ :=
  ((prefixBlocks (n-2)).map fun p => fixedZeroTerm χ p.1 p.2 p.1 (2*Real.pi*β)).sum

private theorem exchange_blocks {α ι : Type*} [Fintype ι] (l : List α) (w : ι → ℂ) (z : α → ι → ℂ) :
    (l.map fun p => ∑ i : ι, w i * z p i).sum =
      ∑ i : ι, w i * (l.map fun p => z p i).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons,List.sum_cons,ih,mul_add,sum_add_distrib]

theorem canonical_character_expansion (n : ℕ) (v : ZMod q) (β : ℝ) :
    canonicalCorrection n v β = ∑ χ : DirichletCharacter ℂ q, additiveWeight v χ * characterZeroSum n χ β :=
  exchange_blocks _ _ _

end GoldbachTwistedMellin
end
end

section
open Complex Finset
noncomputable section
namespace GoldbachConductorGauss

theorem sum_multiples_range (d t : ℕ) (hd : 0 < d) (F : ℕ → ℂ) :
    (∑ r ∈ range (d*t), if d ∣ r then F r else 0) = ∑ j ∈ range t, F (d*j) := by
  rw [← sum_filter]
  refine sum_nbij' (fun r => r/d) (fun j => d*j) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    rw [mem_filter] at hr
    exact mem_range.mpr ((Nat.div_lt_iff_lt_mul hd).mpr (by simpa only [mul_comm t d] using mem_range.mp hr.1))
  · intro j hj
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hj) hd), dvd_mul_right d j⟩
  · intro r hr
    exact Nat.mul_div_cancel' (mem_filter.mp hr).2
  · intro j _
    exact Nat.mul_div_cancel_left j hd
  · intro r hr
    rw [Nat.mul_div_cancel' (mem_filter.mp hr).2]

theorem phase_multiple {d t : ℕ} [NeZero d] [NeZero t] (j : ℕ) :
    ZMod.stdAddChar ((d*j : ℕ) : ZMod (d*t)) = ZMod.stdAddChar (j : ZMod t) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, ZMod.toCircle_natCast, ZMod.toCircle_natCast]
  apply congrArg Complex.exp
  push_cast
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  field_simp
end GoldbachConductorGauss
end
end

section
open Finset Complex ArithmeticFunction
open scoped ComplexConjugate
noncomputable section
namespace GoldbachConductorGauss

private theorem sum_residues {q : ℕ} [NeZero q] (F : ZMod q → ℂ) :
    (∑ a : ZMod q, F a) = ∑ j ∈ range q, F j := by
  exact sum_nbij' ZMod.val (fun j : ℕ => (j : ZMod q))
    (fun a _ => mem_range.mpr (ZMod.val_lt a)) (fun _ _ => mem_univ _)
    (fun a _ => ZMod.natCast_zmod_val a)
    (fun j hj => ZMod.val_natCast_of_lt (mem_range.mp hj))
    (fun a _ => by rw [ZMod.natCast_zmod_val])

private theorem sum_moebius_indicator (m r : ℕ) (hm : m ≠ 0) :
    (∑ d ∈ m.divisors, if d ∣ r then (ArithmeticFunction.moebius d : ℂ) else 0) =
       if r.Coprime m then 1 else 0 := by
  classical
  rw [← sum_filter]
  have hdiv : m.divisors.filter (fun d => d ∣ r) = (r.gcd m).divisors := by
    ext d
    simp [Nat.mem_divisors, hm, (show r.gcd m ≠ 0 from fun he => hm (Nat.gcd_eq_zero_iff.mp he).2), Nat.dvd_gcd_iff, and_comm]
  rw [hdiv]
  have hz := congrArg (fun F : ArithmeticFunction ℤ => F (r.gcd m)) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply,ArithmeticFunction.one_apply] at hz
  rw [← Int.cast_sum, hz]
  by_cases h : r.Coprime m <;> simp [Nat.Coprime] at h ⊢

private theorem induced_value {f m : ℕ} [NeZero f] [NeZero m] (χ : DirichletCharacter ℂ f) (r : ℕ) :
    DirichletCharacter.changeLevel (dvd_mul_right f m) χ (r : ZMod (f*m)) =
      χ (r : ZMod f) * ∑ d ∈ m.divisors, if d ∣ r then (ArithmeticFunction.moebius d : ℂ) else 0 := by
  rw [sum_moebius_indicator _ _ (NeZero.ne m)]
  by_cases hf : r.Coprime f <;> by_cases hm : r.Coprime m
  · have hu := (ZMod.isUnit_iff_coprime r (f*m)).mpr (Nat.coprime_mul_iff_right.mpr ⟨hf,hm⟩)
    rw [ite_eq_left hm, mul_one]
    simpa [ZMod.cast_natCast (dvd_mul_right f m)] using
      DirichletCharacter.changeLevel_eq_cast_of_dvd χ (dvd_mul_right f m) hu.unit
  all_goals
    have hnot : ¬ r.Coprime (f*m) := by simp_all only [Nat.coprime_mul_iff_right, not_false_eq_true, and_false, false_and]
    rw [MulChar.map_nonunit _ (mt (ZMod.isUnit_iff_coprime _ _).mp hnot)]
  · simp [hm]
  · simp [MulChar.map_nonunit χ (mt (ZMod.isUnit_iff_coprime _ _).mp hf)]
  · simp [hm]

set_option maxHeartbeats 1800000 in
private theorem collapse_lift {f k : ℕ} [NeZero f] [NeZero k] (χ : DirichletCharacter ℂ f) :
    (∑ j ∈ range (f*k), χ (j : ZMod f) * ZMod.stdAddChar (j : ZMod (f*k))) =
      if k=1 then gaussSum χ ZMod.stdAddChar else 0 := by
  classical
  by_cases hk : k=1
  · subst k
    simp only [mul_one,ite_true]
    rw [gaussSum, sum_residues]
    apply sum_congr rfl
    intro j _
    apply congrArg (fun z => χ (j : ZMod f) * z)
    rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, ZMod.toCircle_natCast, ZMod.toCircle_natCast]
    simp
  rw [ite_eq_right hk]
  let c : ZMod (f*k) →+* ZMod f := ZMod.castHom (dvd_mul_right f k) _
  let F := fun j : ZMod (f*k) => χ (c j) * ZMod.stdAddChar j
  have hr : (∑ j : ZMod (f*k), F j) = ∑ j ∈ range (f*k), χ (j : ZMod f) * ZMod.stdAddChar (j : ZMod (f*k)) := by
    simpa [F] using sum_residues F
  rw [← hr]
  have hne : (f : ZMod (f*k)) ≠ 0 := by
    have hl : f < f*k := by simpa using (Nat.mul_lt_mul_of_pos_left (show 1<k by have := NeZero.pos k; omega) (NeZero.pos f))
    intro h
    have hv := congrArg ZMod.val h
    simp [ZMod.val_natCast_of_lt hl, NeZero.ne f] at hv
  have phase : ZMod.stdAddChar (f : ZMod (f*k)) ≠ 1 := by
    intro h
    apply hne
    exact ZMod.injective_toCircle (by ext; simpa [ZMod.stdAddChar_apply] using h)
  apply eq_zero_of_mul_eq_self_left phase
  calc
    _ = ∑ j : ZMod (f*k), F ((f : ZMod (f*k)) + j) := by
      rw [Finset.mul_sum]
      refine sum_congr rfl fun j _ => ?_
      simp [F,AddChar.map_add_eq_mul]
      ring
    _ = _ := (Equiv.addLeft (f : ZMod (f*k))).bijective.sum_comp F


private noncomputable def phase (N j : ℕ) : ℂ := Complex.exp (2*Real.pi*I*j/N)
private theorem phase_cast {N : ℕ} [NeZero N] (j : ℕ) :
    ZMod.stdAddChar (j : ZMod N) = phase N j := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_natCast, phase]
private theorem phase_rescale {d t : ℕ} [NeZero d] [NeZero t] (j : ℕ) :
    phase (d*t) (d*j) = phase t j := by
  simpa only [phase_cast] using phase_multiple (d:=d) (t:=t) j

private theorem divisor_block {f m d : ℕ} [NeZero f] [NeZero m] (hd : d ∣ m)
    (χ : DirichletCharacter ℂ f) :
    (∑ r ∈ range (f*m), if d ∣ r then χ (r : ZMod f) * phase (f*m) r else 0) =
      if d=m then χ (m : ZMod f) * gaussSum χ ZMod.stdAddChar else 0 := by
  classical
  obtain ⟨k,rfl⟩ := hd
  have hd0 : d ≠ 0 := by intro h; exact NeZero.ne (d*k) (by simp [h])
  have hk0 : k ≠ 0 := by intro h; exact NeZero.ne (d*k) (by simp [h])
  let : NeZero d := ⟨hd0⟩
  let : NeZero k := ⟨hk0⟩
  have reindex : f*(d*k) = d*(f*k) := by ring
  rw [reindex,sum_multiples_range _ _ (Nat.pos_of_ne_zero hd0)]
  simp_rw [phase_rescale, Nat.cast_mul,map_mul,mul_assoc,←Finset.mul_sum]
  have c := collapse_lift (k:=k) χ
  simp only [phase_cast] at c
  rw [c]
  by_cases hk : k = 1
  · simp [hk]
  · have hne : d ≠ d*k := by
      intro h
      apply hk
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd0) (by simpa using h.symm : d*k = d*1)
    simp [hk,hne]

/-- The Gauss sum of a character inflated from modulus f to f*m.
The factor μ(m)χ(m) includes both the squarefree and coprimality conditions. -/
theorem induced_gaussSum {f m : ℕ} [NeZero f] [NeZero m] (χ : DirichletCharacter ℂ f) :
    gaussSum (DirichletCharacter.changeLevel (dvd_mul_right f m) χ) ZMod.stdAddChar =
      (ArithmeticFunction.moebius m : ℂ) * χ (m : ZMod f) * gaussSum χ ZMod.stdAddChar := by
  classical
  rw [gaussSum,sum_residues]
  calc
    _ = ∑ r ∈ range (f*m), ∑ d ∈ m.divisors,
        (ArithmeticFunction.moebius d : ℂ) * (if d ∣ r then χ (r : ZMod f) * phase (f*m) r else 0) := by
      apply sum_congr rfl
      intro r _
      rw [induced_value,phase_cast]
      simp only [Finset.mul_sum,Finset.sum_mul]
      refine sum_congr rfl fun d _ => ?_
      by_cases h : d ∣ r <;> simp [h]
      ring
    _ = ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ) *
        (if d=m then χ (m : ZMod f)*gaussSum χ ZMod.stdAddChar else 0) := by
      rw [Finset.sum_comm]
      refine sum_congr rfl fun d hd => ?_
      rw [← Finset.mul_sum,divisor_block (Nat.dvd_of_mem_divisors hd) χ]
    _ = _ := by
      rw [Finset.sum_eq_single m]
      · simp [mul_assoc]
      · intro d _ hne; simp [hne]
      · intro h; exact False.elim (h (Nat.mem_divisors.mpr ⟨dvd_refl _,NeZero.ne m⟩))


end GoldbachConductorGauss
end
end

section
open Finset Real Filter
noncomputable section
namespace GoldbachConductorGauss

/-- The uniform elementary divisor bound, with the exponent supplied by the consumer. -/
theorem divisor_count_subpower {ε : ℝ} (he : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ q : ℕ, 0<q → (q.divisors.card:ℝ) ≤ C*(q:ℝ)^ε := by
  classical
  have lim : Tendsto (fun n : ℕ => (n:ℝ)^ε) atTop atTop :=
    (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop
  obtain ⟨M,hM⟩ := eventually_atTop.mp (lim.eventually_ge_atTop 2)
  let K := 1 + 1/(ε*Real.log 2)
  have hg : (0:ℝ)<Real.log 2 := Real.log_pos (by norm_num)
  have hK : 1≤K := by dsimp [K];linarith [one_div_pos.mpr (mul_pos he hg)]
  refine ⟨K^M,by positivity,?_⟩
  intro q hq
  let G := fun p : ℕ => if p<M then K else 1
  let a := q.factorization
  have local_le (p : ℕ) (hp : p∈q.primeFactors) :
      (a p:ℝ)+1 ≤ G p*((p:ℝ)^(a p))^ε := by
    have hp2 : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp1 : (1:ℝ)≤p := by linarith
    have hp0 := zero_lt_one.trans_le hp1
    have ha : (1:ℝ) ≤ (p:ℝ)^(a p) := one_le_pow₀ hp1
    have hX := Real.one_le_rpow ha he.le
    by_cases h : p<M
    · simp only [G,ite_eq_left h,K,add_mul,one_mul]
      have hlog := Real.log_le_log (by norm_num : (0:ℝ)<2) hp2
      have hl := Real.log_le_rpow_div (zero_le_one.trans ha) he
      rw [Real.log_pow] at hl
      have small := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (a p) : (0:ℝ)≤_)
      have hh : (a p : ℝ) ≤ ((p:ℝ)^(a p))^ε/(ε*Real.log 2) := by
        apply (le_div_iff₀ (mul_pos he hg)).mpr
        have hh' := (le_div_iff₀ he).mp hl
        nlinarith only [hh',mul_le_mul_of_nonneg_right small he.le]
      nlinarith only [hh,hX,show 1/(ε*Real.log 2)*((p:ℝ)^a p)^ε = ((p:ℝ)^a p)^ε/(ε*Real.log 2) by ring]
    · simp only [G,ite_eq_right h,one_mul]
      have htwo := hM p (by omega)
      have hpow : (a p:ℝ)+1 ≤ (2:ℝ)^a p := by exact_mod_cast (Nat.lt_two_pow_self (n:=a p))
      exact hpow.trans ((pow_le_pow_left₀ (by norm_num) htwo (a p)).trans_eq (by
        rw [←Real.rpow_mul_natCast hp0.le,←Real.rpow_natCast_mul hp0.le,mul_comm]))
  have hG : (∏ p ∈ q.primeFactors,G p) ≤ K^M := by
    have card : (q.primeFactors.filter (fun p=>p<M)).card ≤ M := by
      simpa using Finset.card_le_card (show q.primeFactors.filter (fun p=>p<M) ⊆ range M from fun _ h => mem_range.mpr (mem_filter.mp h).2)
    simp only [G,← Finset.prod_filter,Finset.prod_const]
    exact pow_le_pow_right₀ hK card
  have prodpow (T : Finset ℕ) : (∏ p ∈ T, ((p:ℝ)^a p)^ε) = (∏ p ∈ T,(p:ℝ)^a p)^ε := by
    induction T using Finset.induction_on with
    | empty => simp
    | insert x t hx ih =>
      rw [prod_insert hx,prod_insert hx,ih,Real.mul_rpow (by positivity) (by positivity)]
  have reconstruct : (∏ p ∈ q.primeFactors,(p:ℝ)^a p) = q := by exact_mod_cast (Nat.prod_primeFactors_pow_factorization hq.ne').symm
  calc
    _ = ∏ p ∈ q.primeFactors, ((a p:ℝ)+1) := by rw [Nat.card_divisors hq.ne'];push_cast;rfl
    _ ≤ ∏ p ∈ q.primeFactors, G p*((p:ℝ)^a p)^ε := Finset.prod_le_prod₀ (fun _ _ => by positivity) local_le
    _ = (∏ p ∈ q.primeFactors,G p)*(q:ℝ)^ε := by rw [Finset.prod_mul_distrib,prodpow,reconstruct]
    _ ≤ _ := mul_le_mul_of_nonneg_right hG (Real.rpow_nonneg (Nat.cast_nonneg q) _)

end GoldbachConductorGauss
end
end

section
open Finset Complex GoldbachGRHWindow DeepThreeQuarters GoldbachConductorGauss DirichletCharacter
open scoped Classical
noncomputable section
namespace GoldbachTwistedMellin
variable {q : ℕ} [NeZero q]

/-- Portion of the canonical correction carried by primitive conductors at most D. -/
def lowConductorCorrection (D : ℝ) (n : ℕ) (a : ZMod q) (β : ℝ) : ℂ :=
  ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => (χ.conductor:ℝ)≤D),
    additiveWeight a χ*characterZeroSum n χ β

end GoldbachTwistedMellin
end
end

section
open Finset Complex DirichletCharacter GoldbachConductorGauss
open scoped ComplexConjugate Classical
noncomputable section
namespace GoldbachTwistedMellin

private theorem mobius_norm (m : ℕ) : ‖(ArithmeticFunction.moebius m : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=m))

/-- All characters inflated from a common level are summed before absolute values.
Their contribution at any residue costs at most φ(f)/φ(q). -/
theorem inflation_projector_bound {f q : ℕ} [NeZero f] [NeZero q] (hd : f ∣ q)
    (a : (ZMod q)ˣ) (r : ZMod q) :
    ‖∑ ψ : DirichletCharacter ℂ f, additiveWeight a (changeLevel hd ψ) * (changeLevel hd ψ) r‖ ≤
      (f.totient:ℝ)/q.totient := by
  classical
  obtain ⟨m,rfl⟩ := hd
  let : NeZero m := ⟨fun h => NeZero.ne (f*m) (by simp [h])⟩
  by_cases hr : IsUnit r
  on_goal 2 => simp [MulChar.map_nonunit _ hr];positivity
  let d := dvd_mul_right f m
  let u := ZMod.unitsMap d a
  let v := ZMod.unitsMap d hr.unit
  have ea (ψ : DirichletCharacter ℂ f) : changeLevel d ψ a = ψ u := changeLevel_eq_cast_of_dvd ψ d a
  have er (ψ : DirichletCharacter ℂ f) : changeLevel d ψ r = ψ v := by
    exact (changeLevel_eq_cast_of_dvd ψ d hr.unit : _)
  have weight (ψ : DirichletCharacter ℂ f) :
      additiveWeight a (changeLevel d ψ) * changeLevel d ψ r =
      ψ u * (((ArithmeticFunction.moebius m:ℂ)*ψ⁻¹ (m:ZMod f)*gaussSum ψ⁻¹ ZMod.stdAddChar)/(f*m).totient) * ψ v := by
    rw [additiveWeight_unit,ea,er,additiveWeight_gauss,AddChar.mulShift_one,←map_inv,induced_gaussSum]
  by_cases hm : IsUnit (m : ZMod f)
  on_goal 2 =>
    have hz (ψ : DirichletCharacter ℂ f) : additiveWeight a (changeLevel d ψ) * changeLevel d ψ r = 0 := by
      rw [weight,MulChar.map_nonunit _ hm];ring
    simp only [hz,sum_const_zero,norm_zero]
    positivity
  let z := u*v*hm.unit⁻¹
  have inv (ψ : DirichletCharacter ℂ f) : ψ⁻¹ (m : ZMod f) = ψ ((hm.unit⁻¹ : (ZMod f)ˣ) : ZMod f) := by
    have hh := ψ.map_mul (hm.unit : ZMod f) (hm.unit⁻¹ : (ZMod f)ˣ)
    have hne : ψ (m : ZMod f) ≠ 0 := (hm.map ψ).ne_zero
    rw [MulChar.inv_apply_eq_inv']
    apply inv_eq_of_mul_eq_one_right
    simpa using hh.symm
  have hφ : (f.totient:ℂ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos f)).ne'
  have scaled (ψ : DirichletCharacter ℂ f) :
      additiveWeight a (changeLevel d ψ) * changeLevel d ψ r =
        ((ArithmeticFunction.moebius m:ℂ)*f.totient/(f*m).totient) * (additiveWeight 1 ψ * ψ z) := by
    rw [weight,inv,additiveWeight_gauss,AddChar.mulShift_one]
    dsimp only [z]
    simp only [Units.val_mul,map_mul]
    field_simp
  simp_rw [scaled]
  rw [←Finset.mul_sum,additiveWeight_inversion,ite_eq_left z.isUnit,one_mul,norm_mul,
    ZMod.stdAddChar_apply,Circle.norm_coe,mul_one,norm_div,norm_mul,Complex.norm_natCast,Complex.norm_natCast]
  exact div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_right (mobius_norm m) (Nat.cast_nonneg f.totient)).trans_eq (one_mul _))
    (Nat.cast_nonneg _)


private theorem induced_character_image {f q : ℕ} [NeZero f] [NeZero q] (hd : f ∣ q) :
    (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor ∣ f) =
      (univ : Finset (DirichletCharacter ℂ f)).image (changeLevel hd) := by
  ext χ
  simp only [mem_filter,mem_univ,true_and,mem_image]
  constructor
  · intro hf
    obtain ⟨_,ψ,e⟩ : χ.FactorsThrough f := (mem_conductorSet_iff_conductor_dvd χ hd).mpr hf
    exact ⟨ψ,e.symm⟩
  · rintro ⟨ψ,rfl⟩
    rw [conductor_changeLevel]
    exact ψ.conductor_dvd_level

/-- For a single primitive conductor f inside q, its combined additive
coefficient on any residue is at most f/φ(q), retaining character phases. -/
theorem conductor_projector_bound {q f : ℕ} [NeZero q] (hf : f∣q) (a : (ZMod q)ˣ) (r : ZMod q) :
    ‖∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor=f),
        additiveWeight a χ * χ r‖ ≤ (f:ℝ)/q.totient := by
  let w := fun χ : DirichletCharacter ℂ q => additiveWeight a χ * χ r
  let P (d : ℕ) := ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor=d), w χ
  let H (d : ℕ) := ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor∣d), w χ
  have sumP (n : ℕ) (hn : 0<n) : ∑ d ∈ n.divisors, P d = H n := by
    let A := (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor ∣ n)
    have maps (χ : DirichletCharacter ℂ q) (hχ : χ∈A) : χ.conductor ∈ n.divisors :=
      Nat.mem_divisors.mpr ⟨(mem_filter.mp hχ).2,hn.ne'⟩
    change _ = ∑ χ ∈ A,w χ
    rw [←sum_fiberwise_of_maps_to maps w]
    refine sum_congr rfl fun d hd => ?_
    dsimp only [P]
    apply sum_congr _ (fun _ _ => rfl)
    ext χ
    simp only [A,mem_filter,mem_univ,true_and]
    exact ⟨fun he => ⟨he ▸ Nat.dvd_of_mem_divisors hd,he⟩,And.right⟩
  have hM := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp sumP f
    (Nat.pos_of_dvd_of_pos hf (NeZero.pos q))
  have hH {d : ℕ} (hd : d∣q) : ‖H d‖ ≤ (d.totient:ℝ)/q.totient := by
    let : NeZero d := ⟨fun h => NeZero.ne q (Nat.eq_zero_of_zero_dvd (h ▸ hd))⟩
    dsimp only [H]
    rw [induced_character_image hd,Finset.sum_image (fun _ _ _ _ h => changeLevel_injective hd h)]
    exact inflation_projector_bound hd a r
  change ‖P f‖ ≤ _
  rw [←hM]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ v ∈ f.divisorsAntidiagonal,(v.2.totient:ℝ)/q.totient := by
      refine sum_le_sum fun v hv => ?_
      rw [norm_mul]
      exact (mul_le_mul (mobius_norm _) (hH ((Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hv)).trans hf))
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = _ := by
      rw [←sum_div,Nat.sum_divisorsAntidiagonal' (fun _ j => (j.totient:ℝ)),←Nat.cast_sum,Nat.sum_totient]

/-- Summed projector for all small conductors, uniformly at every residue. -/
theorem low_projector_bound {q : ℕ} [NeZero q] (D : ℝ) (hD : 0≤D) (a : (ZMod q)ˣ) (r : ZMod q) :
    ‖∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => (χ.conductor:ℝ)≤D),
      additiveWeight a χ*χ r‖ ≤ (q.divisors.card:ℝ)*D/q.totient := by
  let A := (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => (χ.conductor:ℝ)≤D)
  let w := fun χ : DirichletCharacter ℂ q => additiveWeight a χ*χ r
  have maps (χ : DirichletCharacter ℂ q) (_ : χ∈A) : χ.conductor ∈ q.divisors :=
    Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level,NeZero.ne q⟩
  change ‖∑ χ ∈ A,w χ‖ ≤ _
  rw [←sum_fiberwise_of_maps_to maps w]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ _d ∈ q.divisors,D/q.totient := by
      refine sum_le_sum fun d hd => ?_
      by_cases h : (d:ℝ)≤D
      · have sets : A.filter (fun χ => χ.conductor=d) =
            (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor=d) := by
          ext χ
          simp only [A,mem_filter,mem_univ,true_and]
          exact ⟨And.right, fun he => ⟨he ▸ h,he⟩⟩
        rw [sets]
        exact (conductor_projector_bound (Nat.dvd_of_mem_divisors hd) a r).trans (div_le_div_of_nonneg_right h (Nat.cast_nonneg _))
      · have sets : A.filter (fun χ => χ.conductor=d) = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro χ hh
          obtain ⟨hm,he⟩ := mem_filter.mp hh
          exact h (he ▸ (mem_filter.mp hm).2)
        rw [sets,sum_empty,norm_zero];positivity
    _ = _ := by simp [mul_div_assoc]
end GoldbachTwistedMellin
end
end

section
open Finset Complex Set GoldbachSmoothing Goldbach GoldbachGRHWindow DeepThreeQuarters GoldbachConductorGauss
open scoped Classical
noncomputable section
namespace GoldbachTwistedMellin

private theorem phase_main_bound {n l r : ℕ} (hl : 0<l) (hlr : l+1≤r) (hr : r≤n) {γ : ℝ} (hγ : |γ|≤1) :
    ‖transform l r γ 1‖ ≤ 2*n := by
  have hsum : ‖∑ k ∈ Finset.Ioc l r, phase γ k‖ ≤ (n:ℝ) := by
    apply (norm_sum_le ..).trans
    simp only [norm_phase,sum_const,nsmul_eq_mul,mul_one,Nat.card_Ioc]
    exact_mod_cast (Nat.sub_le r l).trans hr
  have hdiff := principal_approx hl hlr γ
  have hrL : (0:ℝ)≤(r:ℝ)-l := sub_nonneg.mpr (by exact_mod_cast (show l≤r by omega))
  have hrU : (r:ℝ)-l≤n := by linarith [show (r:ℝ)≤n by exact_mod_cast hr,Nat.cast_nonneg (α:=ℝ) l]
  have harr := mul_le_mul_of_nonneg_left hγ hrL
  have htri := norm_add_le (transform l r γ 1-∑ k ∈ Finset.Ioc l r,phase γ k) (∑ k ∈ Finset.Ioc l r,phase γ k)
  rw [sub_add_cancel] at htri
  linarith

private theorem weighted_error_budget {n l q : ℕ} [NeZero q] (hn : 1≤n) (hl : 1≤l)
    (hln : l≤n) {γ C d : ℝ} (hC : 0≤C) (hd : 0≤d) (hqs : (q:ℝ)≤Real.sqrt n)
    (hγq : (q:ℝ)*|γ| *(n:ℝ)≤8*Real.sqrt n) :
    Real.sqrt q*(C*(l:ℝ)^(1/2+d)*(logBudget q l)^2*(1+Real.sqrt (1+4*|γ| *l)+Real.log (heightCut l))) ≤
      (12+1700*C)*(n:ℝ)^(3/4+d)*logScale n^3 := by
  let L := logScale n
  let W := 1+Real.sqrt (1+4*|γ| *l)+Real.log (heightCut l)
  let C' := 10*C*L
  have hx : 1≤(l:ℝ) := by exact_mod_cast hl
  have hnR : 1≤(n:ℝ) := by exact_mod_cast hn
  have hxn : (l:ℝ)≤n := by exact_mod_cast hln
  have hL : 1≤L := logScale_one hnR
  have hT : 1 ≤ heightCut l := by linarith [heightCut_ge hx]
  have hW : 0 ≤ W := by dsimp [W];linarith only [Real.sqrt_nonneg (1+4*|γ| *l),Real.log_nonneg hT]
  have hB0 : 0≤logBudget q l := by dsimp [logBudget];linarith only [logHeight_ge_one q (heightCut l)]
  have hB := (log_window_scale hx hxn (hqs.trans (Real.sqrt_le_self_iff.mpr (Or.inr hnR)))).1
  have hC' : 0≤C' := by dsimp [C'];positivity
  let M := C'*(l:ℝ)^(1/2+d)*logBudget q l*W
  have inc : C*(l:ℝ)^(1/2+d)*(logBudget q l)^2*W ≤ M := by
    calc
      _ = (C*(l:ℝ)^(1/2+d)*logBudget q l*W)*logBudget q l := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hB (by positivity)).trans_eq (by dsimp [M,C',L];ring)
  have large := block_budget hx hxn hd hC' hqs hγq
  have pre : C*(l:ℝ)^(1/2+d)*(logBudget q l)^2*W ≤ 2*Real.sqrt n*Real.log n+M+(n:ℝ)*|γ|+Real.log q := by
    have pos : 0≤2*Real.sqrt n*Real.log n := by positivity
    have pos' : 0≤(n:ℝ)*|γ| := by positivity
    linarith only [inc,pos,pos',Real.log_natCast_nonneg q]
  have fin := (mul_le_mul_of_nonneg_left pre (Real.sqrt_nonneg q)).trans large
  have hh := mul_le_mul_of_nonneg_right hL (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) (3/4+d)) (sq_nonneg L))
  dsimp only [C',L] at fin hh hL ⊢
  nlinarith only [fin,hh]

private theorem small_projected_main {q : ℕ} [NeZero q] (D : ℝ) (hD : 1≤D) (a : (ZMod q)ˣ) (T : ℂ) :
    ‖∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => (χ.conductor:ℝ)≤D),
      additiveWeight a χ*(principalFlag χ*T)‖ ≤ ((q.divisors.card:ℝ)*D/q.totient)*‖T‖ := by
  have hcard : (1:ℝ)≤q.divisors.card := by exact_mod_cast Finset.card_pos.mpr ⟨1,Nat.mem_divisors.mpr ⟨one_dvd _,NeZero.ne q⟩⟩
  rw [Finset.sum_eq_single (1 : DirichletCharacter ℂ q)]
  · simp only [principalFlag,ite_true,one_mul,norm_mul,additiveWeight_one,additiveModel_eq_moebius _ a.isUnit,
      norm_div,Complex.norm_natCast]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have hmu : ‖(ArithmeticFunction.moebius q : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=q))
    exact hmu.trans (by nlinarith only [hcard,hD,mul_nonneg (sub_nonneg.mpr hcard) (sub_nonneg.mpr hD)])
  · intro χ _ hχ;simp [principalFlag,hχ]
  · intro h;exact False.elim (h (by simp [DirichletCharacter.conductor_one,hD]))

private theorem small_projected_primes {q n l r : ℕ} [NeZero q] (hn : 1≤n) (hr : r≤n)
    (D : ℝ) (hD : 0≤D) (a : (ZMod q)ˣ) (γ : ℝ) :
    ‖∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => (χ.conductor:ℝ)≤D),
      additiveWeight a χ*(∑ k ∈ Finset.Ioc l r, twistedCoefficient χ k *phase γ k)‖ ≤
      ((q.divisors.card:ℝ)*D/q.totient)*((n:ℝ)*logScale n) := by
  let A := (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => (χ.conductor:ℝ)≤D)
  let B := (q.divisors.card:ℝ)*D/q.totient
  let v := fun k : ℕ => (ArithmeticFunction.vonMangoldt k : ℂ)*phase γ k
  have hB : 0≤B := by dsimp [B];positivity
  have expand : (∑ χ ∈ A,additiveWeight a χ*(∑ k ∈ Finset.Ioc l r,twistedCoefficient χ k*phase γ k)) =
      ∑ k ∈ Finset.Ioc l r,(∑ χ ∈ A,additiveWeight a χ*χ (k:ZMod q))*v k := by
    simp only [Finset.mul_sum,Finset.sum_mul,twistedCoefficient,Pi.mul_apply,v]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun k _ => sum_congr rfl fun χ _ => ?_
    ring
  rw [expand]
  apply (norm_sum_le ..).trans
  have hnR : 1≤(n:ℝ) := by exact_mod_cast hn
  have bound (k : ℕ) (hk : k ∈ Finset.Ioc l r) : ‖(∑ χ ∈ A,additiveWeight a χ*χ (k:ZMod q))*v k‖ ≤ B*logScale n := by
    have hkn := (Finset.mem_Ioc.mp hk).2.trans hr
    have hk0 : 0<(k:ℝ) := by exact_mod_cast (show 0<k by have := (Finset.mem_Ioc.mp hk).1;omega)
    simp only [v,norm_mul,norm_phase,mul_one,Complex.norm_real,Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_mul (low_projector_bound D hD a (k:ZMod q))
      (ArithmeticFunction.vonMangoldt_le_log.trans ((Real.log_le_log hk0 (by exact_mod_cast hkn)).trans (log_le_scale hnR)))
      ArithmeticFunction.vonMangoldt_nonneg hB
  apply (sum_le_sum bound).trans
  simp only [sum_const,nsmul_eq_mul,Nat.card_Ioc]
  have hcnt : ((r-l:ℕ):ℝ)≤n := by exact_mod_cast (Nat.sub_le r l).trans hr
  exact (mul_le_mul_of_nonneg_right hcnt (mul_nonneg hB (zero_le_one.trans (logScale_one hnR)))).trans_eq (by dsimp [B];ring)


set_option maxHeartbeats 1200000 in
private theorem projected_block_bound {n l r q : ℕ} [NeZero q] (hn : 1≤n) (hl : 1≤l) (hlr : l+1≤r) (hrn : r≤n)
    (a : (ZMod q)ˣ) {D C d γ : ℝ} (hD : 1≤D) (hC : 0≤C) (hd : 0≤d)
    (hqs : (q:ℝ)≤Real.sqrt n) (hγ : |γ|≤1) (hγq : (q:ℝ)*|γ| *(n:ℝ) ≤ 8*Real.sqrt n)
    (Z : DirichletCharacter ℂ q → ℂ)
    (err : ∀ χ : DirichletCharacter ℂ q,
      ‖(∑ k ∈ Finset.Ioc l r,twistedCoefficient χ k*phase γ k) -(principalFlag χ*transform l r γ 1-Z χ)‖ ≤
      C*(l:ℝ)^(1/2+d)*(logBudget q l)^2*(1+Real.sqrt (1+4*|γ| *l)+Real.log (heightCut l))) :
    ‖∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => (χ.conductor:ℝ)≤D), additiveWeight a χ*Z χ‖ ≤
      (12+1700*C)*(n:ℝ)^(3/4+d)*logScale n^3 +
        ((q.divisors.card:ℝ)*D/q.totient)*((n:ℝ)*(logScale n+2)) := by
  let A := (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => (χ.conductor:ℝ)≤D)
  let w := additiveWeight (a:ZMod q)
  let P := fun χ : DirichletCharacter ℂ q => ∑ k ∈ Finset.Ioc l r,twistedCoefficient χ k*phase γ k
  let M := fun χ : DirichletCharacter ℂ q => principalFlag χ*transform l r γ 1
  let B := (q.divisors.card:ℝ)*D/q.totient
  let V := C*(l:ℝ)^(1/2+d)*(logBudget q l)^2*(1+Real.sqrt (1+4*|γ| *l)+Real.log (heightCut l))
  let E := ∑ χ ∈ A,w χ*(P χ-(M χ-Z χ))
  have hx : 1≤(l:ℝ) := by exact_mod_cast hl
  have hT : 1≤heightCut l := by linarith [heightCut_ge hx]
  have hW : 0≤1+Real.sqrt (1+4*|γ| *l)+Real.log (heightCut l) := by
    linarith [Real.sqrt_nonneg (1+4*|γ| *l),Real.log_nonneg hT]
  have hV : 0≤V := by dsimp [V];positivity
  have hB : 0≤B := by dsimp [B];positivity
  have hE : ‖E‖ ≤ (12+1700*C)*(n:ℝ)^(3/4+d)*logScale n^3 := by
    calc
      _ ≤ ∑ χ ∈ A, ‖w χ*(P χ-(M χ-Z χ))‖ := norm_sum_le ..
      _ ≤ ∑ χ ∈ A, ‖w χ‖*V := by
        refine sum_le_sum fun χ _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (err χ) (norm_nonneg _)
      _ = (∑ χ ∈ A, ‖w χ‖)*V := (Finset.sum_mul ..).symm
      _ ≤ Real.sqrt q*V := by
        apply mul_le_mul_of_nonneg_right _ hV
        calc
          _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖w χ‖ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => norm_nonneg _)
          _ ≤ _ := sum_norm_additiveWeight_le (q:=q) (a : ZMod q)
      _ ≤ _ := weighted_error_budget (q:=q) (l:=l) (n:=n) hn hl (by omega) hC hd hqs hγq
  have hP : ‖∑ χ ∈ A,w χ*P χ‖ ≤ B*((n:ℝ)*logScale n) := small_projected_primes hn hrn D (zero_le_one.trans hD) a γ
  have hM : ‖∑ χ ∈ A,w χ*M χ‖ ≤ B*(2*n) := (small_projected_main D hD a _).trans
    (mul_le_mul_of_nonneg_left (phase_main_bound hl hlr hrn hγ) hB)
  have eq : (∑ χ ∈ A,w χ*Z χ) = E-(∑ χ ∈ A,w χ*P χ)+(∑ χ ∈ A,w χ*M χ) := by
    simp only [E,mul_sub,sum_sub_distrib]
    abel
  rw [eq]
  apply (norm_add_le ..).trans
  apply (add_le_add (norm_sub_le ..) le_rfl).trans
  dsimp [B] at hP hM
  linarith only [hE,hP,hM]

private theorem low_blocks_eq {q : ℕ} [NeZero q] (D : ℝ) (n : ℕ) (a : ZMod q) (β : ℝ) :
    lowConductorCorrection D n a β =
    ((prefixBlocks (n-2)).map fun p => ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
      (fun χ => (χ.conductor:ℝ)≤D),additiveWeight a χ * fixedZeroTerm χ p.1 p.2 p.1 (2*Real.pi*β)).sum := by
  unfold lowConductorCorrection characterZeroSum
  induction prefixBlocks (n-2) with
  | nil => simp
  | cons p l ih => simp only [List.map_cons,List.sum_cons,mul_add,sum_add_distrib,ih]

/-- The small-conductor contribution costs only D times the divisor count
in the arithmetic part. The explicit-formula error is uniform in the cutoff. -/
theorem projected_low_finite {d : ℝ} (hd : 0<d) (hd' : d≤1/8) :
    ∃ K : ℝ, 0<K ∧ ∀ n : ℕ, 64≤n → ∀ (q : ℕ) [NeZero q], (q:ℝ)≤Real.sqrt n →
      ∀ β : ℝ, |β|≤1/((q:ℝ)*Real.sqrt n) → ∀ D : ℝ, 1≤D → ∀ a : (ZMod q)ˣ,
      ‖lowConductorCorrection D n (a : ZMod q) β‖ ≤
        K*(n:ℝ)^(3/4+2*d)*logScale n^4 +
        9*((q.divisors.card:ℝ)*D/q.totient)*(n:ℝ)*logScale n^2 := by
  obtain ⟨C,hC,model⟩ := fixed_dyadic_model hd hd'
  refine ⟨3*(12+1700*C),by positivity,?_⟩
  intro n hn q _ hq β hβ D hD a
  let L := logScale n
  let B := (q.divisors.card:ℝ)*D/q.totient
  let γ := 2*Real.pi*β
  let V := (12+1700*C)*(n:ℝ)^(3/4+2*d)*L^3+B*((n:ℝ)*(L+2))
  let z := fun p : ℕ×ℕ => ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => (χ.conductor:ℝ)≤D),
    additiveWeight (a:ZMod q) χ*fixedZeroTerm χ p.1 p.2 p.1 γ
  have hn1 : 1≤n := by omega
  have hnR : 1≤(n:ℝ) := by exact_mod_cast hn1
  have hL : 1≤L := logScale_one hnR
  have hB : 0≤B := by dsimp [B];positivity
  have hV : 0≤V := by dsimp [V];positivity
  obtain ⟨hγ,hγq⟩ := angular_range hn (NeZero.pos q) hβ
  have bound (p : ℕ×ℕ) (hp : p∈prefixBlocks (n-2)) : ‖z p‖≤V := by
    obtain ⟨hl,hlr,hr,hrn⟩ := prefixBlocks_valid hp
    exact projected_block_bound hn1 hl hlr (by omega : p.2≤n) a hD hC.le (by linarith : 0≤2*d) hq hγ hγq _
      (fun χ => model q χ p.1 p.2 p.1 γ (by exact_mod_cast hl) le_rfl (by exact_mod_cast hlr) (by exact_mod_cast hr) hγ)
  have pre := dyadic_prefix_corrected (fun _ => (0:ℂ)) z n (by omega) V
    (fun k _ => by simpa using hV) (fun p hp => by simpa using bound p hp)
  simp only [sum_const_zero,zero_add] at pre
  rw [low_blocks_eq]
  apply pre.trans ((mul_le_mul_of_nonneg_right (dyadic_count_le (by omega : 4≤n)) hV).trans ?_)
  change 3*L*V ≤ _ + 9*B*(n:ℝ)*L^2
  have hh := mul_le_mul_of_nonneg_left hL (show 0≤B*(n:ℝ)*L by positivity)
  dsimp only [V,L] at hh ⊢
  nlinarith only [hh]
end GoldbachTwistedMellin
end
end

section
open Finset Complex Set GoldbachGRHWindow DeepThreeQuarters GoldbachConductorGauss Filter
open scoped Classical
noncomputable section
namespace GoldbachTwistedMellin

/-- The conductor projection removes all terms with conductor at most q/n^(1/4). -/
theorem projected_low_three_quarters {η : ℝ} (hη : 0<η) :
    ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ (q : ℕ) [NeZero q], (q:ℝ)≤Real.sqrt n →
      ∀ β : ℝ, |β|≤1/((q:ℝ)*Real.sqrt n) → ∀ D : ℝ, 0≤D →
      D≤(q:ℝ)/(n:ℝ)^(1/4:ℝ) → ∀ a : (ZMod q)ˣ,
      ‖lowConductorCorrection D n (a : ZMod q) β‖ ≤ (n:ℝ)^(3/4+η) := by
  let e := η/6
  have he : 0<e := by dsimp [e];linarith
  obtain ⟨U,hU,divisors⟩ := divisor_count_subpower he
  obtain ⟨V,hV,logs⟩ := quartic_log_scale he
  let d := min (1/8:ℝ) e
  have hd0 : 0<d := lt_min (by norm_num) he
  have hd1 : d≤1/8 := min_le_left ..
  have hde : d≤e := min_le_right ..
  obtain ⟨K,hK,finite⟩ := projected_low_finite hd0 hd1
  let A := K*V + 9*U*(8+4/e)*V
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_absorb A η hη)
  refine ⟨max 64 N,?_⟩
  intro n hn q _ hqs β hβ D hD hd a
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
  have hn0 := zero_lt_one.trans_le hnR
  have hq := NeZero.pos q
  have hqn : (q:ℝ)≤n := hqs.trans (Real.sqrt_le_self_iff.mpr (Or.inr hnR))
  let x := (n:ℝ)^e
  let y := (n:ℝ)^(1/4:ℝ)
  have hx : 0<x := Real.rpow_pos_of_pos hn0 _
  have hy : 0<y := Real.rpow_pos_of_pos hn0 _
  have hpow : (q:ℝ)^e ≤ x := Real.rpow_le_rpow (Nat.cast_nonneg q) hqn he.le
  have hτ : (q.divisors.card:ℝ)≤U*x := (divisors q hq).trans (mul_le_mul_of_nonneg_left hpow hU.le)
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hqφ : (q:ℝ)/q.totient ≤ (8+4/e)*x :=
    (totient_ratio_le_rpow he q hq).trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  have hsp : D/q.totient ≤ ((8+4/e)*x)/y := by
    calc
      _ ≤ ((q:ℝ)/y)/q.totient := div_le_div_of_nonneg_right hd hφ.le
      _ = ((q:ℝ)/q.totient)/y := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hqφ hy.le
  have hlog := logs (n:ℝ) hnR
  by_cases hD1 : 1≤D
  · have hL : 1≤logScale n := logScale_one hnR
    have hlog2 : logScale n ^ 2≤V*x := (pow_le_pow_right₀ hL (by decide : 2≤4)).trans hlog
    have hs : (n:ℝ)^(3/4+2*d) ≤ (n:ℝ)^(3/4+2*e) := Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
    have hi := finite n (by omega) q hqs β hβ D hD1 a
    rw [show (q.divisors.card:ℝ)*D/q.totient = (q.divisors.card:ℝ)*(D/q.totient) by ring] at hi
    apply hi.trans
    calc
      _ ≤ K*(n:ℝ)^(3/4+2*e)*(V*x)+9*((U*x)*(((8+4/e)*x)/y))*(n:ℝ)*(V*x) := by gcongr
      _ = K*V*((n:ℝ)^(3/4+2*e)*(n:ℝ)^e)+9*U*(8+4/e)*V*((n:ℝ)^(1:ℝ)*(n:ℝ)^e*(n:ℝ)^e*(n:ℝ)^e/(n:ℝ)^(1/4:ℝ)) := by
        dsimp [x,y];rw [Real.rpow_one];ring
      _ = A*(n:ℝ)^(3/4+η/2) := by
        rw [←Real.rpow_add hn0,←Real.rpow_add hn0,←Real.rpow_add hn0,←Real.rpow_add hn0,←Real.rpow_sub hn0]
        have e₁ : 3/4+2*e+e=3/4+η/2 := by dsimp [e];ring
        have e₂ : 1+e+e+e-1/4=3/4+η/2 := by dsimp [e];ring
        rw [e₁,e₂];dsimp [A];ring
      _ ≤ _ := hN n (by omega)
  · have empty : (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => (χ.conductor:ℝ)≤D) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro χ _
      have hp : (1:ℝ)≤χ.conductor := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero
      linarith
    simp only [lowConductorCorrection,empty,sum_empty,norm_zero]
    positivity

def projectedThreshold (n q : ℕ) : ℝ := (q:ℝ)/(n:ℝ)^(1/4:ℝ)
def projectedHighCorrection {q : ℕ} [NeZero q] (n : ℕ) (a : ZMod q) (β : ℝ) : ℂ :=
  ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => projectedThreshold n q < (χ.conductor:ℝ)),
    additiveWeight a χ * characterZeroSum n χ β

theorem projected_canonical_split {q : ℕ} [NeZero q] (n : ℕ) (a : ZMod q) (β : ℝ) :
    lowConductorCorrection (projectedThreshold n q) n a β + projectedHighCorrection n a β =
      canonicalCorrection n a β := by
  rw [canonical_character_expansion]
  simpa only [lowConductorCorrection,projectedHighCorrection,not_le] using
    Finset.sum_filter_add_sum_filter_not (s:=(univ:Finset (DirichletCharacter ℂ q)))
      (fun χ => (χ.conductor:ℝ)≤projectedThreshold n q) (fun χ => additiveWeight a χ * characterZeroSum n χ β)

end GoldbachTwistedMellin
end
end

section
open Set Filter Complex Goldbach GoldbachGRHWindow DeepThreeQuarters
noncomputable section
namespace GoldbachTwistedMellin

theorem deep_projected_high_model :
    ∀ η : ℝ, 0<η → ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ t ∈ Icc (0:ℝ) 1, t ∉ wideArcs n →
      ∀ (a q : ℕ) [NeZero q], a≤q → a.Coprime q → (q:ℝ)≤Real.sqrt n →
      |t-(a:ℝ)/q| ≤ 1/((q:ℝ)*Real.sqrt n) →
      ‖weightedSum n primeWeight t + projectedHighCorrection n (a:ZMod q) (t-(a:ℝ)/q)‖ ≤ (n:ℝ)^(3/4+η) := by
  intro η hη
  obtain ⟨N,hN⟩ := deep_canonical_three_quarters (η/2) (half_pos hη)
  obtain ⟨M,hM⟩ := projected_low_three_quarters (half_pos hη)
  obtain ⟨P,hP⟩ := eventually_atTop.mp (eventually_absorb 2 η hη)
  refine ⟨max N (max M P),?_⟩
  intro n hn t ht hdeep a q _ ha hc hq hβ
  let v : ZMod q := a
  let β := t-(a:ℝ)/q
  obtain ⟨u,hu⟩ := (ZMod.isUnit_iff_coprime a q).mpr hc
  have hs : 0≤projectedThreshold n q := by unfold projectedThreshold;positivity
  have hl := hM n (by omega) q hq β hβ (projectedThreshold n q) hs le_rfl u
  rw [hu] at hl
  have hsum := hN n (by omega) t ht hdeep a q ha hc hq hβ
  let S := weightedSum n primeWeight t
  have eq : S+projectedHighCorrection n v β =
      (S+canonicalCorrection n v β) - lowConductorCorrection (projectedThreshold n q) n v β := by
    rw [←projected_canonical_split];abel
  change ‖S+projectedHighCorrection n v β‖ ≤ _
  rw [eq]
  exact (norm_sub_le ..).trans ((add_le_add hsum hl).trans ((le_of_eq (by ring)).trans (hP n (by omega))))

/-- For q at least n^(1/3), the removed sector includes every conductor up to n^(1/12). -/
theorem projected_threshold_includes {n q : ℕ} (hn : 0<n) (hq : (n:ℝ)^(1/3:ℝ)≤q) :
    (n:ℝ)^(1/12:ℝ)≤projectedThreshold n q := by
  have h0 : 0<(n:ℝ) := by exact_mod_cast hn
  calc
    _ = (n:ℝ)^(1/3:ℝ)/(n:ℝ)^(1/4:ℝ) := by rw [←Real.rpow_sub h0];norm_num
    _ ≤ _ := div_le_div_of_nonneg_right hq (by positivity)
end GoldbachTwistedMellin
end
end

section
open Set Complex Goldbach DeepThreeQuarters Filter
noncomputable section
namespace GoldbachTwistedMellin

/-- The exact deep-arc target is equivalent to cancellation in the signed zero sum above the conductor cutoff.
The zero criterion quantifies over every reduced Dirichlet approximant. -/
theorem deep_iff_projected_high_cancellation :
    (∀ η : ℝ, 0<η → ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ t ∈ Icc (0:ℝ) 1, t ∉ wideArcs n →
      ‖weightedSum n primeWeight t‖ ≤ (n:ℝ)^(3/4+η)) ↔
    (∀ η : ℝ, 0<η → ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ t ∈ Icc (0:ℝ) 1, t ∉ wideArcs n →
      ∀ (a q : ℕ) [NeZero q], a≤q → a.Coprime q → (q:ℝ)≤Real.sqrt n →
      |t-(a:ℝ)/q| ≤ 1/((q:ℝ)*Real.sqrt n) →
      ‖projectedHighCorrection n (a:ZMod q) (t-(a:ℝ)/q)‖ ≤ (n:ℝ)^(3/4+η)) := by
  constructor
  · intro target η hη
    obtain ⟨N,hN⟩ := target (η/2) (half_pos hη)
    obtain ⟨M,hM⟩ := deep_projected_high_model (η/2) (half_pos hη)
    obtain ⟨P,hP⟩ := eventually_atTop.1 (eventually_absorb 2 η hη)
    refine ⟨max N (max M P),?_⟩
    intro n hn t ht hdeep a q _ ha hc hq hβ
    have h₁ := hN n (by omega) t ht hdeep
    have h₂ := hM n (by omega) t ht hdeep a q ha hc hq hβ
    let S := weightedSum n primeWeight t
    let Z := projectedHighCorrection n (a:ZMod q) (t-(a:ℝ)/q)
    change ‖Z‖ ≤ _
    have h : Z = (S+Z)-S := by abel
    rw [h]
    exact (norm_sub_le ..).trans ((add_le_add h₂ h₁).trans ((le_of_eq (by ring)).trans (hP n (by omega))))
  · intro zeros η hη
    obtain ⟨N,hN⟩ := zeros (η/2) (half_pos hη)
    obtain ⟨M,hM⟩ := deep_projected_high_model (η/2) (half_pos hη)
    obtain ⟨P,hP⟩ := eventually_atTop.1 (eventually_absorb 2 η hη)
    refine ⟨max 1 (max N (max M P)),?_⟩
    intro n hn t ht hdeep
    obtain ⟨a,q,hq,ha,hc,hden,hβ⟩ := exists_dirichlet n (by omega) t ht
    let : NeZero q := ⟨by omega⟩
    have h₁ := hN n (by omega) t ht hdeep a q ha hc hden hβ
    have h₂ := hM n (by omega) t ht hdeep a q ha hc hden hβ
    let S := weightedSum n primeWeight t
    let Z := projectedHighCorrection n (a:ZMod q) (t-(a:ℝ)/q)
    change ‖S‖ ≤ _
    have h : S = (S+Z)-Z := by abel
    rw [h]
    exact (norm_sub_le ..).trans ((add_le_add h₂ h₁).trans ((le_of_eq (by ring)).trans (hP n (by omega))))
end GoldbachTwistedMellin
end
end

section
open Finset Complex Set Goldbach GoldbachSmoothing GoldbachGRHWindow DeepThreeQuarters Filter
open scoped Classical
noncomputable section
namespace GoldbachTwistedMellin

/-- Mellin size on a dyadic interval at a given real part, including the
character and angular costs. The absolute prime-sum budget is global in n. -/
def localZeroScale (q : ℕ) (X γ σ : ℝ) : ℝ :=
  X^σ * Real.sqrt q * Real.sqrt (1+4*|γ| *X)

def lowerWindowZeros {q : ℕ} [NeZero q] (n : ℕ) (χ : DirichletCharacter ℂ q) (X γ : ℝ) :=
  (exceptionalZeros χ (heightCut X)).filter (fun z => localZeroScale q X γ z.re ≤ (n:ℝ)^(3/4:ℝ))

theorem scaled_residue_bound :
    ∃ C : ℝ, 0<C ∧ ∀ (n q : ℕ) [NeZero q], 1≤n → (q:ℝ)≤n →
      ∀ (χ : DirichletCharacter ℂ q) (a b X γ : ℝ), 1≤X → X≤a → a+1≤b → b+1≤2*X → X≤n →
      Real.sqrt q*‖∑ z ∈ lowerWindowZeros n χ X γ,
        (analyticOrderNatAt (regularizedL χ) z:ℂ)*transform a b γ z‖ ≤
        C*(n:ℝ)^(3/4:ℝ)*logScale n^2 := by
  obtain ⟨K,hK,narrow⟩ := near_line_residues
  refine ⟨100*K,by positivity,?_⟩
  intro n q _ hn hqn χ a b X γ hX ha hab hb hxn
  let Z := lowerWindowZeros n χ X γ
  let A := Real.sqrt (1+4*|γ| *X)
  let B := heightCut X
  let L := logScale n
  let N := (n:ℝ)^(3/4:ℝ)
  have hnR : 1≤(n:ℝ) := by exact_mod_cast hn
  have hL : 1≤L := logScale_one hnR
  have hA : 1≤A := by
    apply Real.one_le_sqrt.mpr
    have hx := mul_nonneg (abs_nonneg γ) (zero_le_one.trans hX)
    linarith
  have hB : 2≤B := by dsimp [B];linarith only [heightCut_ge hX,hX]
  obtain ⟨hlog,hheight⟩ := log_window_scale (q:=q) hX hxn hqn
  have hlb : logHeight q B ≤ 10*L := by
    dsimp [logBudget] at hlog
    dsimp [B,L];linarith
  have hW : 1+A+Real.log B ≤ 10*A*L := by
    have hm := mul_le_mul_of_nonneg_left hL (zero_le_one.trans hA)
    have hm' := mul_le_mul_of_nonneg_right hA (zero_le_one.trans hL)
    dsimp only [B,L] at *
    nlinarith only [hm,hm',hheight,hL,hA]
  have geom {z : ℂ} (hz : z∈Z) : 1/2<z.re ∧ |z.im|≤B ∧ regularizedL χ z=0 :=
    (mem_exceptionalZeros χ B z).mp (mem_filter.mp hz).1
  change Real.sqrt q * ‖∑ z ∈ Z,_‖ ≤ _
  rcases Z.eq_empty_or_nonempty with he|hne
  · rw [he,sum_empty,norm_zero,mul_zero];positivity
  obtain ⟨u,hu,hmax⟩ := Z.exists_max_image Complex.re hne
  have hu1 : u.re ≤ 1 := by
    by_contra! h
    exact regularizedL_ne_zero_right χ h (geom hu).2.2
  have hsc : X^u.re * Real.sqrt q * A ≤ N := (mem_filter.mp hu).2
  have hnorm := norm_sum_le Z (fun z : ℂ => (analyticOrderNatAt (regularizedL χ) z:ℂ)*transform a b γ z)
  simp only [norm_mul,Complex.norm_natCast] at hnorm
  have first := hnorm.trans (narrow q χ Z a b X γ B u.re hX ha hab hb hB hu1
    (fun z hz => ⟨(geom hz).1.le,hmax z hz,(geom hz).2.1⟩))
  have hd : 0≤1+A+Real.log B := by linarith [Real.log_nonneg (by linarith : 1≤B)]
  have hh : 0≤logHeight q B := zero_le_one.trans (logHeight_ge_one _ _)
  calc
    _ ≤ Real.sqrt q*(K*X^u.re*logHeight q B*(1+A+Real.log B)) :=
      mul_le_mul_of_nonneg_left first (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt q*(K*X^u.re*(10*L)*(10*A*L)) := by gcongr
    _ = (100*K*L^2)*(X^u.re*Real.sqrt q*A) := by ring
    _ ≤ (100*K*L^2)*N := mul_le_mul_of_nonneg_left hsc (by positivity)
    _ = _ := by dsimp [N,L];ring


def lowerWindowTerm {q : ℕ} [NeZero q] (n : ℕ) (χ : DirichletCharacter ℂ q) (p : ℕ×ℕ) (γ : ℝ) : ℂ :=
  ∑ z ∈ lowerWindowZeros n χ p.1 γ, (analyticOrderNatAt (regularizedL χ) z:ℂ)*transform p.1 p.2 γ z

def upperWindowTerm {q : ℕ} [NeZero q] (n : ℕ) (χ : DirichletCharacter ℂ q) (p : ℕ×ℕ) (γ : ℝ) : ℂ :=
  ∑ z ∈ (exceptionalZeros χ (heightCut p.1)).filter (fun z => (n:ℝ)^(3/4:ℝ) < localZeroScale q p.1 γ z.re),
    (analyticOrderNatAt (regularizedL χ) z:ℂ)*transform p.1 p.2 γ z

theorem splitWindowTerm {q : ℕ} [NeZero q] (n : ℕ) (χ : DirichletCharacter ℂ q) (p : ℕ×ℕ) (γ : ℝ) :
    lowerWindowTerm n χ p γ + upperWindowTerm n χ p γ = fixedZeroTerm χ p.1 p.2 p.1 γ := by
  simpa only [lowerWindowTerm,lowerWindowZeros,upperWindowTerm,fixedZeroTerm,not_le] using
    Finset.sum_filter_add_sum_filter_not (s:=exceptionalZeros χ (heightCut p.1))
      (fun z => localZeroScale q p.1 γ z.re ≤ (n:ℝ)^(3/4:ℝ))
      (fun z => (analyticOrderNatAt (regularizedL χ) z:ℂ)*transform p.1 p.2 γ z)

def adaptiveCorrection {q : ℕ} [NeZero q] (n : ℕ) (v : ZMod q) (β : ℝ) : ℂ :=
  ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => projectedThreshold n q < (χ.conductor:ℝ)),
    additiveWeight v χ * ((prefixBlocks (n-2)).map fun p => upperWindowTerm n χ p (2*Real.pi*β)).sum

private theorem splitAdaptive {q : ℕ} [NeZero q] (n : ℕ) (v : ZMod q) (β : ℝ) :
    projectedHighCorrection n v β - adaptiveCorrection n v β =
      ((prefixBlocks (n-2)).map fun p =>
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => projectedThreshold n q < (χ.conductor:ℝ)),
          additiveWeight v χ * lowerWindowTerm n χ p (2*Real.pi*β)).sum := by
  unfold projectedHighCorrection adaptiveCorrection characterZeroSum
  induction prefixBlocks (n-2) with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons,List.sum_cons,←splitWindowTerm n,mul_add,sum_add_distrib]
    rw [←ih]
    simp only [←splitWindowTerm n]
    abel

/-- The discarded part of the high-conductor correction is bounded by the
three-quarters scale times a fixed power of the logarithm, on every rational window. -/
theorem adaptive_discarded_finite :
    ∃ K : ℝ, 0<K ∧ ∀ (n : ℕ), 4≤n → ∀ (q : ℕ) [NeZero q], (q:ℝ)≤n → ∀ (v : ZMod q) (β : ℝ),
      ‖projectedHighCorrection n v β - adaptiveCorrection n v β‖ ≤ K*(n:ℝ)^(3/4:ℝ)*logScale n^3 := by
  obtain ⟨C,hC,residues⟩ := scaled_residue_bound
  refine ⟨3*C,by positivity,?_⟩
  intro n hn q _ hq v β
  let A := (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => projectedThreshold n q < (χ.conductor:ℝ))
  let γ := 2*Real.pi*β
  let D := C*(n:ℝ)^(3/4:ℝ)*logScale n^2
  let F := fun p : ℕ×ℕ => ∑ χ ∈ A,additiveWeight v χ * lowerWindowTerm n χ p γ
  have hD : 0≤D := by dsimp [D];positivity
  have hs : 0<Real.sqrt (q:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos q)
  have block (p : ℕ×ℕ) (hp : p∈prefixBlocks (n-2)) : ‖F p‖ ≤ D := by
    obtain ⟨hl,hlr,hr,hrn⟩ := prefixBlocks_valid hp
    have single (χ : DirichletCharacter ℂ q) : ‖lowerWindowTerm n χ p γ‖ ≤ D/Real.sqrt q := by
      apply (le_div_iff₀ hs).mpr
      rw [mul_comm]
      exact residues n q (by omega) hq χ p.1 p.2 p.1 γ (by exact_mod_cast hl) le_rfl
        (by exact_mod_cast hlr) (by exact_mod_cast hr) (by exact_mod_cast (show p.1≤n by omega))
    calc
      _ ≤ ∑ χ ∈ A, ‖additiveWeight v χ * lowerWindowTerm n χ p γ‖ := norm_sum_le ..
      _ ≤ ∑ χ ∈ A, ‖additiveWeight v χ‖*(D/Real.sqrt q) := by
        refine sum_le_sum fun χ _ => ?_
        rw [norm_mul];exact mul_le_mul_of_nonneg_left (single χ) (norm_nonneg _)
      _ = (∑ χ ∈ A, ‖additiveWeight v χ‖)*(D/Real.sqrt q) := (Finset.sum_mul ..).symm
      _ ≤ Real.sqrt q*(D/Real.sqrt q) := by
        apply mul_le_mul_of_nonneg_right _ (div_nonneg hD hs.le)
        calc
          _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖additiveWeight v χ‖ :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => norm_nonneg _)
          _ ≤ _ := sum_norm_additiveWeight_le v
      _ = D := by field_simp
  have pre := dyadic_prefix_corrected (fun _ => (0:ℂ)) F n (by omega) D
    (fun k _ => by simpa using hD) (fun p hp => by simpa using block p hp)
  simp only [sum_const_zero,zero_add] at pre
  rw [splitAdaptive]
  exact pre.trans ((mul_le_mul_of_nonneg_right (dyadic_count_le hn) hD).trans_eq (by dsimp [D];ring))

end GoldbachTwistedMellin
end
end

section
open Set Filter Complex Goldbach GoldbachGRHWindow DeepThreeQuarters
noncomputable section
namespace GoldbachTwistedMellin

/-- The pointwise model now retains only high-conductor characters and the
zeros whose individual dyadic real-part scale exceeds the global budget. -/
theorem deep_adaptive_model :
    ∀ η : ℝ, 0<η → ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ t ∈ Icc (0:ℝ) 1, t ∉ wideArcs n →
      ∀ (a q : ℕ) [NeZero q], a≤q → a.Coprime q → (q:ℝ)≤Real.sqrt n →
      |t-(a:ℝ)/q| ≤ 1/((q:ℝ)*Real.sqrt n) →
      ‖weightedSum n primeWeight t + adaptiveCorrection n (a:ZMod q) (t-(a:ℝ)/q)‖ ≤ (n:ℝ)^(3/4+η) := by
  intro η hη
  obtain ⟨N,hN⟩ := deep_projected_high_model (η/2) (half_pos hη)
  obtain ⟨K,hK,discard⟩ := adaptive_discarded_finite
  obtain ⟨D,hD,logs⟩ := quartic_log_scale (half_pos hη)
  obtain ⟨P,hP⟩ := eventually_atTop.mp (eventually_absorb (1+K*D) η hη)
  refine ⟨max 4 (max N P),?_⟩
  intro n hn t ht hdeep a q _ ha hc hq hβ
  let v : ZMod q := a
  let β := t-(a:ℝ)/q
  have hnR : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hn0 := zero_lt_one.trans_le hnR
  have hL := logScale_one hnR
  have hp := discard n (by omega) q (hq.trans (Real.sqrt_le_self_iff.mpr (Or.inr hnR))) v β
  have hl := (pow_le_pow_right₀ hL (by decide : 3≤4)).trans (logs n hnR)
  have he : ‖projectedHighCorrection n v β - adaptiveCorrection n v β‖ ≤ K*D*(n:ℝ)^(3/4+η/2) := by
    apply hp.trans
    calc
      _ ≤ K*(n:ℝ)^(3/4:ℝ)*(D*(n:ℝ)^(η/2)) := mul_le_mul_of_nonneg_left hl (by positivity)
      _ = _ := by rw [Real.rpow_add hn0];ring
  let S := weightedSum n primeWeight t
  have eq : S+adaptiveCorrection n v β =
      (S+projectedHighCorrection n v β) - (projectedHighCorrection n v β - adaptiveCorrection n v β) := by abel
  change ‖S+adaptiveCorrection n v β‖ ≤ _
  rw [eq]
  exact (norm_sub_le ..).trans ((add_le_add (hN n (by omega) t ht hdeep a q ha hc hq hβ) he).trans
    ((le_of_eq (by ring)).trans (hP n (by omega))))

/-- At a rational centre and q at most n^(3/8), the real-part filter
discards all zeros through 9/16 on every dyadic block. -/
theorem centre_strip_removed {n q : ℕ} (hn : 1≤n) (hq : (q:ℝ)≤(n:ℝ)^(3/8:ℝ))
    {X σ : ℝ} (hX : 1≤X) (hXn : X≤n) (hs : 0≤σ) (hs' : σ≤9/16) :
    localZeroScale q X 0 σ ≤ (n:ℝ)^(3/4:ℝ) := by
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 := zero_lt_one.trans_le hnR
  have hx := (Real.rpow_le_rpow (zero_le_one.trans hX) hXn hs).trans (Real.rpow_le_rpow_of_exponent_le hnR hs')
  have hq' : Real.sqrt q ≤ (n:ℝ)^(3/16:ℝ) := by
    apply (Real.sqrt_le_sqrt hq).trans_eq
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hn0.le]
    norm_num
  simp only [localZeroScale,abs_zero,mul_zero,zero_mul,add_zero,Real.sqrt_one,mul_one]
  apply (mul_le_mul hx hq' (Real.sqrt_nonneg _) (Real.rpow_nonneg hn0.le _)).trans_eq
  rw [←Real.rpow_add hn0]
  norm_num

end GoldbachTwistedMellin
end
end

section
open Set Complex Goldbach DeepThreeQuarters Filter
noncomputable section
namespace GoldbachTwistedMellin

/-- The exact deep-arc target is equivalent to cancellation in the fixed signed zero sum.
The zero criterion quantifies over every reduced Dirichlet approximant. -/
theorem deep_iff_adaptive_cancellation :
    (∀ η : ℝ, 0<η → ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ t ∈ Icc (0:ℝ) 1, t ∉ wideArcs n →
      ‖weightedSum n primeWeight t‖ ≤ (n:ℝ)^(3/4+η)) ↔
    (∀ η : ℝ, 0<η → ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ t ∈ Icc (0:ℝ) 1, t ∉ wideArcs n →
      ∀ (a q : ℕ) [NeZero q], a≤q → a.Coprime q → (q:ℝ)≤Real.sqrt n →
      |t-(a:ℝ)/q| ≤ 1/((q:ℝ)*Real.sqrt n) →
      ‖adaptiveCorrection n (a:ZMod q) (t-(a:ℝ)/q)‖ ≤ (n:ℝ)^(3/4+η)) := by
  constructor
  · intro target η hη
    obtain ⟨N,hN⟩ := target (η/2) (half_pos hη)
    obtain ⟨M,hM⟩ := deep_adaptive_model (η/2) (half_pos hη)
    obtain ⟨P,hP⟩ := eventually_atTop.1 (eventually_absorb 2 η hη)
    refine ⟨max N (max M P),?_⟩
    intro n hn t ht hdeep a q _ ha hc hq hβ
    have h₁ := hN n (by omega) t ht hdeep
    have h₂ := hM n (by omega) t ht hdeep a q ha hc hq hβ
    let S := weightedSum n primeWeight t
    let Z := adaptiveCorrection n (a:ZMod q) (t-(a:ℝ)/q)
    change ‖Z‖ ≤ _
    have h : Z = (S+Z)-S := by abel
    rw [h]
    exact (norm_sub_le ..).trans ((add_le_add h₂ h₁).trans ((le_of_eq (by ring)).trans (hP n (by omega))))
  · intro zeros η hη
    obtain ⟨N,hN⟩ := zeros (η/2) (half_pos hη)
    obtain ⟨M,hM⟩ := deep_adaptive_model (η/2) (half_pos hη)
    obtain ⟨P,hP⟩ := eventually_atTop.1 (eventually_absorb 2 η hη)
    refine ⟨max 1 (max N (max M P)),?_⟩
    intro n hn t ht hdeep
    obtain ⟨a,q,hq,ha,hc,hden,hβ⟩ := exists_dirichlet n (by omega) t ht
    let : NeZero q := ⟨by omega⟩
    have h₁ := hN n (by omega) t ht hdeep a q ha hc hden hβ
    have h₂ := hM n (by omega) t ht hdeep a q ha hc hden hβ
    let S := weightedSum n primeWeight t
    let Z := adaptiveCorrection n (a:ZMod q) (t-(a:ℝ)/q)
    change ‖S‖ ≤ _
    have h : S = (S+Z)-Z := by abel
    rw [h]
    exact (norm_sub_le ..).trans ((add_le_add h₂ h₁).trans ((le_of_eq (by ring)).trans (hP n (by omega))))
end GoldbachTwistedMellin
end
end

section
open Complex Set Finset Goldbach DirichletCharacter
noncomputable section
namespace GoldbachTwistedMellin
variable {f q : ℕ} [NeZero f] [NeZero q]

private def removedEuler (q : ℕ) (χ : DirichletCharacter ℂ f) (s : ℂ) : ℂ :=
  ∏ p ∈ q.primeFactors, (1 - χ p * (p : ℂ) ^ (-s))

omit [NeZero f] [NeZero q] in
private theorem diff_removedEuler (χ : DirichletCharacter ℂ f) :
    Differentiable ℂ (removedEuler q χ) := by
  unfold removedEuler
  apply Differentiable.fun_finsetProd
  intro p hp
  have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
  fun_prop

omit [NeZero f] [NeZero q] in
private theorem removedEuler_ne_zero (χ : DirichletCharacter ℂ f) {s : ℂ} (hs : 0<s.re) :
    removedEuler q χ s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hpR : 1 < (p:ℝ) := by exact_mod_cast hp'.one_lt
  apply sub_ne_zero.mpr
  intro e
  have hlt : ‖χ p * (p:ℂ)^(-s)‖ < 1 := by
    rw [norm_mul,norm_natCast_cpow_of_pos hp'.pos, neg_re]
    calc
      _ ≤ 1*(p:ℝ)^(-s.re) := mul_le_mul_of_nonneg_right (χ.norm_le_one _) (by positivity)
      _ < 1 := by simpa using Real.rpow_lt_one_of_one_lt_of_neg hpR (neg_lt_zero.mpr hs)
  simp [←e] at hlt

private theorem regularized_changeLevel (hd : f ∣ q) (χ : DirichletCharacter ℂ f) :
    regularizedL (changeLevel hd χ) = regularizedL χ * removedEuler q χ := by
  have lhs := (analytic_regularizedL (changeLevel hd χ)).continuousOn
  have rhs := (analytic_regularizedL χ).continuousOn.mul (diff_removedEuler (q:=q) χ).continuous.continuousOn
  apply (continuousOn_univ.mp lhs).ext_on (dense_compl_singleton 1) (continuousOn_univ.mp rhs)
  intro s hs
  have hs1 : s ≠ 1 := hs
  change regularizedL (changeLevel hd χ) s = regularizedL χ s * _
  by_cases hχ : χ = 1
  · subst χ
    have hL := LFunction_changeLevel hd (1 : DirichletCharacter ℂ f) (Or.inr hs1)
    simp only [map_one] at hL ⊢
    simp only [regularizedL,ite_true,LFunctionTrivChar₁,Function.update_of_ne hs1,LFunctionTrivChar]
    rw [hL]
    change _ = _ * ∏ p ∈ q.primeFactors, _
    ring
  · have hi : changeLevel hd χ ≠ 1 := mt (changeLevel_eq_one_iff hd).mp hχ
    simpa only [regularizedL, ite_eq_right hχ, ite_eq_right hi, removedEuler] using
      LFunction_changeLevel hd χ (Or.inl hχ) (s:=s)

theorem zeros_changeLevel (hd : f ∣ q) (χ : DirichletCharacter ℂ f) (B : ℝ) :
    exceptionalZeros (changeLevel hd χ) B = exceptionalZeros χ B := by
  ext s
  rw [mem_exceptionalZeros,mem_exceptionalZeros,regularized_changeLevel,Pi.mul_apply]
  constructor
  · rintro ⟨hl,hi,hz⟩
    exact ⟨hl,hi,(mul_eq_zero.mp hz).resolve_right (removedEuler_ne_zero χ (show 0<s.re by linarith))⟩
  · rintro ⟨hl,hi,hz⟩
    exact ⟨hl,hi,by rw [hz,zero_mul]⟩

theorem order_changeLevel (hd : f ∣ q) (χ : DirichletCharacter ℂ f) {s : ℂ} (hs : 0<s.re) :
    analyticOrderNatAt (regularizedL (changeLevel hd χ)) s = analyticOrderNatAt (regularizedL χ) s := by
  have h := (diff_removedEuler (q:=q) χ).analyticAt s
  rw [regularized_changeLevel,analyticOrderNatAt,analyticOrderAt_mul
    ((analytic_regularizedL χ) _ (Set.mem_univ _)) h,
    h.analyticOrderAt_eq_zero.mpr (removedEuler_ne_zero χ hs),add_zero]
  rfl

theorem fixedZeroTerm_changeLevel (hd : f ∣ q) (χ : DirichletCharacter ℂ f) (a b X β : ℝ) :
    fixedZeroTerm (changeLevel hd χ) a b X β = fixedZeroTerm χ a b X β := by
  unfold fixedZeroTerm
  rw [zeros_changeLevel]
  refine sum_congr rfl fun z hz => ?_
  have h := ((mem_exceptionalZeros χ _ z).mp hz).1
  rw [order_changeLevel hd χ (show 0<z.re by linarith)]

theorem characterZeroSum_changeLevel (hd : f ∣ q) (χ : DirichletCharacter ℂ f) (n : ℕ) (β : ℝ) :
    characterZeroSum n (changeLevel hd χ) β = characterZeroSum n χ β := by
  simp only [characterZeroSum, fixedZeroTerm_changeLevel]

end GoldbachTwistedMellin
end
end

section
open Complex Finset DirichletCharacter GoldbachConductorGauss
open scoped Classical
noncomputable section
namespace GoldbachTwistedMellin

private theorem conductor_fibre {d q : ℕ} [NeZero d] [NeZero q] (hd : d∣q) :
    (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor=d) =
      ((univ : Finset (DirichletCharacter ℂ d)).filter DirichletCharacter.IsPrimitive).image (changeLevel hd) := by
  ext χ
  simp only [mem_filter,mem_univ,true_and,mem_image]
  constructor
  · intro eq
    obtain ⟨_,ψ,he⟩ : χ.FactorsThrough d := eq ▸ χ.factorsThrough_conductor
    refine ⟨ψ,?_,he.symm⟩
    rw [isPrimitive_def,←conductor_changeLevel ψ hd,←he,eq]
  · rintro ⟨ψ,hψ,rfl⟩
    exact (conductor_changeLevel ψ hd).trans hψ

private theorem conductor_lifts {d q : ℕ} [NeZero d] [NeZero q] (hd : d∣q) :
    (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor∣d) =
      (univ : Finset (DirichletCharacter ℂ d)).image (changeLevel hd) := by
  ext χ
  simp only [mem_filter,mem_univ,true_and,mem_image]
  constructor
  · intro hf
    obtain ⟨_,ψ,he⟩ := (mem_conductorSet_iff_conductor_dvd χ hd).mpr hf
    exact ⟨ψ,he.symm⟩
  · rintro ⟨ψ,rfl⟩;rw [conductor_changeLevel];exact ψ.conductor_dvd_level

/-- Unnormalized additive weights preserve both phases of the conductor descent:
the Möbius sign and the value of the inverse character on the quotient. -/
theorem conductor_gauss_weight {d q : ℕ} [NeZero d] [NeZero q] (hd : d∣q)
    (a : ℕ) (ha : a.Coprime q) (ψ : DirichletCharacter ℂ d) :
    (q.totient:ℂ)*additiveWeight (a:ZMod q) (changeLevel hd ψ) =
      (ArithmeticFunction.moebius (q/d):ℂ)*(d.totient:ℂ)*additiveWeight (a:ZMod d) ψ*ψ⁻¹ ((q/d:ℕ):ZMod d) := by
  obtain ⟨m,rfl⟩ := hd
  let : NeZero m := ⟨fun h => NeZero.ne (d*m) (by simp [h])⟩
  have div : d*m/d=m := Nat.mul_div_cancel_left m (NeZero.pos d)
  let D := dvd_mul_right d m
  obtain ⟨u,hu⟩ := (ZMod.isUnit_iff_coprime a (d*m)).mpr ha
  let v := ZMod.unitsMap D u
  have hv : (v:ZMod d)=(a:ZMod d) := by
    change ZMod.castHom D (ZMod d) (u : ZMod (d*m)) = _
    rw [hu,map_natCast]
  have he : changeLevel D ψ u = ψ v := changeLevel_eq_cast_of_dvd ψ D u
  rw [div,←hu,←hv,additiveWeight_unit,additiveWeight_unit,additiveWeight_gauss,additiveWeight_gauss,
    AddChar.mulShift_one,←map_inv,induced_gaussSum,he]
  have hφ : (((d*m).totient:ℕ):ℂ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos (d*m))).ne'
  have hψ : (d.totient:ℂ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos d)).ne'
  simp only [AddChar.mulShift_one]
  field_simp

/-- Families of character data that agree under inflation to any multiple of their level. -/
structure DescendingKernel where
  coeff : {q : ℕ} → [NeZero q] → ℕ → DirichletCharacter ℂ q → ℝ → ℂ
  compatible : ∀ {d q : ℕ} [NeZero d] [NeZero q] (hd : d∣q) (ψ : DirichletCharacter ℂ d) (n : ℕ) (β : ℝ),
    coeff n (changeLevel hd ψ) β = coeff n ψ β

variable (K : DescendingKernel)

def kernelCorrection {q : ℕ} [NeZero q] (n : ℕ) (v : ZMod q) (β : ℝ) : ℂ :=
  ∑ χ : DirichletCharacter ℂ q,additiveWeight v χ * K.coeff n χ β

/-- Character sums at their own level; the quotient twist is zero on a
nonunit. This definition includes level one and both choices of character set. -/
def levelTransform (primitive : Bool) (d m a n : ℕ) (β : ℝ) : ℂ := by
  classical
  exact if h : d=0 then 0 else
    let _ : NeZero d := ⟨h⟩
    ∑ ψ ∈ (if primitive then (univ : Finset (DirichletCharacter ℂ d)).filter DirichletCharacter.IsPrimitive else univ),
      additiveWeight (a:ZMod d) ψ*ψ⁻¹ (m:ZMod d)*K.coeff n ψ β

theorem levelTransform_eq (primitive : Bool) {d : ℕ} [NeZero d] (m a n : ℕ) (β : ℝ) :
    levelTransform K primitive d m a n β =
    ∑ ψ ∈ (if primitive then (univ : Finset (DirichletCharacter ℂ d)).filter DirichletCharacter.IsPrimitive else univ),
      additiveWeight (a:ZMod d) ψ*ψ⁻¹ (m:ZMod d)*K.coeff n ψ β := by
  simp only [levelTransform,dite_eq_right (NeZero.ne d)]

private theorem transport_fibre (primitive : Bool) {d q : ℕ} [NeZero d] [NeZero q] (hd : d∣q)
    (a n : ℕ) (ha : a.Coprime q) (β : ℝ) :
    (q.totient:ℂ)*(∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
      (fun χ => if primitive then χ.conductor=d else χ.conductor∣d),
      additiveWeight (a:ZMod q) χ*K.coeff n χ β) =
    (ArithmeticFunction.moebius (q/d):ℂ)*(d.totient:ℂ)*levelTransform K primitive d (q/d) a n β := by
  let S := if primitive then (univ : Finset (DirichletCharacter ℂ d)).filter DirichletCharacter.IsPrimitive else univ
  have sets : (univ : Finset (DirichletCharacter ℂ q)).filter
      (fun χ => if primitive then χ.conductor=d else χ.conductor∣d) = S.image (changeLevel hd) := by
    cases primitive
    · simpa [S] using conductor_lifts hd
    · simpa [S] using conductor_fibre hd
  rw [sets,Finset.sum_image (fun _ _ _ _ h => changeLevel_injective hd h),levelTransform_eq K,
    Finset.mul_sum,Finset.mul_sum]
  refine sum_congr rfl fun ψ _ => ?_
  rw [←mul_assoc,conductor_gauss_weight hd a ha ψ,K.compatible]
  ring


private def fibreAt {q : ℕ} (a n : ℕ) [NeZero q] (β : ℝ) (d : ℕ) : ℂ :=
  ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor=d),
    additiveWeight (a:ZMod q) χ * K.coeff n χ β

private def liftsAt {q : ℕ} (a n : ℕ) [NeZero q] (β : ℝ) (d : ℕ) : ℂ :=
  ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor∣d),
    additiveWeight (a:ZMod q) χ * K.coeff n χ β

private theorem sum_fibres {q : ℕ} [NeZero q] (a n : ℕ) (β : ℝ) (k : ℕ) (hk : 0<k) :
    (∑ d ∈ k.divisors,fibreAt (q:=q) K a n β d) = liftsAt (q:=q) K a n β k := by
  let A := (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor∣k)
  let w := fun χ : DirichletCharacter ℂ q => additiveWeight (a:ZMod q) χ*K.coeff n χ β
  have maps (χ) (hχ : χ∈A) : χ.conductor ∈ k.divisors := Nat.mem_divisors.mpr ⟨(mem_filter.mp hχ).2,hk.ne'⟩
  change _ = ∑ χ ∈ A, w χ
  rw [←sum_fiberwise_of_maps_to maps w]
  refine sum_congr rfl fun d hd => ?_
  unfold fibreAt
  apply sum_congr _ (fun _ _ => rfl)
  ext χ
  simp only [A,mem_filter,mem_univ,true_and]
  exact ⟨fun e => ⟨e ▸ Nat.dvd_of_mem_divisors hd,e⟩,And.right⟩

private theorem all_level {q : ℕ} [NeZero q] (a n : ℕ) (β : ℝ) :
    levelTransform K false q 1 a n β = kernelCorrection K n (a:ZMod q) β := by
  simp only [levelTransform_eq K,Bool.false_eq_true,ite_false,Nat.cast_one,map_one,mul_one,kernelCorrection]

private theorem all_lifts {q : ℕ} [NeZero q] (a n : ℕ) (β : ℝ) :
    liftsAt (q:=q) K a n β q = kernelCorrection K n (a:ZMod q) β := by
  unfold liftsAt
  rw [kernelCorrection]
  congr 1
  ext χ;simp [χ.conductor_dvd_level]

private theorem primitive_at_level {q : ℕ} [NeZero q] (a n : ℕ) (β : ℝ) :
    levelTransform K true q 1 a n β = fibreAt (q:=q) K a n β q := by
  simp only [levelTransform_eq K,ite_true,Nat.cast_one,map_one,mul_one,fibreAt,isPrimitive_def]

/-- Both directions of descent hold as complex equalities before taking norms.
The inverse has the squared Möbius coefficient. -/
theorem conductor_descent_pair {q : ℕ} [NeZero q] (a n : ℕ) (ha : a.Coprime q) (β : ℝ) :
    ((q.totient:ℂ)*kernelCorrection K n (a:ZMod q) β =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius (q/d):ℂ)*(d.totient:ℂ)*levelTransform K true d (q/d) a n β) ∧
    ((q.totient:ℂ)*levelTransform K true q 1 a n β =
      ∑ d ∈ q.divisors,(ArithmeticFunction.moebius (q/d):ℂ)^2*(d.totient:ℂ)*levelTransform K false d (q/d) a n β) := by
  have hq := NeZero.pos q
  constructor
  · rw [←all_lifts K,←sum_fibres K a n β q hq,Finset.mul_sum]
    refine sum_congr rfl fun d hd => ?_
    let : NeZero d := ⟨(Nat.pos_of_mem_divisors hd).ne'⟩
    simpa only [fibreAt,ite_true] using transport_fibre K true (Nat.dvd_of_mem_divisors hd) a n ha β
  · have inv := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp (sum_fibres (q:=q) K a n β) q hq
    rw [primitive_at_level K,←inv,Finset.mul_sum]
    rw [Nat.sum_divisorsAntidiagonal' (fun m d => (q.totient:ℂ)*((ArithmeticFunction.moebius m:ℂ)*liftsAt (q:=q) K a n β d))]
    refine sum_congr rfl fun d hd => ?_
    let : NeZero d := ⟨(Nat.pos_of_mem_divisors hd).ne'⟩
    have e : (q.totient:ℂ)*liftsAt (q:=q) K a n β d =
        (ArithmeticFunction.moebius (q/d):ℂ)*(d.totient:ℂ)*levelTransform K false d (q/d) a n β := by
      simpa only [liftsAt,Bool.false_eq_true,ite_false] using transport_fibre K false (Nat.dvd_of_mem_divisors hd) a n ha β
    linear_combination (ArithmeticFunction.moebius (q/d):ℂ)*e


/-- A unit quotient is absorbed by changing the numerator at the inducing level.
The twist vanishes identically when the quotient is a nonunit. -/
theorem conductor_twist {d : ℕ} [NeZero d] (p : Bool) (m a n : ℕ) (ha : a.Coprime d) (β : ℝ) :
    levelTransform K p d m a n β =
      if h : IsUnit (m:ZMod d) then
        levelTransform K p d 1 ((a:ZMod d)*(h.unit⁻¹ : (ZMod d)ˣ)).val n β else 0 := by
  classical
  split_ifs with hm
  · rw [levelTransform_eq K,levelTransform_eq K]
    obtain ⟨u,hu⟩ := (ZMod.isUnit_iff_coprime a d).mpr ha
    let v := u*hm.unit⁻¹
    have ev : (((a:ZMod d)*(hm.unit⁻¹ : (ZMod d)ˣ)).val : ZMod d) = v := by
      rw [ZMod.natCast_zmod_val,←hu];rfl
    have inv (ψ : DirichletCharacter ℂ d) : ψ⁻¹ (m:ZMod d)=ψ ((hm.unit⁻¹ : (ZMod d)ˣ):ZMod d) := by
      rw [MulChar.inv_apply_eq_inv']
      apply inv_eq_of_mul_eq_one_right
      simpa using (ψ.map_mul (hm.unit:ZMod d) ((hm.unit⁻¹ : (ZMod d)ˣ):ZMod d)).symm
    refine sum_congr rfl fun ψ _ => ?_
    rw [ev,←hu,additiveWeight_unit u,additiveWeight_unit v,inv]
    simp only [v,Units.val_mul,map_mul,Nat.cast_one,map_one,mul_one]
    ring
  · rw [levelTransform_eq K]
    exact sum_eq_zero fun ψ _ => by rw [MulChar.map_nonunit ψ⁻¹ hm,mul_zero,zero_mul]

theorem conductor_shift_bound {d : ℕ} [NeZero d] (p : Bool) (m a n : ℕ) (ha : a.Coprime d)
    (β B : ℝ) (hB : 0≤B) (all : ∀ b : ℕ, b<d → b.Coprime d → ‖levelTransform K p d 1 b n β‖≤B) :
    ‖levelTransform K p d m a n β‖≤B := by
  rw [conductor_twist K p m a n ha β]
  split_ifs with h
  · let v : ZMod d := (a:ZMod d)*(h.unit⁻¹ : (ZMod d)ˣ)
    have hv : IsUnit v := ((ZMod.isUnit_iff_coprime a d).mpr ha).mul (h.unit⁻¹).isUnit
    exact all v.val (ZMod.val_lt _) ((ZMod.isUnit_iff_coprime _ _).mp (by simpa only [ZMod.natCast_zmod_val] using hv))
  · simpa using hB

/-- Uniform bounds transfer between primitive and full transforms, with loss
at most q/φ(q), at the same ordinate offset. Divisor levels are all that occur. -/
theorem conductor_two_way_bound {q : ℕ} [NeZero q] (p : Bool) (a n : ℕ) (ha : a.Coprime q)
    (β B : ℝ) (hB : 0≤B)
    (estimate : ∀ d ∈ q.divisors, ∀ b : ℕ, b<d → b.Coprime d → ‖levelTransform K p d 1 b n β‖≤B) :
    ‖levelTransform K (!p) q 1 a n β‖ ≤ ((q:ℝ)/q.totient)*B := by
  let c (m : ℕ) : ℂ := if p then (ArithmeticFunction.moebius m:ℂ) else (ArithmeticFunction.moebius m:ℂ)^2
  have e : (q.totient:ℂ)*levelTransform K (!p) q 1 a n β =
      ∑ d ∈ q.divisors,c (q/d)*(d.totient:ℂ)*levelTransform K p d (q/d) a n β := by
    cases p
    · simpa only [c,Bool.not_false,Bool.false_eq_true,ite_false] using (conductor_descent_pair K a n ha β).2
    · simpa only [c,Bool.not_true,ite_true,all_level K] using (conductor_descent_pair K a n ha β).1
  have normc (m : ℕ) : ‖c m‖≤1 := by
    have h : ‖(ArithmeticFunction.moebius m:ℂ)‖≤1 := by
      rw [Complex.norm_intCast];exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=m)
    cases p
    · simpa [c] using pow_le_one₀ (norm_nonneg _) h (n:=2)
    · simpa [c] using h
  have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have lhs : (q.totient:ℝ)*‖levelTransform K (!p) q 1 a n β‖ ≤ (q:ℝ)*B := by
    rw [←Complex.norm_natCast,←norm_mul,e]
    apply (norm_sum_le ..).trans
    calc
      _ ≤ ∑ d ∈ q.divisors,(d.totient:ℝ)*B := by
        refine sum_le_sum fun d hd => ?_
        let : NeZero d := ⟨(Nat.pos_of_mem_divisors hd).ne'⟩
        have hc := Nat.Coprime.of_dvd_right (Nat.dvd_of_mem_divisors hd) ha
        have bound := conductor_shift_bound K p (q/d) a n hc β B hB (estimate d hd)
        simp only [norm_mul,Complex.norm_natCast]
        exact (mul_le_mul (mul_le_mul_of_nonneg_right (normc _) (Nat.cast_nonneg _)) bound (norm_nonneg _) (by positivity)).trans_eq (by ring)
      _ = _ := by rw [←Finset.sum_mul,←Nat.cast_sum,Nat.sum_totient]
  calc
    _ ≤ ((q:ℝ)*B)/q.totient := (le_div_iff₀ hφ).mpr (by rw [mul_comm];exact lhs)
    _ = _ := by ring

end GoldbachTwistedMellin
end
end

section
open Complex Set MeasureTheory
open scoped Interval
noncomputable section
namespace GoldbachTwistedMellin

private def linearFrequency (γ : ℝ) : ℂ := (γ:ℂ)*I
private theorem frequency_norm (γ : ℝ) : ‖linearFrequency γ‖=|γ| := by simp [linearFrequency,Real.norm_eq_abs]

private theorem scaled_power_ibp {l r : ℝ} (hl : 0<l) (hlr : l≤r) (γ : ℝ) {s : ℂ} (hs : 0<s.re) :
    s*(∫ x in l..r,density γ s x) = density γ (s+1) r-density γ (s+1) l-linearFrequency γ*(∫ x in l..r,density γ (s+1) x) := by
  have deriv (x : ℝ) (hx : 0<x) : HasDerivAt (density γ (s+1)) (s*density γ s x+linearFrequency γ*density γ (s+1) x) x := by
    have he := (phase_deriv γ x).mul (hasDerivAt_ofReal_cpow_const hx.ne' (show s≠0 by rintro rfl;simp at hs))
    rw [show density γ (s+1) = fun y : ℝ => phase γ y*(y:ℂ)^s from funext (density_succ γ s)]
    convert he using 1
    unfold density linearFrequency;ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=density γ (s+1)) (a:=l) (b:=r)
    (fun x hx => deriv x (hl.trans_le (((uIcc_of_le hlr) ▸ hx).1)))
    (((integral_density hl hlr γ s).const_mul s).add ((integral_density hl hlr γ (s+1)).const_mul (linearFrequency γ)))
  rw [intervalIntegral.integral_add ((integral_density hl hlr γ s).const_mul s) ((integral_density hl hlr γ (s+1)).const_mul (linearFrequency γ)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at h
  exact eq_sub_of_add_eq h

private theorem sharp_endpoint {X l r γ : ℝ} (hX : 1≤X) (hl : X≤l) (hlr : l≤r) (hr : r≤2*X)
    {s : ℂ} (hs : 0<s.re) (hs' : s.re≤1) (hn : 0<‖s+1‖) :
    ‖∫ x in l..r,density γ (s+1) x‖ ≤ (4*X^2*(2+|γ| *(r-l)))/‖s+1‖ := by
  have xl : 0<l := zero_lt_one.trans_le (hX.trans hl)
  have bnd (x : ℝ) (hx : x ∈ Icc l r) : ‖density γ ((s+1)+1) x‖ ≤ 4*X^2 := by
    rw [density_succ,norm_mul,norm_phase,one_mul,norm_cpow_eq_rpow_re_of_pos (xl.trans_le hx.1),add_re,one_re]
    calc
      x^(s.re+1) ≤ (2*X)^(s.re+1) := Real.rpow_le_rpow (xl.le.trans hx.1) (hx.2.trans hr) (by linarith)
      _ ≤ (2*X)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = _ := by norm_num;ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a:=l) (b:=r)
    (fun x hx => bnd x (by rw [uIoc_of_le hlr] at hx;exact ⟨hx.1.le,hx.2⟩))
  rw [abs_of_nonneg (sub_nonneg.mpr hlr)] at hi
  have e := scaled_power_ibp xl hlr γ (s:=s+1) (by simp only [add_re,one_re];linarith)
  have he := norm_sub_le (density γ ((s+1)+1) r-density γ ((s+1)+1) l) (linearFrequency γ*(∫ x in l..r,density γ ((s+1)+1) x))
  rw [←e,norm_mul,norm_mul,frequency_norm] at he
  apply (le_div_iff₀ hn).mpr
  nlinarith only [he,norm_sub_le (density γ ((s+1)+1) r) (density γ ((s+1)+1) l),
    bnd r (right_mem_Icc.mpr hlr),bnd l (left_mem_Icc.mpr hlr),mul_le_mul_of_nonneg_left hi (abs_nonneg γ)]

/-- The rational offset constraint controls the square of the angular frequency.
Two integrations by parts then cost only the square of the dyadic scale. -/
theorem short_height_decay {X a b γ : ℝ} (hX : 1≤X) (ha : X≤a) (hab : a+1≤b)
    (hb : b+1≤2*X) (hγ : |γ|≤1) (hf : |γ| ^2*X≤64) (s : ℂ)
    (hs : 0<s.re) (hs' : s.re≤1) (ht : 0 < |s.im|) :
    ‖transform a b γ s‖ ≤ 288*X^2/ |s.im| ^2 := by
  let D := 4*X^2/‖s+1‖
  have t1 : |s.im|≤‖s+1‖ := by simpa using abs_im_le_norm (s+1)
  have hn := ht.trans_le t1
  have hD : 0≤D := by dsimp [D];positivity
  have bound {l r : ℝ} (hl : X≤l) (hlr : l≤r) (hr : r≤2*X) : ‖∫ x in l..r,density γ (s+1) x‖ ≤ D*(2+|γ| *(r-l)) :=
    (sharp_endpoint hX hl hlr hr hs hs' hn).trans_eq (by dsimp [D];ring)
  have endpt (l : ℝ) (hl : X≤l) (hr : l+1≤2*X) : ‖∫ x in l..l+1,density γ (s+1) x‖ ≤ 3*D := by
    have h := bound hl (by linarith : l≤l+1) hr
    have hle := mul_le_mul_of_nonneg_left hγ hD
    nlinarith only [h,hle]
  have all : ‖transform a b γ (s+1)‖ ≤ D*(2+|γ| *X) := by
    refine norm_transform_le (zero_lt_one.trans_le hX) ha hab hb γ (s+1) (fun l r hl hlr hr => ?_)
    apply (bound hl hlr hr).trans
    gcongr
    linarith
  have e := transform_recurrence (zero_lt_one.trans_le (hX.trans ha)) hab γ hs
  change s*transform a b γ s = _ - linearFrequency γ*transform a b γ (s+1) at e
  have tr := norm_sub_le ((∫ x in b..b+1,density γ (s+1) x)-(∫ x in a..a+1,density γ (s+1) x)) (linearFrequency γ*transform a b γ (s+1))
  rw [←e,norm_mul,norm_mul,frequency_norm] at tr
  have small : ‖s‖*‖transform a b γ s‖ ≤ 72*D := by
    nlinarith only [tr,norm_sub_le (∫ x in b..b+1,density γ (s+1) x) (∫ x in a..a+1,density γ (s+1) x),
      endpt a ha (by linarith),endpt b (by linarith) hb,mul_le_mul_of_nonneg_left all (abs_nonneg γ),
      mul_le_mul_of_nonneg_left hf hD,mul_le_mul_of_nonneg_left hγ hD]
  have eq : 72*D=288*X^2/‖s+1‖ := by dsimp [D];ring
  rw [eq] at small
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  calc
    _ = |s.im| *‖transform a b γ s‖*|s.im| := by ring
    _ ≤ ‖s‖*‖transform a b γ s‖*‖s+1‖ := mul_le_mul (mul_le_mul_of_nonneg_right (abs_im_le_norm s) (norm_nonneg _)) t1 ht.le (by positivity)
    _ ≤ _ := (le_div_iff₀ hn).mp small
end GoldbachTwistedMellin
end
end

section
open Complex Set Finset Goldbach
noncomputable section
namespace GoldbachTwistedMellin

private def signedBin (y : ℝ) : Bool×ℕ := (decide (0≤y),⌊|y|⌋₊)
private def ordinateCenter (p : Bool×ℕ) : ℝ := if p.1 then (p.2:ℝ) else -(p.2:ℝ)
private theorem bin_range (y : ℝ) : ((signedBin y).2:ℝ) ≤ |y| ∧ |y-ordinateCenter (signedBin y)| ≤ 1 := by
  have h := Nat.floor_le (abs_nonneg y)
  have h' := Nat.lt_floor_add_one |y|
  refine ⟨h,?_⟩
  by_cases hy : 0≤y
  · simp only [abs_of_nonneg hy] at h h'
    simp [ordinateCenter,signedBin,hy,abs_of_nonneg hy,abs_le];constructor <;> linarith
  · have hn := le_of_not_ge hy
    simp only [abs_of_nonpos hn] at h h'
    simp [ordinateCenter,signedBin,hy,abs_of_nonpos hn,abs_le];constructor <;> linarith

private theorem inverse_square_tail (M : ℕ) {T : ℝ} (hT : 2≤T) :
    (∑ j ∈ range M,if ⌊T⌋₊≤j then 1/(j:ℝ)^2 else 0) ≤ 4/T := by
  let J := ⌊T⌋₊
  have hJ : 1≤J := (Nat.le_floor_iff (by linarith : 0≤T)).mpr (by norm_num;linarith)
  have hJR : (1:ℝ)≤J := by exact_mod_cast hJ
  have hJT := Nat.lt_floor_add_one T
  change T < (J:ℝ)+1 at hJT
  have sub : (range M).filter (fun j => J≤j) = Finset.Ico J M := by ext j;simp [and_comm]
  rw [←sum_filter,sub]
  by_cases h : J≤M
  · have per (j : ℕ) (hj : j∈Finset.Ico J M) :
        1/(j:ℝ)^2 ≤ 2*(1/(j:ℝ)-1/((j+1:ℕ):ℝ)) := by
      have hjR : (1:ℝ)≤j := by exact_mod_cast hJ.trans (Finset.mem_Ico.mp hj).1
      have j0 := zero_lt_one.trans_le hjR
      push_cast
      field_simp
      nlinarith only [hjR,sq_nonneg ((j:ℝ)-1)]
    have tele (h : ℕ) :
        (∑ j ∈ range h,(1/(j:ℝ)-1/((j+1:ℕ):ℝ))) = 1/(0:ℝ)-1/(h:ℝ) := by
      induction h with
      | zero => simp
      | succ h ih => rw [sum_range_succ,ih];ring
    apply (sum_le_sum per).trans
    rw [←mul_sum,sum_Ico_eq_sub _ h,tele,tele]
    apply (le_div_iff₀ (by linarith : 0<T)).mpr
    have h0 : 0<(J:ℝ) := zero_lt_one.trans_le hJR
    have hpart : 2*T/(J:ℝ)≤4 := (div_le_iff₀ h0).mpr (by linarith)
    have hrest : 0≤2*T/(M:ℝ) := by positivity
    calc
      _ = 2*T/(J:ℝ)-2*T/(M:ℝ) := by ring
      _ ≤ 4 := by linarith only [hpart,hrest]
  · rw [Finset.Ico_eq_empty_of_le (by omega),sum_empty];positivity

/-- Removing all ordinates above T has cost proportional to X²/T, including analytic multiplicity. -/
theorem short_ordinate_tail :
    ∃ C : ℝ, 0<C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Z : Finset ℂ)
      (a b X γ B T : ℝ), 1≤X → X≤a → a+1≤b → b+1≤2*X → |γ|≤1 → |γ| ^2*X≤64 →
      2≤T → 0≤B → (∀ z∈Z, 1/2≤z.re ∧ z.re≤1 ∧ T ≤ |z.im| ∧ |z.im|≤B) →
      (∑ z ∈ Z,(analyticOrderNatAt (regularizedL χ) z:ℝ)*‖transform a b γ z‖) ≤
        C*X^2*logHeight q B/T := by
  classical
  obtain ⟨K,hK,slice⟩ := unconditional_right_slice_count
  refine ⟨2304*K,by positivity,?_⟩
  intro q _ χ Z a b X γ B T hX ha hab hb hγ hf hT hB geom
  let M := ⌊B⌋₊+1
  let bin := fun z : ℂ => signedBin z.im
  let mult := fun z : ℂ => (analyticOrderNatAt (regularizedL χ) z:ℝ)
  let D := K*logHeight q B*(288*X^2)
  let f (j : ℕ) : ℝ := if ⌊T⌋₊≤j then 1/(j:ℝ)^2 else 0
  have hlog : 0≤logHeight q B := zero_le_one.trans (logHeight_ge_one _ _)
  have hD : 0≤D := by dsimp [D];positivity
  have cover (z : ℂ) (hz : z∈Z) : bin z∈grid M :=
    mem_product.mpr ⟨mem_univ _,mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (geom z hz).2.2.2))⟩
  have per (p : Bool×ℕ) (hp : p∈grid M) :
      (∑ z ∈ Z.filter (fun z => bin z=p),mult z*‖transform a b γ z‖) ≤ D*f p.2 := by
    let Y := Z.filter (fun z => bin z=p)
    by_cases hy : Y.Nonempty
    on_goal 2 =>
      rw [show Z.filter (fun z => bin z=p)=∅ from Finset.not_nonempty_iff_eq_empty.mp hy,sum_empty]
      exact mul_nonneg hD (by dsimp [f];split_ifs <;> positivity)
    obtain ⟨u,hu⟩ := hy
    obtain ⟨huZ,heu⟩ := mem_filter.mp hu
    have jlo : ⌊T⌋₊≤p.2 := by rw [←heu];exact Nat.floor_mono (geom u huZ).2.2.1
    have jone : 1≤⌊T⌋₊ := (Nat.le_floor_iff (by linarith : 0≤T)).mpr (by norm_num;linarith)
    have jpos : 0<(p.2:ℝ) := by exact_mod_cast (show 0<p.2 by omega)
    have hcnt := slice q χ (ordinateCenter p) Y (fun z hz => by
      obtain ⟨hzZ,he⟩ := mem_filter.mp hz
      exact ⟨(geom z hzZ).1,(geom z hzZ).2.1.trans (by norm_num),
        by simpa only [←he,bin] using (bin_range z.im).2⟩)
    have hc : |ordinateCenter p|=(p.2:ℝ) := by dsimp [ordinateCenter];split <;> simp
    have height : logHeight q (ordinateCenter p)≤logHeight q B := by
      apply logHeight_mono_abs;rw [hc,abs_of_nonneg hB,←heu]
      exact (bin_range u.im).1.trans (geom u huZ).2.2.2
    have cnt : (∑ z ∈ Y,mult z) ≤ K*logHeight q B := hcnt.trans (mul_le_mul_of_nonneg_left height hK.le)
    have single (z : ℂ) (hz : z∈Y) : ‖transform a b γ z‖≤288*X^2/(p.2:ℝ)^2 := by
      obtain ⟨hzZ,he⟩ := mem_filter.mp hz
      obtain ⟨h₁,h₂,h₃,_⟩ := geom z hzZ
      have hj : (p.2:ℝ) ≤ |z.im| := by rw [←he];exact (bin_range z.im).1
      apply (short_height_decay hX ha hab hb hγ hf z (by linarith) h₂ (by linarith)).trans
      exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos jpos) (pow_le_pow_left₀ jpos.le hj 2)
    apply (sum_le_sum fun z hz => mul_le_mul_of_nonneg_left (single z hz) (Nat.cast_nonneg _)).trans
    rw [←Finset.sum_mul]
    exact (mul_le_mul_of_nonneg_right cnt (by positivity)).trans_eq (by dsimp [D,f];rw [ite_eq_left jlo];ring)
  have all := sum_le_sum per
  rw [Finset.sum_fiberwise_of_maps_to cover,←Finset.mul_sum,sum_grid_weight] at all
  exact (all.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (inverse_square_tail M hT) (by norm_num : (0:ℝ)≤2)) hD)).trans_eq
    (by dsimp [D];ring)
end GoldbachTwistedMellin
end
end

section
open Finset Complex Set Goldbach GoldbachSmoothing GoldbachGRHWindow DeepThreeQuarters Filter
open scoped Classical
noncomputable section
namespace GoldbachTwistedMellin

theorem tight_phase {n q : ℕ} [NeZero q] (hn : 64≤n) {β X : ℝ} (hx : X≤n)
    (hβ : |β|≤1/((q:ℝ)*Real.sqrt n)) : |2*Real.pi*β|≤1 ∧ |2*Real.pi*β|^2*X≤64 := by
  obtain ⟨h1,h2⟩ := angular_range hn (NeZero.pos q) hβ
  let g := |2*Real.pi*β|
  have hg : 0≤g := abs_nonneg _
  have hq : (1:ℝ)≤q := by exact_mod_cast (NeZero.pos q)
  have gn : g*(n:ℝ)≤8*Real.sqrt n := by
    apply le_trans _ h2
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hg hq) (Nat.cast_nonneg _)
  have hs : 0<Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (show 0<n by omega))
  have gs : g*Real.sqrt n≤8 := by
    apply (mul_le_mul_iff_left₀ hs).mp
    calc
      _ = g*(n:ℝ) := by rw [mul_assoc,←sq,Real.sq_sqrt (Nat.cast_nonneg _)]
      _ ≤ _ := gn
  have sqb := pow_le_pow_left₀ (mul_nonneg hg hs.le) gs 2
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)] at sqb
  exact ⟨h1,(mul_le_mul_of_nonneg_left hx (sq_nonneg g)).trans (by norm_num at sqb;exact sqb)⟩

/-- The local ordinate budget balances the reciprocal-square tail with the global three-quarters error. -/
def ordinateCut (q n : ℕ) (X : ℝ) : ℝ := max 2 (Real.sqrt q*X^2/(n:ℝ)^(3/4:ℝ))

def shortBand {q : ℕ} [NeZero q] (n : ℕ) (χ : DirichletCharacter ℂ q) (p : ℕ×ℕ) (γ : ℝ) :=
  (exceptionalZeros χ (heightCut p.1)).filter (fun z => (n:ℝ)^(3/4:ℝ)<localZeroScale q p.1 γ z.re)

def shortWindowTerm {q : ℕ} [NeZero q] (n : ℕ) (χ : DirichletCharacter ℂ q) (p : ℕ×ℕ) (γ : ℝ) : ℂ :=
  ∑ z ∈ (shortBand n χ p γ).filter (fun z => |z.im|≤ordinateCut q n p.1),
    (analyticOrderNatAt (regularizedL χ) z:ℂ)*transform p.1 p.2 γ z

def tallWindowTerm {q : ℕ} [NeZero q] (n : ℕ) (χ : DirichletCharacter ℂ q) (p : ℕ×ℕ) (γ : ℝ) : ℂ :=
  ∑ z ∈ (shortBand n χ p γ).filter (fun z => ordinateCut q n p.1< |z.im|),
    (analyticOrderNatAt (regularizedL χ) z:ℂ)*transform p.1 p.2 γ z

theorem splitShortTerm {q : ℕ} [NeZero q] (n : ℕ) (χ : DirichletCharacter ℂ q) (p : ℕ×ℕ) (γ : ℝ) :
    shortWindowTerm n χ p γ + tallWindowTerm n χ p γ = upperWindowTerm n χ p γ := by
  simpa only [shortWindowTerm,tallWindowTerm,shortBand,upperWindowTerm,not_le] using
    Finset.sum_filter_add_sum_filter_not (s:=shortBand n χ p γ)
      (fun z => |z.im|≤ordinateCut q n p.1)
      (fun z => (analyticOrderNatAt (regularizedL χ) z:ℂ)*transform p.1 p.2 γ z)

theorem tall_residue_bound :
    ∃ C : ℝ, 0<C ∧ ∀ (n q : ℕ) [NeZero q], 64≤n → (q:ℝ)≤Real.sqrt n →
      ∀ (χ : DirichletCharacter ℂ q) (p : ℕ×ℕ) (β : ℝ), p∈prefixBlocks (n-2) →
      |β|≤1/((q:ℝ)*Real.sqrt n) →
      Real.sqrt q*‖tallWindowTerm n χ p (2*Real.pi*β)‖ ≤ C*(n:ℝ)^(3/4:ℝ)*logScale n := by
  obtain ⟨K,hK,tail⟩ := short_ordinate_tail
  refine ⟨10*K,by positivity,?_⟩
  intro n q _ hn hq χ p β hp hβ
  let X : ℝ := p.1
  let B := heightCut X
  let T := ordinateCut q n p.1
  let γ := 2*Real.pi*β
  let Z := (shortBand n χ p γ).filter (fun z => T< |z.im|)
  obtain ⟨hl,hlr,hr,hrn⟩ := prefixBlocks_valid hp
  have hX : 1≤X := by dsimp [X];exact_mod_cast hl
  have hxn : X≤(n:ℝ) := by dsimp [X];exact_mod_cast (show p.1≤n by omega)
  have hnR : 1≤(n:ℝ) := by exact_mod_cast (show 1≤n by omega)
  have hn0 := zero_lt_one.trans_le hnR
  have hqs := hq.trans (Real.sqrt_le_self_iff.mpr (Or.inr hnR))
  obtain ⟨hγ,hf⟩ := tight_phase (q:=q) hn hxn hβ
  have hT : 2≤T := le_max_left _ _
  have hb : 0≤B := by dsimp [B];linarith only [heightCut_ge hX,hX]
  have geom (z : ℂ) (hz : z∈Z) : 1/2≤z.re ∧ z.re≤1 ∧ T≤|z.im| ∧ |z.im|≤B := by
    obtain ⟨hzB,ht⟩ := mem_filter.mp hz
    obtain ⟨hzR,hzH,hzero⟩ := (mem_exceptionalZeros χ _ z).mp (mem_filter.mp hzB).1
    exact ⟨hzR.le,le_of_not_gt (fun h => regularizedL_ne_zero_right χ h hzero),ht.le,hzH⟩
  have hnorm := norm_sum_le Z (fun z : ℂ => (analyticOrderNatAt (regularizedL χ) z:ℂ)*transform p.1 p.2 γ z)
  simp only [norm_mul,Complex.norm_natCast] at hnorm
  have b := hnorm.trans (tail q χ Z p.1 p.2 X γ B T hX le_rfl (by exact_mod_cast hlr) (by dsimp [X];exact_mod_cast hr) hγ hf hT hb geom)
  obtain ⟨hh,_⟩ := log_window_scale (q:=q) hX hxn hqs
  have hlog : logHeight q B≤10*logScale n := by dsimp [logBudget] at hh;dsimp [B];linarith
  have ht0 : 0<T := by linarith
  have he : Real.sqrt q*X^2/T ≤ (n:ℝ)^(3/4:ℝ) := by
    apply (div_le_iff₀ ht0).mpr
    rw [mul_comm _ T]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hn0 _)).mp (show Real.sqrt q*X^2/(n:ℝ)^(3/4:ℝ) ≤ T from le_max_right _ _)
  have hL0 := zero_le_one.trans (logScale_one hnR)
  calc
    _ ≤ Real.sqrt q*(K*X^2*logHeight q B/T) := mul_le_mul_of_nonneg_left b (Real.sqrt_nonneg _)
    _ = K*(Real.sqrt q*X^2/T)*logHeight q B := by ring
    _ ≤ K*(n:ℝ)^(3/4:ℝ)*(10*logScale n) := by
      have hlog0 := zero_le_one.trans (logHeight_ge_one q B)
      gcongr
    _ = _ := by ring

end GoldbachTwistedMellin
end
end

section
open Complex Set MeasureTheory
open scoped Interval
noncomputable section
namespace GoldbachTwistedMellin

private theorem vertical_sharp_endpoint {X l r γ : ℝ} (hX : 1≤X) (hl : X≤l) (hlr : l≤r) (hr : r≤2*X)
    {s : ℂ} (hs : 0<s.re) (hs' : s.re≤1) (hn : 0<‖s+1‖) :
    ‖∫ x in l..r,density γ (s+1) x‖ ≤ (4*X^(s.re+1)*(2+|γ| *(r-l)))/‖s+1‖ := by
  have xl : 0<l := zero_lt_one.trans_le (hX.trans hl)
  have bnd (x : ℝ) (hx : x ∈ Icc l r) : ‖density γ ((s+1)+1) x‖ ≤ 4*X^(s.re+1) := by
    rw [density_succ,norm_mul,norm_phase,one_mul,norm_cpow_eq_rpow_re_of_pos (xl.trans_le hx.1),add_re,one_re]
    calc
      x^(s.re+1) ≤ (2*X)^(s.re+1) := Real.rpow_le_rpow (xl.le.trans hx.1) (hx.2.trans hr) (by linarith)
      _ = (2:ℝ)^(s.re+1)*X^(s.re+1) := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 4*X^(s.re+1) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
        exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) (by linarith : s.re+1≤2)).trans_eq (by norm_num)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a:=l) (b:=r)
    (fun x hx => bnd x (by rw [uIoc_of_le hlr] at hx;exact ⟨hx.1.le,hx.2⟩))
  rw [abs_of_nonneg (sub_nonneg.mpr hlr)] at hi
  have e := scaled_power_ibp xl hlr γ (s:=s+1) (by simp only [add_re,one_re];linarith)
  have he := norm_sub_le (density γ ((s+1)+1) r-density γ ((s+1)+1) l) (linearFrequency γ*(∫ x in l..r,density γ ((s+1)+1) x))
  rw [←e,norm_mul,norm_mul,frequency_norm] at he
  apply (le_div_iff₀ hn).mpr
  nlinarith only [he,norm_sub_le (density γ ((s+1)+1) r) (density γ ((s+1)+1) l),
    bnd r (right_mem_Icc.mpr hlr),bnd l (left_mem_Icc.mpr hlr),mul_le_mul_of_nonneg_left hi (abs_nonneg γ)]

/-- The rational offset constraint controls the square of the angular frequency.
Two integrations by parts then cost only the square of the dyadic scale. -/
theorem vertical_ordinate_decay {X a b γ : ℝ} (hX : 1≤X) (ha : X≤a) (hab : a+1≤b)
    (hb : b+1≤2*X) (hγ : |γ|≤1) (hf : |γ| ^2*X≤64) (s : ℂ)
    (hs : 0<s.re) (hs' : s.re≤1) (ht : 0 < |s.im|) :
    ‖transform a b γ s‖ ≤ 288*X^(s.re+1)/ |s.im| ^2 := by
  let D := 4*X^(s.re+1)/‖s+1‖
  have t1 : |s.im|≤‖s+1‖ := by simpa using abs_im_le_norm (s+1)
  have hn := ht.trans_le t1
  have hD : 0≤D := by dsimp [D];positivity
  have bound {l r : ℝ} (hl : X≤l) (hlr : l≤r) (hr : r≤2*X) : ‖∫ x in l..r,density γ (s+1) x‖ ≤ D*(2+|γ| *(r-l)) :=
    (vertical_sharp_endpoint hX hl hlr hr hs hs' hn).trans_eq (by dsimp [D];ring)
  have endpt (l : ℝ) (hl : X≤l) (hr : l+1≤2*X) : ‖∫ x in l..l+1,density γ (s+1) x‖ ≤ 3*D := by
    have h := bound hl (by linarith : l≤l+1) hr
    have hle := mul_le_mul_of_nonneg_left hγ hD
    nlinarith only [h,hle]
  have all : ‖transform a b γ (s+1)‖ ≤ D*(2+|γ| *X) := by
    refine norm_transform_le (zero_lt_one.trans_le hX) ha hab hb γ (s+1) (fun l r hl hlr hr => ?_)
    apply (bound hl hlr hr).trans
    gcongr
    linarith
  have e := transform_recurrence (zero_lt_one.trans_le (hX.trans ha)) hab γ hs
  change s*transform a b γ s = _ - linearFrequency γ*transform a b γ (s+1) at e
  have tr := norm_sub_le ((∫ x in b..b+1,density γ (s+1) x)-(∫ x in a..a+1,density γ (s+1) x)) (linearFrequency γ*transform a b γ (s+1))
  rw [←e,norm_mul,norm_mul,frequency_norm] at tr
  have small : ‖s‖*‖transform a b γ s‖ ≤ 72*D := by
    nlinarith only [tr,norm_sub_le (∫ x in b..b+1,density γ (s+1) x) (∫ x in a..a+1,density γ (s+1) x),
      endpt a ha (by linarith),endpt b (by linarith) hb,mul_le_mul_of_nonneg_left all (abs_nonneg γ),
      mul_le_mul_of_nonneg_left hf hD,mul_le_mul_of_nonneg_left hγ hD]
  have eq : 72*D=288*X^(s.re+1)/‖s+1‖ := by dsimp [D];ring
  rw [eq] at small
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  calc
    _ = |s.im| *‖transform a b γ s‖*|s.im| := by ring
    _ ≤ ‖s‖*‖transform a b γ s‖*‖s+1‖ := mul_le_mul (mul_le_mul_of_nonneg_right (abs_im_le_norm s) (norm_nonneg _)) t1 ht.le (by positivity)
    _ ≤ _ := (le_div_iff₀ hn).mp small
end GoldbachTwistedMellin
end
end

section
open Complex Set MeasureTheory
open scoped Interval
noncomputable section
namespace GoldbachTwistedMellin

/-- A zero can contribute beyond the harmonic error only when the phase slope
gets small somewhere on the actual dyadic block, and curvature and endpoint
decay both allow a contribution of that size. -/
def activePhase (Q n : ℕ) (X γ : ℝ) (z : ℂ) : Prop :=
  ∃ x ∈ Icc X (2*X),
    (n:ℝ)^(3/4:ℝ) * max (max 1 (Real.sqrt |z.im|)) (max |γ*x+z.im| (|z.im|^2/X)) <
      Real.sqrt Q*X^z.re*(1+|z.im|)

private theorem separated_window {X a b γ H : ℝ} (hX : 0<X) (ha : X≤a)
    (hab : a+1≤b) (hb : b+1≤2*X) {z : ℂ} (hs : 0≤z.re) (hs' : z.re≤1)
    (hH : 0<H) (sep : ∀ x ∈ Icc X (2*X), H≤|γ*x+z.im|) :
    ‖transform a b γ z‖ ≤ 10*X^z.re/H := by
  apply norm_transform_le hX ha hab hb
  intro l r hl hlr hr
  have he := intervalIntegral.integral_congr (μ:=volume) (f:=density γ z)
    (a:=l) (b:=r) (fun x hx => density_eq ((hX.trans_le hl).trans_le (((uIcc_of_le hlr) ▸ hx).1)) γ z)
  rw [he]
  have bounds := GoldbachOscillation.per_ordinate X l r z.re z.im γ hX hl hlr hr hs hs'
  apply (bounds.2.2 H hH (fun x hx => sep x ⟨hl.trans hx.1,hx.2.trans hr⟩)).trans
  apply (div_le_div_iff_of_pos_right hH).mpr
  have hpow : r^z.re ≤ 2*X^z.re := calc
    _ ≤ (2*X)^z.re := Real.rpow_le_rpow (hX.le.trans (hl.trans hlr)) hr hs
    _ = (2:ℝ)^z.re*X^z.re := Real.mul_rpow (by norm_num) hX.le
    _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa using Real.rpow_le_rpow_of_exponent_le (show (1:ℝ)≤2 by norm_num) hs') (Real.rpow_nonneg hX.le _)
  linarith

theorem inactive_phase_cost {q n : ℕ} [NeZero q] (hn : 1≤n) {X a b γ : ℝ}
    (hX : 1≤X) (ha : X≤a) (hab : a+1≤b) (hb : b+1≤2*X) (hγ : |γ|≤1) (hf : |γ|^2*X≤64)
    (z : ℂ) (hs : 0<z.re) (hs' : z.re≤1) (inactive : ¬ activePhase q n X γ z) :
    (Real.sqrt q*‖transform a b γ z‖)*(1+|z.im|) ≤ 288*(n:ℝ)^(3/4:ℝ) := by
  let Y := X^z.re
  let t := |z.im|
  let N := (n:ℝ)^(3/4:ℝ)
  let A := Real.sqrt q*Y*(1+t)/N
  have hx := zero_lt_one.trans_le hX
  have hN : 0<N := Real.rpow_pos_of_pos (by exact_mod_cast (show 0<n by omega)) _
  have ht : 0≤t := abs_nonneg _
  have hY : 0<Y := Real.rpow_pos_of_pos hx _
  have hq : 0<Real.sqrt q := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos q)
  have hA : 0<A := by dsimp [A];positivity
  have hAN : A*N = Real.sqrt q*Y*(1+t) := div_mul_cancel₀ _ hN.ne'
  have lift (h : ‖transform a b γ z‖*A ≤ 288*Y) :
      Real.sqrt q*‖transform a b γ z‖*(1+t) ≤ 288*N := by
    apply (mul_le_mul_iff_left₀ hY).mp
    calc
      _ = (‖transform a b γ z‖*A)*N := by rw [mul_assoc _ A N,hAN];ring
      _ ≤ (288*Y)*N := mul_le_mul_of_nonneg_right h hN.le
      _ = _ := by ring
  apply lift
  obtain ⟨h0,h1,_⟩ := norm_window_modes hx ha hab hb γ z hs.le hs'
  by_cases lo : A≤1
  · exact (mul_le_mul h0 lo hA.le hY.le).trans (by dsimp only [Y];nlinarith only [hY.le])
  by_cases mid : A≤Real.sqrt t
  · have st := hA.trans_le mid
    have tj : z.im≠0 := by intro e;simp [t,e] at st
    have upper := (le_div_iff₀ st).mp ((h1 tj).trans_eq (by dsimp [Y,t];ring) :
      ‖transform a b γ z‖ ≤ (Y*(3+5*Real.pi))/Real.sqrt t)
    exact (mul_le_mul_of_nonneg_left mid (norm_nonneg _)).trans (upper.trans
      ((mul_le_mul_of_nonneg_left (by linarith only [Real.pi_lt_four] : 3+5*Real.pi≤288) hY.le).trans_eq (mul_comm _ _)))
  by_cases tall : A≤t^2/X
  · have tpos : 0<t := by
      by_contra! h
      have h0 : t=0 := le_antisymm h ht
      rw [h0] at tall
      simp at tall
      linarith
    have decay := vertical_ordinate_decay hX ha hab hb hγ hf z hs hs' tpos
    have hp := (le_div_iff₀ (sq_pos_of_pos tpos)).mp decay
    have powid : X^(z.re+1)=Y*X := by rw [Real.rpow_add hx,Real.rpow_one]
    rw [powid] at hp
    apply (mul_le_mul_of_nonneg_left tall (norm_nonneg _)).trans
    rw [←mul_div_assoc]
    exact (div_le_iff₀ hx).mpr (by linarith only [hp])
  have sep (x : ℝ) (h : x∈Icc X (2*X)) : A≤|γ*x+z.im| := by
    by_contra! h'
    apply inactive
    refine ⟨x,h,?_⟩
    have hm : max (max 1 (Real.sqrt t)) (max |γ*x+z.im| (t^2/X)) < A :=
      max_lt (max_lt (lt_of_not_ge lo) (lt_of_not_ge mid)) (max_lt h' (lt_of_not_ge tall))
    have e := (lt_div_iff₀ hN).mp hm
    rw [mul_comm _ N] at e
    exact e
  exact ((le_div_iff₀ hA).mp (separated_window hx ha hab hb hs.le hs' hA sep)).trans
    (mul_le_mul_of_nonneg_right (by norm_num : (10:ℝ)≤288) hY.le)
end GoldbachTwistedMellin
end
end

section
open Finset Set Complex Goldbach
open scoped Classical
noncomputable section
namespace GoldbachTwistedMellin
private def harmonicBin (t : ℝ) : Bool×ℕ := (decide (0≤t),⌊|t|⌋₊)
private def harmonicCenter (p : Bool×ℕ) : ℝ := if p.1 then (p.2:ℝ) else -(p.2:ℝ)
private theorem harmonic_bin_range (y : ℝ) : ((harmonicBin y).2:ℝ) ≤ |y| ∧ |y-harmonicCenter (harmonicBin y)| ≤ 1 := by
  have h := Nat.floor_le (abs_nonneg y)
  have h' := Nat.lt_floor_add_one |y|
  refine ⟨h,?_⟩
  by_cases hy : 0≤y
  · simp only [abs_of_nonneg hy] at h h'
    simp [harmonicCenter,harmonicBin,hy,abs_of_nonneg hy,abs_le];constructor <;> linarith
  · have hn := le_of_not_ge hy
    simp only [abs_of_nonpos hn] at h h'
    simp [harmonicCenter,harmonicBin,hy,abs_of_nonpos hn,abs_le];constructor <;> linarith


/-- The harmonic weight in the ordinate pays only two logarithms for all
zeros, including their analytic multiplicities, with no restriction on their signs. -/
theorem ordinate_harmonic_mass : ∃ C : ℝ, 0<C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (Z : Finset ℂ) (B : ℝ), 2≤B → (∀ z∈Z, 1/2≤z.re ∧ z.re≤1 ∧ |z.im|≤B) →
    ∑ z ∈ Z, (analyticOrderNatAt (regularizedL χ) z:ℝ)/(1+|z.im|) ≤ C*logHeight q B*(1+Real.log B) := by
  obtain ⟨K,hK,slice⟩ := unconditional_right_slice_count
  refine ⟨100*K,by positivity,?_⟩
  intro q _ χ Z B hB geom
  let M := ⌊B⌋₊
  let y := fun z : ℂ => harmonicBin z.im
  let m := fun z : ℂ => (analyticOrderNatAt (regularizedL χ) z:ℝ)
  have hM : (M:ℝ)≤B := Nat.floor_le (by linarith)
  have hL : 0≤logHeight q B := zero_le_one.trans (logHeight_ge_one _ _)
  have cover (z : ℂ) (hz : z∈Z) : y z∈grid (M+1) :=
    mem_product.mpr ⟨mem_univ _,mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (geom z hz).2.2))⟩
  have per (p : Bool×ℕ) (hp : p∈grid (M+1)) :
      (∑ z ∈ Z.filter (fun z => y z=p), m z/(1+|z.im|)) ≤ (K*logHeight q B)*profile 0 p.2 := by
    let Y := Z.filter (fun z => y z=p)
    have hcnt := slice q χ (harmonicCenter p) Y (fun z hz => by
      obtain ⟨hzZ,he⟩ := mem_filter.mp hz
      exact ⟨(geom z hzZ).1,(geom z hzZ).2.1.trans (by norm_num),
        by simpa only [←he,y] using (harmonic_bin_range z.im).2⟩)
    have hc : |harmonicCenter p|=(p.2:ℝ) := by dsimp [harmonicCenter];split <;> simp
    have hj : p.2≤M := Nat.lt_succ_iff.mp (mem_range.mp (mem_product.mp hp).2)
    have height : logHeight q (harmonicCenter p)≤logHeight q B := by
      apply logHeight_mono_abs;rw [hc,abs_of_nonneg (by linarith : 0≤B)]
      exact (show (p.2:ℝ)≤M by exact_mod_cast hj).trans hM
    have cnt : (∑ z ∈ Y,m z) ≤ K*logHeight q B := hcnt.trans (mul_le_mul_of_nonneg_left height hK.le)
    have single (z : ℂ) (hz : z∈Y) : 1/(1+|z.im|) ≤ profile 0 p.2 := by
      have hpz := (mem_filter.mp hz).2
      have hd : 0<1+|z.im| := by positivity
      by_cases j0 : p.2=0
      · rw [profile,ite_eq_left j0]
        exact (div_le_one hd).mpr (by linarith [abs_nonneg z.im])
      · have jp : 0<(p.2:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero j0
        have hbin : (p.2:ℝ)≤|z.im| := by rw [←hpz];exact (harmonic_bin_range z.im).1
        rw [profile,ite_eq_right j0,ite_eq_right (show ¬p.2≤0 by omega)]
        exact (div_le_div_iff₀ hd jp).mpr (by linarith)
    calc
      _ ≤ ∑ z ∈ Y,m z*profile 0 p.2 := by
        refine sum_le_sum fun z hz => ?_
        calc
          m z/(1+|z.im|) = m z*(1/(1+|z.im|)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (single z hz) (Nat.cast_nonneg _)
      _ = (∑ z ∈ Y,m z)*profile 0 p.2 := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right cnt (profile_nonneg ..)
  have total := sum_le_sum per
  rw [Finset.sum_fiberwise_of_maps_to cover,←Finset.mul_sum,sum_grid_weight] at total
  have hln : Real.log (M+1:ℝ)≤1+Real.log B := by
    have hy := Real.log_le_log (by positivity : 0<(M:ℝ)+1) (by linarith : (M:ℝ)+1≤2*B)
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (by linarith)] at hy
    linarith only [hy,Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))]
  have hprof := profile_sum 0 M
  simp only [Nat.cast_zero,Real.sqrt_zero,mul_zero,add_zero] at hprof
  have bound : 2*(∑ j ∈ range (M+1),profile 0 j)≤100*(1+Real.log B) := by
    linarith only [hprof,hln,Real.log_nonneg (by linarith : 1≤B)]
  exact total.trans ((mul_le_mul_of_nonneg_left bound (mul_nonneg hK.le hL)).trans_eq (by ring))
end GoldbachTwistedMellin
end
end

section
open Finset Complex Set Goldbach GoldbachSmoothing GoldbachGRHWindow DeepThreeQuarters Filter
open scoped Classical
noncomputable section
namespace GoldbachTwistedMellin

def shortSupport {q : ℕ} [NeZero q] (n : ℕ) (χ : DirichletCharacter ℂ q) (p : ℕ×ℕ) (γ : ℝ) :=
  (shortBand n χ p γ).filter (fun z => |z.im|≤ordinateCut q n p.1)

def phaseWindowTerm {q : ℕ} [NeZero q] (n : ℕ) (χ : DirichletCharacter ℂ q) (p : ℕ×ℕ) (γ : ℝ) : ℂ :=
  ∑ z ∈ (shortSupport n χ p γ).filter (activePhase q n p.1 γ),
    (analyticOrderNatAt (regularizedL χ) z:ℂ)*transform p.1 p.2 γ z

def inactiveWindowTerm {q : ℕ} [NeZero q] (n : ℕ) (χ : DirichletCharacter ℂ q) (p : ℕ×ℕ) (γ : ℝ) : ℂ :=
  ∑ z ∈ (shortSupport n χ p γ).filter (fun z => ¬activePhase q n p.1 γ z),
    (analyticOrderNatAt (regularizedL χ) z:ℂ)*transform p.1 p.2 γ z

theorem splitPhaseTerm {q : ℕ} [NeZero q] (n : ℕ) (χ : DirichletCharacter ℂ q) (p : ℕ×ℕ) (γ : ℝ) :
    phaseWindowTerm n χ p γ + inactiveWindowTerm n χ p γ = shortWindowTerm n χ p γ := by
  exact Finset.sum_filter_add_sum_filter_not (s:=shortSupport n χ p γ) (activePhase q n p.1 γ)
    (fun z => (analyticOrderNatAt (regularizedL χ) z:ℂ)*transform p.1 p.2 γ z)

theorem phase_residue_bound :
    ∃ C : ℝ, 0<C ∧ ∀ (n q : ℕ) [NeZero q], 64≤n → (q:ℝ)≤Real.sqrt n →
      ∀ (χ : DirichletCharacter ℂ q) (p : ℕ×ℕ) (β : ℝ), p∈prefixBlocks (n-2) →
      |β|≤1/((q:ℝ)*Real.sqrt n) →
      Real.sqrt q*‖inactiveWindowTerm n χ p (2*Real.pi*β)‖ ≤ C*(n:ℝ)^(3/4:ℝ)*logScale n^2 := by
  obtain ⟨K,hK,mass⟩ := ordinate_harmonic_mass
  refine ⟨28800*K,by positivity,?_⟩
  intro n q _ hn hq χ p β hp hβ
  let X : ℝ := p.1
  let B := heightCut X
  let γ := 2*Real.pi*β
  let N := (n:ℝ)^(3/4:ℝ)
  let Z := (shortSupport n χ p γ).filter (fun z => ¬activePhase q n p.1 γ z)
  let m := fun z : ℂ => (analyticOrderNatAt (regularizedL χ) z:ℝ)
  obtain ⟨hl,hlr,hr,hrn⟩ := prefixBlocks_valid hp
  have hX : 1≤X := by dsimp [X];exact_mod_cast hl
  have hxn : X≤(n:ℝ) := by dsimp [X];exact_mod_cast (show p.1≤n by omega)
  have hnR : 1≤(n:ℝ) := by exact_mod_cast (show 1≤n by omega)
  have hqs := hq.trans (Real.sqrt_le_self_iff.mpr (Or.inr hnR))
  obtain ⟨hγ,hf⟩ := tight_phase (q:=q) hn hxn hβ
  have hb : 2≤B := by dsimp [B];linarith only [heightCut_ge hX,hX]
  have geom (z : ℂ) (hz : z∈Z) : 1/2≤z.re ∧ z.re≤1 ∧ |z.im|≤B := by
    obtain ⟨hzR,hzH,hzero⟩ := (mem_exceptionalZeros χ _ z).mp (mem_filter.mp (mem_filter.mp (mem_filter.mp hz).1).1).1
    exact ⟨hzR.le,le_of_not_gt (fun h => regularizedL_ne_zero_right χ h hzero),hzH⟩
  have single (z : ℂ) (hz : z∈Z) : Real.sqrt q*(m z*‖transform p.1 p.2 γ z‖) ≤ (288*N)*(m z/(1+|z.im|)) := by
    obtain ⟨hlo,hhi,_⟩ := geom z hz
    have hd : 0<1+|z.im| := by positivity
    have e := inactive_phase_cost (q:=q) (n:=n) (a:=(p.1:ℝ)) (b:=(p.2:ℝ)) (by omega) hX le_rfl (by exact_mod_cast hlr) (by dsimp [X];exact_mod_cast hr)
      hγ hf z (by linarith) hhi (mem_filter.mp hz).2
    calc
      _ = m z*(Real.sqrt q*‖transform p.1 p.2 γ z‖) := by ring
      _ ≤ m z*((288*N)/(1+|z.im|)) := mul_le_mul_of_nonneg_left ((le_div_iff₀ hd).mpr e) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hnorm := norm_sum_le Z (fun z : ℂ => (analyticOrderNatAt (regularizedL χ) z:ℂ)*transform p.1 p.2 γ z)
  simp only [norm_mul,Complex.norm_natCast] at hnorm
  obtain ⟨ha,hlg⟩ := log_window_scale (q:=q) hX hxn hqs
  have hlog : logHeight q B≤10*logScale n := by dsimp [logBudget] at ha;dsimp [B];linarith
  have hL := logScale_one hnR
  have hlog' : 1+Real.log B≤10*logScale n := by dsimp [B];linarith
  have log0 : 0≤logHeight q B := zero_le_one.trans (logHeight_ge_one _ _)
  have lo : 0≤1+Real.log B := by linarith [Real.log_nonneg (by linarith : 1≤B)]
  have hN : 0≤N := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc
    _ ≤ Real.sqrt q*(∑ z ∈ Z,m z*‖transform p.1 p.2 γ z‖) := mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)
    _ = ∑ z ∈ Z, Real.sqrt q*(m z*‖transform p.1 p.2 γ z‖) := Finset.mul_sum ..
    _ ≤ ∑ z ∈ Z,(288*N)*(m z/(1+|z.im|)) := sum_le_sum single
    _ = (288*N)*(∑ z ∈ Z,m z/(1+|z.im|)) := (Finset.mul_sum ..).symm
    _ ≤ (288*N)*(K*logHeight q B*(1+Real.log B)) := mul_le_mul_of_nonneg_left (mass q χ Z B hb geom) (by positivity)
    _ ≤ (288*N)*(K*(10*logScale n)*(10*logScale n)) := by gcongr
    _ = _ := by dsimp [N];ring

end GoldbachTwistedMellin
end
end

section
open Complex Finset Set Goldbach GoldbachGRHWindow DeepThreeQuarters DirichletCharacter Filter
open scoped Classical
noncomputable section
namespace GoldbachTwistedMellin

/-- Hold the ambient denominator scale fixed while descending the actual
character. This preserves the frequency and real-part threshold of every block. -/
def phaseKeptBlock {d : ℕ} [NeZero d] (Q n : ℕ) (χ : DirichletCharacter ℂ d) (p : ℕ×ℕ) (γ : ℝ) : ℂ :=
  ∑ z ∈ (((exceptionalZeros χ (heightCut p.1)).filter (fun z => (n:ℝ)^(3/4:ℝ) < localZeroScale Q p.1 γ z.re)).filter (fun z => |z.im| ≤ ordinateCut Q n p.1)).filter (activePhase Q n p.1 γ),
    (analyticOrderNatAt (regularizedL χ) z:ℂ)*transform p.1 p.2 γ z

theorem phaseKeptBlock_inflate {d q : ℕ} [NeZero d] [NeZero q] (hd : d∣q) (Q n : ℕ)
    (ψ : DirichletCharacter ℂ d) (p : ℕ×ℕ) (γ : ℝ) :
    phaseKeptBlock Q n (changeLevel hd ψ) p γ = phaseKeptBlock Q n ψ p γ := by
  unfold phaseKeptBlock
  rw [zeros_changeLevel]
  refine sum_congr rfl fun z hz => ?_
  have h := ((mem_exceptionalZeros ψ _ z).mp (mem_filter.mp (mem_filter.mp (mem_filter.mp hz).1).1).1).1
  rw [order_changeLevel hd ψ (show 0<z.re by linarith)]

end GoldbachTwistedMellin
end
end

section
open Finset Set Complex Goldbach GoldbachSmoothing GoldbachGRHWindow DeepThreeQuarters DirichletCharacter
open scoped Classical
noncomputable section
namespace GoldbachTwistedMellin

/-- At each primitive conductor, the full block and the localized block differ
by a fixed polylogarithmic loss on the three-quarters scale after Gauss normalization. -/
theorem local_character_error : ∃ C : ℝ, 0<C ∧ ∀ (n d : ℕ) [NeZero d], 64≤n → (d:ℝ)≤Real.sqrt n →
    ∀ (χ : DirichletCharacter ℂ d) (β : ℝ), |β|≤1/((d:ℝ)*Real.sqrt n) →
    Real.sqrt d * ‖characterZeroSum n χ β -
      ((prefixBlocks (n-2)).map fun p => phaseWindowTerm n χ p (2*Real.pi*β)).sum‖ ≤
        C*(n:ℝ)^(3/4:ℝ)*logScale n^3 := by
  obtain ⟨A,hA,low⟩ := scaled_residue_bound
  obtain ⟨B,hB,tall⟩ := tall_residue_bound
  obtain ⟨C,hC,inact⟩ := phase_residue_bound
  refine ⟨3*(A+B+C),by positivity,?_⟩
  intro n d _ hn hd χ β hβ
  let γ := 2*Real.pi*β
  let N := (n:ℝ)^(3/4:ℝ)
  let L := logScale n
  let E := (A+B+C)*N*L^2
  let F := fun p : ℕ×ℕ => fixedZeroTerm χ p.1 p.2 p.1 γ - phaseWindowTerm n χ p γ
  have hnR : 1≤(n:ℝ) := by exact_mod_cast (show 1≤n by omega)
  have hL : 1≤L := logScale_one hnR
  have hN : 0≤N := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have dd : 0<Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos d)
  have hE : 0≤E := by dsimp only [E];positivity
  have hdn := hd.trans (Real.sqrt_le_self_iff.mpr (Or.inr hnR))
  have per (p : ℕ×ℕ) (hp : p∈prefixBlocks (n-2)) : ‖F p‖ ≤ E/Real.sqrt d := by
    obtain ⟨hl,hlr,hr,hrn⟩ := prefixBlocks_valid hp
    have l := low n d (by omega) hdn χ p.1 p.2 p.1 γ (by exact_mod_cast hl) le_rfl
      (by exact_mod_cast hlr) (by exact_mod_cast hr) (by exact_mod_cast (show p.1≤n by omega))
    have l' : Real.sqrt d*‖lowerWindowTerm n χ p γ‖≤A*N*L^2 := l
    have t := tall n d hn hd χ p β hp hβ
    have i := inact n d hn hd χ p β hp hβ
    have eq : F p = lowerWindowTerm n χ p γ + tallWindowTerm n χ p γ + inactiveWindowTerm n χ p γ := by
      dsimp only [F]
      rw [←splitWindowTerm n,←splitShortTerm n,←splitPhaseTerm n]
      abel
    have t' : Real.sqrt d*‖tallWindowTerm n χ p γ‖≤B*N*L^2 :=
      t.trans (mul_le_mul_of_nonneg_left (by nlinarith only [hL,sq_nonneg (L-1)] : L≤L^2) (mul_nonneg hB.le hN))
    have i' : Real.sqrt d*‖inactiveWindowTerm n χ p γ‖≤C*N*L^2 := i
    apply (le_div_iff₀ dd).mpr
    rw [mul_comm,eq]
    have tri := (norm_add_le (lowerWindowTerm n χ p γ + tallWindowTerm n χ p γ) (inactiveWindowTerm n χ p γ)).trans
      (add_le_add (norm_add_le (lowerWindowTerm n χ p γ) (tallWindowTerm n χ p γ)) (le_refl _))
    exact (mul_le_mul_of_nonneg_left tri dd.le).trans (by dsimp [E];linarith only [l',t',i'])
  have eq : characterZeroSum n χ β - ((prefixBlocks (n-2)).map fun p => phaseWindowTerm n χ p γ).sum =
      ((prefixBlocks (n-2)).map F).sum := by
    unfold characterZeroSum
    induction prefixBlocks (n-2) with
    | nil => simp
    | cons p l ih => simp only [List.map_cons,List.sum_cons];dsimp only [F] at *;rw [←ih];abel
  have pre := dyadic_prefix_corrected (fun _ => (0:ℂ)) F n (by omega) (E/Real.sqrt d)
    (fun k _ => by simpa using div_nonneg hE dd.le) (fun p hp => by simpa using per p hp)
  simp only [sum_const_zero,zero_add] at pre
  change Real.sqrt d*‖characterZeroSum n χ β-_‖ ≤ _
  rw [eq]
  apply (mul_le_mul_of_nonneg_left (pre.trans (mul_le_mul_of_nonneg_right
    (dyadic_count_le (by omega : 4≤n)) (div_nonneg hE dd.le))) dd.le).trans_eq
  dsimp only [E,N,L]
  field_simp
end GoldbachTwistedMellin
end
end

section
open Complex Finset Set Goldbach GoldbachGRHWindow DeepThreeQuarters DirichletCharacter Filter
open scoped Classical
noncomputable section
namespace GoldbachTwistedMellin

/-- The ambient denominator governs only the conductor threshold. All three
spectral cutoffs use the character's primitive conductor, even after inflation. -/
def intrinsicSpectrum (Q : ℕ) : DescendingKernel where
  coeff := fun {d} _ n χ β => if projectedThreshold n Q < (χ.conductor:ℝ) then
    ((prefixBlocks (n-2)).map fun p => phaseKeptBlock χ.conductor n χ p (2*Real.pi*β)).sum else 0
  compatible := by
    intro d q _ _ hd ψ n β
    simp only [conductor_changeLevel,phaseKeptBlock_inflate]

private def discardedSpectrum (Q : ℕ) : DescendingKernel where
  coeff := fun {d} _ n χ β => (if projectedThreshold n Q < (χ.conductor:ℝ) then characterZeroSum n χ β else 0) -
    (intrinsicSpectrum Q).coeff n χ β
  compatible := by
    intro d q _ _ hd ψ n β
    rw [characterZeroSum_changeLevel,conductor_changeLevel,(intrinsicSpectrum Q).compatible hd]

private theorem discarded_full {q : ℕ} [NeZero q] (a n : ℕ) (β : ℝ) :
    levelTransform (discardedSpectrum q) false q 1 a n β =
      projectedHighCorrection n (a:ZMod q) β - kernelCorrection (intrinsicSpectrum q) n (a:ZMod q) β := by
  rw [levelTransform_eq]
  simp only [Bool.false_eq_true,ite_false,Nat.cast_one,map_one,mul_one,discardedSpectrum,kernelCorrection,
    projectedHighCorrection,Finset.sum_filter,mul_sub,Finset.sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun χ _ => ?_
  split_ifs <;> simp

/-- Transport absolute errors at primitive conductors to a fixed reduced
numerator. The only arithmetic overhead is the totient ratio. -/
theorem intrinsic_error_finite :
    ∃ C : ℝ, 0<C ∧ ∀ (n q a : ℕ) [NeZero q], 64≤n → (q:ℝ)≤Real.sqrt n → a.Coprime q →
    ∀ β : ℝ, |β|≤1/((q:ℝ)*Real.sqrt n) →
    ‖projectedHighCorrection n (a:ZMod q) β - kernelCorrection (intrinsicSpectrum q) n (a:ZMod q) β‖ ≤
      ((q:ℝ)/q.totient)*(C*(n:ℝ)^(3/4:ℝ)*logScale n^3) := by
  obtain ⟨C,hC,errs⟩ := local_character_error
  refine ⟨C,hC,?_⟩
  intro n q a _ hn hq hc β hβ
  let D := C*(n:ℝ)^(3/4:ℝ)*logScale n^3
  have hnR : 1≤(n:ℝ) := by exact_mod_cast (show 1≤n by omega)
  have hL := logScale_one hnR
  have hD : 0≤D := by dsimp [D];positivity
  have loc (d : ℕ) (hd : d∈q.divisors) (b : ℕ) (_ : b<d) (_ : b.Coprime d) :
      ‖levelTransform (discardedSpectrum q) true d 1 b n β‖≤D := by
    let : NeZero d := ⟨(Nat.pos_of_mem_divisors hd).ne'⟩
    have hs : 0<Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_mem_divisors hd)
    have hdq : (d:ℝ)≤q := by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) (Nat.dvd_of_mem_divisors hd)
    have hdn : (d:ℝ)≤Real.sqrt n := hdq.trans hq
    have offset : |β|≤1/((d:ℝ)*Real.sqrt n) := hβ.trans (div_le_div_of_nonneg_left zero_le_one
      (mul_pos (by exact_mod_cast Nat.pos_of_mem_divisors hd) (Real.sqrt_pos.mpr (zero_lt_one.trans_le hnR)))
      (mul_le_mul_of_nonneg_right hdq (Real.sqrt_nonneg _)))
    let S := (univ : Finset (DirichletCharacter ℂ d)).filter IsPrimitive
    have estimate (χ : DirichletCharacter ℂ d) (hχ : χ∈S) : ‖(discardedSpectrum q).coeff n χ β‖ ≤ D/Real.sqrt d := by
      have primitive : χ.conductor=d := (mem_filter.mp hχ).2
      simp only [discardedSpectrum,intrinsicSpectrum,primitive]
      split_ifs with ht
      · apply (le_div_iff₀ hs).mpr
        rw [mul_comm]
        exact errs n d hn hdn χ β offset
      · simpa using div_nonneg hD hs.le
    rw [levelTransform_eq]
    simp only [ite_true,Nat.cast_one,map_one,mul_one]
    calc
      _ ≤ ∑ χ ∈ S,‖additiveWeight (b:ZMod d) χ*(discardedSpectrum q).coeff n χ β‖ := norm_sum_le ..
      _ ≤ ∑ χ ∈ S,‖additiveWeight (b:ZMod d) χ‖*(D/Real.sqrt d) := by
        refine sum_le_sum fun χ hχ => ?_
        rw [norm_mul];exact mul_le_mul_of_nonneg_left (estimate χ hχ) (norm_nonneg _)
      _ = (∑ χ ∈ S, ‖additiveWeight (b:ZMod d) χ‖)*(D/Real.sqrt d) := (Finset.sum_mul ..).symm
      _ ≤ Real.sqrt d*(D/Real.sqrt d) := by
        apply mul_le_mul_of_nonneg_right _ (div_nonneg hD hs.le)
        exact (sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun _ _ _ => norm_nonneg _)).trans (sum_norm_additiveWeight_le (b:ZMod d))
      _ = D := by field_simp
  have he := conductor_two_way_bound (discardedSpectrum q) true a n hc β D hD loc
  change ‖levelTransform (discardedSpectrum q) false q 1 a n β‖ ≤ _ at he
  rw [discarded_full] at he
  exact he
end GoldbachTwistedMellin
end
end

section
open Set Filter Complex Goldbach GoldbachGRHWindow DeepThreeQuarters
noncomputable section
namespace GoldbachTwistedMellin

def conductorCorrection {q : ℕ} [NeZero q] (n : ℕ) (v : ZMod q) (β : ℝ) : ℂ :=
  kernelCorrection (intrinsicSpectrum q) n v β

private theorem conductor_error_polylog :
    ∃ C : ℝ, 0<C ∧ ∀ (n q a : ℕ) [NeZero q], 64≤n → (q:ℝ)≤Real.sqrt n → a.Coprime q →
    ∀ β : ℝ, |β|≤1/((q:ℝ)*Real.sqrt n) →
    ‖projectedHighCorrection n (a:ZMod q) β - conductorCorrection n (a:ZMod q) β‖ ≤
      C*(n:ℝ)^(3/4:ℝ)*logScale n^4 := by
  obtain ⟨C,hC,h⟩ := intrinsic_error_finite
  refine ⟨4*C,by positivity,?_⟩
  intro n q a _ hn hq hc β hβ
  have hnR : (2:ℝ)≤n := by exact_mod_cast (show 2≤n by omega)
  have hqn := hq.trans (Real.sqrt_le_self_iff.mpr (Or.inr (by linarith : 1≤(n:ℝ))))
  have ls : Real.log ((q+2:ℕ):ℝ)≤logScale n := by
    have l := Real.log_le_log (by positivity : (0:ℝ)<((q+2:ℕ):ℝ)) (show ((q+2:ℕ):ℝ)≤2*n by push_cast;linarith)
    dsimp [logScale];linarith
  have ratio := (totient_ratio_le_four_log q (NeZero.pos q)).trans (mul_le_mul_of_nonneg_left ls (by norm_num))
  have ll := logScale_one (by linarith : 1≤(n:ℝ))
  apply (h n q a hn hq hc β hβ).trans
  exact (mul_le_mul_of_nonneg_right ratio (by positivity)).trans_eq (by ring)

/-- The pointwise model now retains only high-conductor characters and the
zeros above the real-part threshold and below the local ordinate cutoff. -/
theorem deep_intrinsic_model :
    ∀ η : ℝ, 0<η → ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ t ∈ Icc (0:ℝ) 1, t ∉ wideArcs n →
      ∀ (a q : ℕ) [NeZero q], a≤q → a.Coprime q → (q:ℝ)≤Real.sqrt n →
      |t-(a:ℝ)/q| ≤ 1/((q:ℝ)*Real.sqrt n) →
      ‖weightedSum n primeWeight t + conductorCorrection n (a:ZMod q) (t-(a:ℝ)/q)‖ ≤ (n:ℝ)^(3/4+η) := by
  intro η hη
  obtain ⟨N,hN⟩ := deep_projected_high_model (η/2) (half_pos hη)
  obtain ⟨K,hK,discard⟩ := conductor_error_polylog
  obtain ⟨D,hD,logs⟩ := quartic_log_scale (half_pos hη)
  obtain ⟨P,hP⟩ := eventually_atTop.mp (eventually_absorb (1+K*D) η hη)
  refine ⟨max 64 (max N P),?_⟩
  intro n hn t ht hdeep a q _ ha hc hq hβ
  let v : ZMod q := a
  let β := t-(a:ℝ)/q
  have hnR : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hn0 := zero_lt_one.trans_le hnR
  have hp := discard n q a (by omega) hq hc β hβ
  have hl := logs n hnR
  have he : ‖projectedHighCorrection n v β - conductorCorrection n v β‖ ≤ K*D*(n:ℝ)^(3/4+η/2) := by
    apply hp.trans
    calc
      _ ≤ K*(n:ℝ)^(3/4:ℝ)*(D*(n:ℝ)^(η/2)) := mul_le_mul_of_nonneg_left hl (by positivity)
      _ = _ := by rw [Real.rpow_add hn0];ring
  let S := weightedSum n primeWeight t
  have eq : S+conductorCorrection n v β =
      (S+projectedHighCorrection n v β) - (projectedHighCorrection n v β - conductorCorrection n v β) := by abel
  change ‖S+conductorCorrection n v β‖ ≤ _
  rw [eq]
  exact (norm_sub_le ..).trans ((add_le_add (hN n (by omega) t ht hdeep a q ha hc hq hβ) he).trans
    ((le_of_eq (by ring)).trans (hP n (by omega))))

/-- The exact deep-arc target is equivalent to cancellation in the fixed signed zero sum.
The zero criterion quantifies over every reduced Dirichlet approximant. -/
theorem deep_iff_conductor_cancellation :
    (∀ η : ℝ, 0<η → ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ t ∈ Icc (0:ℝ) 1, t ∉ wideArcs n →
      ‖weightedSum n primeWeight t‖ ≤ (n:ℝ)^(3/4+η)) ↔
    (∀ η : ℝ, 0<η → ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ t ∈ Icc (0:ℝ) 1, t ∉ wideArcs n →
      ∀ (a q : ℕ) [NeZero q], a≤q → a.Coprime q → (q:ℝ)≤Real.sqrt n →
      |t-(a:ℝ)/q| ≤ 1/((q:ℝ)*Real.sqrt n) →
      ‖conductorCorrection n (a:ZMod q) (t-(a:ℝ)/q)‖ ≤ (n:ℝ)^(3/4+η)) := by
  constructor
  · intro target η hη
    obtain ⟨N,hN⟩ := target (η/2) (half_pos hη)
    obtain ⟨M,hM⟩ := deep_intrinsic_model (η/2) (half_pos hη)
    obtain ⟨P,hP⟩ := eventually_atTop.1 (eventually_absorb 2 η hη)
    refine ⟨max N (max M P),?_⟩
    intro n hn t ht hdeep a q _ ha hc hq hβ
    have h₁ := hN n (by omega) t ht hdeep
    have h₂ := hM n (by omega) t ht hdeep a q ha hc hq hβ
    let S := weightedSum n primeWeight t
    let Z := conductorCorrection n (a:ZMod q) (t-(a:ℝ)/q)
    change ‖Z‖ ≤ _
    have h : Z = (S+Z)-S := by abel
    rw [h]
    exact (norm_sub_le ..).trans ((add_le_add h₂ h₁).trans ((le_of_eq (by ring)).trans (hP n (by omega))))
  · intro zeros η hη
    obtain ⟨N,hN⟩ := zeros (η/2) (half_pos hη)
    obtain ⟨M,hM⟩ := deep_intrinsic_model (η/2) (half_pos hη)
    obtain ⟨P,hP⟩ := eventually_atTop.1 (eventually_absorb 2 η hη)
    refine ⟨max 1 (max N (max M P)),?_⟩
    intro n hn t ht hdeep
    obtain ⟨a,q,hq,ha,hc,hden,hβ⟩ := exists_dirichlet n (by omega) t ht
    let : NeZero q := ⟨by omega⟩
    have h₁ := hN n (by omega) t ht hdeep a q ha hc hden hβ
    have h₂ := hM n (by omega) t ht hdeep a q ha hc hden hβ
    let S := weightedSum n primeWeight t
    let Z := conductorCorrection n (a:ZMod q) (t-(a:ℝ)/q)
    change ‖S‖ ≤ _
    have h : S = (S+Z)-Z := by abel
    rw [h]
    exact (norm_sub_le ..).trans ((add_le_add h₂ h₁).trans ((le_of_eq (by ring)).trans (hP n (by omega))))
end GoldbachTwistedMellin
end
end

section
open Complex Finset Set Goldbach GoldbachGRHWindow DeepThreeQuarters DirichletCharacter Filter
open scoped Classical
noncomputable section
namespace GoldbachTwistedMellin

def localConductorRemainder (q n a : ℕ) (β : ℝ) : ℂ :=
  (∑ d ∈ q.divisors, (ArithmeticFunction.moebius (q/d):ℂ)*(d.totient:ℂ)*
    levelTransform (intrinsicSpectrum q) true d (q/d) a n β)/(q.totient:ℂ)

theorem localConductorRemainder_eq {q : ℕ} [NeZero q] (a n : ℕ) (ha : a.Coprime q) (β : ℝ) :
    localConductorRemainder q n a β = conductorCorrection n (a:ZMod q) β := by
  unfold localConductorRemainder
  have h := (conductor_descent_pair (intrinsicSpectrum q) a n ha β).1
  change _ = kernelCorrection (intrinsicSpectrum q) n (a:ZMod q) β
  rw [←h,mul_div_cancel_left₀ _ (show (q.totient:ℂ)≠0 by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne')]

/-- A uniform estimate for primitive sums on the divisor levels is sufficient
for the original pointwise target; the total normalization loss is q/φ(q). -/
theorem deep_of_conductor_conductor_bounds
    (h : ∀ η : ℝ, 0<η → ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ t ∈ Icc (0:ℝ) 1, t ∉ wideArcs n →
      ∀ (a q : ℕ) [NeZero q], a≤q → a.Coprime q → (q:ℝ)≤Real.sqrt n →
      |t-(a:ℝ)/q| ≤ 1/((q:ℝ)*Real.sqrt n) →
      ∀ d ∈ q.divisors, ∀ b : ℕ, b<d → b.Coprime d →
        ‖levelTransform (intrinsicSpectrum q) true d 1 b n (t-(a:ℝ)/q)‖ ≤ (n:ℝ)^(3/4+η)) :
    ∀ η : ℝ, 0<η → ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ t ∈ Icc (0:ℝ) 1, t ∉ wideArcs n →
      ‖weightedSum n primeWeight t‖ ≤ (n:ℝ)^(3/4+η) := by
  intro η hη
  let e := η/4
  have he : 0<e := by dsimp [e];positivity
  obtain ⟨N,hN⟩ := h e he
  obtain ⟨M,hM⟩ := deep_intrinsic_model (η/2) (half_pos hη)
  obtain ⟨P,hP⟩ := eventually_atTop.mp (eventually_absorb (1+(8+4/e)) η hη)
  refine ⟨max 1 (max N (max M P)),?_⟩
  intro n hn t ht hdeep
  have hnR : 1≤(n:ℝ) := by exact_mod_cast (show 1≤n by omega)
  have hn0 := zero_lt_one.trans_le hnR
  obtain ⟨a,q,hq,ha,hc,hqs,hβ⟩ := exists_dirichlet n (by omega) t ht
  let : NeZero q := ⟨by omega⟩
  let β := t-(a:ℝ)/q
  let Z := conductorCorrection n (a:ZMod q) β
  have estimate := hN n (by omega) t ht hdeep a q ha hc hqs hβ
  have bound := conductor_two_way_bound (intrinsicSpectrum q) true a n hc β ((n:ℝ)^(3/4+e)) (by positivity) estimate
  have eq : levelTransform (intrinsicSpectrum q) false q 1 a n β = Z := by
    rw [levelTransform_eq,intrinsicSpectrum];simp only [Bool.false_eq_true,ite_false,Nat.cast_one,map_one,mul_one]
    rfl
  change ‖levelTransform (intrinsicSpectrum q) false q 1 a n β‖≤_ at bound
  rw [eq] at bound
  have qn : (q:ℝ)≤n := hqs.trans (Real.sqrt_le_self_iff.mpr (Or.inr hnR))
  have hratio := (totient_ratio_le_rpow he q hq).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) qn he.le) (by positivity))
  have hz : ‖Z‖ ≤ (8+4/e)*(n:ℝ)^(3/4+η/2) := by
    apply (bound.trans (mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hn0.le _))).trans_eq
    rw [mul_assoc,←Real.rpow_add hn0]
    have ee : e+(3/4+e)=3/4+η/2 := by dsimp [e];ring
    rw [ee]
  let S := weightedSum n primeWeight t
  have eqS : S = (S+Z)-Z := by abel
  change ‖S‖≤_
  rw [eqS]
  exact (norm_sub_le ..).trans ((add_le_add (hM n (by omega) t ht hdeep a q ha hc hqs hβ) hz).trans
    ((le_of_eq (by ring)).trans (hP n (by omega))))
end GoldbachTwistedMellin
end
end

open Goldbach GoldbachTwistedMellin
theorem PEqualNP.Outside.L_goldbach_deep_three_quarters_filtered_zero_criterion :
let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0
let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t))
let Q := fun n : ℕ => (Nat.log 2 (n+2))^2
let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊
let H := fun n : ℕ => 256 * Q₁ n * Q n
let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}
let f := fun (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) =>
  @ite (ℂ → ℂ) (χ = 1) (Classical.propDecidable _) (DirichletCharacter.LFunctionTrivChar₁ q) (DirichletCharacter.LFunction χ)
let W := fun (l r : ℕ) (β : ℝ) (z : ℂ) =>
  mellin (fun x : ℝ => ((max 0 (min (x-(l:ℝ)) (min 1 ((r:ℝ)+1-x))) : ℝ):ℂ) *
    Complex.exp ((((2*Real.pi*β)*x:ℝ):ℂ)*Complex.I)) z
let g := fun (q : ℕ) [NeZero q] (v : ZMod q) (χ : DirichletCharacter ℂ q) =>
  (starRingEnd ℂ) (∑ r : ZMod q,(starRingEnd ℂ) (ZMod.stdAddChar (v*r))*χ r)/(q.totient:ℂ)
∃ blocks : ℕ → List (ℕ×ℕ), ∃ zeros : (q : ℕ) → [NeZero q] → DirichletCharacter ℂ q → ℝ → Finset ℂ,
  (∀ m, blocks m = if m<2 then [] else (m/2+2,m+2)::blocks (m/2)) ∧
  (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (B : ℝ) (z : ℂ),
    z ∈ zeros q χ B ↔ 1/2 < z.re ∧ |z.im| ≤ B ∧ f q χ z = 0) ∧
  let active := fun (D n : ℕ) (X γ : ℝ) (z : ℂ) => @decide
    (∃ x ∈ Set.Icc X (2*X), (n:ℝ)^(3/4:ℝ)*max (max 1 (Real.sqrt |z.im|))
      (max |γ*x+z.im| (|z.im|^2/X)) < Real.sqrt D*X^z.re*(1+|z.im|)) (Classical.propDecidable _)
  let K := fun (Q d : ℕ) [NeZero d] (n : ℕ) (χ : DirichletCharacter ℂ d) (β : ℝ) =>
    if (Q:ℝ)/(n:ℝ)^(1/4:ℝ) < (χ.conductor:ℝ) then ((blocks (n-2)).map fun p =>
      ∑ z ∈ (((zeros d χ ((2*(p.1:ℝ))^8)).filter (fun z =>
        (n:ℝ)^(3/4:ℝ) < (p.1:ℝ)^z.re * Real.sqrt χ.conductor * Real.sqrt (1+4*|2*Real.pi*β| *p.1))).filter (fun z =>
        |z.im| ≤ max 2 (Real.sqrt χ.conductor*(p.1:ℝ)^2/(n:ℝ)^(3/4:ℝ)))).filter (fun z => active χ.conductor n p.1 (2*Real.pi*β) z = true),
        (analyticOrderNatAt (f d χ) z:ℂ)*W p.1 p.2 β z).sum else 0
  let U := fun (p : Bool) (Q d m a n : ℕ) (β : ℝ) => if h : d=0 then (0:ℂ) else
    let _ : NeZero d := ⟨h⟩
    ∑ χ : DirichletCharacter ℂ d, @ite ℂ (p=false ∨ χ.IsPrimitive) (Classical.propDecidable _)
      (g d (a:ZMod d) χ*χ⁻¹ (m:ZMod d)*K Q d n χ β) 0
  let R := fun (q : ℕ) (n a : ℕ) (β : ℝ) =>
    (∑ d ∈ q.divisors,(ArithmeticFunction.moebius (q/d):ℂ)*(d.totient:ℂ)*U true q d (q/d) a n β)/(q.totient:ℂ)
  (∀ (q : ℕ) [NeZero q] (a n : ℕ), a.Coprime q → ∀ β : ℝ,
    U false q q 1 a n β = R q n a β ∧
    (q.totient:ℂ)*U true q q 1 a n β =
      ∑ d ∈ q.divisors,(ArithmeticFunction.moebius (q/d):ℂ)^2*(d.totient:ℂ)*U false q d (q/d) a n β) ∧
  (∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0:ℝ) 1, t ∉ wideArcs n →
    ∀ (a q : ℕ) [NeZero q], a ≤ q → a.Coprime q → (q:ℝ) ≤ Real.sqrt n →
      |t-(a:ℝ)/q| ≤ 1/((q:ℝ)*Real.sqrt n) →
      ‖S n w t + R q n a (t-(a:ℝ)/q)‖ ≤ (n:ℝ)^(3/4+η)) ∧
  ((∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ wideArcs n → ‖S n w t‖ ≤ (n : ℝ) ^ (3 / 4 + η)) ↔
    (∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0:ℝ) 1, t ∉ wideArcs n →
      ∀ (a q : ℕ) [NeZero q], a ≤ q → a.Coprime q → (q:ℝ) ≤ Real.sqrt n →
        |t-(a:ℝ)/q| ≤ 1/((q:ℝ)*Real.sqrt n) →
        ‖R q n a (t-(a:ℝ)/q)‖ ≤ (n:ℝ)^(3/4+η))) := by
  classical
  intro w E S Q Q₁ H arcs f W g
  refine ⟨prefixBlocks,fun q _ χ B => exceptionalZeros χ B,?_,?_,?_⟩
  · intro m
    rw [prefixBlocks]
    split_ifs <;> rfl
  · intro q _ χ B z
    have hf : f q χ = regularizedL χ := by by_cases h : χ=1 <;> simp [f,regularizedL,h]
    rw [hf]
    exact mem_exceptionalZeros χ B z
  · intro active K U R
    have eqK (Q d : ℕ) [NeZero d] (n : ℕ) (χ : DirichletCharacter ℂ d) (β : ℝ) :
        K Q d n χ β = (intrinsicSpectrum Q).coeff n χ β := by
      have hf : f d χ = regularizedL χ := by by_cases h : χ=1 <;> simp [f,regularizedL,h]
      dsimp only [K,intrinsicSpectrum,phaseKeptBlock]
      simp_rw [hf]
      simp only [active,decide_eq_true_eq,activePhase]
      rfl
    have eqU (p : Bool) (Q d m a n : ℕ) (β : ℝ) :
        U p Q d m a n β = levelTransform (intrinsicSpectrum Q) p d m a n β := by
      by_cases hd : d=0
      · simp [U,levelTransform,hd]
      · let : NeZero d := ⟨hd⟩
        cases p
        · simp only [U,dite_eq_right hd,true_or,ite_true,levelTransform_eq,Bool.false_eq_true,ite_false]
          simp_rw [eqK]
          rfl
        · simp only [U,dite_eq_right hd,Bool.true_eq_false,false_or,levelTransform_eq,ite_true,Finset.sum_filter]
          simp_rw [eqK]
          rfl
    have eqR (q : ℕ) [NeZero q] (n a : ℕ) (β : ℝ) (hc : a.Coprime q) :
        R q n a β = conductorCorrection n (a:ZMod q) β := by
      dsimp only [R]
      simp_rw [eqU]
      exact localConductorRemainder_eq a n hc β
    constructor
    · intro q _ a n hc β
      simp_rw [eqU]
      refine ⟨?_,(conductor_descent_pair (intrinsicSpectrum q) a n hc β).2⟩
      rw [eqR q n a β hc,levelTransform_eq]
      simp only [Bool.false_eq_true,ite_false,Nat.cast_one,map_one,mul_one]
      rfl
    constructor
    · intro η hη
      obtain ⟨N,hN⟩ := deep_intrinsic_model η hη
      refine ⟨N,?_⟩
      intro n hn t ht hdeep a q _ ha hc hq hβ
      rw [eqR q n a _ hc]
      exact hN n hn t ht hdeep a q ha hc hq hβ
    · constructor
      · intro target η hη
        obtain ⟨N,hN⟩ := deep_iff_conductor_cancellation.mp target η hη
        refine ⟨N,?_⟩
        intro n hn t ht hdeep a q _ ha hc hq hβ
        rw [eqR q n a _ hc]
        exact hN n hn t ht hdeep a q ha hc hq hβ
      · intro h
        apply deep_iff_conductor_cancellation.mpr
        intro η hη
        obtain ⟨N,hN⟩ := h η hη
        refine ⟨N,?_⟩
        intro n hn t ht hdeep a q _ ha hc hq hβ
        rw [←eqR q n a _ hc]
        exact hN n hn t ht hdeep a q ha hc hq hβ
