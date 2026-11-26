import Mathlib

/-!
# Pointwise lower bound for every fixed polylogarithmic inner skirt

For each fixed exponent b+4 the cutoff in the numerator of the outer radius is log₂(n+2)^(b+4).
The original denominators, narrow arcs, prime weights and phase are unchanged.
An exact decomposition identifies the still-open outer band reaching the cube-root scale.

The signed rational model is adapted from LogTruSoul, goldbach-proofs PR 2829,
cfde193e18afc4e0ffac53868d514142e908cd36, and its Apache-2.0 source PR 2486,
f3613cf846dfb3e7fe7d04fe6ce51c6ee25e7d4f. Only unconditional model and geometry are used.
The uniform logarithmic square-model estimate is from goldbach-proofs PR 1667,
813ca8c4a3e6ab6ef53180fc5a2c56275a19db88. The original contributor credits follow below.
-/

/-! The short blocks use a central prime interval that moves with the target block. Its Fourier
sum is the difference of two prime sums. At each rational arc its model Dirichlet kernel
has a translated phase, and its two interval endpoints obey common major and minor estimates.
The on-block correlation estimate follows from finite Fourier orthogonality and Bessel.
The analytic background below incorporates the credited major-arc and Vaughan developments. -/
section

/-!
# Major-arc estimates for the prime logarithmic sum

The general finite estimates below are from DFQDZZ, goldbach-proofs PR #316,
revision e4ab24712555ae8c2c926adf19d368a9fb392c35 (Apache-2.0).

The analytic material in the namespaces OAI.LargePrimeGaps is selected and adapted
from OpenAI's openai/math, lean/OAI/NumberTheory/PrimeGaps, at revision
f5702854040e97fa7675c21ba37a9608f5f92dd3, licensed under Apache 2.0 (see LICENSE).
It is specialized to the declarations required for the small-modulus estimate and
ported from toolchain 4.34.1 to the version locked by this repository.
-/

section

-- Source module: CharacterErrors
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
noncomputable def primeCharacterPrefix (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)

noncomputable def primeCharacterError (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  primeCharacterPrefix x χ-if χ=1 then (x:ℂ) else 0

end LargePrimeGaps
end OAI

-- Source module: ConductorBounds
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
def SiegelWalfisz : Prop :=
  ∀ A B : ℝ, 0 < A → 0 < B → ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → ∀ d : ℕ, 0 < d → (d:ℝ) ≤ (Real.log x)^B →
      ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
        ‖primeCharacterError x χ‖ ≤ M*x*(Real.log x)^(-A)

theorem eventually_log_rpow_le_rpow (a : ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, (Real.log x)^a ≤ x^s := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop a hs).bound (by norm_num : (0:ℝ)<1),
    eventually_ge_atTop (1:ℝ)] with x h hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx) _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0≤x) _),one_mul] using h

end LargePrimeGaps
end OAI

-- Source module: LogParameters
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
open Complex Filter Topology
noncomputable def poleRemovedL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q else χ.LFunction

noncomputable def primeLogDerivativeRegular {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -deriv (poleRemovedL χ) s / poleRemovedL χ s

theorem poleRemovedL_differentiable {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : Differentiable ℂ (poleRemovedL χ) := by
  unfold poleRemovedL
  split_ifs with hχ
  · exact DirichletCharacter.differentiable_LFunctionTrivChar₁ q
  · exact DirichletCharacter.differentiable_LFunction hχ

theorem poleRemovedL_ne_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 ≤ s.re) :
    poleRemovedL χ s ≠ 0 := by
  unfold poleRemovedL
  split_ifs with hχ
  · rcases eq_or_ne s 1 with rfl | hs1
    · exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q
    · rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1]
      refine mul_ne_zero (sub_ne_zero.mpr hs1) ?_
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re 1 (.inr hs1) hs
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs

theorem primeLogDerivativeRegular_analyticAt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : poleRemovedL χ s ≠ 0) :
    AnalyticAt ℂ (primeLogDerivativeRegular χ) s := by
  have h := (poleRemovedL_differentiable χ).analyticAt s
  exact h.deriv.neg.div h hs

theorem primeLogDerivativeRegular_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    primeLogDerivativeRegular χ s =
      LSeries (fun n : ℕ => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) s -
        (if χ = 1 then 1 / (s - 1) else 0) := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hL := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  change LSeries (fun n : ℕ => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
    -deriv (LSeries (fun n : ℕ => χ (n : ZMod q))) s /
      LSeries (fun n : ℕ => χ (n : ZMod q)) s at hL
  rw [hL, ← DirichletCharacter.LFunction_eq_LSeries χ hs,
    ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs]
  by_cases hχ : χ = 1
  · subst χ
    have hn := DirichletCharacter.LFunction_ne_zero_of_one_le_re
      (1 : DirichletCharacter ℂ q) (.inr hs1) hs.le
    simp only [primeLogDerivativeRegular, poleRemovedL, ↓reduceIte]
    rw [DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one q hs1,
      DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1]
    change -((s-1)*deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s +
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s) /
      ((s-1)*DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s) = _
    field_simp
    ring
  · simp [primeLogDerivativeRegular, poleRemovedL, hχ]

end LargePrimeGaps
end OAI

-- Source module: DirichletGrowth
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
open Complex Filter Topology
open Complex Filter Topology Set MeasureTheory Asymptotics
noncomputable def discrepancyTail (A : ℝ → ℂ) (u : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioi u, A t * (t:ℂ)^(-(s+1))

lemma discrepancyTail_integrable {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (hD : 0 ≤ D)
    (hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t => A t * (t:ℂ)^(-(s+1))) (Ioi u) := by
  have hp : (-(s+1)).re < -1 := by simp only [neg_re,add_re,one_re]; linarith
  have hi := (integrableOn_Ioi_norm_cpow_of_lt hp hu).const_mul D
  have hm := (integrableOn_Ioi_cpow_of_lt hp hu).aestronglyMeasurable
  refine hi.mono (hA.aestronglyMeasurable.restrict.mul hm) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hD (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg _)

lemma discrepancyTail_norm_le {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (_hD : 0 ≤ D)
    (_hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    ‖discrepancyTail A u s‖ ≤ D * u^(-s.re)/s.re := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) hu).const_mul D
  calc
    _ ≤ ∫ t in Ioi u, D*t^(-s.re-1) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (hu.trans ht)]
      simp only [neg_re,add_re,one_re,neg_add_rev]
      have he : -1 + -s.re = -s.re-1 := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_right (hbound t ht) (Real.rpow_nonneg (hu.trans ht).le _)
    _ = _ := by
      rw [integral_const_mul,integral_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) hu]
      ring_nf

lemma discrepancyTail_eq_mellin {A : ℝ → ℂ} {u : ℝ} (hu : 0 ≤ u) (s : ℂ) :
    discrepancyTail A u s = mellin ((Ioi u).indicator A) (-s) := by
  rw [mellin]
  simp_rw [←Set.indicator_smul]
  rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
  have he : Ioi u ∩ Ioi 0 = Ioi u := Set.inter_eq_left.mpr (fun t ht => hu.trans_lt ht)
  rw [he]
  unfold discrepancyTail
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  ring

lemma discrepancyTail_differentiableAt {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (hD : 0 ≤ D)
    (hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (discrepancyTail A u) s := by
  let B := (Ioi u).indicator A
  have hm : Measurable B := hA.indicator measurableSet_Ioi
  have hb : ∀ t, ‖B t‖ ≤ D := by
    intro t
    by_cases ht : u < t
    · simpa [B,ht] using hbound t ht
    · simpa [B,ht] using hD
  have hloc : LocallyIntegrableOn B (Ioi 0) :=
    ((locallyIntegrable_const D).mono hm.aestronglyMeasurable
      (.of_forall (fun t => (hb t).trans (le_abs_self D)))).locallyIntegrableOn _
  have htop : B =O[atTop] (fun t : ℝ => t^(-(0:ℝ))) := by
    refine isBigO_iff.mpr ⟨D,Eventually.of_forall ?_⟩
    intro t
    simpa using hb t
  have hbot : B =O[𝓝[>] 0] (fun t : ℝ => t^(-(-s.re-1))) := by
    refine isBigO_iff.mpr ⟨0,?_⟩
    filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds hu)] with t ht
    simp [B,not_lt.mpr ht.le]
  have hd := mellin_differentiableAt_of_isBigO_rpow hloc htop
    (by simpa using hs : (-s).re < 0) hbot (by simp : -s.re-1 < (-s).re)
  have he : discrepancyTail A u = fun z => mellin B (-z) := funext (discrepancyTail_eq_mellin hu.le)
  rw [he]
  exact hd.comp s differentiableAt_id.neg

open Finset
lemma periodic_sum_norm_le {f : ℕ → ℂ} {q : ℕ} (hq : 0 < q)
    (hp : ∀ n, f (q+n) = f n) (hz : ∑ n ∈ range q, f n = 0)
    (hb : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) : ‖∑ n ∈ range N, f n‖ ≤ q := by
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    by_cases hN : N < q
    · calc
        _ ≤ ∑ n ∈ range N, ‖f n‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ range N, (1:ℝ) := sum_le_sum (fun n _ => hb n)
        _ = N := by simp
        _ ≤ q := by exact_mod_cast hN.le
    · have he : q+(N-q) = N := Nat.add_sub_of_le (not_lt.mp hN)
      rw [←he, sum_range_add, hz, zero_add]
      simp_rw [hp]
      exact ih _ (Nat.sub_lt (lt_of_lt_of_le hq (not_lt.mp hN)) hq)

lemma char_sum_range_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : ∑ n ∈ range q, χ (n : ZMod q) = 0 := by
  rw [←Fin.sum_univ_eq_sum_range]
  have he := (ZMod.finEquiv q).toEquiv.sum_comp χ
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    have hz := he.trans (MulChar.sum_eq_zero_of_ne_one hχ)
    change (∑ i : Fin (q+1), χ i) = 0 at hz
    calc
      _ = ∑ i : Fin (q+1), χ (i : Fin (q+1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        exact Fin.cast_val_eq_self i
      _ = 0 := hz

lemma char_sum_Icc_norm_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (N : ℕ) : ‖∑ n ∈ Icc 1 N, χ (n : ZMod q)‖ ≤ q+1 := by
  have hr := periodic_sum_norm_le (NeZero.pos q)
    (f := fun n => χ (n : ZMod q)) (by intro n; simp)
    (char_sum_range_zero hχ) (fun n => χ.norm_le_one _) (N+1)
  have he : ∑ n ∈ range (N+1), χ (n : ZMod q) =
      χ (0 : ZMod q) + ∑ n ∈ Icc 1 N, χ (n : ZMod q) := by
    rw [Nat.range_succ_eq_Icc_zero, ←Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le N)]
    simp
  rw [he] at hr
  calc
    _ = ‖(χ (0 : ZMod q) + ∑ n ∈ Icc 1 N, χ (n : ZMod q)) - χ 0‖ := by congr 1; ring
    _ ≤ ‖χ (0 : ZMod q) + ∑ n ∈ Icc 1 N, χ (n : ZMod q)‖ + ‖χ 0‖ := norm_sub_le _ _
    _ ≤ q+1 := add_le_add hr (χ.norm_le_one _)

noncomputable def seriesDiscrepancy (f : ℕ → ℂ) (c : ℂ) (t : ℝ) : ℂ :=
  (∑ n ∈ Icc 1 ⌊t⌋₊, f n) - c*t

lemma measurable_seriesDiscrepancy (f : ℕ → ℂ) (c : ℂ) :
    Measurable (seriesDiscrepancy f c) := by
  exact ((measurable_of_countable (fun N : ℕ => ∑ n ∈ Icc 1 N, f n)).comp
    Nat.measurable_floor).sub (measurable_const.mul Complex.continuous_ofReal.measurable)

noncomputable def regularSeries (f : ℕ → ℂ) (c : ℂ) (s : ℂ) : ℂ :=
  c+s*discrepancyTail (seriesDiscrepancy f c) 1 s

lemma regularSeries_differentiableAt {f : ℕ → ℂ} {c : ℂ} {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (regularSeries f c) s := by
  exact (differentiableAt_const c).add (differentiableAt_id.mul
    (discrepancyTail_differentiableAt zero_lt_one hD (measurable_seriesDiscrepancy f c) hb hs))

lemma regularSeries_eq_LSeries_sub {f : ℕ → ℂ} {c : ℂ} {D : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ 1) (hD : 0 ≤ D)
    (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D) {s : ℂ} (hs : 1 < s.re) :
    regularSeries f c s = LSeries f s - c/(s-1) := by
  have hO : (fun n => ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] (fun n => (n:ℝ)^(1:ℝ)) := by
    refine isBigO_iff.mpr ⟨1, .of_forall (fun n => ?_)⟩
    simp only [Real.rpow_one, one_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (sum_nonneg (fun _ _ => norm_nonneg _))]
    calc
      _ ≤ ∑ _k ∈ Icc 1 n, (1:ℝ) := sum_le_sum (fun n _ => hf n)
      _ ≤ |(n:ℝ)| := by simp
  rw [LSeries_eq_mul_integral' f zero_le_one hs hO]
  have hiA := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb
    (zero_lt_one.trans hs)
  have hi := integrableOn_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs : (-s).re < -1) zero_lt_one
  have he (t : ℝ) (ht : 1 < t) :
      (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t:ℂ)^(-(s+1)) =
      seriesDiscrepancy f c t * (t:ℂ)^(-(s+1)) + c*(t:ℂ)^(-s) := by
    have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans ht).ne'
    have ht1 : (t:ℂ)*(t:ℂ)^(-(s+1)) = (t:ℂ)^(-s) := by
      nth_rw 1 [←Complex.cpow_one (t:ℂ)]
      rw [←Complex.cpow_add _ _ ht0]
      congr 1
      ring
    dsimp [seriesDiscrepancy]
    rw [sub_mul, mul_assoc c, ht1]
    ring
  have hs0 : s-1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hv : ∫ t in Ioi (1:ℝ), (t:ℂ)^(-s) = 1/(s-1) := by
    rw [integral_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs : (-s).re < -1) zero_lt_one]
    simp only [ofReal_one, one_cpow]
    have he : -s+1 = -(s-1) := by ring
    rw [he, neg_div_neg_eq]
  have hint : (∫ t in Ioi (1:ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t:ℂ)^(-(s+1))) =
      ∫ t in Ioi (1:ℝ), seriesDiscrepancy f c t * (t:ℂ)^(-(s+1)) + c*(t:ℂ)^(-s) :=
    setIntegral_congr_fun measurableSet_Ioi (fun {t} ht => he t ht)
  rw [hint,
    integral_add hiA (hi.const_mul c), integral_const_mul, hv]
  dsimp [regularSeries,discrepancyTail]
  field_simp [hs0]
  ring

lemma sum_Icc_zero_eq {f : ℕ → ℂ} (hf : f 0 = 0) (N : ℕ) :
    ∑ k ∈ Icc 0 N, f k = ∑ k ∈ Icc 1 N, f k := by
  rw [←Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le N)]
  simp [hf]

lemma weighted_sum_abel {f : ℕ → ℂ} (hf : f 0 = 0) {N : ℕ} (hN : 1 ≤ N)
    {s : ℂ} (hs : 0 < s.re) :
    ∑ n ∈ Icc 1 N, f n * (n:ℂ)^(-s) =
      (∑ n ∈ Icc 1 N, f n)*(N:ℂ)^(-s) +
        s*∫ t in (1:ℝ)..N, (∑ n ∈ Icc 1 ⌊t⌋₊, f n)*(t:ℂ)^(-(s+1)) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hd (t:ℝ) (ht : t ∈ Set.Icc 1 (N:ℝ)) :
      HasDerivAt (fun t : ℝ => (t:ℂ)^(-s)) ((-s)*(t:ℂ)^(-(s+1))) t := by
    rw [show -(s+1) = -s-1 by ring]
    exact hasDerivAt_ofReal_cpow_const ((zero_lt_one.trans_le ht.1).ne') (neg_ne_zero.mpr hs0)
  have hcont : ContinuousOn (fun t : ℝ => (-s)*(t:ℂ)^(-(s+1))) (Set.Icc 1 (N:ℝ)) := by
    intro t ht
    exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const _ _
      (.inr (zero_lt_one.trans_le ht.1).ne'))).continuousWithinAt
  have hi : IntegrableOn (deriv (fun t:ℝ => (t:ℂ)^(-s))) (Set.Icc 1 (N:ℝ)) :=
    hcont.integrableOn_Icc.congr_fun (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have ha := sum_mul_eq_sub_sub_integral_mul' f hN (fun t ht => (hd t (by simpa using ht)).differentiableAt) (by simpa using hi)
  have he : (insert 1 (Finset.Ioc 1 N) : Finset ℕ) = Finset.Icc 1 N := by
    ext k
    simp only [Finset.mem_insert,Finset.mem_Ioc,Finset.mem_Icc]
    omega
  have hint : (∫ t in Set.Ioc (1:ℝ) (N:ℝ),
      deriv (fun t:ℝ => (t:ℂ)^(-s)) t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k) =
      (-s)*∫ t in (1:ℝ)..N, (∑ k ∈ Icc 1 ⌊t⌋₊, f k)*(t:ℂ)^(-(s+1)) := by
    rw [intervalIntegral.integral_of_le hNR, ←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hd t ⟨ht.1.le,ht.2⟩).deriv,sum_Icc_zero_eq hf]
    ring
  simp only [Nat.cast_one, Complex.ofReal_natCast, Complex.ofReal_one] at ha
  rw [hint] at ha
  simp only [one_cpow,one_mul,sum_Icc_zero_eq hf,Finset.Icc_self,sum_singleton] at ha
  conv_lhs => rw [←he,sum_insert (by simp)]
  simp only [Nat.cast_one,one_cpow,mul_one]
  simp_rw [mul_comm (f _) ((_:ℂ)^(-s))]
  rw [ha]
  ring

lemma cpow_sub_eq_mul_intervalIntegral {N : ℝ} (hN : 1 ≤ N) (s : ℂ) :
    (N:ℂ)^(1-s)-1 = (1-s)*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
  by_cases hs : s = 1
  · subst s
    simp
  · have hn : (0:ℝ) ∉ Set.uIcc 1 N := by rw [Set.uIcc_of_le hN]; simp
    rw [integral_cpow (.inr ⟨by simpa using hs,hn⟩)]
    simp only [Complex.ofReal_one,one_cpow]
    have he : -s+1 = 1-s := by ring
    rw [he]
    field_simp

lemma regularSeries_cutoff {f : ℕ → ℂ} {c : ℂ} {D : ℝ} (hf : f 0 = 0)
    (hD : 0 ≤ D) (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D)
    {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    regularSeries f c s = (∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) -
      seriesDiscrepancy f c N * (N:ℂ)^(-s) +
      s*discrepancyTail (seriesDiscrepancy f c) N s -
      c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N:ℂ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN).ne'
  have hi := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb hs
  have htail := intervalIntegral.integral_Ioi_sub_Ioi hi hNR
  have hp : ∀ t ∈ Set.Icc (1:ℝ) (N:ℝ),
      (t:ℂ)*(t:ℂ)^(-(s+1)) = (t:ℂ)^(-s) := by
    intro t ht
    have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le ht.1).ne'
    nth_rw 1 [←Complex.cpow_one (t:ℂ)]
    rw [←Complex.cpow_add _ _ ht0]
    congr 1
    ring
  have hip : IntervalIntegrable (fun t:ℝ => (t:ℂ)^(-s)) volume 1 N :=
    intervalIntegral.intervalIntegrable_cpow (.inr (by rw [Set.uIcc_of_le hNR]; simp))
  have hiA : IntervalIntegrable (fun t:ℝ => seriesDiscrepancy f c t*(t:ℂ)^(-(s+1))) volume 1 N :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hNR).mpr (hi.mono_set Set.Ioc_subset_Ioi_self)
  have hint : (∫ t in (1:ℝ)..N, (∑ n ∈ Icc 1 ⌊t⌋₊, f n)*(t:ℂ)^(-(s+1))) =
      (∫ t in (1:ℝ)..N, seriesDiscrepancy f c t*(t:ℂ)^(-(s+1))) +
        c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
    rw [←intervalIntegral.integral_const_mul, ←intervalIntegral.integral_add hiA (hip.const_mul c)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hNR] at ht
    dsimp [seriesDiscrepancy]
    rw [sub_mul,mul_assoc c,hp t ht]
    ring
  have hab := weighted_sum_abel hf hN hs
  rw [hint, ←htail] at hab
  have hpow : (N:ℂ)*(N:ℂ)^(-s) = (N:ℂ)^(1-s) := by
    nth_rw 1 [←Complex.cpow_one (N:ℂ)]
    rw [←Complex.cpow_add _ _ hn0]
    congr 1
  have hc := cpow_sub_eq_mul_intervalIntegral hNR s
  simp only [Complex.ofReal_natCast] at hc
  dsimp [regularSeries,discrepancyTail]
  rw [hab]
  simp only [seriesDiscrepancy,Nat.floor_natCast,Complex.ofReal_natCast]
  rw [sub_mul,mul_assoc c,hpow,sub_eq_iff_eq_add.mp hc]
  ring

lemma sum_cpow_norm_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {ε : ℝ} (hε : 0 < ε)
    {s : ℂ} (hs : 1-ε ≤ s.re) {N : ℕ} (_hN : 1 ≤ N) :
    ‖∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)‖ ≤
      (∑' n : ℕ, (n:ℝ)^(-1-ε)) * (N:ℝ)^(2*ε) := by
  have hsumm : Summable (fun n : ℕ => (n:ℝ)^(-1-ε)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ‖f n*(n:ℂ)^(-s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 N, (n:ℝ)^(-1-ε)*(N:ℝ)^(2*ε) := by
      apply sum_le_sum
      intro n hn
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
      have hnN : (n:ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
      have hn0 := zero_lt_one.trans_le hn1
      rw [norm_mul]
      have hn0C : (n:ℂ) = ((n:ℝ):ℂ) := by simp
      rw [hn0C,Complex.norm_cpow_eq_rpow_re_of_pos hn0,Complex.neg_re]
      calc
        _ ≤ (n:ℝ)^(-s.re) := by
          simpa using mul_le_mul_of_nonneg_right (hf n) (Real.rpow_nonneg hn0.le (-s.re))
        _ ≤ (n:ℝ)^(-1+ε) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        _ = (n:ℝ)^(-1-ε)*(n:ℝ)^(2*ε) := by rw [←Real.rpow_add hn0]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn0.le hnN (by positivity))
          (Real.rpow_nonneg hn0.le _)
    _ = (∑ n ∈ Icc 1 N, (n:ℝ)^(-1-ε))*(N:ℝ)^(2*ε) := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hsumm.sum_le_tsum _ (fun n _ => Real.rpow_nonneg n.cast_nonneg _))
      (Real.rpow_nonneg N.cast_nonneg _)

lemma norm_intervalIntegral_cpow_le {ε N : ℝ} (hε : 0 < ε) (hN : 1 ≤ N)
    {s : ℂ} (hs : 1-ε ≤ s.re) :
    ‖∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ ≤ N^ε/ε := by
  have hn : (0:ℝ) ∉ Set.uIcc 1 N := by rw [Set.uIcc_of_le hN]; simp
  calc
    _ ≤ ∫ t in (1:ℝ)..N, t^(-1+ε) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hN
        (.of_forall (fun t ht => ?_)) (intervalIntegral.intervalIntegrable_rpow (.inr hn))
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht.1),Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le ht.1.le (by linarith)
    _ = (N^ε-1)/ε := by
      rw [integral_rpow (.inl (by linarith : -1 < -1+ε))]
      have he : -1+ε+1 = ε := by ring
      simp [he]
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hε.le

lemma regularSeries_norm_cutoff {f : ℕ → ℂ} {c : ℂ} {D ε : ℝ}
    (hf0 : f 0 = 0) (hf : ∀ n, ‖f n‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hD : 0 ≤ D)
    (hb : ∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D)
    (hε : 0 < ε) (hε1 : ε ≤ 1/2) {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hs : 1-ε ≤ s.re) (hNs : D*(1+‖s‖) ≤ N) :
    ‖regularSeries f c s‖ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε))+2+1/ε)*(N:ℝ)^(2*ε) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNP := zero_lt_one.trans_le hNR
  have hs0 : 0 < s.re := by linarith
  have hhalf : 1/2 ≤ s.re := by linarith
  have htail := discrepancyTail_norm_le hNP hD (measurable_seriesDiscrepancy f c)
    (fun t ht => hb t (hNR.trans ht.le)) hs0
  have hboundary : ‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ ≤ D*(N:ℝ)^(-s.re) := by
    rw [norm_mul, ←Complex.ofReal_natCast N, Complex.norm_cpow_eq_rpow_re_of_pos hNP,Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hb _ hNR) (Real.rpow_nonneg hNP.le _)
  have hsmall : ‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
      ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖ ≤ 2*(N:ℝ)^ε := by
    have ht : D*(N:ℝ)^(-s.re)/s.re ≤ 2*D*(N:ℝ)^(-s.re) := by
      apply (div_le_iff₀ hs0).mpr
      have hn := Real.rpow_nonneg hNP.le (-s.re)
      nlinarith [mul_nonneg hD hn,mul_nonneg (mul_nonneg hD hn) (sub_nonneg.mpr hhalf)]
    have he : (N:ℝ)*(N:ℝ)^(-s.re) ≤ (N:ℝ)^ε := by
      nth_rw 1 [←Real.rpow_one (N:ℝ)]
      rw [←Real.rpow_add hNP]
      apply Real.rpow_le_rpow_of_exponent_le hNR
      linarith
    calc
      _ ≤ D*(N:ℝ)^(-s.re) + ‖s‖*(2*D*(N:ℝ)^(-s.re)) := by
        nth_rw 2 [norm_mul]
        exact add_le_add hboundary (mul_le_mul_of_nonneg_left (htail.trans ht) (norm_nonneg s))
      _ ≤ 2*(N:ℝ)*(N:ℝ)^(-s.re) := by
        have hcoeff : D+2*‖s‖*D ≤ 2*(N:ℝ) := by nlinarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hcoeff) (Real.rpow_nonneg hNP.le (-s.re))]
      _ ≤ _ := by nlinarith [he]
  have hi : ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ ≤ (N:ℝ)^ε/ε := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans (by
      simpa using norm_intervalIntegral_cpow_le hε hNR hs)
  have hp : (N:ℝ)^ε ≤ (N:ℝ)^(2*ε) := Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
  rw [regularSeries_cutoff hf0 hD (fun t ht => hb t ht.le) hN hs0]
  calc
    _ ≤ ‖∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)‖ +
        (‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
        ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖) +
        ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := by
      calc
        _ ≤ ‖(∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) - seriesDiscrepancy f c N * (N:ℂ)^(-s) +
             s*discrepancyTail (seriesDiscrepancy f c) N s‖ +
             ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := norm_sub_le _ _
        _ ≤ (‖(∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) - seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
             ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖) +
             ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := add_le_add (norm_add_le _ _) le_rfl
        _ ≤ _ := by
          have htri := norm_sub_le (∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) (seriesDiscrepancy f c N * (N:ℂ)^(-s))
          linarith
    _ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε)))*(N:ℝ)^(2*ε) +
      2*(N:ℝ)^ε+(N:ℝ)^ε/ε := add_le_add (add_le_add (sum_cpow_norm_le hf hε hs hN) hsmall) hi
    _ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε)))*(N:ℝ)^(2*ε) +
      2*(N:ℝ)^(2*ε)+(N:ℝ)^(2*ε)/ε := by
        linarith [div_le_div_of_nonneg_right hp hε.le]
    _ = _ := by ring

lemma regularSeries_norm_small_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℕ → ℂ) (c : ℂ) (D : ℝ),
      f 0 = 0 → (∀ n, ‖f n‖ ≤ 1) → ‖c‖ ≤ 1 → 0 ≤ D →
      (∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D) →
      ∀ s : ℂ, 1-ε ≤ s.re →
      ‖regularSeries f c s‖ ≤ K*((D+1)*(‖s‖+2))^(2*ε) := by
  let K₀ := (∑' n : ℕ, (n:ℝ)^(-1-ε))+2+1/ε
  have hK₀ : 0 < K₀ := by
    have ht : 0 ≤ ∑' n : ℕ, (n:ℝ)^(-1-ε) := tsum_nonneg (fun n => Real.rpow_nonneg n.cast_nonneg _)
    dsimp [K₀]
    positivity
  refine ⟨K₀*2^(2*ε), by positivity, ?_⟩
  intro f c D hf0 hf hc hD hb s hs
  let B := (D+1)*(‖s‖+2)
  have hB : 1 ≤ B := by dsimp [B]; nlinarith [norm_nonneg s]
  let N := ⌈B⌉₊
  have hBN : B ≤ (N:ℝ) := Nat.le_ceil B
  have hN : 1 ≤ N := by exact_mod_cast (hB.trans hBN)
  have hN2 : (N:ℝ) ≤ 2*B := by
    have := Nat.ceil_lt_add_one (zero_lt_one.trans_le hB).le
    change (N:ℝ) < B+1 at this
    linarith
  have hcut := regularSeries_norm_cutoff hf0 hf hc hD hb hε hε1 hN hs
    (show D*(1+‖s‖) ≤ (N:ℝ) from (by dsimp [B] at hBN; nlinarith [norm_nonneg s]))
  calc
    _ ≤ K₀*(N:ℝ)^(2*ε) := hcut
    _ ≤ K₀*(2*B)^(2*ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow N.cast_nonneg hN2 (by positivity)) hK₀.le
    _ = _ := by rw [Real.mul_rpow (by norm_num) (by linarith : 0 ≤ B)]; ring

def positiveCoefficients (f : ℕ → ℂ) (n : ℕ) : ℂ := if n = 0 then 0 else f n

lemma positiveCoefficients_zero (f : ℕ → ℂ) : positiveCoefficients f 0 = 0 := by simp [positiveCoefficients]

lemma positiveCoefficients_norm_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (n : ℕ) :
    ‖positiveCoefficients f n‖ ≤ 1 := by
  by_cases hn : n=0 <;> simp [positiveCoefficients,hn,hf]

lemma sum_positiveCoefficients (f : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, positiveCoefficients f n = ∑ n ∈ Icc 1 N, f n := by
  apply sum_congr rfl
  intro n hn
  simp [positiveCoefficients,show n ≠ 0 from Nat.ne_of_gt (mem_Icc.mp hn).1]

lemma LSeries_positiveCoefficients (f : ℕ → ℂ) (s : ℂ) :
    LSeries (positiveCoefficients f) s = LSeries f s := by
  apply LSeries_congr
  intro n hn
  simp [positiveCoefficients,hn]

lemma discrepancy_character_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (t : ℝ) :
    ‖seriesDiscrepancy (positiveCoefficients (fun n => χ (n : ZMod q))) 0 t‖ ≤ q+1 := by
  simpa [seriesDiscrepancy,sum_positiveCoefficients] using char_sum_Icc_norm_le hχ ⌊t⌋₊

lemma discrepancy_constant_bound {t : ℝ} (ht : 1 ≤ t) :
    ‖seriesDiscrepancy (positiveCoefficients (fun _ => 1)) 1 t‖ ≤ 1 := by
  simp only [seriesDiscrepancy,sum_positiveCoefficients,Finset.sum_const,nsmul_eq_mul,
    mul_one,Nat.card_Icc,Nat.add_sub_cancel,one_mul]
  rw [←Complex.ofReal_natCast,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have ht0 := (show (0:ℝ) ≤ t by linarith)
  rw [abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le ht0))]
  have := Nat.lt_floor_add_one t
  linarith

lemma regularSeries_character_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) 0 s = χ.LFunction s := by
  let f := positiveCoefficients (fun n => χ (n : ZMod q))
  have hfrac : AnalyticOnNhd ℂ (regularSeries f 0) {s : ℂ | 0 < s.re} := by
    apply DifferentiableOn.analyticOnNhd ?_ (show IsOpen {z : ℂ | 0 < z.re} from isOpen_lt continuous_const Complex.continuous_re)
    intro s hs
    exact (regularSeries_differentiableAt (by positivity : (0:ℝ) ≤ q+1)
      (fun t _ => discrepancy_character_bound hχ t) hs).differentiableWithinAt
  have hL : AnalyticOnNhd ℂ χ.LFunction {s : ℂ | 0 < s.re} :=
    fun s _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
  have he : regularSeries f 0 =ᶠ[𝓝 (2:ℂ)] χ.LFunction := by
    filter_upwards [(continuous_re.tendsto (2:ℂ)).eventually (lt_mem_nhds (by norm_num : (1:ℝ) < (2:ℂ).re))] with z hz
    rw [regularSeries_eq_LSeries_sub (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
      (by positivity : (0:ℝ) ≤ q+1) (fun t _ => discrepancy_character_bound hχ t) hz]
    simp only [zero_div,sub_zero]
    rw [LSeries_positiveCoefficients,DirichletCharacter.LFunction_eq_LSeries χ hz]
  exact hfrac.eqOn_of_preconnected_of_eventuallyEq hL (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ {s:ℂ | 0<s.re} by norm_num) he hs

lemma LFunction_norm_small_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 1-ε ≤ s.re →
      ‖χ.LFunction s‖ ≤ K*((q+2)*(‖s‖+2))^(2*ε) := by
  obtain ⟨K,hK,h⟩ := regularSeries_norm_small_power hε hε1
  refine ⟨K,hK,fun q _ χ hχ s hs => ?_⟩
  have he := h _ 0 (q+1) (positiveCoefficients_zero _) (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by simp) (by positivity) (fun t _ => discrepancy_character_bound hχ t) s hs
  rw [regularSeries_character_eq hχ (by linarith)] at he
  convert he using 1
  congr 3
  ring

lemma regularSeries_deriv_norm_small_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℕ → ℂ) (c : ℂ) (D : ℝ),
      f 0 = 0 → (∀ n, ‖f n‖ ≤ 1) → ‖c‖ ≤ 1 → 0 ≤ D →
      (∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D) →
      ∀ s : ℂ, 1-ε/2 ≤ s.re →
      ‖deriv (regularSeries f c) s‖ ≤ K*((D+1)*(‖s‖+2))^(2*ε) := by
  obtain ⟨K,hK,h⟩ := regularSeries_norm_small_power hε hε1
  refine ⟨K*2^(2*ε)/(ε/2),by positivity,?_⟩
  intro f c D hf0 hf hc hD hb s hs
  have hε2 : 0 < ε/2 := by positivity
  have hre (z:ℂ) (hz : dist z s ≤ ε/2) : 1-ε ≤ z.re := by
    have hd := Complex.re_le_norm (s-z)
    rw [Complex.sub_re,←dist_eq_norm,dist_comm] at hd
    linarith
  have hd : DiffContOnCl ℂ (regularSeries f c) (Metric.ball s (ε/2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hε2.ne']
    intro z hz
    exact (regularSeries_differentiableAt hD (fun t ht => hb t ht.le) (by
      have := hre z (Metric.mem_closedBall.mp hz)
      linarith)).differentiableWithinAt
  have hbnd (z:ℂ) (hz : z ∈ Metric.sphere s (ε/2)) :
      ‖regularSeries f c z‖ ≤ K*2^(2*ε)*((D+1)*(‖s‖+2))^(2*ε) := by
    have hdist := Metric.mem_sphere.mp hz
    have hzR := hre z hdist.le
    have hnorm : ‖z‖+2 ≤ 2*(‖s‖+2) := by
      have : ‖z‖ ≤ dist z s + ‖s‖ := by simpa [dist_eq_norm] using norm_add_le (z-s) s
      rw [hdist] at this
      nlinarith [norm_nonneg s]
    calc
      _ ≤ K*((D+1)*(‖z‖+2))^(2*ε) := h f c D hf0 hf hc hD hb z hzR
      _ ≤ K*(2*((D+1)*(‖s‖+2)))^(2*ε) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)) hK.le
      _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity)]; ring
  have hder := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hε2 hd hbnd
  convert hder using 1
  ring

end LargePrimeGaps
end OAI

-- Source module: TaylorBounds
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
open Complex Filter Topology
open Complex Filter Topology Set MeasureTheory Asymptotics
open Finset
open Complex Filter Topology Finset
lemma power_series_tail_bound {a : ℕ → ℝ} {M r z : ℝ} (_hM : 0 ≤ M)
    (hr : 0 < r) (hz : 0 ≤ z) (hzr : z < r)
    (hb : ∀ n, |a n| ≤ M/r^n) (N : ℕ) :
    |∑' n : ℕ, a (n+N)*z^(n+N)| ≤ M*(z/r)^N/(1-z/r) := by
  have hρ : 0 ≤ z/r := div_nonneg hz hr.le
  have hρ1 : z/r < 1 := (div_lt_one hr).mpr hzr
  have hg := (summable_geometric_of_lt_one hρ hρ1).mul_left (M*(z/r)^N)
  have hbound (n : ℕ) : ‖a (n+N)*z^(n+N)‖ ≤ (M*(z/r)^N)*(z/r)^n := by
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg hz _)]
    calc
      _ ≤ (M/r^(n+N))*z^(n+N) := mul_le_mul_of_nonneg_right (hb _) (pow_nonneg hz _)
      _ = M*(z/r)^(n+N) := by rw [div_pow]; ring
      _ = _ := by rw [pow_add]; ring
  have hn := hg.of_nonneg_of_le (fun n => norm_nonneg _) hbound
  calc
    _ = ‖∑' n : ℕ, a (n+N)*z^(n+N)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℕ, ‖a (n+N)*z^(n+N)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n : ℕ, (M*(z/r)^N)*(z/r)^n := hn.tsum_le_tsum hbound hg
    _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one hρ hρ1]; rfl

lemma residue_lower_bound_of_taylor {a : ℕ → ℝ} {R M r z : ℝ} {N : ℕ}
    (hM : 0 ≤ M) (hr : 0 < r) (hz : 1 < z) (hzr : z < r)
    (hb : ∀ n, |a n| ≤ M/r^n) (ha0 : 1-R ≤ a 0)
    (ha : ∀ n, -R ≤ a n) (hN : 1 ≤ N)
    (hvalue : (∑' n : ℕ, a n*z^n) ≤ R/(z-1))
    (htail : M*(z/r)^N/(1-z/r) ≤ 1/2) :
    (z-1)/2 ≤ R*z^N := by
  have heach : ∀ n, (if n=0 then 1 else (0:ℝ)) - R*z^n ≤ a n*z^n := by
    intro n
    by_cases hn : n=0
    · simpa [hn] using ha0
    · simp only [hn,↓reduceIte,zero_sub]
      nlinarith [mul_le_mul_of_nonneg_right (ha n) (pow_nonneg (zero_lt_one.trans hz).le n)]
  have hsum := Finset.sum_le_sum (s := range N) (fun n _ => heach n)
  have hzero : (∑ n ∈ range N, if n=0 then 1 else (0:ℝ)) = 1 := by
    simp [show 0 < N by omega]
  rw [sum_sub_distrib,hzero,←mul_sum] at hsum
  have htail' := power_series_tail_bound hM hr (zero_lt_one.trans hz).le hzr hb N
  have ht : -(1/2:ℝ) ≤ ∑' n : ℕ, a (n+N)*z^(n+N) := by
    have := (abs_le.mp (htail'.trans htail)).1
    linarith
  have hs : Summable (fun n : ℕ => a n*z^n) := by
    have hρ : 0 ≤ z/r := by positivity
    have hρ1 : z/r < 1 := (div_lt_one hr).mpr hzr
    apply ((summable_geometric_of_lt_one hρ hρ1).mul_left M).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg (zero_lt_one.trans hz).le _)]
    calc
      _ ≤ (M/r^n)*z^n := mul_le_mul_of_nonneg_right (hb _) (pow_nonneg (zero_lt_one.trans hz).le _)
      _ = M*(z/r)^n := by rw [div_mul_eq_mul_div,div_pow]; ring
  have hdecomp := hs.sum_add_tsum_nat_add N
  have hm : 1/2 ≤ R/(z-1)+R*(∑ n ∈ range N, z^n) := by linarith
  have hgeom := geom_sum_mul z N
  have hv := (le_div_iff₀ (sub_pos.mpr hz)).mp
    (show (1/2:ℝ) ≤ (R+R*(∑ n ∈ range N, z^n)*(z-1))/(z-1) from by
      rw [add_div,mul_div_cancel_right₀ _ (sub_pos.mpr hz).ne']
      exact hm)
  have hid : R+R*(∑ n ∈ range N, z^n)*(z-1) = R*z^N := by
    rw [mul_assoc R, hgeom]
    ring
  rw [hid] at hv
  linarith

noncomputable def signedTaylorCoeff (H : ℂ → ℂ) (n : ℕ) : ℝ :=
  (((-1:ℂ)^n)*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2).re

lemma signedTaylorCoeff_hasSum {H : ℂ → ℂ} {r z : ℝ}
    (hf : DifferentiableOn ℂ H (Metric.ball 2 r)) (hz : |z| < r) :
    HasSum (fun n => signedTaylorCoeff H n*z^n) (H ((2-z:ℝ):ℂ)).re := by
  have hmem : ((2-z:ℝ):ℂ) ∈ Metric.ball (2:ℂ) r := by
    rw [Metric.mem_ball,dist_eq_norm]
    have he : ((2-z:ℝ):ℂ)-(2:ℂ) = -(z:ℂ) := by push_cast; ring
    simpa [he,Complex.norm_real,Real.norm_eq_abs] using hz
  have hs := (Complex.hasSum_taylorSeries_on_ball hf hmem).map Complex.reCLM Complex.continuous_re
  change HasSum (fun n => ((n.factorial:ℂ)⁻¹ *
    ((((2-z:ℝ):ℂ)-2)^n * iteratedDeriv n H 2)).re) (H ((2-z:ℝ):ℂ)).re at hs
  convert hs using 1
  funext n
  dsimp [signedTaylorCoeff]
  have he : ((2-z:ℝ):ℂ)-(2:ℂ) = -(z:ℂ) := by push_cast; ring
  rw [he, show (-(z:ℂ))^n = (-1:ℂ)^n * (z:ℂ)^n by rw [←mul_pow]; congr 1; ring]
  have hmul : (n.factorial:ℂ)⁻¹*((-1:ℂ)^n*(z:ℂ)^n*iteratedDeriv n H 2) =
      ((-1:ℂ)^n*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2)*(z:ℂ)^n := by ring
  rw [hmul]
  simp only [←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero]

lemma signedTaylorCoeff_norm_bound {H : ℂ → ℂ} {r M : ℝ} (hr : 0 < r)
    (hf : DiffContOnCl ℂ H (Metric.ball 2 r))
    (hb : ∀ s ∈ Metric.sphere 2 r, ‖H s‖ ≤ M) (n : ℕ) :
    |signedTaylorCoeff H n| ≤ M/r^n := by
  have hder := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hf hb
  have hfact : (n.factorial:ℝ) ≠ 0 := by positivity
  calc
    _ ≤ ‖(-1:ℂ)^n*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2‖ := Complex.abs_re_le_norm _
    _ = (n.factorial:ℝ)⁻¹*‖iteratedDeriv n H 2‖ := by simp [norm_pow]
    _ ≤ (n.factorial:ℝ)⁻¹*((n.factorial:ℝ)*M/r^n) := by gcongr
    _ = _ := by field_simp

lemma signedTaylorCoeff_pole (R : ℝ) (n : ℕ) :
    signedTaylorCoeff (fun s : ℂ => (R:ℂ)/(s-1)) n = R := by
  unfold signedTaylorCoeff
  simp only [div_eq_mul_inv,iteratedDeriv_const_mul_field]
  have hi : iteratedDeriv n (fun s : ℂ => (s-1)⁻¹) 2 = (-1:ℂ)^n*n.factorial := by
    rw [iteratedDeriv_eq_iterate]
    simpa only [one_mul,one_pow, show (2:ℂ)-1=1 by norm_num, one_zpow,mul_one] using
      congrFun (iter_deriv_inv_linear_sub n (1:ℂ) 1) 2
  rw [hi]
  have hf : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hp : (-1:ℂ)^n*(-1:ℂ)^n = 1 := by rw [←mul_pow]; simp
  have he : (-1:ℂ)^n*(n.factorial:ℂ)⁻¹*((R:ℂ)*((-1:ℂ)^n*n.factorial)) = R := by
    calc
      _ = ((-1:ℂ)^n*(-1:ℂ)^n)*(R:ℂ)*((n.factorial:ℂ)⁻¹*n.factorial) := by ring
      _ = _ := by rw [hp,inv_mul_cancel₀ hf]; ring
  rw [he,Complex.ofReal_re]

lemma signedTaylorCoeff_sub {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 2)
    (hG : AnalyticAt ℂ G 2) (n : ℕ) :
    signedTaylorCoeff (fun s => F s-G s) n = signedTaylorCoeff F n-signedTaylorCoeff G n := by
  unfold signedTaylorCoeff
  have hd := iteratedDeriv_sub (n:=n) hF.contDiffAt hG.contDiffAt
  change iteratedDeriv n (fun s => F s-G s) 2 = _ at hd
  rw [hd,mul_sub,Complex.sub_re]

open scoped ComplexOrder in
lemma signedTaylorCoeff_LSeries_nonneg {a : ℕ → ℂ} (ha : ∀ n, 0 ≤ a n)
    (hc : LSeries.abscissaOfAbsConv a < (2:ℝ)) (n : ℕ) :
    0 ≤ signedTaylorCoeff (LSeries a) n := by
  have h := LSeries.iteratedDeriv_alternating ha hc n
  have hf : (0:ℝ) ≤ (n.factorial:ℝ)⁻¹ := by positivity
  have hr := (Complex.nonneg_iff.mp h).1
  unfold signedTaylorCoeff
  have he : (-1:ℂ)^n*(n.factorial:ℂ)⁻¹*iteratedDeriv n (LSeries a) 2 =
      (n.factorial:ℂ)⁻¹*((-1:ℂ)^n*iteratedDeriv n (LSeries a) 2) := by ring
  rw [he]
  simpa using mul_nonneg hf hr

open scoped ComplexOrder in
lemma LSeries_two_re_ge_one {a : ℕ → ℂ} (ha : ∀ n, 0 ≤ a n)
    (ha1 : 1 ≤ a 1) (hc : LSeries.abscissaOfAbsConv a < (2:ℝ)) :
    1 ≤ (LSeries a 2).re := by
  have hs : LSeriesSummable a 2 := LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hc)
  have hl := hs.le_tsum 1 (fun n _ => LSeries.term_nonneg (ha n) 2)
  have hterm : LSeries.term a 2 1 = a 1 := by simp
  rw [hterm] at hl
  exact (Complex.le_def.mp (ha1.trans hl)).1

open scoped ComplexOrder in
set_option maxHeartbeats 800000 in
lemma signedTaylorCoeff_regular_nonneg {H : ℂ → ℂ} {a : ℕ → ℂ} {R : ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha1 : 1 ≤ a 1)
    (hc : LSeries.abscissaOfAbsConv a < (2:ℝ))
    (he : H =ᶠ[𝓝 (2:ℂ)] fun s => LSeries a s-(R:ℂ)/(s-1)) :
    1-R ≤ (H 2).re ∧ ∀ n, -R ≤ signedTaylorCoeff H n := by
  have hL : AnalyticAt ℂ (LSeries a) 2 := LSeries_analyticOnNhd a 2 (by simpa using hc)
  have hP : AnalyticAt ℂ (fun s : ℂ => (R:ℂ)/(s-1)) 2 :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (by norm_num)
  constructor
  · rw [he.self_of_nhds]
    have h := LSeries_two_re_ge_one ha ha1 hc
    simp only [show (2:ℂ)-1=1 by norm_num,div_one,Complex.sub_re,Complex.ofReal_re]
    linarith
  · intro n
    unfold signedTaylorCoeff
    rw [he.iteratedDeriv_eq]
    change -R ≤ signedTaylorCoeff (fun s => LSeries a s-(R:ℂ)/(s-1)) n
    rw [signedTaylorCoeff_sub hL hP,signedTaylorCoeff_pole]
    linarith [signedTaylorCoeff_LSeries_nonneg ha hc n]

lemma residue_polynomial_lower {a : ℕ → ℝ} {R A Q z ε : ℝ}
    (hA : 0 ≤ A) (hQ : 2 ≤ Q) (hQA : 12*A ≤ Q)
    (hz : 1 < z) (hz1 : z ≤ 5/4) (hzε : 60*(z-1) ≤ ε)
    (hb : ∀ n, |a n| ≤ (A*Q^4)/(3/2)^n)
    (ha0 : 1-R ≤ a 0) (ha : ∀ n, -R ≤ a n)
    (hv : (∑' n : ℕ, a n*z^n) ≤ R/(z-1)) :
    ((z-1)/(2*z))*Q^(-ε) ≤ R := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hz0 : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hz
  let N : ℕ := ⌈60*Real.log Q⌉₊
  have hNlo : 60*Real.log Q ≤ (N:ℝ) := Nat.le_ceil _
  have hNhi : (N:ℝ) < 60*Real.log Q+1 := Nat.ceil_lt_add_one (by positivity)
  have hN : 1 ≤ N := by
    have : 0 < (N:ℝ) := lt_of_lt_of_le (by positivity) hNlo
    exact_mod_cast (show 1 ≤ N from Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast this.ne'))
  have hρ : 0 ≤ z/(3/2) := by positivity
  have hρ1 : z/(3/2) ≤ 5/6 := by linarith
  have hlogρ : Real.log (5/6:ℝ) ≤ -(1/6:ℝ) := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 5/6)
    linarith
  have hdecay : (z/(3/2))^N ≤ Q^(-10:ℝ) := by
    calc
      _ ≤ (5/6:ℝ)^N := pow_le_pow_left₀ hρ hρ1 N
      _ = Real.exp (Real.log (5/6:ℝ)*(N:ℝ)) := by
        rw [←Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 5/6)]
      _ ≤ Real.exp (Real.log Q*(-10)) := by
        apply Real.exp_le_exp.mpr
        have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
        nlinarith [mul_le_mul_of_nonneg_right hlogρ hN0]
      _ = _ := (Real.rpow_def_of_pos hQ0 _).symm
  have htail : (A*Q^4)*(z/(3/2))^N/(1-z/(3/2)) ≤ 1/2 := by
    have hden : 0 < 1-z/(3/2) := by linarith
    have hpow : Q^4*Q^(-10:ℝ) ≤ Q⁻¹ := by
      calc
        _ = Q^(-6:ℝ) := by
          rw [←Real.rpow_natCast,←Real.rpow_add hQ0]
          norm_num
        _ ≤ Q^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
        _ = Q⁻¹ := Real.rpow_neg_one Q
    have hp : (A*Q^4)*(z/(3/2))^N ≤ A/Q := by
      calc
        _ ≤ (A*Q^4)*Q^(-10:ℝ) := mul_le_mul_of_nonneg_left hdecay (by positivity)
        _ ≤ A*Q⁻¹ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hpow hA
        _ = _ := by rw [div_eq_mul_inv]
    have hAQ : A/Q ≤ 1/12 := (div_le_iff₀ hQ0).mpr (by linarith)
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hres := residue_lower_bound_of_taylor (by positivity : (0:ℝ) ≤ A*Q^4)
    (by norm_num : (0:ℝ) < 3/2) hz (by linarith : z < 3/2) hb ha0 ha hN hv htail
  have hzpow : z^N ≤ z*Q^ε := by
    have hlogz' : 60*Real.log z ≤ ε := by
      have := Real.log_le_sub_one_of_pos hz0
      linarith
    calc
      _ = Real.exp (Real.log z*(N:ℝ)) := by rw [←Real.rpow_natCast,Real.rpow_def_of_pos hz0]
      _ ≤ Real.exp (Real.log z+(Real.log Q)*ε) := by
        apply Real.exp_le_exp.mpr
        have h1 := mul_le_mul_of_nonneg_left hNhi.le hlogz.le
        have h2 := mul_le_mul_of_nonneg_left hlogz' hlogQ.le
        nlinarith
      _ = _ := by rw [Real.exp_add,Real.exp_log hz0,Real.rpow_def_of_pos hQ0]
  have hR : 0 ≤ R := by
    by_contra! h
    have := mul_neg_of_neg_of_pos h (pow_pos hz0 N)
    linarith
  have hres' : (z-1)/2 ≤ R*(z*Q^ε) := hres.trans (mul_le_mul_of_nonneg_left hzpow hR)
  rw [Real.rpow_neg hQ0.le,←div_eq_mul_inv]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hQ0 ε)).mpr
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*z)).mpr
  nlinarith

open Complex Filter Topology Finset Set MeasureTheory
noncomputable def zetaRegular : ℂ → ℂ :=
  regularSeries (positiveCoefficients (fun _ => 1)) 1

lemma zetaRegular_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ zetaRegular s :=
  regularSeries_differentiableAt zero_le_one (fun _ ht => discrepancy_constant_bound ht.le) hs

lemma zetaRegular_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    zetaRegular s = riemannZeta s-1/(s-1) := by
  rw [zetaRegular,regularSeries_eq_LSeries_sub (positiveCoefficients_norm_le (by simp))
    zero_le_one (fun _ ht => discrepancy_constant_bound ht.le) hs,LSeries_positiveCoefficients]
  rw [show (fun _ : ℕ => (1:ℂ)) = 1 from rfl,LSeries_one_eq_riemannZeta hs]

lemma poleRemovedZeta_eq {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunctionTrivChar₁ 1 s = (s-1)*zetaRegular s+1 := by
  have hF : AnalyticOnNhd ℂ (DirichletCharacter.LFunctionTrivChar₁ 1) {s : ℂ | 0 < s.re} :=
    fun z _ => (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).analyticAt z
  have hG : AnalyticOnNhd ℂ (fun s : ℂ => (s-1)*zetaRegular s+1) {s : ℂ | 0 < s.re} := by
    apply DifferentiableOn.analyticOnNhd ?_ (show IsOpen {z : ℂ | 0 < z.re} from isOpen_lt continuous_const Complex.continuous_re)
    intro z hz
    exact (((differentiableAt_id.sub_const 1).mul (zetaRegular_differentiableAt hz)).add_const 1).differentiableWithinAt
  have he : DirichletCharacter.LFunctionTrivChar₁ 1 =ᶠ[𝓝 (2:ℂ)]
      fun s : ℂ => (s-1)*zetaRegular s+1 := by
    filter_upwards [(continuous_re.tendsto (2:ℂ)).eventually
      (lt_mem_nhds (by norm_num : (1:ℝ) < (2:ℂ).re))] with z hz
    have hz1 : z ≠ 1 := by intro h; simp [h] at hz
    rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hz1,
      DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq,
      zetaRegular_eq_of_one_lt_re hz]
    field_simp
    ring
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ {s : ℂ | 0 < s.re} by norm_num) he hs

lemma zetaRegular_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    zetaRegular s = riemannZeta s-1/(s-1) := by
  have h := poleRemovedZeta_eq hs
  rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hs1,
    DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq] at h
  have hn : s-1 ≠ 0 := sub_ne_zero.mpr hs1
  apply (mul_left_cancel₀ hn)
  rw [mul_sub,mul_div_cancel₀ _ hn]
  linear_combination -h

lemma regularSeries_norm_simple {f : ℕ → ℂ} {c : ℂ} {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    ‖regularSeries f c s‖ ≤ ‖c‖+‖s‖*D/s.re := by
  have h := discrepancyTail_norm_le zero_lt_one hD (measurable_seriesDiscrepancy f c) hb hs
  simp only [Real.one_rpow,mul_one] at h
  calc
    _ ≤ ‖c‖+‖s*discrepancyTail (seriesDiscrepancy f c) 1 s‖ := norm_add_le _ _
    _ ≤ ‖c‖+‖s‖*(D/s.re) := by rw [norm_mul]; gcongr
    _ = _ := by ring

lemma closedBall_two_re_norm {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    (1/4:ℝ) ≤ s.re ∧ ‖s‖ ≤ 4 := by
  have hd := Metric.mem_closedBall.mp hs
  have hr := Complex.re_le_norm ((2:ℂ)-s)
  rw [Complex.sub_re,←dist_eq_norm,dist_comm] at hr
  have hn : ‖s‖ ≤ dist s 2+‖(2:ℂ)‖ := by simpa [dist_eq_norm] using norm_add_le (s-2) (2:ℂ)
  norm_num at hr hn
  constructor <;> linarith

lemma zetaRegular_norm_le_seventeen {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    ‖zetaRegular s‖ ≤ 17 := by
  obtain ⟨hre,hnorm⟩ := closedBall_two_re_norm hs
  have hp : 0 < s.re := by linarith
  have h := regularSeries_norm_simple zero_le_one (fun _ ht => discrepancy_constant_bound ht.le) hp
  change ‖zetaRegular s‖ ≤ _ at h
  norm_num at h
  have hq : ‖s‖/s.re ≤ 16 := (div_le_iff₀ hp).mpr (by linarith)
  linarith

lemma LFunction_norm_polynomial {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    ‖χ.LFunction s‖ ≤ 16*((q:ℝ)+1) := by
  obtain ⟨hre,hnorm⟩ := closedBall_two_re_norm hs
  have hp : 0 < s.re := by linarith
  have hb := regularSeries_norm_simple (by positivity : (0:ℝ) ≤ q+1)
    (fun t _ => discrepancy_character_bound hχ t) hp
  rw [regularSeries_character_eq hχ hp] at hb
  simp only [norm_zero,zero_add] at hb
  apply hb.trans
  apply (div_le_iff₀ hp).mpr
  nlinarith [Nat.cast_nonneg (α:=ℝ) q]

noncomputable def regularizedZetaProduct (P : ℂ → ℂ) (s : ℂ) : ℂ :=
  zetaRegular s*P s+dslope P 1 s

lemma regularizedZetaProduct_differentiableOn {P : ℂ → ℂ}
    (hP : DifferentiableOn ℂ P {s : ℂ | 0 < s.re}) :
    DifferentiableOn ℂ (regularizedZetaProduct P) {s : ℂ | 0 < s.re} := by
  have hs : {s : ℂ | 0 < s.re} ∈ 𝓝 (1:ℂ) :=
    (show IsOpen {z : ℂ | 0 < z.re} from isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hd := (Complex.differentiableOn_dslope hs).mpr hP
  have hz : DifferentiableOn ℂ zetaRegular {s : ℂ | 0 < s.re} :=
    fun s hs => (zetaRegular_differentiableAt hs).differentiableWithinAt
  exact (hz.mul hP).add hd

lemma regularizedZetaProduct_eq {P : ℂ → ℂ} {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    regularizedZetaProduct P s = riemannZeta s*P s-P 1/(s-1) := by
  rw [regularizedZetaProduct,zetaRegular_eq hs hs1,dslope_of_ne P hs1,slope_def_field]
  ring

lemma regularizedZetaProduct_bound {P : ℂ → ℂ} {B : ℝ}
    (hP : DifferentiableOn ℂ P {s : ℂ | 0 < s.re}) (_hB : 0 ≤ B)
    (hb : ∀ s ∈ Metric.closedBall (2:ℂ) (7/4:ℝ), ‖P s‖ ≤ B) :
    DiffContOnCl ℂ (regularizedZetaProduct P) (Metric.ball 2 (3/2:ℝ)) ∧
      ∀ s ∈ Metric.closedBall (2:ℂ) (3/2:ℝ), ‖regularizedZetaProduct P s‖ ≤ 21*B := by
  have hsRe (s : ℂ) (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) : 0 < s.re := by
    have := (closedBall_two_re_norm hs).1
    linarith
  have hder (s : ℂ) (hs : s ∈ Metric.closedBall 2 (3/2:ℝ)) : ‖deriv P s‖ ≤ 4*B := by
    have hsub : Metric.closedBall s (1/4:ℝ) ⊆ Metric.closedBall (2:ℂ) (7/4:ℝ) := by
      intro z hz
      have hdist := dist_triangle z s (2:ℂ)
      have hz' := Metric.mem_closedBall.mp hz
      have hs' := Metric.mem_closedBall.mp hs
      apply Metric.mem_closedBall.mpr
      linarith
    have hdiff : DiffContOnCl ℂ P (Metric.ball s (1/4:ℝ)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ (by norm_num : (1/4:ℝ) ≠ 0)]
      exact hP.mono (fun z hz => hsRe z (hsub hz))
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ) < 1/4)
      hdiff (fun z hz => hb z (hsub (Metric.sphere_subset_closedBall hz)))
    convert h using 1; ring
  have hone : (1:ℂ) ∈ Metric.closedBall (2:ℂ) (3/2:ℝ) := by
    norm_num [Metric.mem_closedBall,dist_eq_norm]
  have hdslope (s : ℂ) (hs : s ∈ Metric.closedBall 2 (3/2:ℝ)) : ‖dslope P 1 s‖ ≤ 4*B := by
    by_cases hs1 : s = 1
    · subst s
      simpa only [dslope_same] using hder 1 hone
    · rw [dslope_of_ne P hs1,slope_def_field,norm_div]
      have hd := (convex_closedBall (2:ℂ) (3/2:ℝ)).norm_image_sub_le_of_norm_deriv_le
        (fun z hz => (hP z (hsRe z (Metric.closedBall_subset_closedBall (by norm_num) hz))).differentiableAt
          ((show IsOpen {z : ℂ | 0 < z.re} from isOpen_lt continuous_const Complex.continuous_re).mem_nhds
            (hsRe z (Metric.closedBall_subset_closedBall (by norm_num) hz)))) hder hone hs
      exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs1))).mpr hd
  constructor
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by norm_num : (3/2:ℝ) ≠ 0)]
    exact (regularizedZetaProduct_differentiableOn hP).mono
      (fun z hz => hsRe z (Metric.closedBall_subset_closedBall (by norm_num) hz))
  · intro s hs
    have hs' := Metric.closedBall_subset_closedBall (by norm_num : (3/2:ℝ) ≤ 7/4) hs
    calc
      _ ≤ ‖zetaRegular s*P s‖+‖dslope P 1 s‖ := norm_add_le _ _
      _ ≤ 17*B+4*B := by rw [norm_mul]; gcongr; exact zetaRegular_norm_le_seventeen hs'; exact hb s hs'; exact hdslope s hs
      _ = _ := by ring

open Complex Finset ArithmeticFunction
open scoped ComplexOrder
def PrimePowerEq (p : ℕ) (f g : ArithmeticFunction ℂ) : Prop :=
  ∀ k : ℕ, f (p^k) = g (p^k)

lemma PrimePowerEq.refl (p : ℕ) (f : ArithmeticFunction ℂ) : PrimePowerEq p f f := fun _ => rfl

lemma PrimePowerEq.mul {p : ℕ} (hp : p.Prime) {f f' g g' : ArithmeticFunction ℂ}
    (hf : PrimePowerEq p f f') (hg : PrimePowerEq p g g') : PrimePowerEq p (f*g) (f'*g') := by
  intro k
  simp only [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨i,hi,hxi⟩ := (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp
    (Nat.fst_mem_divisors_of_mem_antidiagonal hx)).1
  obtain ⟨j,hj,hxj⟩ := (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp
    (Nat.snd_mem_divisors_of_mem_antidiagonal hx)).1
  rw [hxi,hxj,hf,hg]

lemma primePower_zeta {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (p^k) = 1 := by
  simp [hp.ne_zero]

lemma primePower_one {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (1 : ArithmeticFunction ℂ) (p^k) = (0:ℂ)^k := by
  cases k with
  | zero => simp
  | succ k =>
    have hn : p^(k+1) ≠ 1 := by
      have h : 1 < p^(k+1) := one_lt_pow₀ hp.one_lt (by omega)
      omega
    simp [hp.ne_one]

lemma primePower_character {q p : ℕ} (χ : DirichletCharacter ℂ q) (hp : p.Prime) (k : ℕ) :
    toArithmeticFunction (χ ·) (p^k) = χ (p : ZMod q)^k := by
  simp [toArithmeticFunction,hp.ne_zero]

lemma arithmetic_convolution_nonneg {f g : ArithmeticFunction ℂ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (n : ℕ) : 0 ≤ (f*g) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hf x.1) (hg x.2))

noncomputable def biquadraticCoefficients {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) : ArithmeticFunction ℂ :=
  ArithmeticFunction.zeta * toArithmeticFunction (χ ·) * toArithmeticFunction (ψ ·) *
    (toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·))

lemma biquadraticCoefficients_multiplicative {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    (biquadraticCoefficients χ ψ).IsMultiplicative := by
  exact ((isMultiplicative_zeta.natCast.mul (DirichletCharacter.isMultiplicative_toArithmeticFunction χ)).mul
    (DirichletCharacter.isMultiplicative_toArithmeticFunction ψ)).mul
    ((DirichletCharacter.isMultiplicative_toArithmeticFunction χ).pmul (DirichletCharacter.isMultiplicative_toArithmeticFunction ψ))

lemma biquadraticCoefficients_comm {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    biquadraticCoefficients χ ψ = biquadraticCoefficients ψ χ := by
  unfold biquadraticCoefficients
  rw [ArithmeticFunction.pmul_comm]
  ring

lemma biquadratic_prime_zero {q r p : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hp : p.Prime)
    (hχ : χ (p : ZMod q) = 0) :
    PrimePowerEq p (biquadraticCoefficients χ ψ) ψ.zetaMul := by
  have hf : PrimePowerEq p (toArithmeticFunction (χ ·)) 1 := by
    intro k
    rw [primePower_character χ hp, hχ,primePower_one hp]
  have hh : PrimePowerEq p ((toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·))) 1 := by
    intro k
    rw [ArithmeticFunction.pmul_apply,primePower_character χ hp,primePower_character ψ hp,
      hχ,←mul_pow,zero_mul,primePower_one hp]
  have h := ((PrimePowerEq.refl p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)).mul hp hf).mul hp
    (PrimePowerEq.refl p (toArithmeticFunction (ψ ·))) |>.mul hp hh
  simpa only [mul_one,biquadraticCoefficients,DirichletCharacter.zetaMul] using h

lemma biquadratic_prime_one {q r p : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hp : p.Prime)
    (hχ : χ (p : ZMod q) = 1) :
    PrimePowerEq p (biquadraticCoefficients χ ψ) (ψ.zetaMul*ψ.zetaMul) := by
  have hf : PrimePowerEq p (toArithmeticFunction (χ ·)) ArithmeticFunction.zeta := by
    intro k
    rw [primePower_character χ hp,hχ,one_pow,primePower_zeta hp]
  have hh : PrimePowerEq p ((toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)))
      (toArithmeticFunction (ψ ·)) := by
    intro k
    rw [ArithmeticFunction.pmul_apply,primePower_character χ hp,hχ,one_pow,one_mul]
  have h := ((PrimePowerEq.refl p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)).mul hp hf).mul hp
    (PrimePowerEq.refl p (toArithmeticFunction (ψ ·))) |>.mul hp hh
  have he : (ArithmeticFunction.zeta : ArithmeticFunction ℂ)*ArithmeticFunction.zeta*
      toArithmeticFunction (ψ ·)*toArithmeticFunction (ψ ·) = ψ.zetaMul*ψ.zetaMul := by
    unfold DirichletCharacter.zetaMul
    ring
  simpa only [he,biquadraticCoefficients] using h

lemma biquadratic_prime_neg_one {q r p : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hp : p.Prime)
    (hχ : χ (p : ZMod q) = -1) (hψ : ψ (p : ZMod r) = -1) :
    PrimePowerEq p (biquadraticCoefficients χ ψ) (χ.zetaMul*χ.zetaMul) := by
  have hg : PrimePowerEq p (toArithmeticFunction (ψ ·)) (toArithmeticFunction (χ ·)) := by
    intro k
    rw [primePower_character ψ hp,primePower_character χ hp,hχ,hψ]
  have hh : PrimePowerEq p ((toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)))
      ArithmeticFunction.zeta := by
    intro k
    rw [ArithmeticFunction.pmul_apply,primePower_character χ hp,primePower_character ψ hp,
      hχ,hψ,←mul_pow,neg_mul_neg,one_mul,one_pow,primePower_zeta hp]
  have h := ((PrimePowerEq.refl p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)).mul hp
    (PrimePowerEq.refl p (toArithmeticFunction (χ ·)))).mul hp hg |>.mul hp hh
  have he : (ArithmeticFunction.zeta : ArithmeticFunction ℂ)*toArithmeticFunction (χ ·)*
      toArithmeticFunction (χ ·)*ArithmeticFunction.zeta = χ.zetaMul*χ.zetaMul := by
    unfold DirichletCharacter.zetaMul
    ring
  simpa only [he,biquadraticCoefficients] using h

lemma biquadraticCoefficients_nonneg {q r : ℕ} {χ : DirichletCharacter ℂ q}
    {ψ : DirichletCharacter ℂ r} (hχ : χ^2=1) (hψ : ψ^2=1) (n : ℕ) :
    0 ≤ biquadraticCoefficients χ ψ n := by
  have hp (p : ℕ) (hp : p.Prime) (k : ℕ) : 0 ≤ biquadraticCoefficients χ ψ (p^k) := by
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ (p:ZMod q) with h0|h1|hm
    · rw [biquadratic_prime_zero χ ψ hp h0 k]
      exact DirichletCharacter.zetaMul_nonneg hψ _
    · rw [biquadratic_prime_one χ ψ hp h1 k]
      exact arithmetic_convolution_nonneg (DirichletCharacter.zetaMul_nonneg hψ)
        (DirichletCharacter.zetaMul_nonneg hψ) _
    · rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hψ (p:ZMod r) with h0|h1|hm'
      · rw [biquadraticCoefficients_comm χ ψ,biquadratic_prime_zero ψ χ hp h0 k]
        exact DirichletCharacter.zetaMul_nonneg hχ _
      · rw [biquadraticCoefficients_comm χ ψ,biquadratic_prime_one ψ χ hp h1 k]
        exact arithmetic_convolution_nonneg (DirichletCharacter.zetaMul_nonneg hχ)
          (DirichletCharacter.zetaMul_nonneg hχ) _
      · rw [biquadratic_prime_neg_one χ ψ hp hm hm' k]
        exact arithmetic_convolution_nonneg (DirichletCharacter.zetaMul_nonneg hχ)
          (DirichletCharacter.zetaMul_nonneg hχ) _
  rcases eq_or_ne n 0 with rfl|hn
  · simp
  · simpa only [(biquadraticCoefficients_multiplicative χ ψ).multiplicative_factorization _ hn,
      Finsupp.prod, Nat.support_factorization] using
      Finset.prod_nonneg (fun p hp' => hp p (Nat.prime_of_mem_primeFactors hp') _)

end LargePrimeGaps
end OAI

-- Source module: SiegelBounds
namespace OAI
namespace LargePrimeGaps
section
open Complex Filter Topology Set MeasureTheory Finset ArithmeticFunction
lemma quadratic_character_im {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ^2=1)
    (a : ZMod q) : (χ a).im = 0 := by
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ a with h|h|h <;> simp [h]

lemma regularSeries_im_zero {f : ℕ → ℂ} {c : ℂ} {D : ℝ}
    (hf : ∀ n, (f n).im=0) (hc : c.im=0) (hD : 0 ≤ D)
    (hb : ∀ t, 1<t → ‖seriesDiscrepancy f c t‖ ≤ D) {x : ℝ} (hx : 0<x) :
    (regularSeries f c x).im=0 := by
  have hi := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb
    (show 0<(x:ℂ).re from hx)
  have he : (discrepancyTail (seriesDiscrepancy f c) 1 x).im=0 := by
    unfold discrepancyTail
    change RCLike.im (∫ t in Ioi (1:ℝ), seriesDiscrepancy f c t*(t:ℂ)^(-((x:ℂ)+1)))=0
    rw [←integral_im hi]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp : ((t:ℂ)^(-((x:ℂ)+1))).im=0 := by
      rw [show -((x:ℂ)+1)= (-(x+1):ℝ) by push_cast; rfl,
        ←Complex.ofReal_cpow (by exact (zero_lt_one.trans ht).le : 0≤t)]
      rfl
    change (seriesDiscrepancy f c t * (t:ℂ)^(-((x:ℂ)+1))).im=0
    rw [Complex.mul_im,hp,mul_zero,zero_add]
    have hz : (seriesDiscrepancy f c t).im=0 := by simp [seriesDiscrepancy,Complex.mul_im,hc,hf]
    rw [hz,zero_mul]
  simp [regularSeries,Complex.mul_im,hc,he]

lemma quadratic_LFunction_im {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (hχ2 : χ^2=1) {x : ℝ} (hx : 0<x) : (χ.LFunction x).im=0 := by
  rw [←regularSeries_character_eq hχ hx]
  apply regularSeries_im_zero _ (by simp) (by positivity : (0:ℝ)≤q+1)
    (fun t _ => discrepancy_character_bound hχ t) hx
  intro n
  simp only [positiveCoefficients]
  split_ifs <;> simp [quadratic_character_im hχ2]

lemma LSeries_character_summable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (toArithmeticFunction (fun n : ℕ => χ (n : ZMod q))) s := by
  apply (LSeriesSummable_congr _ (fun h => (χ.apply_eq_toArithmeticFunction_apply h).symm)).mpr
  exact ZMod.LSeriesSummable_of_one_lt_re χ hs

lemma LSeries_character_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    LSeries (toArithmeticFunction (fun n : ℕ => χ (n : ZMod q))) s = χ.LFunction s := by
  rw [χ.LFunction_eq_LSeries hs]
  exact (LSeries_congr χ.apply_eq_toArithmeticFunction_apply s).symm

lemma LSeries_zeta_complex_eq {s : ℂ} (hs : 1<s.re) :
    LSeries (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s=riemannZeta s := by
  rw [←LSeries_one_eq_riemannZeta hs]
  apply LSeries_congr
  intro n hn
  simp [hn]

lemma LSeries_zetaMul_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) : LSeries χ.zetaMul s=riemannZeta s*χ.LFunction s := by
  have hz : LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m:=1) _ hs
    intro n hn
    simp [hn]
  rw [DirichletCharacter.zetaMul,ArithmeticFunction.LSeries_mul' hz
    (LSeries_character_summable χ hs),LSeries_character_eq χ hs,LSeries_zeta_complex_eq hs]

open scoped ComplexOrder in
lemma quadratic_LFunction_re_pos_of_one_lt {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ2 : χ^2=1) {x : ℝ} (hx : 1<x) :
    0<(χ.LFunction x).re := by
  have hp := LSeries.positive (DirichletCharacter.zetaMul_nonneg hχ2)
    (χ.isMultiplicative_zetaMul.map_one ▸ zero_lt_one)
    (lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun s hs => χ.LSeriesSummable_zetaMul hs)) (show (1:EReal)<x by exact_mod_cast hx))
  rw [LSeries_zetaMul_eq χ hx] at hp
  have hr := (Complex.pos_iff.mp hp).1
  rw [Complex.mul_re,riemannZeta_im_eq_zero_of_one_lt hx,zero_mul,sub_zero] at hr
  exact (mul_pos_iff.mp hr).resolve_right (fun h => (riemannZeta_re_pos_of_one_lt hx).not_ge h.1.le) |>.2

lemma quadratic_LFunction_re_pos_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (hχ2 : χ^2=1) : 0<(χ.LFunction 1).re := by
  have hc : Continuous (fun x : ℝ => (χ.LFunction x).re) :=
    Complex.continuous_re.comp ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal)
  have hn : 0≤(χ.LFunction 1).re := by
    apply ge_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto (fun x : ℝ => (χ.LFunction x).re) (𝓝[>] 1) (𝓝 ((χ.LFunction 1).re)))
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (quadratic_LFunction_re_pos_of_one_lt hχ2 hx).le
  refine lt_of_le_of_ne hn ?_
  intro he
  apply DirichletCharacter.LFunction_apply_one_ne_zero hχ
  apply Complex.ext
  · simpa using he.symm
  · simpa using quadratic_LFunction_im hχ hχ2 (x:=1) zero_lt_one

lemma quadratic_LFunction_re_pos_of_no_root {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ≠1) (hχ2 : χ^2=1)
    {β : ℝ} (hβ : 0<β) (hβ1 : β≤1)
    (hz : ∀ x ∈ Set.Icc β 1, χ.LFunction x≠0) : 0<(χ.LFunction β).re := by
  by_contra! hn
  have hc : Continuous (fun x : ℝ => (χ.LFunction x).re) :=
    Complex.continuous_re.comp ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal)
  obtain ⟨x,hx,hxe⟩ := intermediate_value_Icc hβ1 hc.continuousOn
    (show (0:ℝ) ∈ Set.Icc ((χ.LFunction β).re) ((χ.LFunction 1).re) from
      ⟨hn,(quadratic_LFunction_re_pos_one hχ hχ2).le⟩)
  apply hz x hx
  apply Complex.ext
  · simpa using hxe
  · simpa using quadratic_LFunction_im hχ hχ2 (hβ.trans_le hx.1)

end
section
open Complex Finset ArithmeticFunction
noncomputable def productCharacter {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : DirichletCharacter ℂ (q*r) :=
  χ.changeLevel (dvd_mul_right q r) * ψ.changeLevel (dvd_mul_left r q)

lemma changeLevel_natCast {q m : ℕ} (χ : DirichletCharacter ℂ q) (hqm : q∣m)
    {n : ℕ} (hn : n.Coprime m) :
    χ.changeLevel hqm (n : ZMod m)=χ (n : ZMod q) := by
  have h := χ.changeLevel_eq_cast_of_dvd hqm (ZMod.unitOfCoprime n hn)
  simp only [ZMod.coe_unitOfCoprime] at h
  rw [ZMod.cast_natCast hqm] at h
  exact h

lemma productCharacter_apply {q r n : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : productCharacter χ ψ (n : ZMod (q*r))=
      χ (n : ZMod q)*ψ (n : ZMod r) := by
  by_cases hn : n.Coprime (q*r)
  · simp only [productCharacter,MulChar.mul_apply,changeLevel_natCast _ _ hn]
  · rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]
    by_cases hq : n.Coprime q
    · have hr : ¬n.Coprime r := fun hr => hn (hq.mul_right hr)
      rw [ψ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime]),mul_zero]
    · rw [χ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime]),zero_mul]

lemma productCharacter_quadratic {q r : ℕ} {χ : DirichletCharacter ℂ q}
    {ψ : DirichletCharacter ℂ r} (hχ : χ^2=1) (hψ : ψ^2=1) :
    (productCharacter χ ψ)^2=1 := by
  simp [productCharacter,mul_pow,←map_pow,hχ,hψ]

lemma productCharacter_ne_one_of_levels_ne {q r : ℕ} [NeZero q] [NeZero r]
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hψ2 : ψ^2=1) (hqr : q≠r) :
    productCharacter χ ψ≠1 := by
  intro h
  have h2 : (ψ.changeLevel (dvd_mul_left r q))^2=1 := by rw [←map_pow,hψ2,map_one]
  have he : χ.changeLevel (dvd_mul_right q r) = ψ.changeLevel (dvd_mul_left r q) := by
    calc
      _ = (χ.changeLevel (dvd_mul_right q r)*ψ.changeLevel (dvd_mul_left r q))*
          ψ.changeLevel (dvd_mul_left r q) := by rw [mul_assoc,←pow_two,h2,mul_one]
      _ = _ := by rw [show χ.changeLevel (dvd_mul_right q r)*ψ.changeLevel (dvd_mul_left r q)=1 from h,one_mul]
  have hc := congrArg DirichletCharacter.conductor he
  rw [DirichletCharacter.conductor_changeLevel,DirichletCharacter.conductor_changeLevel,
    hχ,hψ] at hc
  exact hqr hc

lemma productCharacter_toArithmeticFunction {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) :
    toArithmeticFunction (productCharacter χ ψ ·)=
      (toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)) := by
  ext n
  by_cases hn : n=0
  · simp [hn]
  · rw [ArithmeticFunction.pmul_apply]
    simp [toArithmeticFunction,hn,productCharacter_apply]

end
section
open Complex Filter Topology Set MeasureTheory Finset
open scoped ComplexOrder in
lemma zeta_product_residue_lower {P : ℂ → ℂ} {a : ℕ → ℂ} {A B Q β ε : ℝ}
    (hP : DifferentiableOn ℂ P {s : ℂ | 0<s.re})
    (hB : 0≤B) (hb : ∀ s ∈ Metric.closedBall (2:ℂ) (7/4:ℝ), ‖P s‖≤B)
    (hA : 0≤A) (hQ : 2≤Q) (hQA : 12*A≤Q) (hBQ : 21*B≤A*Q^4)
    (hβ : 3/4≤β) (hβ1 : β<1) (hβε : 60*(1-β)≤ε)
    (ha : ∀ n, 0≤a n) (ha1 : 1≤a 1) (haC : LSeries.abscissaOfAbsConv a≤1)
    (haP : ∀ s : ℂ, 1<s.re → LSeries a s=riemannZeta s*P s)
    (hvalue : (riemannZeta β*P β).re≤0) (hreal : (P 1).im=0) :
    ((1-β)/(2*(2-β)))*Q^(-ε)≤(P 1).re := by
  let H := regularizedZetaProduct P
  have hR : P 1=((P 1).re:ℂ) := by apply Complex.ext <;> simp [hreal]
  obtain ⟨hf,hbound⟩ := regularizedZetaProduct_bound hP hB hb
  have he : H =ᶠ[𝓝 (2:ℂ)] fun s => LSeries a s-((P 1).re:ℂ)/(s-1) := by
    filter_upwards [(continuous_re.tendsto (2:ℂ)).eventually
      (lt_mem_nhds (by norm_num : (1:ℝ)<(2:ℂ).re))] with s hs
    have hs1 : s≠1 := by intro h; simp [h] at hs
    rw [show H s=regularizedZetaProduct P s from rfl,regularizedZetaProduct_eq (by linarith) hs1,
      ←haP s hs,hR]
    simp only [Complex.ofReal_re]
  have hac : LSeries.abscissaOfAbsConv a<(2:ℝ) := haC.trans_lt (by exact_mod_cast (show (1:ℝ)<2 by norm_num))
  obtain ⟨ha0,han⟩ := signedTaylorCoeff_regular_nonneg ha ha1 hac he
  have hz : 1<2-β := by linarith
  have hz0 : 0<2-β := by linarith
  have hzr : 2-β<(3/2:ℝ) := by linarith
  have hv : (∑' n : ℕ, signedTaylorCoeff H n*(2-β)^n)≤(P 1).re/((2-β)-1) := by
    rw [(signedTaylorCoeff_hasSum hf.differentiableOn (by rwa [abs_of_pos hz0])).tsum_eq]
    have hβ0 : 0<β := by linarith
    have hβne : (β:ℂ)≠1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [show (2-(2-β):ℝ)=β by ring]
    change (regularizedZetaProduct P β).re≤_
    rw [regularizedZetaProduct_eq hβ0 hβne,Complex.sub_re,hR,
      ←Complex.ofReal_one,←Complex.ofReal_sub,←Complex.ofReal_div,Complex.ofReal_re]
    have hid : (P 1).re/(β-1) = -(P 1).re/((2-β)-1) := by
      rw [show β-1 = -((2-β)-1) by ring,div_neg,neg_div]
    simp only [Complex.ofReal_one,Complex.ofReal_re]
    rw [hid,neg_div,sub_neg_eq_add]
    exact add_le_of_nonpos_left hvalue
  have hn (n : ℕ) : |signedTaylorCoeff H n|≤(A*Q^4)/(3/2)^n := by
    apply (signedTaylorCoeff_norm_bound (by norm_num : (0:ℝ)<3/2) hf
      (fun s hs => (hbound s (Metric.sphere_subset_closedBall hs)).trans hBQ) n)
  have hr := residue_polynomial_lower (ε:=ε) hA hQ hQA hz (by linarith) (by linarith) hn
    (by simpa [signedTaylorCoeff] using ha0) han hv
  convert hr using 1
  congr 2
  ring

lemma zeta_re_neg_near_one {β : ℝ} (hβ : 99/100≤β) (hβ1 : β<1) :
    (riemannZeta β).re<0 := by
  have hβ0 : 0<β := by linarith
  have hβne : (β:ℂ)≠1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hmem : (β:ℂ) ∈ Metric.closedBall 2 (7/4:ℝ) := by
    rw [Metric.mem_closedBall,dist_eq_norm,←Complex.ofReal_ofNat,←Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,abs_of_neg (by linarith : β-2<0)]
    linarith
  have hb := (Complex.re_le_norm (zetaRegular β)).trans (zetaRegular_norm_le_seventeen hmem)
  rw [zetaRegular_eq hβ0 hβne,Complex.sub_re,←Complex.ofReal_one,
    ←Complex.ofReal_sub,←Complex.ofReal_div,Complex.ofReal_re] at hb
  have hd : 1/(β-1)≤-100 := (div_le_iff_of_neg (by linarith : β-1<0)).mpr (by linarith)
  linarith

end
open Complex Filter Topology Set MeasureTheory Finset ArithmeticFunction
lemma LSeries_zeta_complex_summable {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m:=1) _ hs
  intro n hn
  simp [hn]

lemma biquadraticCoefficients_summable {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (biquadraticCoefficients χ ψ) s := by
  rw [biquadraticCoefficients,←productCharacter_toArithmeticFunction]
  exact ArithmeticFunction.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_mul
      (ArithmeticFunction.LSeriesSummable_mul (LSeries_zeta_complex_summable hs) (LSeries_character_summable χ hs))
      (LSeries_character_summable ψ hs)) (LSeries_character_summable (productCharacter χ ψ) hs)

lemma LSeries_biquadratic_eq {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) {s : ℂ} (hs : 1<s.re) :
    LSeries (biquadraticCoefficients χ ψ) s=
      riemannZeta s*(χ.LFunction s*ψ.LFunction s*(productCharacter χ ψ).LFunction s) := by
  have hz := LSeries_zeta_complex_summable hs
  have hχ := LSeries_character_summable χ hs
  have hψ := LSeries_character_summable ψ hs
  have hp := LSeries_character_summable (productCharacter χ ψ) hs
  rw [biquadraticCoefficients,←productCharacter_toArithmeticFunction,
    ArithmeticFunction.LSeries_mul' (ArithmeticFunction.LSeriesSummable_mul (ArithmeticFunction.LSeriesSummable_mul hz hχ) hψ) hp,
    ArithmeticFunction.LSeries_mul' (ArithmeticFunction.LSeriesSummable_mul hz hχ) hψ,
    ArithmeticFunction.LSeries_mul' hz hχ,LSeries_zeta_complex_eq hs,
    LSeries_character_eq χ hs,LSeries_character_eq ψ hs,
    LSeries_character_eq (productCharacter χ ψ) hs]
  ring

lemma quadratic_residue_lower_of_no_root {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ≠1) (hχ2 : χ^2=1)
    {β ε : ℝ} (hβ : 99/100≤β) (hβ1 : β<1) (hβε : 60*(1-β)≤ε)
    (hq : (4032:ℝ)≤q+1) (hz : ∀ x ∈ Set.Icc β 1, χ.LFunction x≠0) :
    ((1-β)/(2*(2-β)))*((q:ℝ)+1)^(-ε)≤‖χ.LFunction 1‖ := by
  have hQ : (2:ℝ)≤q+1 := by linarith
  have hpow : (q:ℝ)+1≤((q:ℝ)+1)^4 := le_self_pow₀ (by linarith) (by norm_num)
  have hv : (riemannZeta β*χ.LFunction β).re≤0 := by
    rw [Complex.mul_re,quadratic_LFunction_im hχ hχ2 (by linarith),mul_zero,sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (zeta_re_neg_near_one hβ hβ1).le
      (quadratic_LFunction_re_pos_of_no_root hχ hχ2 (by linarith) hβ1.le hz).le
  apply le_trans _ (Complex.re_le_norm _)
  apply zeta_product_residue_lower (a:=χ.zetaMul) (A:=336) (B:=16*((q:ℝ)+1))
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn (by positivity)
    (fun s hs => LFunction_norm_polynomial hχ hs) (by norm_num) hQ
    (by norm_num; exact hq) (by nlinarith) (by linarith) hβ1 hβε
    (DirichletCharacter.zetaMul_nonneg hχ2)
    (by simp only [χ.isMultiplicative_zetaMul.map_one,le_refl])
    (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun s hs => χ.LSeriesSummable_zetaMul hs))
    (fun s hs => LSeries_zetaMul_eq χ hs) hv
    (by simpa using quadratic_LFunction_im hχ hχ2 (x:=1) zero_lt_one)

lemma biquadratic_norm_bound {q r : ℕ} [NeZero q] [NeZero r]
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ r}
    (hχ : χ≠1) (hψ : ψ≠1) (hp : productCharacter χ ψ≠1)
    {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    ‖χ.LFunction s*ψ.LFunction s*(productCharacter χ ψ).LFunction s‖≤
      16^3*((q:ℝ)+1)^2*((r:ℝ)+1)^2 := by
  have hq0 : (0:ℝ)≤q := Nat.cast_nonneg q
  have hr0 : (0:ℝ)≤r := Nat.cast_nonneg r
  have hp' := LFunction_norm_polynomial hp hs
  simp only [Nat.cast_mul] at hp'
  calc
    _ ≤ (16*((q:ℝ)+1))*(16*((r:ℝ)+1))*(16*((q:ℝ)*r+1)) := by
      simp only [norm_mul]
      gcongr
      · exact LFunction_norm_polynomial hχ hs
      · exact LFunction_norm_polynomial hψ hs
    _ ≤ _ := by nlinarith [mul_nonneg hq0 hr0]

lemma biquadratic_residue_lower_of_root {q r : ℕ} [NeZero q] [NeZero r]
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ r}
    (hχ : χ≠1) (hχ2 : χ^2=1) (hψ : ψ≠1) (hψ2 : ψ^2=1)
    (hp : productCharacter ψ χ≠1) {β ε : ℝ}
    (hβ : 3/4≤β) (hβ1 : β<1) (hβε : 60*(1-β)≤ε)
    (hq : (12*(21*16^3*((r:ℝ)+1)^2))≤q+1) (hq1 : (2:ℝ)≤q+1)
    (hz : ψ.LFunction β=0) :
    ((1-β)/(2*(2-β)))*((q:ℝ)+1)^(-ε)≤
      ‖ψ.LFunction 1‖*‖χ.LFunction 1‖*‖(productCharacter ψ χ).LFunction 1‖ := by
  let P := fun s => ψ.LFunction s*χ.LFunction s*(productCharacter ψ χ).LFunction s
  have hd : Differentiable ℂ P :=
    ((DirichletCharacter.differentiable_LFunction hψ).mul
      (DirichletCharacter.differentiable_LFunction hχ)).mul
      (DirichletCharacter.differentiable_LFunction hp)
  have hpow : ((q:ℝ)+1)^2≤((q:ℝ)+1)^4 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have hb : ∀ s ∈ Metric.closedBall (2:ℂ) (7/4:ℝ),
      ‖P s‖≤16^3*((r:ℝ)+1)^2*((q:ℝ)+1)^2 := fun s hs => biquadratic_norm_bound hψ hχ hp hs
  have hiψ : (ψ.LFunction 1).im=0 := by simpa using quadratic_LFunction_im hψ hψ2 (x:=1) zero_lt_one
  have hiχ : (χ.LFunction 1).im=0 := by simpa using quadratic_LFunction_im hχ hχ2 (x:=1) zero_lt_one
  have hip : ((productCharacter ψ χ).LFunction 1).im=0 := by
    simpa using quadratic_LFunction_im hp (productCharacter_quadratic hψ2 hχ2) (x:=1) zero_lt_one
  have hreal : (P 1).im=0 := by simp [P,Complex.mul_im,hiψ,hiχ,hip]
  have hR := zeta_product_residue_lower (P:=P) (a:=biquadraticCoefficients ψ χ)
    (A:=21*16^3*((r:ℝ)+1)^2) (B:=16^3*((r:ℝ)+1)^2*((q:ℝ)+1)^2)
    hd.differentiableOn (by positivity) hb (by positivity) hq1 hq
    (by nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ)≤21*16^3*((r:ℝ)+1)^2)])
    hβ hβ1 hβε (biquadraticCoefficients_nonneg hψ2 hχ2)
    (by simp only [(biquadraticCoefficients_multiplicative ψ χ).map_one,le_refl])
    (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun s hs => biquadraticCoefficients_summable ψ χ hs))
    (fun s hs => LSeries_biquadratic_eq ψ χ hs) (by simp [P,hz]) hreal
  have := hR.trans (Complex.re_le_norm (P 1))
  simpa only [P,norm_mul] using this

lemma quadratic_siegel_eventual {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c Q₀ : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → χ^2=1 → Q₀≤(q:ℝ)+1 → c*((q:ℝ)+1)^(-ε)≤‖χ.LFunction 1‖ := by
  classical
  let β₀ : ℝ := 1-ε/240
  have hβ₀ : 99/100≤β₀ := by dsimp [β₀]; linarith
  have hβ₀1 : β₀<1 := by dsimp [β₀]; linarith
  by_cases hex : ∃ r : ℕ, ∃ ψ : DirichletCharacter ℂ (r+1),
      ψ.IsPrimitive ∧ ψ≠1 ∧ ψ^2=1 ∧ ∃ β ∈ Set.Icc β₀ 1, ψ.LFunction β=0
  · obtain ⟨r,ψ,hψprim,hψ,hψ2,β,hβI,hzero⟩ := hex
    have hβ1 : β<1 := lt_of_le_of_ne hβI.2 (by
      intro he
      apply DirichletCharacter.LFunction_apply_one_ne_zero hψ
      simpa [he] using hzero)
    have hβ : 99/100≤β := hβ₀.trans hβI.1
    have hβε : 60*(1-β)≤ε/2 := by dsimp [β₀] at hβI; linarith [hβI.1]
    obtain ⟨K,hK,hgrowth⟩ := LFunction_norm_small_power (by linarith : 0<ε/4)
      (by linarith : ε/4≤1/2)
    let D : ℝ := 3*((r:ℝ)+3)
    let U : ℝ := ‖ψ.LFunction 1‖*K*D^(ε/2)
    have hD : 0<D := by dsimp [D]; positivity
    have hU : 0<U := by
      exact mul_pos (mul_pos (norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero hψ)) hK)
        (Real.rpow_pos_of_pos hD _)
    let c : ℝ := (1-β)/(2*(2-β))/U
    have hc : 0<c := div_pos (div_pos (by linarith) (by linarith)) hU
    refine ⟨c,max (12*(21*16^3*(((r+1:ℕ):ℝ)+1)^2)) ((r:ℝ)+3),hc,?_⟩
    intro q _ χ hχprim hχ hχ2 hq
    have hq1 : (2:ℝ)≤q+1 := by have := (le_max_right _ _).trans hq; have : (0:ℝ)≤r := Nat.cast_nonneg r; linarith
    have hqr : r+1≠q := by
      have hr := (le_max_right _ _).trans hq
      intro he
      rw [←he] at hr
      push_cast at hr
      linarith
    have hp : productCharacter ψ χ≠1 :=
      productCharacter_ne_one_of_levels_ne hψprim hχprim hχ2 hqr
    have hl := biquadratic_residue_lower_of_root hχ hχ2 hψ hψ2 hp
      (by linarith) hβ1 hβε ((le_max_left _ _).trans hq) hq1 hzero
    have hb := hgrowth ((r+1)*q) (productCharacter ψ χ) hp 1 (by simp; linarith)
    have hQ0 : 0<(q:ℝ)+1 := by positivity
    have he : 2*(ε/4)=ε/2 := by ring
    rw [he] at hb
    have hbase : (((r+1)*q:ℕ):ℝ)+2≤((r:ℝ)+3)*((q:ℝ)+1) := by push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) q,Nat.cast_nonneg (α:=ℝ) r]
    have hb' : ‖(productCharacter ψ χ).LFunction 1‖≤K*D^(ε/2)*((q:ℝ)+1)^(ε/2) := by
      apply hb.trans
      simp only [norm_one]
      calc
        K*(((((r+1)*q:ℕ):ℝ)+2)*(1+2))^(ε/2) ≤ K*(D*((q:ℝ)+1))^(ε/2) := by
          apply mul_le_mul_of_nonneg_left _ hK.le
          apply Real.rpow_le_rpow (by positivity) _ (by linarith)
          dsimp [D]
          nlinarith
        _ = _ := by rw [Real.mul_rpow hD.le hQ0.le]; ring
    have hupper : ‖ψ.LFunction 1‖*‖χ.LFunction 1‖*‖(productCharacter ψ χ).LFunction 1‖≤
        U*((q:ℝ)+1)^(ε/2)*‖χ.LFunction 1‖ := by
      calc
        _ ≤ ‖ψ.LFunction 1‖*‖χ.LFunction 1‖*(K*D^(ε/2)*((q:ℝ)+1)^(ε/2)) := by gcongr
        _ = _ := by dsimp [U]; ring
    have hlow := hl.trans hupper
    have hQp : 0<((q:ℝ)+1)^(ε/2) := Real.rpow_pos_of_pos hQ0 _
    have hexp : ((q:ℝ)+1)^(-ε)*((q:ℝ)+1)^(ε/2)=((q:ℝ)+1)^(-(ε/2)) := by
      rw [←Real.rpow_add hQ0]; congr 1; ring
    have hfinal : U*(c*((q:ℝ)+1)^(-ε)*((q:ℝ)+1)^(ε/2)) ≤
        U*(‖χ.LFunction 1‖*((q:ℝ)+1)^(ε/2)) := by
      calc
        U*(c*((q:ℝ)+1)^(-ε)*((q:ℝ)+1)^(ε/2)) =
            ((1-β)/(2*(2-β)))*((q:ℝ)+1)^(-(ε/2)) := by
          rw [mul_assoc c,hexp]
          dsimp [c]
          field_simp
        _ ≤ U*(‖χ.LFunction 1‖*((q:ℝ)+1)^(ε/2)) := by simpa only [mul_assoc,mul_left_comm,mul_comm] using hlow
    exact (mul_le_mul_iff_left₀ hQp).mp ((mul_le_mul_iff_right₀ hU).mp hfinal)
  · refine ⟨(1-β₀)/(2*(2-β₀)),4032,div_pos (by linarith) (by linarith),?_⟩
    intro q hq χ hχprim hχ hχ2 hqbig
    apply quadratic_residue_lower_of_no_root hχ hχ2 hβ₀ hβ₀1
      (by dsimp [β₀]; linarith) hqbig
    intro x hx hz
    apply hex
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q => exact ⟨q,χ,hχprim,hχ,hχ2,x,hx,hz⟩

lemma finite_positive_lower {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i∈S,0<f i) : ∃ c : ℝ, 0<c ∧ ∀ i∈S,c≤f i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,zero_lt_one,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨c,hc,hcb⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine ⟨min c (f a),lt_min hc (hf a (Finset.mem_insert_self _ _)),?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hcb i hi)

lemma LFunction_one_finite_lower (N : ℕ) :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      q≤N → χ≠1 → c≤‖χ.LFunction 1‖ := by
  classical
  induction N with
  | zero => exact ⟨1,zero_lt_one,fun q _ χ hq _ => (NeZero.ne q (Nat.eq_zero_of_le_zero hq)).elim⟩
  | succ N ih =>
    obtain ⟨c,hc,hcb⟩ := ih
    obtain ⟨d,hd,hdb⟩ := finite_positive_lower
      ((Finset.univ : Finset (DirichletCharacter ℂ (N+1))).filter (·≠1))
      (fun χ => ‖χ.LFunction 1‖) (fun χ hχ =>
        norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero (Finset.mem_filter.mp hχ).2))
    refine ⟨min c d,lt_min hc hd,?_⟩
    intro q _ χ hq hχ
    rcases Nat.le_succ_iff_eq_or_le.mp hq with rfl|hq
    · exact (min_le_right _ _).trans (hdb χ (by simp [hχ]))
    · exact (min_le_left _ _).trans (hcb q χ hq hχ)

theorem quadratic_siegel {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → χ^2=1 → c*((q:ℝ)+1)^(-ε)≤‖χ.LFunction 1‖ := by
  obtain ⟨c,Q₀,hc,hcb⟩ := quadratic_siegel_eventual hε hε1
  obtain ⟨d,hd,hdb⟩ := LFunction_one_finite_lower ⌈Q₀⌉₊
  refine ⟨min c d,lt_min hc hd,?_⟩
  intro q _ χ hχp hχ hχ2
  by_cases hq : Q₀≤(q:ℝ)+1
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (by positivity) _)).trans
      (hcb q χ hχp hχ hχ2 hq)
  · have hqn : q≤⌈Q₀⌉₊ := by
      have := Nat.le_ceil Q₀
      have : (q:ℝ)≤(⌈Q₀⌉₊:ℝ) := by linarith
      exact_mod_cast this
    have hp : ((q:ℝ)+1)^(-ε)≤1 := Real.rpow_le_one_of_one_le_of_nonpos (by have := Nat.cast_nonneg (α:=ℝ) q; linarith) (by linarith)
    exact (mul_le_of_le_one_right (le_of_lt (lt_min hc hd)) hp).trans
      ((min_le_right _ _).trans (hdb q χ hqn hχ))

end LargePrimeGaps
end OAI

-- Source module: ZeroFreeBounds
namespace OAI
namespace LargePrimeGaps
section
open Complex Filter Topology Set MeasureTheory Finset
lemma periodic_sum_norm_le_mul {f : ℕ → ℂ} {q : ℕ} {D : ℝ} (hq : 0<q) (hD : 0≤D)
    (hp : ∀ n,f (q+n)=f n) (hz : ∑ n∈range q,f n=0)
    (hb : ∀ n,‖f n‖≤D) (N : ℕ) : ‖∑ n∈range N,f n‖≤q*D := by
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    by_cases hN : N<q
    · calc
        _ ≤ ∑ n∈range N,‖f n‖ := norm_sum_le _ _
        _ ≤ ∑ _n∈range N,D := sum_le_sum (fun n _ => hb n)
        _ = N*D := by simp
        _ ≤ q*D := mul_le_mul_of_nonneg_right (by exact_mod_cast hN.le) hD
    · have he : q+(N-q)=N := Nat.add_sub_of_le (not_lt.mp hN)
      rw [←he,sum_range_add,hz,zero_add]
      simp_rw [hp]
      exact ih _ (Nat.sub_lt (lt_of_lt_of_le hq (not_lt.mp hN)) hq)

noncomputable def characterMean {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  (∑ n∈range q,χ (n : ZMod q))/(q:ℂ)

lemma characterMean_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖characterMean χ‖≤1 := by
  rw [characterMean,norm_div,Complex.norm_natCast]
  apply (div_le_one (by exact_mod_cast NeZero.pos q : (0:ℝ)<q)).mpr
  calc
    _ ≤ ∑ n∈range q,‖χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n∈range q,(1:ℝ) := sum_le_sum (fun n _ => χ.norm_le_one _)
    _ = q := by simp

lemma characterMean_eq_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ≠1) :
    characterMean χ=0 := by simp [characterMean,char_sum_range_zero hχ]

lemma discrepancy_characterMean_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {t : ℝ} (ht : 1≤t) :
    ‖seriesDiscrepancy (positiveCoefficients (fun n => χ (n : ZMod q))) (characterMean χ) t‖≤2*q+3 := by
  let c := characterMean χ
  have hc : ‖c‖≤1 := characterMean_norm_le χ
  have hb (n : ℕ) : ‖χ (n : ZMod q)-c‖≤2 := (norm_sub_le _ _).trans (by linarith [χ.norm_le_one (n : ZMod q)])
  have hz : ∑ n∈range q,(χ (n : ZMod q)-c)=0 := by
    rw [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul]
    dsimp [c,characterMean]
    have hq : (q:ℂ)≠0 := by exact_mod_cast NeZero.ne q
    field_simp
    ring
  have hr := periodic_sum_norm_le_mul (NeZero.pos q) (by norm_num : (0:ℝ)≤2)
    (f:=fun n => χ (n : ZMod q)-c) (by intro n; simp) hz hb (⌊t⌋₊+1)
  have he : ∑ n∈range (⌊t⌋₊+1),(χ (n : ZMod q)-c) =
      χ (0 : ZMod q)-c+ ∑ n∈Icc 1 ⌊t⌋₊,(χ (n : ZMod q)-c) := by
    rw [Nat.range_succ_eq_Icc_zero,←Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le ⌊t⌋₊)]
    simp
    ring
  have ht0 : 0≤t := by linarith
  have hfloor : ‖(⌊t⌋₊:ℂ)-(t:ℂ)‖≤1 := by
    rw [←Complex.ofReal_natCast,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le ht0))]
    have := Nat.lt_floor_add_one t
    linarith
  have heq : seriesDiscrepancy (positiveCoefficients (fun n => χ (n : ZMod q))) c t =
      (∑ n∈range (⌊t⌋₊+1),(χ (n : ZMod q)-c))-(χ 0-c)+c*((⌊t⌋₊:ℂ)-(t:ℂ)) := by
    rw [he]
    simp only [seriesDiscrepancy,sum_positiveCoefficients,sum_sub_distrib,sum_const,Nat.card_Icc,
      Nat.add_sub_cancel,nsmul_eq_mul]
    ring
  rw [heq]
  calc
    _ ≤ ‖∑ n∈range (⌊t⌋₊+1),(χ (n : ZMod q)-c)‖+‖χ 0-c‖+‖c*((⌊t⌋₊:ℂ)-(t:ℂ))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (q:ℝ)*2+2+1 := by
      gcongr
      · simpa using hb 0
      · rw [norm_mul]; exact (mul_le_mul hc hfloor (norm_nonneg _) zero_le_one).trans_eq (by ring)
    _ = _ := by ring

lemma LFunction_regularSeries_characterMean {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    χ.LFunction s = regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) (characterMean χ) s+
      characterMean χ/(s-1) := by
  rw [regularSeries_eq_LSeries_sub (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by positivity : (0:ℝ)≤2*q+3) (fun t ht => discrepancy_characterMean_bound χ ht.le) hs,
    sub_add_cancel,LSeries_positiveCoefficients,←χ.LFunction_eq_LSeries hs]

lemma LFunction_deriv_norm_small_power {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1/2) :
    ∃ K : ℝ,0<K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),χ≠1 →
      ∀ s : ℂ,1-ε/2 ≤ s.re → ‖deriv χ.LFunction s‖≤K*((q+2)*(‖s‖+2))^(2*ε) := by
  obtain ⟨K,hK,h⟩ := regularSeries_deriv_norm_small_power hε hε1
  refine ⟨K,hK,?_⟩
  intro q _ χ hχ s hs
  have he : regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) 0 =ᶠ[𝓝 s] χ.LFunction := by
    filter_upwards [(continuous_re.tendsto s).eventually (lt_mem_nhds (by linarith : 0<s.re))] with z hz
    exact regularSeries_character_eq hχ hz
  rw [←he.deriv_eq]
  have hb := h _ 0 (q+1) (positiveCoefficients_zero _) (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by simp) (by positivity) (fun t _ => discrepancy_character_bound hχ t) s hs
  convert hb using 1
  congr 3
  ring

noncomputable def characterRegular {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) (characterMean χ)

lemma character_line_bounds {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1/2) :
    ∃ K : ℝ,1≤K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
      (∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
        ‖characterRegular χ s‖≤K*((q+2)*(|t|+2))^(2*ε)) ∧
      (χ≠1 → ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
        ‖deriv χ.LFunction s‖≤K*((q+2)*(|t|+2))^(2*ε)) := by
  obtain ⟨K₀,hK₀,h₀⟩ := regularSeries_norm_small_power hε hε1
  obtain ⟨K₁,hK₁,h₁⟩ := LFunction_deriv_norm_small_power hε hε1
  let K := 1+K₀*8^(2*ε)+K₁*4^(2*ε)
  have hp₀ : 0≤K₀*8^(2*ε) := by positivity
  have hp₁ : 0≤K₁*4^(2*ε) := by positivity
  have hK : 1≤K := by dsimp [K]; linarith
  refine ⟨K,hK,?_⟩
  intro q _ χ t
  have hq : (0:ℝ)≤q := Nat.cast_nonneg q
  have ht : 0≤|t| := abs_nonneg t
  have hp : 0≤((q:ℝ)+2)*(|t|+2) := by positivity
  have he : 0≤2*ε := by positivity
  constructor
  · intro s hs hn
    have hb := h₀ _ (characterMean χ) (2*q+3) (positiveCoefficients_zero _)
      (positiveCoefficients_norm_le (fun n => χ.norm_le_one _)) (characterMean_norm_le χ)
      (by positivity) (fun t ht => discrepancy_characterMean_bound χ ht) s (by linarith)
    change ‖characterRegular χ s‖≤_ at hb
    have hb' : (2*q+3+1)*(‖s‖+2)≤8*(((q:ℝ)+2)*(|t|+2)) := by
      nlinarith [mul_nonneg (show (0:ℝ)≤2*q+4 by positivity) (sub_nonneg.mpr hn)]
    calc
      _ ≤ K₀*((2*q+3+1)*(‖s‖+2))^(2*ε) := hb
      _ ≤ K₀*(8*(((q:ℝ)+2)*(|t|+2)))^(2*ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb' he) hK₀.le
      _ = (K₀*8^(2*ε))*(((q:ℝ)+2)*(|t|+2))^(2*ε) := by rw [Real.mul_rpow (by norm_num) hp]; ring
      _ ≤ _ := by gcongr; dsimp [K]; linarith
  · intro hχ s hs hn
    have hb := h₁ q χ hχ s (by linarith)
    have hb' : (q+2)*(‖s‖+2)≤4*(((q:ℝ)+2)*(|t|+2)) := by
      nlinarith [mul_nonneg (show (0:ℝ)≤q+2 by positivity) (sub_nonneg.mpr hn)]
    calc
      _ ≤ K₁*((q+2)*(‖s‖+2))^(2*ε) := hb
      _ ≤ K₁*(4*(((q:ℝ)+2)*(|t|+2)))^(2*ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb' he) hK₁.le
      _ = (K₁*4^(2*ε))*(((q:ℝ)+2)*(|t|+2))^(2*ε) := by rw [Real.mul_rpow (by norm_num) hp]; ring
      _ ≤ _ := by gcongr; dsimp [K]; linarith

lemma line_growth_lipschitz {f : ℂ → ℂ} {t D : ℝ} (hf : Differentiable ℂ f)
    (hb : ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) → ‖deriv f s‖≤D)
    {z w : ℂ} (hz : 1 ≤ z.re) (hw : 1 ≤ w.re)
    (hzn : ‖z‖+2≤4*(|t|+2)) (hwn : ‖w‖+2≤4*(|t|+2)) :
    ‖f z-f w‖≤D*‖z-w‖ := by
  let S := {s : ℂ | 1 ≤ s.re} ∩ Metric.closedBall 0 (4*(|t|+2)-2)
  have hS : Convex ℝ S := (convex_halfSpace_re_ge 1).inter (convex_closedBall 0 _)
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s:=S) (fun z _ => hf z) ?_ hS
      ⟨hw,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
      ⟨hz,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
  intro s hs
  exact hb s hs.1 (by have := hs.2; simp only [Metric.mem_closedBall,dist_zero_right] at this; linarith)

end
lemma three_four_one_lower {a D E : ℝ} (ha : 0≤a) (hD : 1≤D) (hE : 1≤E)
    (h : ∀ δ : ℝ,0<δ → δ≤1 → 1≤(2*D/δ)^3*(a+D*δ)^4*E) :
    1/(256*D^6*E)≤a := by
  have hD0 : 0<D := by linarith
  have hE0 : 0<E := by linarith
  let δ := 1/(256*D^7*E)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδ1 : δ≤1 := by
    have hp : (1:ℝ)≤D^7 := one_le_pow₀ hD
    have hp' : (1:ℝ)≤D^7*E := one_le_mul_of_one_le_of_one_le hp hE
    dsimp [δ]
    apply (div_le_one (by positivity)).mpr
    linarith
  have he : 1/(256*D^6*E)=D*δ := by dsimp [δ]; field_simp
  rw [he]
  by_contra! han
  have hb : a+D*δ≤2*D*δ := by linarith
  have hh := h δ hδ hδ1
  have hu : (2*D/δ)^3*(a+D*δ)^4*E≤(2*D/δ)^3*(2*D*δ)^4*E := by gcongr
  have hv : (2*D/δ)^3*(2*D*δ)^4*E=1/2 := by dsimp [δ]; field_simp; norm_num
  rw [hv] at hu
  linarith

open Complex Filter Topology Finset
lemma line_sample_norm {δ t u : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1) (hu : |u|≤2*|t|) :
    ‖(1:ℂ)+δ+I*u‖+2≤4*(|t|+2) := by
  have h := Complex.norm_le_abs_re_add_abs_im ((1:ℂ)+δ+I*u)
  simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
    Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_self,add_zero,Complex.add_im,
    Complex.one_im,Complex.mul_im,one_mul,zero_add] at h
  rw [abs_of_nonneg (by linarith : (0:ℝ)≤1+δ)] at h
  linarith [abs_nonneg t]

lemma LFunction_norm_le_regular_add_pole {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    ‖χ.LFunction s‖≤‖characterRegular χ s‖+1/‖s-1‖ := by
  rw [LFunction_regularSeries_characterMean χ hs]
  apply (norm_add_le _ _).trans
  dsimp [characterRegular]
  apply add_le_add le_rfl
  rw [norm_div]
  exact div_le_div_of_nonneg_right (characterMean_norm_le χ) (norm_nonneg _)

lemma characterRegular_eq_nonprincipal {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {s : ℂ} (hs : 0<s.re) : characterRegular χ s=χ.LFunction s := by
  rw [characterRegular,characterMean_eq_zero hχ,regularSeries_character_eq hχ hs]

lemma nonprincipal_line_lower_aux {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {t c K P : ℝ} (hc : 0<c) (_hc1 : c≤1) (hK : 1≤K) (hP : 1≤P)
    (hr : ∀ ψ : DirichletCharacter ℂ q,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P)
    (hd : ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) → ‖deriv χ.LFunction s‖≤K*P)
    (hsi : χ^2=1 → c/P≤‖χ.LFunction 1‖) :
    min (c/2) (1/(256*K^6*(K+K/c)))/P^8≤‖χ.LFunction (1+I*t)‖ := by
  have hK0 : 0<K := by linarith
  have hP0 : 0<P := by linarith
  have hhc : 0<K+K/c := by positivity
  have hKP : 1≤K*P := one_le_mul_of_one_le_of_one_le hK hP
  have hn0 : ‖(1:ℂ)+I*t‖+2≤4*(|t|+2) := by
    simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
  have hn1 : ‖(1:ℂ)‖+2≤4*(|t|+2) := by norm_num; linarith [abs_nonneg t]
  by_cases hsmall : χ^2=1 ∧ |t|≤c/(2*K*P^2)
  · have hdiff := line_growth_lipschitz (DirichletCharacter.differentiable_LFunction hχ) hd
      (z:=1) (w:=1+I*t) (by simp) (by simp) hn1 hn0
    have hnorm : ‖(1:ℂ)-(1+I*t)‖=|t| := by
      rw [show (1:ℂ)-(1+I*t)=-(I*t) by ring,norm_neg,norm_mul,Complex.norm_I,one_mul,
        Complex.norm_real,Real.norm_eq_abs]
    rw [hnorm] at hdiff
    have hdiff' : ‖χ.LFunction 1-χ.LFunction (1+I*t)‖≤c/(2*P) := by
      calc
        _ ≤ K*P*|t| := hdiff
        _ ≤ K*P*(c/(2*K*P^2)) := mul_le_mul_of_nonneg_left hsmall.2 (by positivity)
        _ = _ := by field_simp
    have hval : c/(2*P)≤‖χ.LFunction (1+I*t)‖ := by
      have htri := norm_add_le (χ.LFunction 1-χ.LFunction (1+I*t)) (χ.LFunction (1+I*t))
      rw [sub_add_cancel] at htri
      have he : c/P=2*(c/(2*P)) := by ring
      have hsi' := hsi hsmall.1
      rw [he] at hsi'
      linarith
    have hP8 : P≤P^8 := by simpa using pow_le_pow_right₀ hP (show (1:ℕ)≤8 by norm_num)
    calc
      _ ≤ (c/2)/P^8 := div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
      _ ≤ (c/2)/P := div_le_div_of_nonneg_left (by positivity) hP0 hP8
      _ = c/(2*P) := by ring
      _ ≤ _ := hval
  · have hLo : 1/(256*(K*P)^6*((K+K/c)*P^2))≤‖χ.LFunction (1+I*t)‖ := by
      apply three_four_one_lower (norm_nonneg _) hKP
        (one_le_mul_of_one_le_of_one_le (by linarith [div_pos hK0 hc]) (one_le_pow₀ hP))
      intro δ hδ hδ1
      have hrδ : ((1:ℂ)+δ+I*t).re=1+δ := by simp
      have hrδ2 : ((1:ℂ)+δ+2*I*t).re=1+δ := by simp
      have hnδ := line_sample_norm hδ.le hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
      have hnδ2 : ‖(1:ℂ)+δ+2*I*t‖+2≤4*(|t|+2) := by
        simpa only [show I*((2*t:ℝ):ℂ)=2*I*t by push_cast; ring] using
          line_sample_norm hδ.le hδ1 (t:=t) (u:=2*t) (by rw [abs_mul]; norm_num)
      have hL0 : ‖DirichletCharacter.LFunctionTrivChar q (1+δ)‖≤2*(K*P)/δ := by
        have hn : ‖(1:ℂ)+δ‖+2≤4*(|t|+2) := by
          simpa using line_sample_norm hδ.le hδ1 (t:=t) (u:=0) (by simp)
        have hreg := hr (1:DirichletCharacter ℂ q) (1+δ) (by simp; linarith) hn
        have hp := LFunction_norm_le_regular_add_pole (1:DirichletCharacter ℂ q)
          (s:=1+δ) (by simp; linarith)
        have hden : ‖(1:ℂ)+δ-1‖=δ := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
        rw [hden] at hp
        change ‖DirichletCharacter.LFunction (1:DirichletCharacter ℂ q) (1+δ)‖≤_
        apply (hp.trans (add_le_add hreg le_rfl)).trans
        apply (le_div_iff₀ hδ).mpr
        have hd : (K*P)*δ≤K*P := mul_le_of_le_one_right (by positivity) hδ1
        field_simp
        nlinarith
      have hLχ : ‖χ.LFunction (1+δ+I*t)‖≤‖χ.LFunction (1+I*t)‖+(K*P)*δ := by
        have hl := line_growth_lipschitz (DirichletCharacter.differentiable_LFunction hχ) hd
          (z:=1+δ+I*t) (w:=1+I*t) (by simp; linarith) (by simp) hnδ hn0
        have hden : ‖(1:ℂ)+δ+I*t-(1+I*t)‖=δ := by
          rw [show (1:ℂ)+δ+I*t-(1+I*t)=(δ:ℂ) by ring,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
        rw [hden] at hl
        have ht := norm_add_le (χ.LFunction (1+δ+I*t)-χ.LFunction (1+I*t)) (χ.LFunction (1+I*t))
        rw [sub_add_cancel] at ht
        linarith
      have hL2 : ‖(χ^2).LFunction (1+δ+2*I*t)‖≤(K+K/c)*P^2 := by
        by_cases hχ2 : χ^2=1
        · have ht : c/(2*K*P^2)< |t| := lt_of_not_ge (fun ht => hsmall ⟨hχ2,ht⟩)
          have ht0 : 0< |t| := (by positivity : 0<c/(2*K*P^2)).trans ht
          have hp := LFunction_norm_le_regular_add_pole (χ^2) (s:=1+δ+2*I*t) (by rw [hrδ2]; linarith)
          have hn : 2*|t|≤‖(1:ℂ)+δ+2*I*t-1‖ := by
            have h := Complex.abs_im_le_norm ((1:ℂ)+δ+2*I*t-1)
            simpa [abs_mul] using h
          have hfrac : 1/‖(1:ℂ)+δ+2*I*t-1‖≤K*P^2/c := by
            apply (div_le_div_of_nonneg_left zero_le_one (by positivity : 0<2*|t|) hn).trans
            apply (div_le_iff₀ (by positivity : 0<2*|t|)).mpr
            have ht' := (div_lt_iff₀ (by positivity : 0<2*K*P^2)).mp ht
            rw [div_mul_eq_mul_div]
            apply (le_div_iff₀ hc).mpr
            nlinarith
          have hreg := hr (χ^2) (1+δ+2*I*t) (by rw [hrδ2]; linarith) hnδ2
          have hP2 : P≤P^2 := by nlinarith
          have h := hp.trans (add_le_add hreg hfrac)
          apply h.trans
          calc
            K*P+K*P^2/c ≤ K*P^2+K*P^2/c := add_le_add (mul_le_mul_of_nonneg_left hP2 hK0.le) le_rfl
            _ = _ := by ring
        · have hreg := hr (χ^2) (1+δ+2*I*t) (by rw [hrδ2]; linarith) hnδ2
          rw [characterRegular_eq_nonprincipal hχ2 (by rw [hrδ2]; linarith)] at hreg
          have hP2 : P≤P^2 := by nlinarith
          exact hreg.trans (by nlinarith [mul_le_mul_of_nonneg_left hP2 hK0.le,div_pos hK0 hc])
      have hprod := χ.norm_LFunction_product_ge_one hδ t
      simp only [norm_mul,norm_pow] at hprod
      exact hprod.trans (by gcongr)
    calc
      _ ≤ (1/(256*K^6*(K+K/c)))/P^8 := div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = 1/(256*(K*P)^6*((K+K/c)*P^2)) := by field_simp
      _ ≤ _ := hLo

lemma nonprincipal_line_lower {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ,0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → ∀ t : ℝ,
        c*(((q:ℝ)+2)*(|t|+2))^(-ε)≤‖χ.LFunction (1+I*t)‖ := by
  obtain ⟨K,hK,hgrowth⟩ := character_line_bounds (by linarith : 0<ε/16) (by linarith : ε/16≤1/2)
  obtain ⟨c₀,hc₀,hsiegel⟩ := quadratic_siegel (by linarith : 0<ε/8) (by linarith : ε/8≤1)
  let c := min c₀ 1
  have hc : 0<c := lt_min hc₀ zero_lt_one
  have hc1 : c≤1 := min_le_right _ _
  let d := min (c/2) (1/(256*K^6*(K+K/c)))
  have hK0 : 0<K := by linarith
  have hd : 0<d := by dsimp [d]; positivity
  refine ⟨d,hd,?_⟩
  intro q _ χ hχp hχ t
  let X : ℝ := ((q:ℝ)+2)*(|t|+2)
  let P : ℝ := X^(ε/8)
  have hX : 1≤X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
  have hX0 : 0<X := by linarith
  have hP : 1≤P := Real.one_le_rpow hX (by positivity)
  have he : 2*(ε/16)=ε/8 := by ring
  have hsi : χ^2=1 → c/P≤‖χ.LFunction 1‖ := by
    intro hχ2
    have hq : (q:ℝ)+1≤X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
    calc
      c/P = c*X^(-(ε/8)) := by rw [Real.rpow_neg hX0.le]; rfl
      _ ≤ c₀*((q:ℝ)+1)^(-(ε/8)) := by
        apply mul_le_mul (min_le_left _ _) (Real.rpow_le_rpow_of_nonpos (by positivity) hq (by linarith))
          (Real.rpow_nonneg hX0.le _) hc₀.le
      _ ≤ _ := hsiegel q χ hχp hχ hχ2
  have hh := nonprincipal_line_lower_aux hχ hc hc1 hK hP
    (fun ψ s hs hn => by simpa only [he] using (hgrowth q ψ t).1 s hs hn)
    (fun s hs hn => by simpa only [he] using (hgrowth q χ t).2 hχ s hs hn) hsi
  have hP8 : P^8=X^ε := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast hX0.le]
    congr 1
    norm_num
  change d/P^8≤_ at hh
  rw [hP8] at hh
  change d*X^(-ε)≤_
  simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hh

lemma character_interior_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {t K P δ : ℝ} (hK : 1≤K) (hP : 1≤P) (hδ : 0<δ) (hδ1 : δ≤1)
    (hr : ∀ ψ : DirichletCharacter ℂ q,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P) :
    δ/(2*K*P)≤‖χ.LFunction (1+δ+I*t)‖ := by
  have hKP : 1≤K*P := one_le_mul_of_one_le_of_one_le hK hP
  have hKP0 : 0<K*P := by linarith
  have hb (ψ : DirichletCharacter ℂ q) (u : ℝ) (hu : |u|≤2*|t|) :
      ‖ψ.LFunction (1+δ+I*u)‖≤2*K*P/δ := by
    have hp := LFunction_norm_le_regular_add_pole ψ (s:=1+δ+I*u) (by simp; linarith)
    have hn : δ≤‖(1:ℂ)+δ+I*u-1‖ := by
      simpa using Complex.re_le_norm ((1:ℂ)+δ+I*u-1)
    have hreg := hr ψ (1+δ+I*u) (by simp; linarith) (line_sample_norm hδ.le hδ1 hu)
    have hfrac := div_le_div_of_nonneg_left zero_le_one hδ hn
    apply (hp.trans (add_le_add hreg hfrac)).trans
    apply (le_div_iff₀ hδ).mpr
    have hd := mul_le_of_le_one_right hKP0.le hδ1
    have he : (K*P+1/δ)*δ=K*P*δ+1 := by field_simp
    rw [he]
    nlinarith
  have h0 : ‖DirichletCharacter.LFunctionTrivChar q (1+δ)‖≤2*K*P/δ := by
    simpa using hb (1:DirichletCharacter ℂ q) 0 (by simp)
  have h2 : ‖(χ^2).LFunction (1+δ+2*I*t)‖≤2*K*P/δ := by
    simpa only [show I*((2*t:ℝ):ℂ)=2*I*t by push_cast; ring] using hb (χ^2) (2*t) (by rw [abs_mul]; norm_num)
  have hh := χ.norm_LFunction_product_ge_one hδ t
  simp only [norm_mul,norm_pow] at hh
  have hu : 1≤(2*K*P/δ)^3*‖χ.LFunction (1+δ+I*t)‖^4*(2*K*P/δ) := hh.trans (by gcongr)
  have hp : (1:ℝ)^4≤((2*K*P/δ)*‖χ.LFunction (1+δ+I*t)‖)^4 := by convert hu using 1 <;> ring
  have hv := le_of_pow_le_pow_left₀ (by norm_num : (4:ℕ)≠0) (by positivity) hp
  apply (div_le_iff₀ (by positivity : 0<2*K*P)).mpr
  have he : (2*K*P/δ)*‖χ.LFunction (1+δ+I*t)‖=(‖χ.LFunction (1+δ+I*t)‖*(2*K*P))/δ := by ring
  rw [he] at hv
  simpa only [one_mul] using (le_div_iff₀ hδ).mp hv

lemma nonprincipal_strip_lower_aux {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {t c K P δ : ℝ} (hc : 0<c) (hK : 1≤K) (hP : 1≤P)
    (hδ : 0≤δ) (hδ1 : δ≤1)
    (hr : ∀ ψ : DirichletCharacter ℂ q,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P)
    (hd : ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) → ‖deriv χ.LFunction s‖≤K*P)
    (hl : c/P≤‖χ.LFunction (1+I*t)‖) :
    (c/(4*K^2))/P^3≤‖χ.LFunction (1+δ+I*t)‖ := by
  have hK0 : 0<K := by linarith
  have hP0 : 0<P := by linarith
  by_cases hnear : δ≤c/(2*K*P^2)
  · have hn0 : ‖(1:ℂ)+I*t‖+2≤4*(|t|+2) := by
      simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
    have hnδ := line_sample_norm hδ hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
    have hdif := line_growth_lipschitz (DirichletCharacter.differentiable_LFunction hχ) hd
      (z:=1+I*t) (w:=1+δ+I*t) (by simp) (by simp; linarith) hn0 hnδ
    have hnorm : ‖(1:ℂ)+I*t-(1+δ+I*t)‖=δ := by
      rw [show (1:ℂ)+I*t-(1+δ+I*t)=-(δ:ℂ) by ring,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hδ]
    rw [hnorm] at hdif
    have hdb : ‖χ.LFunction (1+I*t)-χ.LFunction (1+δ+I*t)‖≤c/(2*P) := by
      apply hdif.trans
      calc
        K*P*δ ≤ K*P*(c/(2*K*P^2)) := mul_le_mul_of_nonneg_left hnear (by positivity)
        _ = _ := by field_simp
    have htri := norm_add_le (χ.LFunction (1+I*t)-χ.LFunction (1+δ+I*t)) (χ.LFunction (1+δ+I*t))
    rw [sub_add_cancel] at htri
    have hva : c/(2*P)≤‖χ.LFunction (1+δ+I*t)‖ := by
      have he : c/P=2*(c/(2*P)) := by ring
      rw [he] at hl
      linarith
    apply le_trans ?_ hva
    rw [div_div]
    apply div_le_div_of_nonneg_left hc.le (by positivity)
    have hP3 : P≤P^3 := by simpa using pow_le_pow_right₀ hP (show (1:ℕ)≤3 by norm_num)
    have hK2 : 1≤K^2 := one_le_pow₀ hK
    nlinarith [mul_le_mul_of_nonneg_left hP3 (show (0:ℝ)≤4*K^2 by positivity)]
  · have hδ0 : 0<δ := (by positivity : 0<c/(2*K*P^2)).trans (lt_of_not_ge hnear)
    apply le_trans ?_ (character_interior_lower χ hK hP hδ0 hδ1 hr)
    calc
      (c/(4*K^2))/P^3 = (c/(2*K*P^2))/(2*K*P) := by field_simp; norm_num
      _ ≤ δ/(2*K*P) := div_le_div_of_nonneg_right (le_of_not_ge hnear) (by positivity)

lemma nonprincipal_strip_lower {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ,0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → ∀ σ t : ℝ, 1≤σ → σ≤2 →
        c*(((q:ℝ)+2)*(|t|+2))^(-ε)≤‖χ.LFunction (σ+I*t)‖ := by
  obtain ⟨K,hK,hg⟩ := character_line_bounds (by linarith : 0<ε/6) (by linarith : ε/6≤1/2)
  obtain ⟨c,hc,hl⟩ := nonprincipal_line_lower (by linarith : 0<ε/3) (by linarith : ε/3≤1)
  have hK0 : 0<K := by linarith
  refine ⟨c/(4*K^2),by positivity,?_⟩
  intro q _ χ hχp hχ σ t hσ hσ2
  let X : ℝ := ((q:ℝ)+2)*(|t|+2)
  let P : ℝ := X^(ε/3)
  have hX : 1≤X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
  have hX0 : 0<X := by linarith
  have hP : 1≤P := Real.one_le_rpow hX (by positivity)
  have he : 2*(ε/6)=ε/3 := by ring
  have hl' : c/P≤‖χ.LFunction (1+I*t)‖ := by
    have hh := hl q χ hχp hχ t
    change c*X^(-(ε/3))≤_ at hh
    change c/X^(ε/3)≤_
    simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hh
  have hb := nonprincipal_strip_lower_aux hχ hc hK hP (δ:=σ-1) (by linarith) (by linarith)
    (fun ψ s hs hn => by simpa only [he] using (hg q ψ t).1 s hs hn)
    (fun s hs hn => by simpa only [he] using (hg q χ t).2 hχ s hs hn) hl'
  have hP3 : P^3=X^ε := by dsimp [P]; rw [←Real.rpow_mul_natCast hX0.le]; congr 1; norm_num
  rw [hP3] at hb
  have hs : (1:ℂ)+((σ-1:ℝ):ℂ)+I*t=(σ:ℂ)+I*t := by push_cast; ring
  rw [hs] at hb
  change (c/(4*K^2))*X^(-ε)≤_
  simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hb

end LargePrimeGaps
end OAI

-- Source module: PrincipalGrowth
namespace OAI
namespace LargePrimeGaps
open Complex Filter Topology
lemma zetaRegular_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ s : ℂ, 1-ε/2 ≤ s.re →
      ‖zetaRegular s‖ ≤ K*(‖s‖+2)^(2*ε) ∧
      ‖deriv zetaRegular s‖ ≤ K*(‖s‖+2)^(2*ε) := by
  obtain ⟨K₀,hK₀,h₀⟩ := regularSeries_norm_small_power hε hε1
  obtain ⟨K₁,hK₁,h₁⟩ := regularSeries_deriv_norm_small_power hε hε1
  let K := 1+(K₀+K₁)*2^(2*ε)
  have hK : 1 ≤ K := by dsimp [K]; linarith [show 0 < (K₀+K₁)*2^(2*ε) by positivity]
  refine ⟨K,hK,?_⟩
  intro s hs
  have hb₀ := h₀ _ 1 1 (positiveCoefficients_zero _) (positiveCoefficients_norm_le (by simp))
    (by simp) zero_le_one (fun t ht => discrepancy_constant_bound ht) s (by linarith)
  have hb₁ := h₁ _ 1 1 (positiveCoefficients_zero _) (positiveCoefficients_norm_le (by simp))
    (by simp) zero_le_one (fun t ht => discrepancy_constant_bound ht) s hs
  change ‖zetaRegular s‖ ≤ _ at hb₀
  change ‖deriv zetaRegular s‖ ≤ _ at hb₁
  norm_num only [one_add_one_eq_two] at hb₀ hb₁
  rw [Real.mul_rpow (by norm_num) (by positivity)] at hb₀ hb₁
  constructor
  · apply hb₀.trans
    have hc : K₀*2^(2*ε) ≤ K := by dsimp [K]; nlinarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (2*ε)]
    calc
      _ = (K₀*2^(2*ε))*(‖s‖+2)^(2*ε) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  · apply hb₁.trans
    have hc : K₁*2^(2*ε) ≤ K := by dsimp [K]; nlinarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (2*ε)]
    calc
      _ = (K₁*2^(2*ε))*(‖s‖+2)^(2*ε) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

lemma zeta_deriv_eq_regular {s : ℂ} (hs : 0 < s.re) (hs1 : s≠1) :
    deriv riemannZeta s = deriv zetaRegular s-1/(s-1)^2 := by
  have he : riemannZeta =ᶠ[𝓝 s] fun z => zetaRegular z+1/(z-1) := by
    filter_upwards [(continuous_re.tendsto s).eventually (lt_mem_nhds hs),
      eventually_ne_nhds hs1] with z hz hz1
    rw [zetaRegular_eq hz hz1,sub_add_cancel]
  rw [he.deriv_eq]
  have hd := (hasDerivAt_const s (1:ℂ)).div ((hasDerivAt_id s).sub_const 1) (sub_ne_zero.mpr hs1)
  have hh := (zetaRegular_differentiableAt hs).hasDerivAt.add hd
  simpa only [Pi.add_def, Pi.div_def, id_eq, zero_mul, one_mul, zero_sub, neg_div, sub_eq_add_neg, zero_add] using hh.deriv

lemma horizontal_growth_lipschitz {f : ℂ → ℂ} {t D : ℝ}
    (hf : ∀ s : ℂ, 1 ≤ s.re → s.im=t → DifferentiableAt ℂ f s)
    (hb : ∀ s : ℂ, 1 ≤ s.re → s.im=t → ‖s‖+2 ≤ 4*(|t|+2) → ‖deriv f s‖ ≤ D)
    {z w : ℂ} (hz : 1 ≤ z.re) (hw : 1 ≤ w.re) (hzt : z.im=t) (hwt : w.im=t)
    (hzn : ‖z‖+2 ≤ 4*(|t|+2)) (hwn : ‖w‖+2 ≤ 4*(|t|+2)) :
    ‖f z-f w‖ ≤ D*‖z-w‖ := by
  let S := ({s : ℂ | 1 ≤ s.re} ∩ {s : ℂ | s.im=t}) ∩ Metric.closedBall 0 (4*(|t|+2)-2)
  have hi : Convex ℝ {s : ℂ | s.im=t} := convex_hyperplane (.mk Complex.add_im Complex.smul_im) t
  have hS : Convex ℝ S := ((convex_halfSpace_re_ge 1).inter hi).inter (convex_closedBall 0 _)
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s:=S) (fun z hz => hf z hz.1.1 hz.1.2) ?_ hS
    ⟨⟨hw,hwt⟩,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
    ⟨⟨hz,hzt⟩,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
  intro s hs
  exact hb s hs.1.1 hs.1.2 (by have := hs.2; simp only [Metric.mem_closedBall,dist_zero_right] at this; linarith)

lemma zeta_high_line_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ t : ℝ, 1 ≤ |t| →
      (∀ ψ : DirichletCharacter ℂ 1, ∀ s : ℂ, 1 ≤ s.re → ‖s‖+2 ≤ 4*(|t|+2) →
        ‖characterRegular ψ s‖ ≤ K*(|t|+2)^(2*ε)) ∧
      (∀ s : ℂ, 1 ≤ s.re → s.im=t → ‖s‖+2 ≤ 4*(|t|+2) →
        ‖deriv riemannZeta s‖ ≤ K*(|t|+2)^(2*ε)) := by
  obtain ⟨K₀,hK₀,h₀⟩ := character_line_bounds hε hε1
  obtain ⟨K₁,hK₁,h₁⟩ := zetaRegular_bounds hε hε1
  let K := K₀*3^(2*ε)+K₁*4^(2*ε)+1
  have hK₀' : 0 < K₀ := by linarith
  have hK₁' : 0 < K₁ := by linarith
  have hK : 1 ≤ K := by dsimp [K]; linarith [show 0 < K₀*3^(2*ε) by positivity, show 0 < K₁*4^(2*ε) by positivity]
  refine ⟨K,hK,?_⟩
  intro t ht
  have hP : 1 ≤ (|t|+2)^(2*ε) := Real.one_le_rpow (by linarith [abs_nonneg t]) (by positivity)
  constructor
  · intro ψ s hs hn
    have hb := (h₀ 1 ψ t).1 s hs hn
    norm_num only [Nat.cast_one,show (1:ℝ)+2=3 by norm_num] at hb
    rw [Real.mul_rpow (by norm_num) (by positivity)] at hb
    apply hb.trans
    have hc : K₀*3^(2*ε) ≤ K := by dsimp [K]; linarith [show 0 < K₁*4^(2*ε) by positivity]
    convert mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (|t|+2)^(2*ε)) using 1
    ring
  · intro s hs him hn
    have hs1 : s≠1 := by intro h; simp [h] at him; rw [←him] at ht; norm_num at ht
    have hd := (h₁ s (by linarith)).2
    have hden : 1 ≤ ‖s-1‖ := by
      have h := Complex.abs_im_le_norm (s-1)
      simp only [Complex.sub_im,Complex.one_im,sub_zero,him] at h
      exact ht.trans h
    have hfrac : ‖(1:ℂ)/(s-1)^2‖ ≤ 1 := by
      simp only [norm_div,norm_one,norm_pow]
      exact div_le_one_of_le₀ (one_le_pow₀ hden) (by positivity)
    rw [zeta_deriv_eq_regular (by linarith) hs1]
    apply (norm_sub_le _ _).trans
    have hnorm := Real.rpow_le_rpow (by positivity : 0 ≤ ‖s‖+2) hn (by positivity : 0 ≤ 2*ε)
    rw [Real.mul_rpow (by norm_num) (by positivity)] at hnorm
    have hc : K₁*4^(2*ε)+1 ≤ K := by dsimp [K]; linarith [show 0 < K₀*3^(2*ε) by positivity]
    calc
      _ ≤ K₁*(‖s‖+2)^(2*ε)+1 := add_le_add hd hfrac
      _ ≤ (K₁*4^(2*ε))*(|t|+2)^(2*ε)+(|t|+2)^(2*ε) := by nlinarith
      _ = (K₁*4^(2*ε)+1)*(|t|+2)^(2*ε) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

lemma zeta_high_line_lower_aux {t K P : ℝ} (ht : 1 ≤ |t|) (hK : 1 ≤ K) (hP : 1 ≤ P)
    (hr : ∀ ψ : DirichletCharacter ℂ 1, ∀ s : ℂ, 1 ≤ s.re → ‖s‖+2 ≤ 4*(|t|+2) →
      ‖characterRegular ψ s‖ ≤ K*P)
    (hd : ∀ s : ℂ, 1 ≤ s.re → s.im=t → ‖s‖+2 ≤ 4*(|t|+2) → ‖deriv riemannZeta s‖ ≤ K*P) :
    (1/(512*K^7))/P^7 ≤ ‖riemannZeta (1+I*t)‖ := by
  have hK0 : 0 < K := by linarith
  have hP0 : 0 < P := by linarith
  have hKP : 1 ≤ K*P := one_le_mul_of_one_le_of_one_le hK hP
  have hh : 1/(256*(K*P)^6*(2*K*P)) ≤ ‖riemannZeta (1+I*t)‖ := by
    apply three_four_one_lower (norm_nonneg _) hKP (by linarith)
    intro δ hδ hδ1
    have hn0 : ‖(1:ℂ)+I*t‖+2 ≤ 4*(|t|+2) := by
      simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
    have hnδ := line_sample_norm hδ.le hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
    have hL0 : ‖DirichletCharacter.LFunctionTrivChar 1 (1+δ)‖ ≤ 2*(K*P)/δ := by
      have hn : ‖(1:ℂ)+δ‖+2 ≤ 4*(|t|+2) := by
        simpa using line_sample_norm hδ.le hδ1 (t:=t) (u:=0) (by simp)
      have hreg := hr 1 (1+δ) (by simp; linarith) hn
      have hp := LFunction_norm_le_regular_add_pole (1:DirichletCharacter ℂ 1)
        (s:=1+δ) (by simp; linarith)
      have hden : ‖(1:ℂ)+δ-1‖=δ := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
      rw [hden] at hp
      change ‖DirichletCharacter.LFunction (1:DirichletCharacter ℂ 1) (1+δ)‖ ≤ _
      apply (hp.trans (add_le_add hreg le_rfl)).trans
      apply (le_div_iff₀ hδ).mpr
      have hd := mul_le_of_le_one_right (by positivity : 0 ≤ K*P) hδ1
      field_simp
      nlinarith
    have hL1 : ‖riemannZeta (1+δ+I*t)‖ ≤ ‖riemannZeta (1+I*t)‖+(K*P)*δ := by
      have hf (s : ℂ) (_hs : 1 ≤ s.re) (him : s.im=t) : DifferentiableAt ℂ riemannZeta s := by
        apply differentiableAt_riemannZeta
        intro hs
        simp [hs] at him
        rw [←him] at ht
        norm_num at ht
      have hl := horizontal_growth_lipschitz hf hd (z:=1+δ+I*t) (w:=1+I*t)
        (by simp; linarith) (by simp) (by simp) (by simp) hnδ hn0
      have hden : ‖(1:ℂ)+δ+I*t-(1+I*t)‖=δ := by
        rw [show (1:ℂ)+δ+I*t-(1+I*t)=(δ:ℂ) by ring,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
      rw [hden] at hl
      have hh := norm_add_le (riemannZeta (1+δ+I*t)-riemannZeta (1+I*t)) (riemannZeta (1+I*t))
      rw [sub_add_cancel] at hh
      linarith
    have hL2 : ‖riemannZeta (1+δ+2*I*t)‖ ≤ 2*K*P := by
      have hn : ‖(1:ℂ)+δ+2*I*t‖+2 ≤ 4*(|t|+2) := by
        simpa only [show I*((2*t:ℝ):ℂ)=2*I*t by push_cast; ring] using
          line_sample_norm hδ.le hδ1 (t:=t) (u:=2*t) (by rw [abs_mul]; norm_num)
      have hp := LFunction_norm_le_regular_add_pole (1:DirichletCharacter ℂ 1)
        (s:=1+δ+2*I*t) (by simp; linarith)
      rw [DirichletCharacter.LFunction_modOne_eq] at hp
      have hreg := hr 1 (1+δ+2*I*t) (by simp; linarith) hn
      have hden : 1 ≤ ‖(1:ℂ)+δ+2*I*t-1‖ := by
        have hb := Complex.abs_im_le_norm ((1:ℂ)+δ+2*I*t-1)
        simp [abs_mul] at hb
        linarith
      have hfrac : 1/‖(1:ℂ)+δ+2*I*t-1‖ ≤ 1 := div_le_one_of_le₀ hden (norm_nonneg _)
      linarith
    have hprod := (1:DirichletCharacter ℂ 1).norm_LFunction_product_ge_one hδ t
    simp only [one_pow,DirichletCharacter.LFunction_modOne_eq,norm_mul,norm_pow] at hprod
    have hL0' : ‖riemannZeta (1+δ)‖ ≤ 2*(K*P)/δ := by
      simpa only [DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq] using hL0
    exact hprod.trans (by gcongr)
  convert hh using 1
  field_simp
  ring

lemma zeta_high_line_lower {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 1 ≤ |t| →
      c*(|t|+2)^(-ε) ≤ ‖riemannZeta (1+I*t)‖ := by
  obtain ⟨K,hK,hg⟩ := zeta_high_line_bounds (by linarith : 0 < ε/14) (by linarith : ε/14 ≤ 1/2)
  have hK0 : 0 < K := by linarith
  refine ⟨1/(512*K^7),by positivity,?_⟩
  intro t ht
  let P : ℝ := (|t|+2)^(ε/7)
  have hP : 1 ≤ P := Real.one_le_rpow (by linarith [abs_nonneg t]) (by positivity)
  have he : 2*(ε/14)=ε/7 := by ring
  have hh := zeta_high_line_lower_aux ht hK hP
    (fun ψ s hs hn => by simpa only [he] using (hg t ht).1 ψ s hs hn)
    (fun s hs him hn => by simpa only [he] using (hg t ht).2 s hs him hn)
  have hP7 : P^7=(|t|+2)^ε := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast (by positivity : 0 ≤ |t|+2)]
    congr 1
    norm_num
  rw [hP7] at hh
  simpa only [Real.rpow_neg (by positivity : 0 ≤ |t|+2),div_eq_mul_inv] using hh

lemma zeta_high_strip_lower_aux {t c K P δ : ℝ} (ht : 1 ≤ |t|) (hc : 0<c) (hK : 1≤K) (hP : 1≤P)
    (hδ : 0≤δ) (hδ1 : δ≤1)
    (hr : ∀ ψ : DirichletCharacter ℂ 1,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P)
    (hd : ∀ s : ℂ,1 ≤ s.re → s.im=t → ‖s‖+2≤4*(|t|+2) → ‖deriv riemannZeta s‖≤K*P)
    (hl : c/P≤‖riemannZeta (1+I*t)‖) :
    (c/(4*K^2))/P^3≤‖riemannZeta (1+δ+I*t)‖ := by
  have hK0 : 0<K := by linarith
  have hP0 : 0<P := by linarith
  by_cases hnear : δ≤c/(2*K*P^2)
  · have hn0 : ‖(1:ℂ)+I*t‖+2≤4*(|t|+2) := by
      simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
    have hnδ := line_sample_norm hδ hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
    have hf (s : ℂ) (_hs : 1 ≤ s.re) (him : s.im=t) : DifferentiableAt ℂ riemannZeta s := by
      apply differentiableAt_riemannZeta
      intro hs
      simp [hs] at him
      rw [←him] at ht
      norm_num at ht
    have hdif := horizontal_growth_lipschitz hf hd
      (z:=1+I*t) (w:=1+δ+I*t) (by simp) (by simp; linarith) (by simp) (by simp) hn0 hnδ
    have hnorm : ‖(1:ℂ)+I*t-(1+δ+I*t)‖=δ := by
      rw [show (1:ℂ)+I*t-(1+δ+I*t)=-(δ:ℂ) by ring,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hδ]
    rw [hnorm] at hdif
    have hdb : ‖riemannZeta (1+I*t)-riemannZeta (1+δ+I*t)‖≤c/(2*P) := by
      apply hdif.trans
      calc
        K*P*δ ≤ K*P*(c/(2*K*P^2)) := mul_le_mul_of_nonneg_left hnear (by positivity)
        _ = _ := by field_simp
    have htri := norm_add_le (riemannZeta (1+I*t)-riemannZeta (1+δ+I*t)) (riemannZeta (1+δ+I*t))
    rw [sub_add_cancel] at htri
    have hva : c/(2*P)≤‖riemannZeta (1+δ+I*t)‖ := by
      have he : c/P=2*(c/(2*P)) := by ring
      rw [he] at hl
      linarith
    apply le_trans ?_ hva
    rw [div_div]
    apply div_le_div_of_nonneg_left hc.le (by positivity)
    have hP3 : P≤P^3 := by simpa using pow_le_pow_right₀ hP (show (1:ℕ)≤3 by norm_num)
    have hK2 : 1≤K^2 := one_le_pow₀ hK
    nlinarith [mul_le_mul_of_nonneg_left hP3 (show (0:ℝ)≤4*K^2 by positivity)]
  · have hδ0 : 0<δ := (by positivity : 0<c/(2*K*P^2)).trans (lt_of_not_ge hnear)
    have hInt := character_interior_lower (1:DirichletCharacter ℂ 1) hK hP hδ0 hδ1 hr
    rw [DirichletCharacter.LFunction_modOne_eq] at hInt
    apply le_trans ?_ hInt
    calc
      (c/(4*K^2))/P^3 = (c/(2*K*P^2))/(2*K*P) := by field_simp; norm_num
      _ ≤ δ/(2*K*P) := div_le_div_of_nonneg_right (le_of_not_ge hnear) (by positivity)

lemma zeta_high_strip_lower {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ,0<c ∧ ∀ σ t : ℝ, 1≤σ → σ≤2 → 1 ≤ |t| →
        c*(|t|+2)^(-ε)≤‖riemannZeta (σ+I*t)‖ := by
  obtain ⟨K,hK,hg⟩ := zeta_high_line_bounds (by linarith : 0<ε/6) (by linarith : ε/6≤1/2)
  obtain ⟨c,hc,hl⟩ := zeta_high_line_lower (by linarith : 0<ε/3) (by linarith : ε/3≤1)
  have hK0 : 0<K := by linarith
  refine ⟨c/(4*K^2),by positivity,?_⟩
  intro σ t hσ hσ2 ht
  let X : ℝ := (|t|+2)
  let P : ℝ := X^(ε/3)
  have hX : 1≤X := by dsimp [X]; linarith [abs_nonneg t]
  have hX0 : 0<X := by linarith
  have hP : 1≤P := Real.one_le_rpow hX (by positivity)
  have he : 2*(ε/6)=ε/3 := by ring
  have hl' : c/P≤‖riemannZeta (1+I*t)‖ := by
    have hh := hl t ht
    change c*X^(-(ε/3))≤_ at hh
    change c/X^(ε/3)≤_
    simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hh
  have hb := zeta_high_strip_lower_aux ht hc hK hP (δ:=σ-1) (by linarith) (by linarith)
    (fun ψ s hs hn => by simpa only [he] using (hg t ht).1 ψ s hs hn)
    (fun s hs him hn => by simpa only [he] using (hg t ht).2 s hs him hn) hl'
  have hP3 : P^3=X^ε := by dsimp [P]; rw [←Real.rpow_mul_natCast hX0.le]; congr 1; norm_num
  rw [hP3] at hb
  have hs : (1:ℂ)+((σ-1:ℝ):ℂ)+I*t=(σ:ℂ)+I*t := by push_cast; ring
  rw [hs] at hb
  change (c/(4*K^2))*X^(-ε)≤_
  simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hb

lemma principal_deriv_eq_regular {s : ℂ} (hs : 0 < s.re) :
    deriv (poleRemovedL (1:DirichletCharacter ℂ 1)) s = zetaRegular s+(s-1)*deriv zetaRegular s := by
  have he : poleRemovedL (1:DirichletCharacter ℂ 1) =ᶠ[𝓝 s] (fun z => (z-1)*zetaRegular z+1) := by
    filter_upwards [(continuous_re.tendsto s).eventually (lt_mem_nhds hs)] with z hz
    simpa only [poleRemovedL,ite_true] using poleRemovedZeta_eq hz
  have hh := (((hasDerivAt_id s).sub_const 1).mul (zetaRegular_differentiableAt hs).hasDerivAt).add_const 1
  rw [he.deriv_eq]
  simpa only [id_eq,one_mul,Pi.mul_apply] using hh.deriv

lemma principal_deriv_growth {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, 1-ε/4 ≤ s.re →
      ‖deriv (poleRemovedL (1:DirichletCharacter ℂ 1)) s‖ ≤ K*(‖s‖+2)*(‖s‖+2)^ε := by
  obtain ⟨K,hK,hb⟩ := zetaRegular_bounds (by linarith : 0 < ε/2) (by linarith : ε/2 ≤ 1/2)
  have hK0 : 0 < K := by linarith
  refine ⟨K,hK0,?_⟩
  intro s hs
  obtain ⟨hl,hd⟩ := hb s (by linarith)
  rw [show 2*(ε/2)=ε by ring] at hl hd
  rw [principal_deriv_eq_regular (by linarith)]
  have hn : ‖s-1‖ ≤ ‖s‖+1 := by simpa using norm_sub_le s 1
  calc
    _ ≤ ‖zetaRegular s‖+‖s-1‖*‖deriv zetaRegular s‖ := by
      apply (norm_add_le _ _).trans_eq
      rw [norm_mul]
    _ ≤ K*(‖s‖+2)^ε+(‖s‖+1)*(K*(‖s‖+2)^ε) := by gcongr
    _ = _ := by ring

lemma principal_strip_lower {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
      c*(|t|+2)/((|t|+2)^ε) ≤ ‖poleRemovedL (1:DirichletCharacter ℂ 1) (σ+I*t)‖ := by
  obtain ⟨c₀,hc₀,hl⟩ := zeta_high_strip_lower hε hε1
  let F := poleRemovedL (1:DirichletCharacter ℂ 1)
  let S : Set ℂ := (fun p : ℝ×ℝ => (p.1:ℂ)+I*p.2) '' (Set.Icc 1 2 ×ˢ Set.Icc (-1) 1)
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hmem (z : ℂ) : z∈S ↔ 1 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ 1 := by
    constructor
    · rintro ⟨⟨u,v⟩,⟨hu,hv⟩,rfl⟩
      simpa [abs_le,and_assoc] using And.intro hu hv
    · rintro ⟨h₁,h₂,h₃⟩
      refine ⟨(z.re,z.im),⟨⟨h₁,h₂⟩,abs_le.mp h₃⟩,?_⟩
      simpa only [mul_comm] using Complex.re_add_im z
  have hc : ContinuousOn (fun z => (F z)⁻¹) S := by
    intro z hz
    exact (((poleRemovedL_differentiable 1).continuous.continuousAt).inv₀
      (poleRemovedL_ne_zero 1 ((hmem z).mp hz).1)).continuousWithinAt
  obtain ⟨M,hM⟩ := hS.exists_bound_of_continuousOn hc
  let D := max M 1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let c := min (c₀/3) (1/(3*D))
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c,hc,?_⟩
  intro σ t hσ hσ2
  let z : ℂ := (σ:ℂ)+I*t
  have hz : 1 ≤ z.re := by simpa [z] using hσ
  have hT : 1 ≤ |t|+2 := by linarith [abs_nonneg t]
  have hP : 1 ≤ (|t|+2)^ε := Real.one_le_rpow hT hε.le
  by_cases ht : 1 ≤ |t|
  · have hz1 : z≠1 := by intro hh; have hi := congrArg Complex.im hh; simp [z] at hi; simp [hi] at ht; norm_num at ht
    have he : F z=(z-1)*riemannZeta z := by
      simp only [F,poleRemovedL,ite_true,DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hz1,
        DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq]
    have hnorm : (|t|+2)/3 ≤ ‖z-1‖ := by
      have hi := Complex.abs_im_le_norm (z-1)
      simp [z] at hi
      linarith
    have hlow := hl σ t hσ hσ2 ht
    rw [Real.rpow_neg (by positivity : 0 ≤ |t|+2),←div_eq_mul_inv] at hlow
    change c*(|t|+2)/( |t|+2)^ε ≤ ‖F z‖
    rw [he,norm_mul]
    calc
      _ ≤ (c₀/3)*(|t|+2)/(|t|+2)^ε := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)) (by positivity)
      _ = ((|t|+2)/3)*(c₀/(|t|+2)^ε) := by ring
      _ ≤ _ := mul_le_mul hnorm hlow (by positivity) (norm_nonneg _)
  · have ht1 : |t| ≤ 1 := le_of_not_ge ht
    have hzS : z∈S := (hmem z).mpr ⟨hz,by simpa [z] using hσ2,by simpa [z] using ht1⟩
    have hb := (hM z hzS).trans (le_max_left M 1)
    have hn : 0 < ‖F z‖ := norm_pos_iff.mpr (poleRemovedL_ne_zero 1 hz)
    rw [norm_inv,inv_eq_one_div] at hb
    have hlow : 1/D ≤ ‖F z‖ := by
      apply (div_le_iff₀ hD).mpr
      have hh := (div_le_iff₀ hn).mp hb
      nlinarith
    change c*(|t|+2)/(|t|+2)^ε ≤ ‖F z‖
    apply le_trans ?_ hlow
    calc
      _ ≤ c*(|t|+2) := div_le_self (by positivity) hP
      _ ≤ (1/(3*D))*3 := mul_le_mul (min_le_right _ _) (by linarith) (by positivity) (by positivity)
      _ = 1/D := by ring

end LargePrimeGaps
end OAI

-- Source module: RieszBounds
namespace OAI
namespace LargePrimeGaps
open Complex Filter Topology
noncomputable def logRiesz (f : ℂ → ℂ) (s : ℂ) : ℂ := (-deriv f s / f s)/(s*(s+1))

lemma near_line_denominator {z w : ℂ} {r : ℝ} (hz : 1 ≤  z.re) (hr : r ≤ 1/4)
    (hw : w∈Metric.closedBall z r) :
    w≠0 ∧ w+1≠0 ∧ (|z.im|+2)^2 ≤ 16*‖w‖*‖w+1‖ := by
  have hd : ‖w-z‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
  have hre := Complex.re_le_norm (z-w)
  rw [Complex.sub_re,norm_sub_rev] at hre
  have hwre : 3/4 ≤ w.re := by linarith
  have hw0 : w≠0 := by intro h; simp [h] at hwre; norm_num at hwre
  have hw1 : w+1≠0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hna : 3/4 ≤ ‖w‖ := hwre.trans (Complex.re_le_norm w)
  have hnb : 3/4 ≤ ‖w+1‖ := by
    have h := Complex.re_le_norm (w+1)
    simp only [Complex.add_re,Complex.one_re] at h
    linarith
  have ha : |z.im| ≤ ‖w‖+r := by
    have ht := norm_add_le (z-w) w
    rw [sub_add_cancel,norm_sub_rev] at ht
    linarith [Complex.abs_im_le_norm z]
  have hb : |z.im| ≤ ‖w+1‖+r := by
    have ht := norm_add_le (z-w) (w+1)
    rw [show z-w+(w+1)=z+1 by ring,norm_sub_rev] at ht
    have hi := Complex.abs_im_le_norm (z+1)
    simp only [Complex.add_im,Complex.one_im,add_zero] at hi
    linarith
  have ha' : |z.im|+2 ≤ 4*‖w‖ := by linarith
  have hb' : |z.im|+2 ≤ 4*‖w+1‖ := by linarith
  refine ⟨hw0,hw1,?_⟩
  have hp := mul_le_mul ha' hb' (by positivity : 0 ≤ |z.im|+2) (by positivity : 0 ≤ 4*‖w‖)
  nlinarith

lemma logRiesz_local {f : ℂ → ℂ} {z : ℂ} {r m M : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1/4) (hm : 0 < m) (hM : 0 ≤ M) (hz : 1 ≤  z.re)
    (hf : ∀ w∈Metric.closedBall z r,AnalyticAt ℂ f w)
    (hb : ∀ w∈Metric.closedBall z r,‖deriv f w‖ ≤ M)
    (hl : m ≤ ‖f z‖) (hMr : M*r ≤ m/2) :
    (∀ w∈Metric.closedBall z r,f w≠0) ∧
      DiffContOnCl ℂ (logRiesz f) (Metric.ball z r) ∧
      ∀ w∈Metric.closedBall z r,‖logRiesz f w‖ ≤ (32*M/m)/(|z.im|+2)^2 := by
  have hmem : z∈Metric.closedBall z r := Metric.mem_closedBall_self hr.le
  have hlo (w : ℂ) (hw : w∈Metric.closedBall z r) : m/2 ≤ ‖f w‖ := by
    have hd := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun w hw => (hf w hw).differentiableAt) hb (convex_closedBall z r) hw hmem
    have hdist : ‖z-w‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hw
    have hd' := hd.trans (mul_le_mul_of_nonneg_left hdist hM)
    have ht := norm_add_le (f z-f w) (f w)
    rw [sub_add_cancel] at ht
    linarith
  have hne (w : ℂ) (hw : w∈Metric.closedBall z r) : f w≠0 := by
    exact norm_pos_iff.mp ((by positivity : 0 < m/2).trans_le (hlo w hw))
  refine ⟨hne,?_,?_⟩
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    intro w hw
    obtain ⟨hw0,hw1,_⟩ := near_line_denominator hz hr1 hw
    exact (((hf w hw).deriv.neg.div (hf w hw) (hne w hw)).div
      (analyticAt_id.mul (analyticAt_id.add analyticAt_const)) (mul_ne_zero hw0 hw1)).differentiableWithinAt
  · intro w hw
    obtain ⟨hw0,hw1,hden⟩ := near_line_denominator hz hr1 hw
    have hnorm : 0 < ‖w‖*‖w+1‖ := mul_pos (norm_pos_iff.mpr hw0) (norm_pos_iff.mpr hw1)
    have hb₀ : ‖deriv f w‖/‖f w‖ ≤ 2*M/m := by
      apply (div_le_div₀ hM (hb w hw) (by positivity : 0 < m/2) (hlo w hw)).trans_eq
      ring
    have hb₁ : 1/(‖w‖*‖w+1‖) ≤ 16/(|z.im|+2)^2 := by
      apply (div_le_div_iff₀ hnorm (by positivity)).mpr
      nlinarith
    simp only [logRiesz,norm_div,norm_neg,norm_mul]
    calc
      _ = (‖deriv f w‖/‖f w‖)*(1/(‖w‖*‖w+1‖)) := by ring
      _  ≤  (2*M/m)*(16/(|z.im|+2)^2) := mul_le_mul hb₀ hb₁ (by positivity) (by positivity)
      _ = _ := by ring

lemma logRiesz_iteratedDeriv_bound {f : ℂ → ℂ} {z : ℂ} {r m M : ℝ}
    (n : ℕ) (hr : 0 < r) (hr1 : r ≤ 1/4) (hm : 0 < m) (hM : 0 ≤ M) (hz : 1 ≤  z.re)
    (hf : ∀ w∈Metric.closedBall z r,AnalyticAt ℂ f w)
    (hb : ∀ w∈Metric.closedBall z r,‖deriv f w‖ ≤ M)
    (hl : m ≤ ‖f z‖) (hMr : M*r ≤ m/2) :
    ‖iteratedDeriv n (logRiesz f) z‖ ≤ (n.factorial:ℝ)*((32*M/m)/(|z.im|+2)^2)/r^n := by
  have hh := logRiesz_local hr hr1 hm hM hz hf hb hl hMr
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hh.2.1
    (fun w hw => hh.2.2 w (Metric.sphere_subset_closedBall hw))

lemma logRiesz_power_bound {f : ℂ → ℂ} {z : ℂ} {P W c K d : ℝ} (n : ℕ)
    (hP : 1 ≤ P) (hW : 0 < W) (hc : 0 < c) (hK : 0 < K) (hd : 0 < d)
    (hd1 : d ≤ 1/4) (hKd : K*d ≤ c/2) (hz : 1 ≤ z.re)
    (hf : ∀ w∈Metric.closedBall z (d/P^2), AnalyticAt ℂ f w)
    (hb : ∀ w∈Metric.closedBall z (d/P^2), ‖deriv f w‖ ≤ K*W*P)
    (hl : c*W/P ≤ ‖f z‖) :
    ‖iteratedDeriv n (logRiesz f) z‖ ≤
      ((n.factorial:ℝ)*(32*K/c)/d^n)*P^(2*n+2)/(|z.im|+2)^2 := by
  have hP0 : 0 < P := by linarith
  have hr1 : d/P^2 ≤ 1/4 := by
    apply (div_le_self hd.le (one_le_pow₀ hP)).trans hd1
  have hMr : (K*W*P)*(d/P^2) ≤ (c*W/P)/2 := by
    calc
      _ = (K*d)*W/P := by field_simp
      _ ≤ (c/2)*W/P := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hKd hW.le) hP0.le
      _ = _ := by ring
  have hh := logRiesz_iteratedDeriv_bound n (by positivity : 0 < d/P^2) hr1
    (by positivity : 0 < c*W/P) (by positivity : 0 ≤ K*W*P) hz hf hb hl hMr
  apply hh.trans_eq
  rw [div_pow,pow_add,pow_mul]
  field_simp

lemma near_strip_geometry {σ t d P η : ℝ} (hσ : 1 ≤ σ) (hσ2 : σ ≤ 2)
    (hP : 1 ≤ P) (hd : 0 ≤ d) (hd1 : d ≤ 1/4) (hdη : d ≤ η/4)
    {w : ℂ} (hw : w∈Metric.closedBall ((σ:ℂ)+I*t) (d/P^2)) :
    1-η/4 ≤ w.re ∧ ‖w‖+2 ≤ 3*(|t|+2) := by
  have hr : d/P^2 ≤ d := div_le_self hd (one_le_pow₀ hP)
  have hdist : ‖w-((σ:ℂ)+I*t)‖ ≤ d/P^2 := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
  have hre := Complex.re_le_norm (((σ:ℂ)+I*t)-w)
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.I_re,Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_self,add_zero,norm_sub_rev] at hre
  have hnorm := norm_add_le (w-((σ:ℂ)+I*t)) ((σ:ℂ)+I*t)
  rw [sub_add_cancel] at hnorm
  have hnz := Complex.norm_le_abs_re_add_abs_im ((σ:ℂ)+I*t)
  simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,
    one_mul,sub_self,zero_add,add_zero,abs_of_nonneg (by linarith : 0 ≤ σ)] at hnz
  constructor <;> linarith [abs_nonneg t]

lemma nonprincipal_logRiesz_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
        ‖iteratedDeriv n (logRiesz χ.LFunction) (σ+I*t)‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*(|t|+2)^(-(3/2:ℝ)) := by
  let ε : ℝ := 1/(4*(n+1:ℕ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    apply (div_le_one (by positivity : 0 < 4*((n+1:ℕ):ℝ))).mpr
    have hn : (1:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast (Nat.succ_pos n)
    linarith
  obtain ⟨c,hc,hl⟩ := nonprincipal_strip_lower hε hε1
  obtain ⟨K₀,hK₀,hb⟩ := LFunction_deriv_norm_small_power (by linarith : 0 < ε/2) (by linarith : ε/2 ≤ 1/2)
  let K := K₀*3^ε
  have hK : 0 < K := by dsimp [K]; positivity
  let d := min (min (1/4) (ε/4)) (c/(2*K))
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1/4 := (min_le_left _ _).trans (min_le_left _ _)
  have hdε : d ≤ ε/4 := (min_le_left _ _).trans (min_le_right _ _)
  have hKd : K*d ≤ c/2 := by
    have h := min_le_right (min (1/4) (ε/4)) (c/(2*K))
    change d ≤ c/(2*K) at h
    have hh := mul_le_mul_of_nonneg_left h hK.le
    have he : K*(c/(2*K))=c/2 := by field_simp
    rwa [he] at hh
  let D := (n.factorial:ℝ)*(32*K/c)/d^n
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro q _ χ hχp hχ σ t hσ hσ2
  let X : ℝ := ((q:ℝ)+2)*(|t|+2)
  let P : ℝ := X^ε
  have hX : 1 ≤ X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
  have hX0 : 0 < X := by linarith
  have hP : 1 ≤ P := Real.one_le_rpow hX hε.le
  have hlow : c*1/P ≤ ‖χ.LFunction (σ+I*t)‖ := by
    have h := hl q χ hχp hχ σ t hσ hσ2
    change c*X^(-ε) ≤ _ at h
    simpa only [mul_one,Real.rpow_neg hX0.le,div_eq_mul_inv] using h
  have hbound : ∀ w∈Metric.closedBall ((σ:ℂ)+I*t) (d/P^2), ‖deriv χ.LFunction w‖ ≤ K*1*P := by
    intro w hw
    obtain ⟨hre,hnorm⟩ := near_strip_geometry hσ hσ2 hP hd.le hd1 hdε hw
    have h := hb q χ hχ w (by linarith)
    rw [show 2*(ε/2)=ε by ring] at h
    have hn : ((q:ℝ)+2)*(‖w‖+2) ≤ 3*X := by
      dsimp [X]
      nlinarith [mul_nonneg (show (0:ℝ) ≤ q+2 by positivity) (sub_nonneg.mpr hnorm)]
    calc
      _ ≤ K₀*((q+2)*(‖w‖+2))^ε := h
      _ ≤ K₀*(3*X)^ε := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hn hε.le) hK₀.le
      _ = K*1*P := by rw [Real.mul_rpow (by norm_num) hX0.le]; dsimp [K,P]; ring
  have hh := logRiesz_power_bound n hP zero_lt_one hc hK hd hd1 hKd (by simpa using hσ)
    (fun w _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt w) hbound hlow
  have he : ε*(2*n+2:ℕ)=1/2 := by
    dsimp [ε]
    push_cast
    field_simp
    ring
  have hpow : P^(2*n+2)=X^(1/2:ℝ) := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast hX0.le,he]
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_add] at hh
  change ‖iteratedDeriv n (logRiesz χ.LFunction) (σ+I*t)‖ ≤ D*P^(2*n+2)/(|t|+2)^2 at hh
  rw [hpow] at hh
  apply hh.trans_eq
  dsimp [X]
  rw [Real.mul_rpow (by positivity) (by positivity),Real.rpow_neg (by positivity : 0 ≤ |t|+2)]
  have ht : (|t|+2)^(1/2:ℝ)*(|t|+2)^(3/2:ℝ)=(|t|+2)^2 := by
    rw [←Real.rpow_add (by positivity),show (1/2:ℝ)+3/2=2 by norm_num]
    norm_num
  field_simp
  rw [←ht]

end LargePrimeGaps
end OAI

-- Source module: MellinSmoothing
namespace OAI
namespace LargePrimeGaps
open Complex Real Set MeasureTheory Filter Topology
noncomputable def rieszKernel : ℝ → ℂ := (Ioc 0 1).indicator (fun t => 1-(t:ℂ))

lemma hasMellin_rieszKernel {s : ℂ} (hs : 0<s.re) :
    HasMellin rieszKernel s (1/(s*(s+1))) := by
  have h₀ := hasMellin_one_Ioc hs
  have h₁ := hasMellin_cpow_Ioc 1 (by simp; linarith : 0<s.re+(1:ℂ).re)
  have hh := hasMellin_sub h₀.1 h₁.1
  rw [h₀.2,h₁.2] at hh
  have he : (fun t : ℝ => (Ioc 0 1).indicator (fun _ : ℝ => (1:ℂ)) t-
      (Ioc 0 1).indicator (fun t : ℝ => (t:ℂ)^(1:ℂ)) t)=rieszKernel := by
    ext t
    by_cases ht : t∈Ioc (0:ℝ) 1 <;> simp [rieszKernel,ht]
  rw [he] at hh
  have hs0 : s≠0 := by intro h; simp [h] at hs
  have hs1 : s+1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have heval : 1/s-1/(s+1)=1/(s*(s+1)) := by field_simp; ring
  rwa [heval] at hh

lemma rieszKernel_eq_max {x : ℝ} (hx : 0<x) : rieszKernel x=(max (1-x) 0:ℝ) := by
  by_cases hx1 : x≤1
  · simp [rieszKernel,Set.mem_Ioc,hx,hx1]
  · simp [rieszKernel,Set.mem_Ioc,hx,hx1,max_eq_right (by linarith : 1-x≤(0:ℝ))]

lemma rieszKernel_continuousAt {x : ℝ} (hx : 0<x) : ContinuousAt rieszKernel x := by
  have he : rieszKernel =ᶠ[𝓝 x] (fun x : ℝ => ((max (1-x) 0:ℝ):ℂ)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact rieszKernel_eq_max hy
  exact (show ContinuousAt (fun x : ℝ => ((max (1-x) 0:ℝ):ℂ)) x by fun_prop).congr he.symm

lemma rieszDenominator_bound {s : ℂ} (hs : 1≤ s.re) :
    ‖1/(s*(s+1))‖≤2/(1+s.im^2) := by
  have ha : 1≤‖s‖ := hs.trans (Complex.re_le_norm s)
  have hb : 1≤‖s+1‖ := by have h := Complex.re_le_norm (s+1); simp at h; linarith
  have hai : |s.im|≤‖s‖ := Complex.abs_im_le_norm s
  have hbi : |s.im|≤‖s+1‖ := by simpa using Complex.abs_im_le_norm (s+1)
  have hp : 1≤‖s‖*‖s+1‖ := one_le_mul_of_one_le_of_one_le ha hb
  have hpi : s.im^2≤‖s‖*‖s+1‖ := by
    simpa only [←sq, sq_abs] using mul_le_mul hai hbi (abs_nonneg _) (norm_nonneg _)
  rw [norm_div,norm_one,norm_mul]
  apply (div_le_div_iff₀ (by positivity : 0<‖s‖*‖s+1‖) (by positivity : 0<1+s.im^2)).mpr
  nlinarith

set_option maxHeartbeats 800000 in
lemma rieszDenominator_verticalIntegrable {σ : ℝ} (hσ : 1≤σ) :
    VerticalIntegrable (fun s : ℂ => 1/(s*(s+1))) σ := by
  have hne (t : ℝ) : (σ:ℂ)+(t:ℂ)*I≠0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hne1 (t : ℝ) : (σ:ℂ)+(t:ℂ)*I+1≠0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hm : Continuous (fun t : ℝ => 1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro t
    exact mul_ne_zero (hne t) (hne1 t)
  apply (integrable_inv_one_add_sq.const_mul 2).mono' hm.aestronglyMeasurable
  filter_upwards [] with t
  have hb := rieszDenominator_bound (s:=(σ:ℂ)+t*I) (by simpa using hσ)
  simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,mul_zero,
    Complex.ofReal_re,Complex.I_im,mul_one,add_zero,zero_add,div_eq_mul_inv] using hb

lemma rieszKernel_mellinInv {σ x : ℝ} (hσ : 1≤σ) (hx : 0<x) :
    mellinInv σ (fun s : ℂ => 1/(s*(s+1))) x=rieszKernel x := by
  have hσ0 : (0:ℝ)<σ := by linarith
  have hm (t : ℝ) : mellin rieszKernel (σ+t*I)=1/((σ+t*I)*(σ+t*I+1)) :=
    (hasMellin_rieszKernel (by simpa using hσ0)).2
  have hF : VerticalIntegrable (mellin rieszKernel) σ := by
    unfold VerticalIntegrable
    simp_rw [hm]
    exact rieszDenominator_verticalIntegrable hσ
  rw [←mellinInv_mellin_eq σ rieszKernel hx (hasMellin_rieszKernel (by simpa using hσ0)).1 hF
    (rieszKernel_continuousAt hx)]
  simp only [mellinInv,hm]

open Complex Filter Topology
lemma principal_logRiesz_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
        ‖iteratedDeriv n (logRiesz (poleRemovedL (1:DirichletCharacter ℂ 1))) (σ+I*t)‖ ≤
          D*(|t|+2)^(-(3/2:ℝ)) := by
  let ε : ℝ := 1/(4*(n+1:ℕ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    apply (div_le_one (by positivity : 0 < 4*((n+1:ℕ):ℝ))).mpr
    have hn : (1:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast (Nat.succ_pos n)
    linarith
  obtain ⟨c,hc,hl⟩ := principal_strip_lower hε hε1
  obtain ⟨K₀,hK₀,hb⟩ := principal_deriv_growth hε hε1
  let K := 3*K₀*3^ε
  have hK : 0 < K := by dsimp [K]; positivity
  let d := min (min (1/4) (ε/4)) (c/(2*K))
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1/4 := (min_le_left _ _).trans (min_le_left _ _)
  have hdε : d ≤ ε/4 := (min_le_left _ _).trans (min_le_right _ _)
  have hKd : K*d ≤ c/2 := by
    have h := min_le_right (min (1/4) (ε/4)) (c/(2*K))
    change d ≤ c/(2*K) at h
    have hh := mul_le_mul_of_nonneg_left h hK.le
    have he : K*(c/(2*K))=c/2 := by field_simp
    rwa [he] at hh
  let D := (n.factorial:ℝ)*(32*K/c)/d^n
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro σ t hσ hσ2
  let X : ℝ := (|t|+2)
  let P : ℝ := X^ε
  have hX : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg t]
  have hX0 : 0 < X := by linarith
  have hP : 1 ≤ P := Real.one_le_rpow hX hε.le
  have hlow : c*(|t|+2)/P ≤ ‖poleRemovedL (1:DirichletCharacter ℂ 1) (σ+I*t)‖ := hl σ t hσ hσ2
  have hbound : ∀ w∈Metric.closedBall ((σ:ℂ)+I*t) (d/P^2),
      ‖deriv (poleRemovedL (1:DirichletCharacter ℂ 1)) w‖ ≤ K*(|t|+2)*P := by
    intro w hw
    obtain ⟨hre,hnorm⟩ := near_strip_geometry hσ hσ2 hP hd.le hd1 hdε hw
    have h := hb w hre
    calc
      _ ≤ K₀*(‖w‖+2)*(‖w‖+2)^ε := h
      _ ≤ K₀*(3*X)*(3*X)^ε := by gcongr
      _ = K*(|t|+2)*P := by rw [Real.mul_rpow (by norm_num) hX0.le]; dsimp [K,P,X]; ring
  have hh := logRiesz_power_bound n hP (by positivity : 0 < |t|+2) hc hK hd hd1 hKd (by simpa using hσ)
    (fun w _ => (poleRemovedL_differentiable (1:DirichletCharacter ℂ 1)).analyticAt w) hbound hlow
  have he : ε*(2*n+2:ℕ)=1/2 := by
    dsimp [ε]
    push_cast
    field_simp
    ring
  have hpow : P^(2*n+2)=X^(1/2:ℝ) := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast hX0.le,he]
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_add] at hh
  change ‖iteratedDeriv n (logRiesz (poleRemovedL (1:DirichletCharacter ℂ 1))) (σ+I*t)‖ ≤ D*P^(2*n+2)/(|t|+2)^2 at hh
  rw [hpow] at hh
  apply hh.trans_eq
  dsimp [X]
  rw [Real.rpow_neg (by positivity : 0 ≤ |t|+2)]
  have ht : (|t|+2)^(1/2:ℝ)*(|t|+2)^(3/2:ℝ)=(|t|+2)^2 := by
    rw [←Real.rpow_add (by positivity),show (1/2:ℝ)+3/2=2 by norm_num]
    norm_num
  field_simp
  rw [←ht]

lemma primitive_logRiesz_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
        ‖iteratedDeriv n (logRiesz (poleRemovedL χ)) (σ+I*t)‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*(|t|+2)^(-(3/2:ℝ)) := by
  obtain ⟨D₀,hD₀,h₀⟩ := nonprincipal_logRiesz_bound n
  obtain ⟨D₁,hD₁,h₁⟩ := principal_logRiesz_bound n
  refine ⟨max D₀ D₁,lt_of_lt_of_le hD₀ (le_max_left _ _),?_⟩
  intro q _ χ hχp σ t hσ hσ2
  have hq : 1 ≤ ((q:ℝ)+2)^(1/2:ℝ) := Real.one_le_rpow (by linarith [Nat.cast_nonneg (α:=ℝ) q]) (by norm_num)
  by_cases hχ : χ=1
  · subst χ
    have hq1 : q=1 := by simpa [DirichletCharacter.IsPrimitive,DirichletCharacter.conductor_one] using hχp.symm
    subst q
    have hq' : 1 ≤ ((1:ℝ)+2)^(1/2:ℝ) := by simpa only [Nat.cast_one] using hq
    have hb := h₁ σ t hσ hσ2
    apply hb.trans
    have hc : D₁ ≤ max D₀ D₁*((1:ℝ)+2)^(1/2:ℝ) := by
      calc
        D₁ ≤ max D₀ D₁ := le_max_right _ _
        _ ≤ _ := le_mul_of_one_le_right (le_trans hD₀.le (le_max_left _ _)) hq'
    simpa only [Nat.cast_one] using mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (|t|+2)^(-(3/2:ℝ)))
  · have hb := h₀ q χ hχp hχ σ t hσ hσ2
    simp only [poleRemovedL,hχ,ite_false]
    apply hb.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)

lemma logRiesz_poleRemoved_analyticAt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 ≤ s.re) : AnalyticAt ℂ (logRiesz (poleRemovedL χ)) s := by
  have h₀ : s≠0 := by intro h; simp [h] at hs; norm_num at hs
  have h₁ : s+1≠0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  exact (primeLogDerivativeRegular_analyticAt χ (poleRemovedL_ne_zero χ hs)).div
    (analyticAt_id.mul (analyticAt_id.add analyticAt_const)) (mul_ne_zero h₀ h₁)

open Complex Filter Topology MeasureTheory
open scoped FourierTransform
lemma analyticAt_iteratedDeriv_local {f : ℂ → ℂ} {z : ℂ} (h : AnalyticAt ℂ f z) (n : ℕ) :
    AnalyticAt ℂ (iteratedDeriv n f) z := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

lemma vertical_contDiff {f : ℂ → ℂ} {z a : ℂ}
    (hf : ∀ t : ℝ, AnalyticAt ℂ f (z+a*t)) :
    ContDiff ℝ ⊤ (fun t : ℝ => f (z+a*t)) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hr : ContDiffAt ℝ ⊤ (fun t : ℝ => (t:ℂ)) t := Complex.ofRealCLM.contDiff.contDiffAt
  exact ((hf t).contDiffAt.restrict_scalars ℝ).comp t
    (contDiffAt_const.add (contDiffAt_const.mul hr))

lemma vertical_iteratedDeriv {f : ℂ → ℂ} {z a : ℂ}
    (hf : ∀ t : ℝ, AnalyticAt ℂ f (z+a*t)) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => f (z+a*t)) =
      fun t : ℝ => a^n * iteratedDeriv n f (z+a*t) := by
  induction n with
  | zero => ext t; simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    have ha : HasDerivAt (fun t : ℝ => z+a*t) a t := by
      convert (((hasDerivAt_id (t:ℂ)).const_mul a).const_add z).comp_ofReal using 1 <;> simp
    have hd := ((analyticAt_iteratedDeriv_local (hf t) n).differentiableAt.hasDerivAt.comp t ha).const_mul (a^n)
    rw [iteratedDeriv_succ]
    simpa only [Function.comp_def,pow_succ,mul_assoc,mul_comm,mul_left_comm] using hd.deriv

noncomputable def decayMajorant (t : ℝ) : ℝ := (1+|t|)^(-(3/2:ℝ))

lemma decayMajorant_integrable : Integrable decayMajorant := by
  change Integrable (fun t : ℝ => (1+|t|)^(-(3/2:ℝ)))
  simpa only [Real.norm_eq_abs] using
    (integrable_one_add_norm (E:=ℝ) (by norm_num : (Module.finrank ℝ ℝ:ℝ) < 3/2))

lemma integrable_of_decay_bound {g : ℝ → ℂ} {M : ℝ} (hg : Continuous g)
    (hb : ∀ t, ‖g t‖ ≤ M*decayMajorant t) : Integrable g := by
  exact (decayMajorant_integrable.const_mul M).mono' hg.aestronglyMeasurable (Filter.Eventually.of_forall hb)

lemma integral_norm_le_of_decay_bound {g : ℝ → ℂ} {M : ℝ} (hg : Continuous g)
    (hb : ∀ t, ‖g t‖ ≤ M*decayMajorant t) :
    ∫ t, ‖g t‖ ≤ M*(∫ t, decayMajorant t) := by
  rw [←integral_const_mul]
  exact integral_mono (integrable_of_decay_bound hg hb).norm
    (decayMajorant_integrable.const_mul M) hb

lemma fourierInv_decay {g : ℝ → ℂ} (hg : ContDiff ℝ ⊤ g)
    (hi : ∀ n : ℕ, Integrable (iteratedDeriv n g)) (n : ℕ) {M u : ℝ}
    (hb : (∫ t, ‖iteratedDeriv n g t‖) ≤ M) (hu : 0 < |u|) :
    ‖𝓕⁻ g u‖ ≤ M/|u|^n := by
  have he := congrFun (Real.fourier_iteratedDeriv (N:=⊤) (hg.of_le le_top) (fun n _ => hi n) (n:=n) (by simp)) (-u)
  have hn := VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
    (innerₗ ℝ) (iteratedDeriv n g) (-u)
  change ‖𝓕 (iteratedDeriv n g) (-u)‖ ≤ _ at hn
  have hn' := hn.trans hb
  rw [he,norm_smul,norm_pow] at hn'
  have hc : ‖(2:ℂ)*Real.pi*I*(-u)‖=2*Real.pi*|u| := by
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  simp only [Complex.ofReal_neg] at hn'
  rw [hc] at hn'
  rw [Real.fourierInv_eq_fourier_neg]
  apply (le_div_iff₀ (pow_pos hu n)).mpr
  have hπ : (1:ℝ) ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  have hpow : |u|^n ≤ (2*Real.pi*|u|)^n := by
    gcongr
    exact le_mul_of_one_le_left hu.le hπ
  nlinarith [mul_le_mul_of_nonneg_right hpow (norm_nonneg (𝓕 g (-u)))]

open Complex Real Set MeasureTheory Filter Topology
lemma mellinInv_const_mul (σ : ℝ) (f : ℂ → ℂ) (a : ℂ) (x : ℝ) :
    mellinInv σ (fun s => a*f s) x=a*mellinInv σ f x := by
  simp [mellinInv,smul_eq_mul,Complex.real_smul,mul_left_comm,integral_const_mul,mul_assoc]

lemma mellinInv_term_riesz {σ y : ℝ} (hσ : 1≤σ) (hy : 0<y)
    (a : ℕ → ℂ) (n : ℕ) :
    mellinInv σ (fun s => LSeries.term a s n/(s*(s+1))) y=
      if n=0 then 0 else a n*rieszKernel ((n:ℝ)*y) := by
  by_cases hn : n=0
  · simp [hn,mellinInv]
  rw [ite_eq_right hn]
  have hi := rieszKernel_mellinInv hσ (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hy)
  rw [←hi]
  simp only [mellinInv,LSeries.term_of_ne_zero hn,smul_eq_mul,Complex.real_smul]
  rw [mul_left_comm (a n) ((1/(2*π):ℝ):ℂ)]
  congr 1
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg n) hy.le]
  simp only [Complex.ofReal_natCast,Complex.cpow_neg]
  ring

lemma riesz_inverse_integrand_norm {σ y : ℝ} (hy : 0<y) (a : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    ‖(y:ℂ)^(-((σ:ℂ)+t*I))*(LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))‖=
      (y^(-σ)*‖LSeries.term a (σ:ℂ) n‖)*‖1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))‖ := by
  simp only [norm_mul,norm_div,norm_one,Complex.norm_cpow_eq_rpow_re_of_pos hy,
    Complex.neg_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero,LSeries.norm_term_eq]
  ring

lemma riesz_inverse_integrand_summable {σ y : ℝ} (hσ : 1≤σ) (hy : 0<y)
    (a : ℕ → ℂ) (ha : LSeriesSummable a (σ:ℂ)) :
    (∀ n : ℕ, Integrable (fun t : ℝ => (y:ℂ)^(-((σ:ℂ)+t*I))*
        (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))))) ∧
    Summable (fun n : ℕ => ∫ t : ℝ, ‖(y:ℂ)^(-((σ:ℂ)+t*I))*
        (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))‖) := by
  have hc (n : ℕ) : Continuous (fun t : ℝ => (y:ℂ)^(-((σ:ℂ)+t*I))*
      (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))) := by
    have hz (t : ℝ) : (σ:ℂ)+t*I≠0 := by
      intro hh; have := congrArg Complex.re hh; simp at this; linarith
    have hz1 (t : ℝ) : (σ:ℂ)+t*I+1≠0 := by
      intro hh; have := congrArg Complex.re hh; simp at this; linarith
    have hd : Continuous (fun t : ℝ => ((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)) := by fun_prop
    have he : Continuous (fun t : ℝ => -((σ:ℂ)+t*I)) := by fun_prop
    apply (he.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).mul
    apply Continuous.div _ hd (fun t => mul_ne_zero (hz t) (hz1 t))
    by_cases hn : n=0
    · simpa [hn] using (continuous_const : Continuous (fun _t : ℝ => (0:ℂ)))
    · simp only [LSeries.term_of_ne_zero hn]
      apply continuous_const.div
      · exact (show Continuous (fun t : ℝ => (σ:ℂ)+t*I) by fun_prop).const_cpow
          (.inl (Nat.cast_ne_zero.mpr hn))
      · intro t; exact Complex.cpow_ne_zero_iff.mpr (.inl (Nat.cast_ne_zero.mpr hn))
  have hnorm (n : ℕ) : Integrable (fun t : ℝ => ‖(y:ℂ)^(-((σ:ℂ)+t*I))*
      (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))‖) := by
    simp_rw [riesz_inverse_integrand_norm hy]
    exact (rieszDenominator_verticalIntegrable hσ).norm.const_mul _
  refine ⟨fun n => (integrable_norm_iff (hc n).aestronglyMeasurable).mp (hnorm n), ?_⟩
  simp_rw [riesz_inverse_integrand_norm hy,integral_const_mul]
  exact (ha.norm.mul_left (y^(-σ))).mul_right _

lemma mellinInv_LSeries_riesz {σ y : ℝ} (hσ : 1≤σ) (hy : 0<y)
    (a : ℕ → ℂ) (ha : LSeriesSummable a (σ:ℂ)) :
    mellinInv σ (fun s => LSeries a s/(s*(s+1))) y=
      ∑' n : ℕ, if n=0 then 0 else a n*rieszKernel ((n:ℝ)*y) := by
  obtain ⟨hi,hs⟩ := riesz_inverse_integrand_summable hσ hy a ha
  have he := integral_tsum_of_summable_integral_norm hi hs
  simp only [mellinInv,smul_eq_mul,Complex.real_smul]
  simp only [LSeries,←tsum_div_const,←tsum_mul_left]
  rw [←he,←tsum_mul_left]
  apply tsum_congr
  intro n
  exact mellinInv_term_riesz hσ hy a n

noncomputable def rieszSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n*(1-(n:ℂ)/(x:ℂ))

lemma rieszKernel_tsum_eq {x : ℝ} (hx : 0<x) (a : ℕ → ℂ) :
    (∑' n : ℕ, if n=0 then 0 else a n*rieszKernel ((n:ℝ)*(1/x)))=rieszSum a x := by
  classical
  rw [tsum_eq_sum (s:=Finset.Ioc 0 ⌊x⌋₊)]
  · apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn0,hnx⟩ := Finset.mem_Ioc.mp hn
    have hn0' : (0:ℝ)<n := by exact_mod_cast hn0
    have hnx' : (n:ℝ)≤x := (Nat.le_floor_iff hx.le).mp hnx
    have hm0 : 0<(n:ℝ)*(1/x) := mul_pos hn0' (one_div_pos.mpr hx)
    have hm1 : (n:ℝ)*(1/x)≤1 := by rw [mul_one_div]; exact (div_le_one hx).mpr hnx'
    rw [ite_eq_right (by omega : n≠0),rieszKernel,
      Set.indicator_of_mem (show (n:ℝ)*(1/x)∈Ioc (0:ℝ) 1 from ⟨hm0,hm1⟩)]
    push_cast
    ring
  · intro n hn
    by_cases hn0 : n=0
    · simp [hn0]
    have hnx : x<(n:ℝ) := by
      have hnot : ¬n≤⌊x⌋₊ := by intro h; exact hn (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0,h⟩)
      exact lt_of_not_ge (fun h => hnot ((Nat.le_floor_iff hx.le).mpr h))
    have hm1 : ¬(n:ℝ)*(1/x)≤1 := by rw [mul_one_div]; exact not_le.mpr ((lt_div_iff₀ hx).mpr (by simpa using hnx))
    rw [ite_eq_right hn0,rieszKernel,
      Set.indicator_of_notMem (show (n:ℝ)*(1/x)∉Ioc (0:ℝ) 1 from fun h => hm1 h.2),mul_zero]

lemma rieszSum_mellinInv {σ x : ℝ} (hσ : 1≤σ) (hx : 0<x)
    (a : ℕ → ℂ) (ha : LSeriesSummable a (σ:ℂ)) :
    mellinInv σ (fun s => LSeries a s/(s*(s+1))) (1/x)=rieszSum a x := by
  rw [mellinInv_LSeries_riesz hσ (one_div_pos.mpr hx) a ha,rieszKernel_tsum_eq hx]

open Complex Real Set MeasureTheory Filter Topology
noncomputable def poleRieszKernel (y : ℝ) : ℂ :=
  (1/2:ℂ)*((y:ℂ)^(-1:ℂ)*rieszKernel y-rieszKernel y)

lemma hasMellin_poleRieszKernel {s : ℂ} (hs : 1<s.re) :
    HasMellin poleRieszKernel s (1/((s-1)*s*(s+1))) := by
  have h₀ := hasMellin_rieszKernel (s:=s) (by linarith)
  have h₁ := hasMellin_rieszKernel (s:=s+(-1)) (by simp; linarith)
  have hshift : MellinConvergent (fun t : ℝ => (t:ℂ)^(-1:ℂ) • rieszKernel t) s :=
    MellinConvergent.cpow_smul.mpr h₁.1
  have hm := mellin_cpow_smul rieszKernel s (-1)
  have hh := hasMellin_sub hshift h₀.1
  rw [hm,h₁.2,h₀.2] at hh
  have hhalf := hasMellin_const_smul hh.1 (1/2:ℂ)
  rw [hh.2] at hhalf
  have he : (1/2:ℂ) • (1/((s+-1)*(s+-1+1))-1/(s*(s+1)))=
      1/((s-1)*s*(s+1)) := by
    have hs0 : s≠0 := by intro h; simp [h] at hs; norm_num at hs
    have hs1 : s-1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    have hs2 : s+1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [show s+-1+1=s by ring,←sub_eq_add_neg]
    simp only [smul_eq_mul]
    field_simp [hs0,hs1,hs2]
    ring
  rw [he] at hhalf
  change HasMellin (fun t : ℝ => (1/2:ℂ)*((t:ℂ)^(-1:ℂ)*rieszKernel t-rieszKernel t)) s _
  simpa only [smul_eq_mul] using hhalf

lemma poleRieszKernel_continuousAt {y : ℝ} (hy : 0<y) :
    ContinuousAt poleRieszKernel y := by
  apply continuousAt_const.mul
  apply ContinuousAt.sub _ (rieszKernel_continuousAt hy)
  apply ContinuousAt.mul _ (rieszKernel_continuousAt hy)
  simp only [Complex.cpow_neg_one]
  have hr : ContinuousAt (fun t : ℝ => (t:ℂ)) y := Complex.continuous_ofReal.continuousAt
  exact hr.inv₀ (Complex.ofReal_ne_zero.mpr hy.ne')

set_option maxHeartbeats 3000000 in
lemma poleRiesz_verticalIntegrable {σ : ℝ} (hσ : 1<σ) :
    VerticalIntegrable (fun s : ℂ => 1/((s-1)*s*(s+1))) σ := by
  have hn (t : ℝ) : ((σ:ℂ)+t*I-1)*((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)≠0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · intro h; have := congrArg Complex.re h; simp at this; linarith
      · intro h; have := congrArg Complex.re h; simp at this; linarith
    · intro h; have := congrArg Complex.re h; simp at this; linarith
  have hc : Continuous (fun t : ℝ => 1/(((σ:ℂ)+t*I-1)*((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))) :=
    continuous_const.div (by fun_prop) hn
  have hbase : Integrable (fun t : ℝ => ‖1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))‖) :=
    (rieszDenominator_verticalIntegrable hσ.le).norm
  change Integrable (fun t : ℝ => 1/(((σ:ℂ)+t*I-1)*((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))
  apply (hbase.const_mul (1/(σ-1))).mono' hc.aestronglyMeasurable
  filter_upwards [] with t
  rw [norm_div,norm_one,norm_mul,norm_mul]
  have hl : σ-1 ≤ ‖(σ:ℂ)+t*I-1‖ := by simpa using Complex.re_le_norm ((σ:ℂ)+t*I-1)
  have hn0 : 0<‖(σ:ℂ)+t*I-1‖ := lt_of_lt_of_le (by linarith) hl
  have hh : 1/‖(σ:ℂ)+t*I-1‖ ≤ 1/(σ-1) := one_div_le_one_div_of_le (by linarith) hl
  simpa only [norm_div,norm_one,norm_mul,div_eq_mul_inv,mul_inv_rev,norm_inv,mul_assoc,mul_comm,mul_left_comm,one_mul,mul_one]
    using mul_le_mul_of_nonneg_right hh (norm_nonneg (1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))))

lemma poleRiesz_mellinInv {σ y : ℝ} (hσ : 1<σ) (hy : 0<y) :
    mellinInv σ (fun s : ℂ => 1/((s-1)*s*(s+1))) y=poleRieszKernel y := by
  have hm (t : ℝ) : mellin poleRieszKernel (σ+t*I)=1/((σ+t*I-1)*(σ+t*I)*(σ+t*I+1)) :=
    (hasMellin_poleRieszKernel (by simpa using hσ)).2
  have hf : VerticalIntegrable (mellin poleRieszKernel) σ := by
    unfold VerticalIntegrable
    simp_rw [hm]
    exact poleRiesz_verticalIntegrable hσ
  rw [←mellinInv_mellin_eq σ poleRieszKernel hy
    (hasMellin_poleRieszKernel (by simpa using hσ)).1 hf (poleRieszKernel_continuousAt hy)]
  simp only [mellinInv,hm]

lemma poleRieszKernel_inv {x : ℝ} (hx : 1≤x) :
    poleRieszKernel (1/x)=((x/2-1+1/(2*x):ℝ):ℂ) := by
  have hx0 : 0<x := by linarith
  have hy : 0<1/x := one_div_pos.mpr hx0
  have hy1 : 1/x≤1 := (div_le_one hx0).mpr hx
  rw [poleRieszKernel,rieszKernel_eq_max hy,max_eq_left (by linarith : 0≤1-1/x)]
  simp only [Complex.cpow_neg_one,Complex.ofReal_div,Complex.ofReal_one,inv_div,div_one,
    Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat]
  have hn : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  field_simp
  ring

lemma mellinInv_integrable {σ y : ℝ} (hy : 0<y) {f : ℂ → ℂ}
    (hf : VerticalIntegrable f σ) :
    Integrable (fun t : ℝ => (y:ℂ)^(-((σ:ℂ)+t*I))*f ((σ:ℂ)+t*I)) := by
  have he : Continuous (fun t : ℝ => -((σ:ℂ)+t*I)) := by fun_prop
  have hc := he.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hy.ne'))
  apply (hf.norm.const_mul (y^(-σ))).mono' (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with t
  change ‖(y:ℂ)^(-((σ:ℂ)+t*I))*f ((σ:ℂ)+t*I)‖ ≤ y^(-σ)*‖f ((σ:ℂ)+t*I)‖
  simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy,Complex.neg_re,
    Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    mul_zero,zero_mul,sub_self,add_zero,le_refl]

lemma mellinInv_add_of_verticalIntegrable {σ y : ℝ} (hy : 0<y) {f g : ℂ → ℂ}
    (hf : VerticalIntegrable f σ) (hg : VerticalIntegrable g σ) :
    mellinInv σ (fun s => f s+g s) y=mellinInv σ f y+mellinInv σ g y := by
  simp only [mellinInv,smul_eq_mul,Complex.real_smul,mul_add]
  rw [integral_add (mellinInv_integrable hy hf) (mellinInv_integrable hy hg),mul_add]

open Complex Real Set MeasureTheory Filter Topology
open scoped FourierTransform
end LargePrimeGaps
end OAI

-- Source module: RieszDecay
namespace OAI
namespace LargePrimeGaps
open Complex Filter Topology
open Complex Filter Topology MeasureTheory
open Complex Real Set MeasureTheory Filter Topology
open scoped FourierTransform
noncomputable def logRieszVertical {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) : ℂ := logRiesz (poleRemovedL χ) (σ+2*π*t*I)

lemma logRieszVertical_contDiff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1≤σ) : ContDiff ℝ ⊤ (logRieszVertical χ σ) := by
  have h : ∀ t : ℝ, AnalyticAt ℂ (logRiesz (poleRemovedL χ)) ((σ:ℂ)+(2*π*I)*(t:ℂ)) := by
    intro t
    apply logRiesz_poleRemoved_analyticAt
    simpa using hσ
  convert vertical_contDiff h using 1
  ext t
  dsimp [logRieszVertical]
  congr 1
  ring

lemma logRieszVertical_iteratedDeriv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1≤σ) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (logRieszVertical χ σ) t=
      ((2:ℂ)*π*I)^n*iteratedDeriv n (logRiesz (poleRemovedL χ)) (σ+2*π*t*I) := by
  have h : ∀ t : ℝ, AnalyticAt ℂ (logRiesz (poleRemovedL χ)) ((σ:ℂ)+(2*π*I)*(t:ℂ)) := by
    intro t
    apply logRiesz_poleRemoved_analyticAt
    simpa using hσ
  have he : logRieszVertical χ σ=(fun t : ℝ => logRiesz (poleRemovedL χ) ((σ:ℂ)+(2*π*I)*(t:ℂ))) := by
    ext t
    dsimp [logRieszVertical]
    congr 1
    ring
  simpa only [he,mul_assoc,mul_comm,mul_left_comm] using congrFun (vertical_iteratedDeriv h n) t

lemma logRieszVertical_bound (n : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ σ t : ℝ, 1≤σ → σ≤2 →
        ‖iteratedDeriv n (logRieszVertical χ σ) t‖ ≤
          (D*((q:ℝ)+2)^(1/2:ℝ))*decayMajorant t := by
  obtain ⟨D,hD,hb⟩ := primitive_logRiesz_bound n
  refine ⟨(2*π)^n*D,by positivity,?_⟩
  intro q _ χ hp σ t hσ hσ2
  have he : (σ:ℂ)+2*π*t*I=(σ:ℂ)+I*((2*π*t:ℝ):ℂ) := by push_cast; ring
  rw [logRieszVertical_iteratedDeriv χ hσ,norm_mul,norm_pow,he]
  have hc : ‖(2:ℂ)*π*I‖=2*π := by simp [abs_of_pos pi_pos]
  rw [hc]
  have ht : (|2*π*t|+2)^(-(3/2:ℝ)) ≤ decayMajorant t := by
    dsimp [decayMajorant]
    apply Real.rpow_le_rpow_of_nonpos (by positivity)
    · rw [abs_mul,abs_mul,abs_of_pos pi_pos]
      norm_num
      nlinarith [abs_nonneg t,pi_gt_three]
    · norm_num
  calc
    _ ≤ (2*π)^n*(D*((q:ℝ)+2)^(1/2:ℝ)*(|2*π*t|+2)^(-(3/2:ℝ))) :=
      mul_le_mul_of_nonneg_left (hb q χ hp σ (2*π*t) hσ hσ2) (by positivity)
    _ ≤ (2*π)^n*(D*((q:ℝ)+2)^(1/2:ℝ)*decayMajorant t) := by gcongr
    _ = _ := by ring

lemma logRieszVertical_integrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ : ℝ} (hσ : 1≤σ) (hσ2 : σ≤2) (n : ℕ) :
    Integrable (iteratedDeriv n (logRieszVertical χ σ)) := by
  obtain ⟨D,hD,hb⟩ := logRieszVertical_bound n
  exact integrable_of_decay_bound
    ((logRieszVertical_contDiff χ hσ).continuous_iteratedDeriv n (by simp))
    (hb q χ hp σ · hσ hσ2)

lemma logRiesz_mellinInv_bound (n : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ σ x : ℝ, 1≤σ → σ≤2 → 1<x →
        ‖mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*x^σ/(Real.log x)^n := by
  obtain ⟨D,hD,hb⟩ := logRieszVertical_bound n
  let J : ℝ := ∫ t, decayMajorant t
  refine ⟨D*(|J|+1),by dsimp [J]; positivity,?_⟩
  intro q _ χ hp σ x hσ hσ2 hx
  have hx0 : 0<x := by linarith
  have hlog : 0<Real.log x := Real.log_pos hx
  have hi := logRieszVertical_integrable χ hp hσ hσ2
  have hg := logRieszVertical_contDiff χ hσ
  have hb' : (∫ t, ‖iteratedDeriv n (logRieszVertical χ σ) t‖) ≤ D*((q:ℝ)+2)^(1/2:ℝ)*J :=
    integral_norm_le_of_decay_bound (hg.continuous_iteratedDeriv n (by simp)) (hb q χ hp σ · hσ hσ2)
  have hf := fourierInv_decay hg hi n hb' (u:=Real.log x) (by rwa [abs_of_pos hlog])
  rw [mellinInv_eq_fourierInv σ _ (one_div_pos.mpr hx0),norm_smul,
    Complex.norm_cpow_eq_rpow_re_of_pos (one_div_pos.mpr hx0)]
  have he : -(Real.log (1/x))=Real.log x := by simp
  rw [he]
  change (1/x)^(-σ)*‖𝓕⁻ (logRieszVertical χ σ) (Real.log x)‖ ≤ _
  rw [one_div,Real.inv_rpow hx0.le,←Real.rpow_neg hx0.le,neg_neg]
  have hJ : J ≤ |J|+1 := by linarith [le_abs_self J]
  have hfac : 0≤ D*((q:ℝ)+2)^(1/2:ℝ) := by positivity
  calc
    _ ≤ x^σ*(D*((q:ℝ)+2)^(1/2:ℝ)*J/|Real.log x|^n) := mul_le_mul_of_nonneg_left hf (by positivity)
    _ ≤ x^σ*(D*((q:ℝ)+2)^(1/2:ℝ)*(|J|+1)/(Real.log x)^n) := by
      rw [abs_of_pos hlog]
      gcongr
    _ = _ := by ring

open Complex Real Set MeasureTheory Filter Topology
noncomputable def primeCoefficients {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)

noncomputable def characterMain {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ := by
  classical
  exact if χ=1 then 1 else 0

lemma characterMain_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) : ‖characterMain χ‖≤1 := by
  unfold characterMain
  split_ifs <;> norm_num

lemma primeCoefficients_summable {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (primeCoefficients χ) s := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs

lemma primeCoefficients_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖primeCoefficients χ n‖≤Real.log n := by
  rw [primeCoefficients,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact (mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)).trans
    ArithmeticFunction.vonMangoldt_le_log

lemma primeRiesz_identity {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1<s.re) :
    LSeries (primeCoefficients χ) s/(s*(s+1))=
      logRiesz (poleRemovedL χ) s+characterMain χ*(1/((s-1)*s*(s+1))) := by
  have he := primeLogDerivativeRegular_eq χ hs
  change primeLogDerivativeRegular χ s=LSeries (primeCoefficients χ) s-_ at he
  have hlog : logRiesz (poleRemovedL χ) s=primeLogDerivativeRegular χ s/(s*(s+1)) := rfl
  have hs0 : s≠0 := by intro h; simp [h] at hs; norm_num at hs
  have hs1 : s-1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hs2 : s+1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [hlog,he,characterMain]
  split_ifs <;> field_simp <;> ring

lemma logRiesz_verticalIntegrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ : ℝ} (hσ : 1≤σ) (hσ2 : σ≤2) :
    VerticalIntegrable (logRiesz (poleRemovedL χ)) σ := by
  have hπ : (2*π:ℝ)≠0 := by positivity
  have hi := (logRieszVertical_integrable χ hp hσ hσ2 0).comp_mul_left' (inv_ne_zero hπ)
  simp only [iteratedDeriv_zero] at hi
  have he : (fun t : ℝ => logRieszVertical χ σ ((2*π)⁻¹*t))=
      (fun t : ℝ => logRiesz (poleRemovedL χ) (σ+t*I)) := by
    ext t
    dsimp [logRieszVertical]
    congr 1
    push_cast
    field_simp
  rwa [he] at hi

set_option maxHeartbeats 800000 in
lemma primeRiesz_mellinInv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ x : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) (hx : 0<x) :
    mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)=
      rieszSum (primeCoefficients χ) x-characterMain χ*poleRieszKernel (1/x) := by
  have he : rieszSum (primeCoefficients χ) x=
      mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)+characterMain χ*poleRieszKernel (1/x) := by
    rw [←rieszSum_mellinInv hσ.le hx _ (primeCoefficients_summable χ (by simpa using hσ))]
    calc
      _ = mellinInv σ (fun s => logRiesz (poleRemovedL χ) s+
          characterMain χ*(1/((s-1)*s*(s+1)))) (1/x) := by
        unfold mellinInv
        congr 1
        apply integral_congr_ae
        filter_upwards [] with t
        rw [primeRiesz_identity χ (by simpa using hσ)]
      _ = mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)+
          mellinInv σ (fun s => characterMain χ*(1/((s-1)*s*(s+1)))) (1/x) :=
        mellinInv_add_of_verticalIntegrable (one_div_pos.mpr hx)
          (logRiesz_verticalIntegrable χ hp hσ.le hσ2) ((poleRiesz_verticalIntegrable hσ).const_mul _)
      _ = _ := by rw [mellinInv_const_mul,poleRiesz_mellinInv hσ (one_div_pos.mpr hx)]
  linear_combination -he

lemma primeRiesz_error_bound (n : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ σ x : ℝ, 1<σ → σ≤2 → 1<x →
        ‖rieszSum (primeCoefficients χ) x-characterMain χ*(x:ℂ)/2‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*x^σ/(Real.log x)^n+1 := by
  obtain ⟨D,hD,hb⟩ := logRiesz_mellinInv_bound n
  refine ⟨D,hD,?_⟩
  intro q _ χ hp σ x hσ hσ2 hx
  have he := primeRiesz_mellinInv χ hp hσ hσ2 (by linarith : 0<x)
  rw [poleRieszKernel_inv hx.le] at he
  have he' : rieszSum (primeCoefficients χ) x-characterMain χ*(x:ℂ)/2=
      mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)+characterMain χ*((-1+1/(2*x):ℝ):ℂ) := by
    push_cast at he ⊢
    linear_combination -he
  rw [he']
  apply (norm_add_le _ _).trans
  apply add_le_add (hb q χ hp σ x hσ.le hσ2 hx)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have ht : |-1+1/(2*x)|≤1 := by
    rw [abs_le]
    have hx0 : 0<x := by linarith
    have ht0 : 0≤1/(2*x) := by positivity
    have ht1 : 1/(2*x)≤1 := (div_le_one (by positivity)).mpr (by linarith)
    constructor <;> linarith
  exact (mul_le_mul (characterMain_norm_le χ) ht (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

open Complex Real Set MeasureTheory Filter Topology
noncomputable def weightedPrefix (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, ((x-(n:ℝ):ℝ):ℂ)*a n

lemma weightedPrefix_difference {x h : ℝ} (hh : 0≤h) (a : ℕ → ℂ) :
    weightedPrefix a (x+h)-weightedPrefix a x=
      (h:ℂ)*(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)+
      ∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n := by
  classical
  have hfloor : ⌊x⌋₊≤⌊x+h⌋₊ := Nat.floor_mono (by linarith)
  have he : Finset.Ioc 0 ⌊x+h⌋₊=Finset.Ioc 0 ⌊x⌋₊ ∪ Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊ := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_union]
    omega
  have hd : Disjoint (Finset.Ioc 0 ⌊x⌋₊) (Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) := by
    rw [Finset.disjoint_left]
    intro n h₁ h₂
    simp only [Finset.mem_Ioc] at h₁ h₂
    omega
  unfold weightedPrefix
  rw [he,Finset.sum_union hd]
  have hs : (∑ n∈Finset.Ioc 0 ⌊x⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n)=
      (h:ℂ)*(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)+
      ∑ n∈Finset.Ioc 0 ⌊x⌋₊, ((x-(n:ℝ):ℝ):ℂ)*a n := by
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    push_cast
    ring
  rw [hs]
  ring

lemma weightedPrefix_tail_bound {x h L : ℝ} (hx : 0≤x) (hh : 0≤h) (hL : 0≤L)
    (a : ℕ → ℂ) (ha : ∀ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ‖a n‖≤L) :
    ‖∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n‖ ≤ (h+1)*(h*L) := by
  have hfloor : ⌊x⌋₊≤⌊x+h⌋₊ := Nat.floor_mono (by linarith)
  have hn (n : ℕ) (hn : n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) :
      0≤x+h-(n:ℝ) ∧ x+h-(n:ℝ)≤h := by
    obtain ⟨h₁,h₂⟩ := Finset.mem_Ioc.mp hn
    have hlo : x<(n:ℝ) := by
      have hn' : (⌊x⌋₊:ℝ)+1≤n := by exact_mod_cast h₁
      linarith [Nat.lt_floor_add_one x]
    have hup : (n:ℝ)≤x+h := (Nat.le_floor_iff (by linarith)).mp h₂
    constructor <;> linarith
  have hc : ((Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊).card:ℝ) ≤ h+1 := by
    rw [Nat.card_Ioc,Nat.cast_sub hfloor]
    have hlo := Nat.lt_floor_add_one x
    have hup := Nat.floor_le (by linarith : 0≤x+h)
    linarith
  calc
    _ ≤ ∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ‖((x+h-(n:ℝ):ℝ):ℂ)*a n‖ := norm_sum_le _ _
    _ ≤ ∑ _n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, h*L := by
      apply Finset.sum_le_sum
      intro n hn'
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hn n hn').1]
      exact mul_le_mul (hn n hn').2 (ha n hn') (norm_nonneg _) hh
    _ = ((Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊).card:ℝ)*(h*L) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (mul_nonneg hh hL)

lemma prefix_unsmoothing {x h L : ℝ} (hx : 0≤x) (hh : 0<h) (hL : 0≤L)
    (a : ℕ → ℂ) (δ : ℂ) (ha : ∀ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ‖a n‖≤L) :
    ‖(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ)‖ ≤
      (‖weightedPrefix a (x+h)-δ*((x+h:ℝ):ℂ)^2/2‖+
        ‖weightedPrefix a x-δ*(x:ℂ)^2/2‖)/h+(h+1)*L+‖δ‖*h/2 := by
  let T := ∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n
  let E (y : ℝ) := weightedPrefix a y-δ*(y:ℂ)^2/2
  have he : (h:ℂ)*((∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ))=
      (E (x+h)-E x)-T+δ*(h:ℂ)^2/2 := by
    have hd := weightedPrefix_difference (x:=x) hh.le a
    change weightedPrefix a (x+h)-weightedPrefix a x = _+T at hd
    dsimp [E]
    push_cast
    linear_combination -hd
  have hn : h*‖(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ)‖ ≤
      (‖E (x+h)‖+‖E x‖)+((h+1)*(h*L))+‖δ‖*h^2/2 := by
    calc
      _ = ‖(h:ℂ)*((∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ))‖ := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
      _ = ‖(E (x+h)-E x)-T+δ*(h:ℂ)^2/2‖ := congrArg norm he
      _ ≤ ‖E (x+h)-E x‖+‖T‖+‖δ*(h:ℂ)^2/2‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (‖E (x+h)‖+‖E x‖)+((h+1)*(h*L))+‖δ‖*h^2/2 := by
        have hT : ‖T‖≤(h+1)*(h*L) := weightedPrefix_tail_bound hx hh.le hL a ha
        have hδ : ‖δ*(h:ℂ)^2/2‖=‖δ‖*h^2/2 := by
          simp [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
        rw [hδ]
        exact add_le_add (add_le_add (norm_sub_le _ _) hT) le_rfl
  have hd : h*((‖E (x+h)‖+‖E x‖)/h+(h+1)*L+‖δ‖*h/2)=
      (‖E (x+h)‖+‖E x‖)+((h+1)*(h*L))+‖δ‖*h^2/2 := by field_simp
  dsimp [E] at hn hd
  apply (mul_le_mul_iff_left₀ hh).mp
  rw [mul_comm _ h, mul_comm _ h, hd]
  exact hn

open Complex Real Set MeasureTheory Filter Topology
lemma weightedPrefix_eq_mul_rieszSum (a : ℕ → ℂ) {x : ℝ} (hx : 0<x) :
    weightedPrefix a x=(x:ℂ)*rieszSum a x := by
  unfold weightedPrefix rieszSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hx0 : (x:ℂ)≠0 := by exact_mod_cast hx.ne'
  push_cast
  field_simp

lemma rpow_one_add_inv_log {x : ℝ} (hx : 1<x) :
    x^(1+1/Real.log x)=Real.exp 1*x := by
  have hx0 : 0<x := by linarith
  have hlog : Real.log x≠0 := (Real.log_pos hx).ne'
  rw [Real.rpow_add hx0,Real.rpow_one,Real.rpow_def_of_pos hx0]
  rw [mul_one_div_cancel hlog]
  ring

lemma primeWeighted_error_bound (a : ℝ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ x : ℝ, 1<x → 1≤Real.log x →
        ‖weightedPrefix (primeCoefficients χ) x-characterMain χ*(x:ℂ)^2/2‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*x^2*(Real.log x)^(-a)+x := by
  obtain ⟨D,hD,hb⟩ := primeRiesz_error_bound ⌈a⌉₊
  refine ⟨D*Real.exp 1,by positivity,?_⟩
  intro q _ χ hp x hx hL
  have hx0 : 0<x := by linarith
  have hlog : 0<Real.log x := Real.log_pos hx
  have hσ : 1<1+1/Real.log x := by linarith [one_div_pos.mpr hlog]
  have hσ2 : 1+1/Real.log x≤2 := by
    have : 1/Real.log x≤1 := (div_le_one hlog).mpr hL
    linarith
  have he : weightedPrefix (primeCoefficients χ) x-characterMain χ*(x:ℂ)^2/2=
      (x:ℂ)*(rieszSum (primeCoefficients χ) x-characterMain χ*(x:ℂ)/2) := by
    rw [weightedPrefix_eq_mul_rieszSum _ hx0]
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx0]
  calc
    _ ≤ x*(D*((q:ℝ)+2)^(1/2:ℝ)*x^(1+1/Real.log x)/(Real.log x)^⌈a⌉₊+1) :=
      mul_le_mul_of_nonneg_left (hb q χ hp _ x hσ hσ2 hx) hx0.le
    _ = D*Real.exp 1*((q:ℝ)+2)^(1/2:ℝ)*x^2*(Real.log x)^(-(⌈a⌉₊:ℝ))+x := by
      rw [rpow_one_add_inv_log hx,Real.rpow_neg hlog.le,Real.rpow_natCast]
      ring
    _ ≤ _ := by
      have hn : a≤(⌈a⌉₊:ℝ) := Nat.le_ceil a
      gcongr

end LargePrimeGaps
end OAI

-- Source module: Main
namespace OAI
namespace LargePrimeGaps
open Complex Filter Topology
open Complex Filter Topology MeasureTheory
open scoped FourierTransform
open Complex Real Set MeasureTheory Filter Topology
lemma primeCharacterError_log_bound (A B : ℝ) (hA : 0<A) (hB : 0<B) :
    ∃ M : ℝ, 0<M ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ x : ℝ, 2≤x → 1≤Real.log x → (Real.log x)^(2*A+2)≤x →
        (q:ℝ)≤(Real.log x)^B →
        ‖primeCharacterError x χ‖≤M*x*(Real.log x)^(-A) := by
  obtain ⟨D,hD,hb⟩ := primeWeighted_error_bound (B+2*A+2)
  refine ⟨15*D+8,by positivity,?_⟩
  intro q _ χ hp x hx hL hpower hq
  let L := Real.log x
  let K := A+2
  let a := B+2*A+2
  let Q := ((q:ℝ)+2)^(1/2:ℝ)
  let h := x/L^K
  have hx0 : 0<x := by linarith
  have hx1 : 1<x := by linarith
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hK : 0<K := by dsimp [K]; linarith
  have ha : 0<a := by dsimp [a]; linarith
  have hpK : 0<L^K := Real.rpow_pos_of_pos hL0 _
  have hh0 : 0<h := div_pos hx0 hpK
  have hK1 : 1≤L^K := Real.one_le_rpow hL hK.le
  have hhx : h≤x := (div_le_self hx0.le hK1)
  have hKh : L^K≤x := by
    apply (Real.rpow_le_rpow_of_exponent_le hL (show K≤2*A+2 by dsimp [K]; linarith)).trans
    exact hpower
  have hh1 : 1≤h := (le_div_iff₀ hpK).mpr (by simpa using hKh)
  have hyx : x≤x+h := by linarith
  have hy : 1<x+h := by linarith
  have hy2 : x+h≤2*x := by linarith
  have hLy : L≤Real.log (x+h) := Real.log_le_log hx0 hyx
  have hLy1 : 1≤Real.log (x+h) := hL.trans hLy
  have hLy2 : Real.log (x+h)≤2*L := by
    calc
      _ ≤ Real.log (x^2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; rfl
  have hQ0 : 0≤Q := by dsimp [Q]; positivity
  have hQ : Q≤3*L^B := by
    have hq2 : 1≤(q:ℝ)+2 := by have := Nat.cast_nonneg (α:=ℝ) q; linarith
    have hqpow : Q≤(q:ℝ)+2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hq2 (show (1/2:ℝ)≤1 by norm_num)
    have hLB : 1≤L^B := Real.one_le_rpow hL hB.le
    linarith
  let E (y : ℝ) := ‖weightedPrefix (primeCoefficients χ) y-characterMain χ*(y:ℂ)^2/2‖
  have hEx : E x≤D*Q*x^2*L^(-a)+x := hb q χ hp x hx1 hL
  have hEy : E (x+h)≤4*D*Q*x^2*L^(-a)+2*x := by
    calc
      _ ≤ D*Q*(x+h)^2*(Real.log (x+h))^(-a)+(x+h) := hb q χ hp (x+h) hy hLy1
      _ ≤ D*Q*(2*x)^2*L^(-a)+2*x := by
        apply add_le_add _ hy2
        apply mul_le_mul _ (Real.rpow_le_rpow_of_nonpos hL0 hLy (neg_nonpos.mpr ha.le)) (by positivity) (by positivity)
        gcongr
      _ = _ := by ring
  have hcoeff (n : ℕ) (hn : n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) :
      ‖primeCoefficients χ n‖≤2*L := by
    have hn0 : 0<(n:ℝ) := by exact_mod_cast (show 0<n by have := (Finset.mem_Ioc.mp hn).1; omega)
    have hnx : (n:ℝ)≤x+h := (Nat.le_floor_iff (by linarith : 0≤x+h)).mp (Finset.mem_Ioc.mp hn).2
    exact (primeCoefficients_norm_le χ n).trans ((Real.log_le_log hn0 hnx).trans hLy2)
  have heq : primeCharacterError x χ=
      (∑ n∈Finset.Ioc 0 ⌊x⌋₊, primeCoefficients χ n)-characterMain χ*(x:ℂ) := by
    classical
    simp only [primeCharacterError,primeCharacterPrefix,primeCoefficients,characterMain]
    split_ifs <;> simp
  rw [heq]
  have hu := prefix_unsmoothing hx0.le hh0 (show 0≤2*L by positivity)
    (primeCoefficients χ) (characterMain χ) hcoeff
  change _≤(E (x+h)+E x)/h+(h+1)*(2*L)+‖characterMain χ‖*h/2 at hu
  have hδ : ‖characterMain χ‖*h/2≤h := by
    have := mul_le_mul_of_nonneg_right (characterMain_norm_le χ) hh0.le
    linarith
  have htail : (h+1)*(2*L)≤4*h*L := by nlinarith
  have herr : (E (x+h)+E x)/h ≤ 15*D*x*L^(-A)+3*x*L^(-A) := by
    calc
      _ ≤ (5*D*Q*x^2*L^(-a)+3*x)/h := by
        apply div_le_div_of_nonneg_right _ hh0.le
        linarith
      _ ≤ (5*D*(3*L^B)*x^2*L^(-a)+3*x)/h := by gcongr
      _ = (15*D*L^B*x^2*L^(-a)+3*x)/h := by ring
      _ = 15*D*x*L^(-A)+3*L^K := by
        dsimp [h]
        rw [div_eq_mul_inv,inv_div]
        have hr : L^B*L^(-a)*L^K=L^(-A) := by
          rw [←Real.rpow_add hL0,←Real.rpow_add hL0]
          congr 1
          dsimp [a,K]
          ring
        field_simp
        linear_combination 15*D*x*hr
      _ ≤ _ := by
        have ht : L^K≤x*L^(-A) := by
          calc
            _ = L^(2*A+2)*L^(-A) := by rw [←Real.rpow_add hL0]; congr 1; dsimp [K]; ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hpower (by positivity)
        nlinarith [ht]
  have hsmall : h≤x*L^(-A) := by
    dsimp [h]
    rw [div_eq_mul_inv,←Real.rpow_neg hL0.le]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (show -K≤-A by dsimp [K]; linarith)) hx0.le
  have htail' : 4*h*L≤4*x*L^(-A) := by
    calc
      _ = 4*x*L^(1-K) := by
        dsimp [h]
        rw [div_eq_mul_inv,Real.rpow_sub hL0,Real.rpow_one]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL (show 1-K≤-A by dsimp [K]; linarith)) (by positivity)
  calc
    _ ≤ (E (x+h)+E x)/h+(h+1)*(2*L)+‖characterMain χ‖*h/2 := hu
    _ ≤ (15*D*x*L^(-A)+3*x*L^(-A))+4*x*L^(-A)+x*L^(-A) := by
      exact add_le_add (add_le_add herr (htail.trans htail')) (hδ.trans hsmall)
    _ = _ := by ring

theorem siegelWalfisz : SiegelWalfisz := by
  intro A B hA hB
  obtain ⟨M,hM,hb⟩ := primeCharacterError_log_bound A B hA hB
  have hevent : ∀ᶠ x : ℝ in atTop, 2≤x ∧ 1≤Real.log x ∧ (Real.log x)^(2*A+2)≤x := by
    filter_upwards [eventually_ge_atTop (2:ℝ),eventually_ge_atTop (Real.exp 1),
      eventually_log_rpow_le_rpow (2*A+2) (by norm_num : (0:ℝ)<1)] with x hx hex hp
    refine ⟨hx,?_,by simpa only [Real.rpow_one] using hp⟩
    rw [←Real.log_exp (1:ℝ)]
    exact Real.log_le_log (Real.exp_pos _) hex
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.mp hevent
  refine ⟨M,hM,max x₀ 2,by have := le_max_right x₀ (2:ℝ); linarith,?_⟩
  intro x hx d hd hdlog χ hχ
  let : NeZero d := ⟨ne_of_gt hd⟩
  obtain ⟨hx2,hlog,hpower⟩ := hx₀ x ((le_max_left _ _).trans hx)
  exact hb d χ hχ x hx2 hlog hpower hdlog

end LargePrimeGaps
end OAI


-- Source module: OrthantIntegrals
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable def residueSlice (f : ℕ → ℝ) (L U q c : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ioc L U).filter (fun n => n % q = c), f n

noncomputable def residuePrefix (f : ℕ → ℝ) (Y q c : ℕ) : ℝ :=
  residueSlice f 0 Y q c

end LargePrimeGaps
end OAI

-- Source module: CharacterErrors
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
theorem character_prefix_orthogonality (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    ∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterPrefix x χ=
      (q.totient:ℂ)*(residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c:ℂ) := by
  classical
  have : NeZero q := ⟨ne_of_gt hq⟩
  have hu : IsUnit (c:ZMod q) := (ZMod.isUnit_iff_coprime c q).mpr hcop
  have he (n : ℕ) : (c:ZMod q)=(n:ZMod q) ↔ n % q = c := by
    rw [ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt hc]
    exact eq_comm
  unfold primeCharacterPrefix
  simp_rw [Finset.mul_sum,←mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [←Finset.sum_mul,DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu,he]
  simp only [residuePrefix,residueSlice,Complex.ofReal_sum,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> simp

theorem character_error_orthogonality (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    ∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterError x χ=
      (q.totient:ℂ)*((residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient:ℝ):ℂ) := by
  classical
  have : NeZero q := ⟨ne_of_gt hq⟩
  have hu : IsUnit (c:ZMod q) := (ZMod.isUnit_iff_coprime c q).mpr hcop
  have huinv : IsUnit (c:ZMod q)⁻¹ := by
    obtain ⟨u,hu⟩ := hu
    rw [←hu,ZMod.inv_coe_unit]
    exact (u⁻¹).isUnit
  have ht : (q.totient:ℂ)≠0 := by exact_mod_cast ne_of_gt (Nat.totient_pos.mpr hq)
  simp only [primeCharacterError,mul_sub,Finset.sum_sub_distrib]
  rw [character_prefix_orthogonality x hq hc hcop]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte,MulChar.one_apply huinv,one_mul]
  push_cast
  field_simp

theorem endpointClassError_le_character_sum (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient|≤
      (∑ χ : DirichletCharacter ℂ q, ‖primeCharacterError x χ‖)/(q.totient:ℝ) := by
  have hphi : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  apply (le_div_iff₀ hphi).mpr
  have hh := character_error_orthogonality x hq hc hcop
  calc
    _ = ‖(q.totient:ℂ)*((residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient:ℝ):ℂ)‖ := by
      rw [norm_mul,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,mul_comm]
    _ = ‖∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterError x χ‖ := congrArg norm hh.symm
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖χ (c:ZMod q)⁻¹*primeCharacterError x χ‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro χ _
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

theorem vonMangoldt_noncoprime_sum_le (X : ℕ) {q : ℕ} (hq : 0<q) :
    (∑ n∈(Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n)≤(Nat.log 2 X:ℝ)*Real.log q := by
  classical
  let S := (Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q ∧ ArithmeticFunction.vonMangoldt n≠0)
  have he : (∑ n∈(Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n)=∑ n∈S,ArithmeticFunction.vonMangoldt n := by
    simp only [S,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hcop : Nat.Coprime n q <;> by_cases hn : ArithmeticFunction.vonMangoldt n=0 <;> simp [hcop,hn]
  rw [he]
  have hsub : S⊆(q^(Nat.log 2 X)).divisors := by
    intro n hn
    obtain ⟨hnI,hnq,hnv⟩ := Finset.mem_filter.mp hn
    obtain ⟨p,k,hp,_hk,hpkn⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hnv
    have hp' : p.Prime := Nat.prime_iff.mpr hp
    have hdp : p∣q := by
      by_contra hd
      have hc := (hp'.coprime_iff_not_dvd).mpr hd
      exact hnq (hpkn ▸ hc.pow_left k)
    have hkX : k≤Nat.log 2 X := by
      apply Nat.le_log_of_pow_le (by norm_num : 1<2)
      calc
        2^k≤p^k := Nat.pow_le_pow_left hp'.two_le k
        _ = n := hpkn
        _ ≤ X := (Finset.mem_Ioc.mp hnI).2
    apply Nat.mem_divisors.mpr
    refine ⟨?_,pow_ne_zero _ (ne_of_gt hq)⟩
    rw [←hpkn]
    exact (pow_dvd_pow_of_dvd hdp k).trans (pow_dvd_pow q hkX)
  calc
    _ ≤ ∑ n∈(q^(Nat.log 2 X)).divisors,ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log ((q^(Nat.log 2 X):ℕ):ℝ) := ArithmeticFunction.vonMangoldt_sum
    _ = _ := by rw [Nat.cast_pow,Real.log_pow]

theorem primitiveCharacter_eq_one_iff {q : ℕ} (hq : 0<q) (χ : DirichletCharacter ℂ q) :
    χ.primitiveCharacter=1 ↔ χ=1 := by
  have : NeZero q := ⟨ne_of_gt hq⟩
  constructor
  · intro h
    rw [←DirichletCharacter.changeLevel_primitiveCharacter χ,h,DirichletCharacter.changeLevel_one]
  · rintro rfl
    exact DirichletCharacter.primitiveCharacter_one

theorem primeCharacterPrefix_primitive_difference (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterPrefix x χ-primeCharacterPrefix x χ.primitiveCharacter‖≤
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have hsame (n : ℕ) (hn : Nat.Coprime n q) :
      χ.primitiveCharacter (n:ZMod χ.conductor)=χ (n:ZMod q) := by
    simpa only [Int.cast_natCast] using χ.primitiveCharacter_apply_of_isCoprime hn.isCoprime
  have hzero (n : ℕ) (hn : ¬Nat.Coprime n q) : χ (n:ZMod q)=0 :=
    χ.map_nonunit (fun h => hn ((ZMod.isUnit_iff_coprime n q).mp h))
  calc
    _ = ‖∑ n∈Finset.Ioc 0 ⌊x⌋₊,(χ (n:ZMod q)-χ.primitiveCharacter (n:ZMod χ.conductor))*
        (ArithmeticFunction.vonMangoldt n:ℂ)‖ := by
      congr 1
      simp only [primeCharacterPrefix,sub_mul,Finset.sum_sub_distrib]
    _ ≤ ∑ n∈Finset.Ioc 0 ⌊x⌋₊,‖(χ (n:ZMod q)-χ.primitiveCharacter (n:ZMod χ.conductor))*
        (ArithmeticFunction.vonMangoldt n:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n∈(Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬Nat.Coprime n q),ArithmeticFunction.vonMangoldt n := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro n _
      by_cases hn : Nat.Coprime n q
      · simp [hn,hsame n hn]
      · simp only [ite_eq_left hn,hzero n hn,zero_sub,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
          (χ.primitiveCharacter.norm_le_one _)
    _ ≤ _ := vonMangoldt_noncoprime_sum_le _ hq

theorem primeCharacterError_primitive_difference (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter‖≤
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have he : primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter=
      primeCharacterPrefix x χ-primeCharacterPrefix x χ.primitiveCharacter := by
    simp only [primeCharacterError,primitiveCharacter_eq_one_iff hq χ]
    ring
  rw [he]
  exact primeCharacterPrefix_primitive_difference x hq χ

theorem primeCharacterError_le_primitive (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterError x χ‖≤‖primeCharacterError x χ.primitiveCharacter‖+
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have hn := norm_add_le (primeCharacterError x χ.primitiveCharacter)
    (primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter)
  rw [add_sub_cancel] at hn
  exact hn.trans (add_le_add_right (primeCharacterError_primitive_difference x hq χ) _)

end LargePrimeGaps
end OAI

end

open Finset Filter MeasureTheory
open scoped Topology

namespace GoldbachMajorArc

noncomputable section

def primeWeight (k : ℕ) : ℝ := if k.Prime then Real.log (k : ℝ) else 0

def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def primeSum (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), (primeWeight k : ℂ) * phase ((k : ℝ) * t)

private theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

/-- The geometric sum in the rational-frequency approximation, with the same endpoints as the prime sum. -/
def kernel (n : ℕ) (β : ℝ) : ℂ := ∑ k ∈ range (n + 1), phase ((k : ℝ) * β)

def unitMean (q a : ℕ) : ℂ :=
  (∑ r ∈ (range q).filter (fun r => Nat.Coprime r q), phase ((r : ℝ) * ((a : ℝ) / q))) /
    (q.totient : ℂ)

def centerErrorTerm (r : ℝ) (A : ℂ) (k : ℕ) : ℂ :=
  (primeWeight k : ℂ) * phase ((k : ℝ) * r) - A

/-- The largest initial segment discrepancy at the center, through the last term k = n. -/
def prefixError (n : ℕ) (r : ℝ) (A : ℂ) : ℝ :=
  (range (n + 2)).sup' ⟨0, by simp⟩ (fun m => ‖∑ k ∈ range m, centerErrorTerm r A k‖)

private theorem prefix_le {m n : ℕ} (hm : m ≤ n + 1) (r : ℝ) (A : ℂ) :
    ‖∑ k ∈ range m, centerErrorTerm r A k‖ ≤ prefixError n r A :=
  Finset.le_sup' (fun m => ‖∑ k ∈ range m, centerErrorTerm r A k‖) (mem_range.mpr (by omega))

private theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private theorem phase_step (k : ℕ) (β : ℝ) :
    ‖phase (((k + 1 : ℕ) : ℝ) * β) - phase ((k : ℝ) * β)‖ ≤ 2 * Real.pi * |β| := by
  have shift : ((k + 1 : ℕ) : ℝ) * β = k * β + β := by push_cast; ring
  rw [shift, phase_add, ← mul_sub_one, norm_mul, norm_phase, one_mul]
  unfold phase
  rw [mul_comm _ Complex.I]
  calc
    _ ≤ ‖2 * Real.pi * β‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = _ := by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]

/-- Abel summation transports the finite initial segment discrepancies at r to a nearby frequency. -/
theorem shifted_sum_error (n : ℕ) (r β : ℝ) (A : ℂ) :
    ‖primeSum n (r + β) - A * kernel n β‖ ≤
      prefixError n r A * (1 + 2 * Real.pi * (n : ℝ) * |β|) := by
  let g := centerErrorTerm r A
  let v := fun k : ℕ => phase ((k : ℝ) * β)
  let D := prefixError n r A
  have hD : 0 ≤ D := (norm_nonneg _).trans (prefix_le (m := 0) (n := n) (by omega) r A)
  have expand : primeSum n (r + β) - A * kernel n β = ∑ k ∈ range (n + 1), v k * g k := by
    unfold primeSum kernel
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_add, phase_add]
    dsimp [v, g, centerErrorTerm]
    ring
  have habel := Finset.sum_range_by_parts (M := ℂ) v g (n + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at habel
  have hfirst : ‖v n * ∑ k ∈ range (n + 1), g k‖ ≤ D := by
    rw [norm_mul, show ‖v n‖ = 1 from norm_phase _, one_mul]
    exact prefix_le le_rfl r A
  have htail : ‖∑ i ∈ range n, (v (i + 1) - v i) * ∑ k ∈ range (i + 1), g k‖ ≤
      (n : ℝ) * (2 * Real.pi * |β| * D) := by
    calc
      _ ≤ ∑ i ∈ range n, ‖(v (i + 1) - v i) * ∑ k ∈ range (i + 1), g k‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i ∈ range n, 2 * Real.pi * |β| * D := by
        refine sum_le_sum fun i hi => ?_
        rw [norm_mul]
        exact mul_le_mul (phase_step i β) (prefix_le (by have := mem_range.mp hi; omega) r A)
          (norm_nonneg _) (by positivity)
      _ = _ := by simp
  rw [expand, habel]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ D + n * (2 * Real.pi * |β| * D) := add_le_add hfirst htail
    _ = _ := by dsimp [D]; ring

private theorem phase_nat (k : ℕ) : phase (k : ℝ) = 1 := by
  unfold phase
  convert Complex.exp_nat_mul_two_pi_mul_I k using 2
  push_cast
  ring

private theorem phase_modulo {q : ℕ} (hq : 0 < q) (k a : ℕ) :
    phase ((k : ℝ) * ((a : ℝ) / q)) = phase (((k % q : ℕ) : ℝ) * ((a : ℝ) / q)) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hk : (k : ℝ) = ((k % q : ℕ) : ℝ) + q * ((k / q : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div k q).symm
  have harg : (k : ℝ) * ((a : ℝ) / q) =
      ((k % q : ℕ) : ℝ) * ((a : ℝ) / q) + (((k / q * a : ℕ) : ℝ)) := by
    push_cast
    nth_rw 1 [hk]
    field_simp
  rw [harg, phase_add, phase_nat, mul_one]

/-- Logarithmic prime weight in one residue class for the initial segment 0 ≤ k < m. -/
def classMass (m q b : ℕ) : ℝ := ∑ k ∈ (range m).filter (fun k => k % q = b), primeWeight k

def classError (m q b : ℕ) : ℝ :=
  classMass m q b - if b.Coprime q then (m : ℝ) / q.totient else 0

/-- Exact expansion of the initial segment discrepancy at a rational center in progression errors. -/
theorem center_prefix_eq {q : ℕ} (hq : 0 < q) (a m : ℕ) :
    ∑ k ∈ range m, centerErrorTerm ((a : ℝ) / q) (unitMean q a) k =
      ∑ b ∈ range q, (classError m q b : ℂ) * phase ((b : ℝ) * ((a : ℝ) / q)) := by
  let e := fun k : ℕ => phase ((k : ℝ) * ((a : ℝ) / q))
  have masses : (∑ k ∈ range m, (primeWeight k : ℂ) * e k) =
      ∑ b ∈ range q, (classMass m q b : ℂ) * e b := by
    symm
    calc
      _ = ∑ b ∈ range q, ∑ k ∈ (range m).filter (fun k => k % q = b),
          (primeWeight k : ℂ) * e k := by
        refine sum_congr rfl fun b _ => ?_
        rw [classMass, Complex.ofReal_sum, sum_mul]
        refine sum_congr rfl fun k hk => ?_
        have he : e k = e b := by
          dsimp [e]
          rw [phase_modulo hq k a, (mem_filter.mp hk).2]
        rw [he]
      _ = _ := sum_fiberwise_of_maps_to (fun k _ => mem_range.mpr (Nat.mod_lt k hq)) _
  have model : (m : ℂ) * unitMean q a =
      ∑ b ∈ range q, (↑(if b.Coprime q then (m : ℝ) / q.totient else 0) : ℂ) * e b := by
    calc
      _ = ((m : ℂ) / q.totient) * ∑ b ∈ (range q).filter (fun b => b.Coprime q), e b := by
        unfold unitMean
        dsimp [e]
        ring
      _ = _ := by
        rw [mul_sum, sum_filter]
        refine sum_congr rfl fun b _ => ?_
        by_cases h : b.Coprime q
        · rw [ite_eq_left h, ite_eq_left h, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast]
        · rw [ite_eq_right h, ite_eq_right h, Complex.ofReal_zero, zero_mul]
  change (∑ k ∈ range m, ((primeWeight k : ℂ) * e k - unitMean q a)) = _
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, masses, model, ← sum_sub_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [← sub_mul, classError, Complex.ofReal_sub]

/-- A useful bound even without a uniform prime number theorem in progressions. -/
theorem center_prefix_bound {q : ℕ} (hq : 0 < q) (a m : ℕ) :
    ‖∑ k ∈ range m, centerErrorTerm ((a : ℝ) / q) (unitMean q a) k‖ ≤
      ∑ b ∈ range q, |classError m q b| := by
  rw [center_prefix_eq hq]
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro b _
  rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs]

end

end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset Filter MeasureTheory
open OAI.LargePrimeGaps

noncomputable section

/-- The character form of Siegel–Walfisz gives a uniform bound for a reduced class.
The second term pays for replacing the character by its primitive character. -/
theorem progression_error (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ q b : ℕ, 0 < q → (q : ℝ) ≤ (Real.log x) ^ B →
        b < q → b.Coprime q →
        |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q b - x / q.totient| ≤
          M * x * (Real.log x) ^ (-A) + (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log q := by
  obtain ⟨M, hM, x₀, hx₀, hχ⟩ := siegelWalfisz A B hA hB
  refine ⟨M, hM, x₀, hx₀, ?_⟩
  intro x hx q b hq hqlog hb hcop
  let : NeZero q := ⟨hq.ne'⟩
  have hchar (χ : DirichletCharacter ℂ q) :
      ‖primeCharacterError x χ‖ ≤
        M * x * (Real.log x) ^ (-A) + (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log q := by
    have hcond : (χ.conductor : ℝ) ≤ q := by
      exact_mod_cast Nat.le_of_dvd hq χ.conductor_dvd_level
    exact (primeCharacterError_le_primitive x hq χ).trans (add_le_add
      (hχ x hx χ.conductor (Nat.pos_of_ne_zero χ.conductor_ne_zero) (hcond.trans hqlog) χ.primitiveCharacter
        χ.primitiveCharacter_isPrimitive) (le_refl _))
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  apply (endpointClassError_le_character_sum x hq hb hcop).trans
  apply (div_le_iff₀ hφ).mpr
  calc
    _ ≤ ∑ _χ : DirichletCharacter ℂ q,
        (M * x * (Real.log x) ^ (-A) + (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log q) :=
      sum_le_sum fun χ _ => hchar χ
    _ = _ := by rw [sum_const, card_univ, hcard, nsmul_eq_mul, mul_comm]

private theorem primeWeight_le_mangoldt (k : ℕ) :
    primeWeight k ≤ ArithmeticFunction.vonMangoldt k := by
  by_cases hk : k.Prime
  · simp [primeWeight, hk, ArithmeticFunction.vonMangoldt_apply_prime hk]
  · simp [primeWeight, hk]

private theorem classMass_succ (N q b : ℕ) :
    classMass (N + 1) q b =
      ∑ k ∈ (Ioc 0 N).filter (fun k => k % q = b), primeWeight k := by
  rw [classMass, Nat.range_succ_eq_Icc_zero, sum_filter, sum_filter, ← add_sum_Ioc_eq_sum_Icc]
  · simp [primeWeight]
  · exact Nat.zero_le _

/-- Restriction to one class can discard no more prime-power mass than ψ(N) − θ(N). -/
theorem prime_power_correction (N q b : ℕ) :
    |classMass (N + 1) q b - residuePrefix ArithmeticFunction.vonMangoldt N q b| ≤
      Chebyshev.psi N - Chebyshev.theta N := by
  rw [classMass_succ, residuePrefix, residueSlice, abs_sub_comm, ← sum_sub_distrib,
    abs_of_nonneg (sum_nonneg fun k _ => sub_nonneg.mpr (primeWeight_le_mangoldt k))]
  have htotal : (∑ k ∈ Ioc 0 N, (ArithmeticFunction.vonMangoldt k - primeWeight k)) =
      Chebyshev.psi N - Chebyshev.theta N := by
    simp only [sum_sub_distrib, Chebyshev.psi, Chebyshev.theta, Nat.floor_natCast, sum_filter,
      primeWeight]
  rw [← htotal]
  apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
  exact fun k _ _ => sub_nonneg.mpr (primeWeight_le_mangoldt k)

/-- Siegel–Walfisz for the actual logarithmic prime weights, uniformly in reduced residue
classes. The additive terms account for nonprimitive characters and proper prime powers. -/
theorem prime_progression_error (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
      ∀ N q b : ℕ, x₀ ≤ N → 0 < q → (q : ℝ) ≤ (Real.log N) ^ B →
        b < q → b.Coprime q →
        |classMass (N + 1) q b - (N : ℝ) / q.totient| ≤
          M * N * (Real.log N) ^ (-A) + (Nat.log 2 N : ℝ) * Real.log q +
            2 * Real.sqrt N * Real.log N := by
  obtain ⟨M, hM, x₀, hx₀, h⟩ := progression_error A B hA hB
  refine ⟨M, hM, x₀, hx₀, ?_⟩
  intro N q b hN hq hlog hb hcop
  have he := h (N : ℝ) hN q b hq hlog hb hcop
  simp only [Nat.floor_natCast] at he
  have hpow := (prime_power_correction N q b).trans (Chebyshev.psi_sub_theta_le (hx₀.le.trans hN))
  exact (abs_sub_le _ (residuePrefix ArithmeticFunction.vonMangoldt N q b) _).trans
    ((add_le_add hpow he).trans_eq (add_comm _ _))

private theorem classMass_nonunit (N q b : ℕ) (hq : 0 < q) (hb : ¬ b.Coprime q) :
    classMass (N + 1) q b ≤ (Nat.log 2 N : ℝ) * Real.log q := by
  rw [classMass_succ]
  have hs : (Ioc 0 N).filter (fun k => k % q = b) ⊆
      (Ioc 0 N).filter (fun k => ¬ k.Coprime q) := by
    intro k hk
    obtain ⟨hkN, hkb⟩ := mem_filter.mp hk
    refine mem_filter.mpr ⟨hkN, fun h => hb ?_⟩
    rw [← hkb, Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_rec, Nat.gcd_comm]
    exact h.gcd_eq_one
  calc
    _ ≤ ∑ k ∈ (Ioc 0 N).filter (fun k => k % q = b), ArithmeticFunction.vonMangoldt k :=
      sum_le_sum fun k _ => primeWeight_le_mangoldt k
    _ ≤ ∑ k ∈ (Ioc 0 N).filter (fun k => ¬ k.Coprime q), ArithmeticFunction.vonMangoldt k :=
      sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ ≤ _ := vonMangoldt_noncoprime_sum_le N hq

/-- A single error budget for every residue, with the initial segment length and the q-dependent
constant exactly as in the expansion of the prime exponential sum. -/
theorem all_class_error (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
      ∀ N q b : ℕ, x₀ ≤ N → 0 < q → (q : ℝ) ≤ (Real.log N) ^ B → b < q →
        |classError (N + 1) q b| ≤
          M * N * (Real.log N) ^ (-A) + (Nat.log 2 N : ℝ) * Real.log q +
            2 * Real.sqrt N * Real.log N + 1 := by
  obtain ⟨M, hM, x₀, hx₀, h⟩ := prime_progression_error A B hA hB
  refine ⟨M, hM, x₀, hx₀, ?_⟩
  intro N q b hN hq hlog hb
  have hN' : (1 : ℝ) ≤ N := hx₀.le.trans hN
  have hL : 0 ≤ Real.log N := Real.log_nonneg hN'
  by_cases hcop : b.Coprime q
  · rw [classError, ite_eq_left hcop]
    have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
    have hlast : |(N : ℝ) / q.totient - ((N + 1 : ℕ) : ℝ) / q.totient| ≤ 1 := by
      rw [show (N : ℝ) / q.totient - ((N + 1 : ℕ) : ℝ) / q.totient = -(1 / (q.totient : ℝ)) by
        push_cast; ring, abs_neg, abs_of_nonneg (by positivity)]
      exact (div_le_one (by linarith)).mpr hφ
    exact (abs_sub_le _ ((N : ℝ) / q.totient) _).trans (add_le_add (h N q b hN hq hlog hb hcop) hlast)
  · rw [classError, ite_eq_right hcop, sub_zero, abs_of_nonneg (by
      unfold classMass
      apply sum_nonneg
      intro k _
      unfold primeWeight
      split_ifs with h
      · exact Real.log_nonneg (by exact_mod_cast h.one_le)
      · exact le_rfl)]
    have hmain : 0 ≤ M * N * (Real.log N) ^ (-A) := by positivity
    have hpower : 0 ≤ 2 * Real.sqrt N * Real.log N := by positivity
    linarith [classMass_nonunit N q b hq hcop]

end

end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset Filter MeasureTheory
open scoped ComplexConjugate

noncomputable section

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

end
end GoldbachMajorArc

/- The finite CRT and prime-power calculations below adapt goldbach-proofs PRs #207 (XianWu18) and #203 (wzhxzkk), Apache-2.0. -/
namespace GoldbachMajorArc.RamanujanCRT
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

end GoldbachMajorArc.RamanujanCRT
namespace GoldbachMajorArc.RamanujanPower
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

end GoldbachMajorArc.RamanujanPower

namespace GoldbachMajorArc

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

theorem ram_unit (q h : ℕ) (hc : h.Coprime q) : ram q h = ram q 1 := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ k =>
      have hc' := (Nat.coprime_pow_right_iff (Nat.succ_pos k) h p).mp hc
      rw [ram_unit_power hp k h hc', ram_unit_power hp k 1 (by simp)]
  | coprime q r hq hr hqr iq ir =>
    obtain ⟨h₁,h₂⟩ := Nat.coprime_mul_iff_right.mp hc
    rw [ram_mul (by omega) (by omega) hqr, ram_mul (by omega) (by omega) hqr, iq h₁, ir h₂]

theorem unitMean_eq_ram {q a : ℕ} (h : a.Coprime q) :
    unitMean q a = ram q 1 / (q.totient : ℂ) := by
  calc
    _ = ram q a / (q.totient : ℂ) := by
      apply congrArg (fun z : ℂ => z / (q.totient : ℂ))
      apply sum_congr rfl
      intro k _
      exact congrArg phase (by ring)
    _ = _ := congrArg (fun z : ℂ => z / (q.totient : ℂ)) (ram_unit q a h)

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

theorem sum_centers_eq_coefficient (q n : ℕ) :
    (∑ a ∈ (range q).filter (fun a => a.Coprime q),
      (unitMean q a) ^ 2 * phase (-(n : ℝ) * ((a : ℝ) / q))) = coefficient q n := by
  unfold coefficient ram
  rw [map_sum, mul_sum]
  refine sum_congr rfl fun a ha => ?_
  rw [unitMean_eq_ram (mem_filter.mp ha).2]
  congr 1
  unfold phase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

end
end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset
noncomputable section

def badFactor (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1) ^ 2

private theorem badFactor_nonneg (p : ℕ) : 0 ≤ badFactor p := by unfold badFactor; positivity

private theorem tail_telescope (m : ℕ) :
    ∏ p ∈ range (m + 5), (if 5 ≤ p then 1 + badFactor p else 1) ≤
      4 * ((m : ℝ) + 3) / (3 * ((m : ℝ) + 4)) := by
  induction m with
  | zero =>
    have h : ∏ p ∈ range (0 + 5), (if 5 ≤ p then 1 + badFactor p else 1) = 1 :=
      prod_eq_one fun p hp => ite_eq_right (Nat.not_le.mpr (mem_range.mp hp))
    norm_num [h]
  | succ m ih =>
    rw [show m.succ + 5 = (m + 5) + 1 by omega, prod_range_succ, ite_eq_left (show 5 ≤ m + 5 by omega)]
    apply (mul_le_mul_of_nonneg_right ih (by linarith [badFactor_nonneg (m + 5)])).trans
    unfold badFactor
    push_cast
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have h₁ : 0 < (m : ℝ) + 4 := by linarith
    have h₂ : 0 < (m : ℝ) + 1 + 4 := by linarith
    rw [show (m : ℝ) + 5 - 1 = m + 4 by ring]
    field_simp
    nlinarith only [hm]

private theorem product_tail_le {s : Finset ℕ} (hs : ∀ p ∈ s, 5 ≤ p) :
    ∏ p ∈ s, (1 + badFactor p) ≤ 4 / 3 := by
  let m := s.sup id
  have hsub : s ⊆ range (m + 5) := by
    intro p hp
    have h : p ≤ m := Finset.le_sup (f := id) hp
    exact mem_range.mpr (by omega)
  calc
    _ = ∏ p ∈ s, (if 5 ≤ p then 1 + badFactor p else 1) :=
      prod_congr rfl fun p hp => (ite_eq_left (hs p hp)).symm
    _ ≤ ∏ p ∈ range (m + 5), (if 5 ≤ p then 1 + badFactor p else 1) := by
      refine prod_le_prod_of_subset_of_one_le₀ hsub ?_ ?_
      · intro i _
        split_ifs <;> linarith [badFactor_nonneg i]
      · intro i _ _
        split_ifs <;> linarith [badFactor_nonneg i]
    _ ≤ _ := tail_telescope m
    _ ≤ 4 / 3 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
      linarith

/-- Every finite set of odd primes has absolute Euler excess at most 2/3.
Separate p = 3 and telescope the comparison product starting at p = 5. -/
theorem product_bad_factors {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) :
    ∏ p ∈ s, (1 + badFactor p) ≤ 5 / 3 := by
  have hrest : ∀ p ∈ s.erase 3, 5 ≤ p := by
    intro p hp
    obtain ⟨hne, hmem⟩ := mem_erase.mp hp
    obtain ⟨hprime, hpos⟩ := hs p hmem
    have hfour : p ≠ 4 := by rintro rfl; exact (by decide : ¬ Nat.Prime 4) hprime
    omega
  have hsub : s ⊆ insert 3 (s.erase 3) := by intro p hp; by_cases p = 3 <;> simp_all
  calc
    _ ≤ ∏ p ∈ insert 3 (s.erase 3), (1 + badFactor p) :=
      prod_le_prod_of_subset_of_one_le₀ hsub (fun p _ => by linarith [badFactor_nonneg p])
        (fun p _ _ => by linarith [badFactor_nonneg p])
    _ = (5 / 4) * ∏ p ∈ s.erase 3, (1 + badFactor p) := by
      rw [prod_insert (notMem_erase _ _)]
      congr 1
      norm_num [badFactor]
    _ ≤ (5 / 4) * (4 / 3) := mul_le_mul_of_nonneg_left (product_tail_le hrest) (by norm_num)
    _ = _ := by norm_num

/-- Summing the signed factors at primes away from an even target leaves at least
a third of the mass at d. The function W may already include a denominator cutoff. -/
theorem negative_factors_lower {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ 2 < p)
    (W : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ W k) (hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i)
    {d : ℕ} (hd : 0 < d) :
    W d / 3 ≤ ∑ t ∈ s.powerset, (∏ p ∈ t, -badFactor p) * W (d * ∏ p ∈ t, p) := by
  let P := s.powerset.erase ∅
  have hempty : ∅ ∈ s.powerset := mem_powerset.mpr (empty_subset _)
  have hrest : (∑ t ∈ P, ∏ p ∈ t, badFactor p) + 1 ≤ 5 / 3 := by
    have h := prod_one_add (f := badFactor) s
    rw [← sum_erase_add _ _ hempty] at h
    simp only [prod_empty] at h
    rw [← h]
    exact product_bad_factors hs
  have hterm (t : Finset ℕ) (ht : t ∈ P) :
      -(W d * ∏ p ∈ t, badFactor p) ≤ (∏ p ∈ t, -badFactor p) * W (d * ∏ p ∈ t, p) := by
    have ht' : t ⊆ s := mem_powerset.mp (mem_erase.mp ht).2
    have hprod : 0 < ∏ p ∈ t, p := prod_pos fun p hp => (hs p (ht' hp)).1.pos
    have hle := hmono d (d * ∏ p ∈ t, p) hd (Nat.le_mul_of_pos_right d hprod)
    apply (abs_le.mp ?_).1
    rw [abs_mul, abs_of_nonneg (hnonneg _), Finset.abs_prod]
    simp_rw [abs_neg, abs_of_nonneg (badFactor_nonneg _)]
    rw [mul_comm (W d)]
    exact mul_le_mul_of_nonneg_left hle (prod_nonneg fun _ _ => badFactor_nonneg _)
  have low := sum_le_sum hterm
  simp only [sum_neg_distrib, ← mul_sum] at low
  have cap := mul_le_mul_of_nonneg_left (show (∑ t ∈ P, ∏ p ∈ t, badFactor p) ≤ 2 / 3 by linarith) (hnonneg d)
  rw [← sum_erase_add _ _ hempty]
  simp only [prod_empty, mul_one, one_mul]
  dsimp only [P] at low cap
  linarith

end
end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset
noncomputable section

private theorem coefficient_not_squarefree {q : ℕ} (n : ℕ) (hq : 0 < q)
    (hs : ¬ Squarefree q) : coefficient q n = 0 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => exact (hs squarefree_one).elim
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => exact (hs (by simpa using hp.squarefree)).elim
      | succ j => exact coefficient_higher_power hp j n
  | coprime a b ha hb hab ia ib =>
    rw [coefficient_mul (by omega) (by omega) hab]
    by_cases h : Squarefree a
    · rw [ib (by omega) (fun h' => hs ((Nat.squarefree_mul hab).mpr ⟨h,h'⟩)), mul_zero]
    · rw [ia (by omega) h, zero_mul]

private theorem coefficient_prime_product (n : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    coefficient (∏ p ∈ s, p) n = ((∏ p ∈ s, localCoefficient p n : ℝ) : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficient_one]
  | @insert p s hp ih =>
    have hprime := hs p (mem_insert_self _ _)
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (mem_insert_of_mem hr)
    have hcop : p.Coprime (∏ r ∈ s, r) := Nat.coprime_prod_right_iff.mpr fun r hr =>
      (Nat.coprime_primes hprime (hs' r hr)).mpr fun he => hp (he ▸ hr)
    rw [prod_insert hp, prod_insert hp, coefficient_mul hprime.pos (prod_pos fun r hr => (hs' r hr).pos) hcop,
      coefficient_prime hprime, ih hs', Complex.ofReal_mul]

private theorem reindex_denominators (Q n : ℕ) (W : ℕ → ℝ) (hcut : ∀ q, Q < q → W q = 0) :
    (∑ q ∈ Icc 1 Q, (coefficient q n).re * W q) =
    ∑ t ∈ ((range (Q + 1)).filter Nat.Prime).powerset, (∏ p ∈ t, localCoefficient p n) * W (∏ p ∈ t, p) := by
  classical
  let P := (range (Q + 1)).filter Nat.Prime
  have hprime {t : Finset ℕ} (ht : t ∈ P.powerset) : ∀ p ∈ t, p.Prime :=
    fun p hp => (mem_filter.mp (mem_powerset.mp ht hp)).2
  symm
  apply sum_bij_ne_zero (fun t _ _ => ∏ p ∈ t, p)
  · intro t ht hnz
    exact mem_Icc.mpr ⟨prod_pos fun p hp => (hprime ht p hp).pos, le_of_not_gt fun h => hnz (by rw [hcut _ h, mul_zero])⟩
  · intro s hs _ t ht _ he
    exact (Nat.primeFactors_prod (hprime hs)).symm.trans ((congrArg Nat.primeFactors he).trans (Nat.primeFactors_prod (hprime ht)))
  · intro q hq hnz
    have hq' := mem_Icc.mp hq
    have hsq : Squarefree q := by
      by_contra hh
      exact hnz (by rw [coefficient_not_squarefree n hq'.1 hh]; simp)
    have hprod := Nat.prod_primeFactors_of_squarefree hsq
    have hsub : q.primeFactors ∈ P.powerset := by
      apply mem_powerset.mpr
      intro p hp
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_mem_primeFactors hp).trans hq'.2)),
        Nat.prime_of_mem_primeFactors hp⟩
    have hc := coefficient_prime_product n q.primeFactors (hprime hsub)
    rw [hprod] at hc
    exact ⟨q.primeFactors, hsub, fun hh => hnz (by rw [hprod] at hh; simpa only [hc, Complex.ofReal_re] using hh), hprod⟩
  · intro t ht _
    rw [coefficient_prime_product n t (hprime ht), Complex.ofReal_re]

private theorem signed_powerset_floor (n : ℕ) (W : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ W k)
    (hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i)
    (B G : Finset ℕ) (hB : ∀ p ∈ B, (p.Prime ∧ 2 < p) ∧ ¬ p ∣ n)
    (hG : ∀ p ∈ G, p.Prime ∧ p ∣ n) (d : ℕ) (hd : 0 < d) :
    W d / 3 ≤ ∑ t ∈ (G ∪ B).powerset,
      (∏ p ∈ t, localCoefficient p n) * W (d * ∏ p ∈ t, p) := by
  classical
  induction G using Finset.induction_on generalizing d with
  | empty =>
    rw [empty_union]
    apply (negative_factors_lower (fun p hp => (hB p hp).1) W hnonneg hmono hd).trans
    apply le_of_eq
    apply sum_congr rfl
    intro t ht
    congr 1
    apply prod_congr rfl
    intro p hp
    simp [localCoefficient, badFactor, (hB p (mem_powerset.mp ht hp)).2]
  | @insert p G hp ih =>
    have hp' := hG p (mem_insert_self _ _)
    have hG' : ∀ r ∈ G, r.Prime ∧ r ∣ n := fun r hr => hG _ (mem_insert_of_mem hr)
    have hpB : p ∉ B := fun h => (hB p h).2 hp'.2
    have hpGB : p ∉ G ∪ B := by simp [hp, hpB]
    have hsign : 0 ≤ localCoefficient p n := by
      have h : (1 : ℝ) < p := by exact_mod_cast hp'.1.one_lt
      simp [localCoefficient, hp'.2, le_of_lt h]
    rw [insert_union, sum_powerset_insert hpGB]
    have hsecond : 0 ≤ ∑ t ∈ (G ∪ B).powerset, (∏ r ∈ insert p t, localCoefficient r n) *
        W (d * ∏ r ∈ insert p t, r) := by
      calc
        0 ≤ localCoefficient p n * (∑ t ∈ (G ∪ B).powerset, (∏ r ∈ t, localCoefficient r n) *
            W (d * p * ∏ r ∈ t, r)) :=
          mul_nonneg hsign ((div_nonneg (hnonneg _) (by norm_num)).trans (ih hG' _ (Nat.mul_pos hd hp'.1.pos)))
        _ = _ := by
          rw [mul_sum]
          apply sum_congr rfl
          intro t ht
          have hpt : p ∉ t := fun h => hpGB (mem_powerset.mp ht h)
          rw [prod_insert hpt, prod_insert hpt, ← mul_assoc d, mul_assoc (localCoefficient p n)]
    linarith [ih hG' d hd]

/-- The even-target arithmetic main term retains at least one third of the q = 1
mass under every nonnegative decreasing weight supported on the denominator cutoff. -/
theorem arithmetic_floor {Q n : ℕ} (hn : Even n) (W : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ W k)
    (hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i) (hcut : ∀ q, Q < q → W q = 0) :
    W 1 / 3 ≤ ∑ q ∈ Icc 1 Q, (coefficient q n).re * W q := by
  classical
  let P := (range (Q+1)).filter Nat.Prime
  let G := P.filter (fun p => p ∣ n)
  let B := P.filter (fun p => ¬ p ∣ n)
  have hGB : G ∪ B = P := by ext p; simp [G, B]; tauto
  have hB (p : ℕ) (hp : p ∈ B) : (p.Prime ∧ 2 < p) ∧ ¬ p ∣ n := by
    have hp' := (mem_filter.mp hp)
    have hpr := (mem_filter.mp hp'.1).2
    have hne : p ≠ 2 := fun e => hp'.2 (e ▸ even_iff_two_dvd.mp hn)
    exact ⟨⟨hpr, lt_of_le_of_ne hpr.two_le (Ne.symm hne)⟩, hp'.2⟩
  have hG (p : ℕ) (hp : p ∈ G) : p.Prime ∧ p ∣ n :=
    ⟨(mem_filter.mp (mem_filter.mp hp).1).2,(mem_filter.mp hp).2⟩
  have h := signed_powerset_floor n W hnonneg hmono B G hB hG 1 zero_lt_one
  rw [hGB] at h
  rw [reindex_denominators Q n W hcut]
  simpa only [one_mul] using h

end
end GoldbachMajorArc


/-! Bounds for the aggregate size of the Ramanujan coefficients of DFQDZZ's PR #316.
The bound is uniform in the frequency, including when the frequency has many prime divisors. -/
namespace GoldbachMajorArc
open Finset
noncomputable section

private def parityFactor (q : ℕ) : ℝ := if Even q then 2 else 1

private lemma parityFactor_coprime {u v : ℕ} (hc : u.Coprime v) :
    parityFactor (u*v) = parityFactor u * parityFactor v := by
  have hboth (hu : Even u) (hv : Even v) : False := by
    have hd := Nat.dvd_gcd (even_iff_two_dvd.mp hu) (even_iff_two_dvd.mp hv)
    rw [hc.gcd_eq_one] at hd; omega
  by_cases hu : Even u
  · have hv : ¬ Even v := hboth hu
    simp [parityFactor, hu, hv]
  · by_cases hv : Even v <;> simp [parityFactor, Nat.even_mul, hu, hv]

private lemma coeffPrime_size (n p : ℕ) (hp : p.Prime) :
    (p : ℝ) * ‖coefficient p n‖^2 ≤ parityFactor p := by
  have hp2 : 2 ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : 0 < (p : ℝ) - 1 := by linarith
  have h1 : ‖coefficient p n‖ ≤ 1 / ((p : ℝ) - 1) := by
    rw [coefficient_prime hp, Complex.norm_real, Real.norm_eq_abs]
    unfold localCoefficient
    split_ifs with hd
    · rw [abs_of_nonneg (by positivity)]
    · rw [abs_neg, abs_of_nonneg (by positivity)]
      apply one_div_le_one_div_of_le hp0; nlinarith
  have h2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 2) (Nat.cast_nonneg p)
  apply h2.trans
  by_cases htwo : p = 2
  · subst p; norm_num [parityFactor]
  have hp3 : 3 ≤ (p : ℝ) := by exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
  have hodd : ¬Even p := Nat.not_even_iff_odd.mpr (hp.odd_of_ne_two htwo)
  rw [parityFactor, ite_eq_right hodd, div_pow, one_pow, ← mul_div_assoc, mul_one]
  apply (div_le_iff₀ (by positivity)).mpr; nlinarith [sq_nonneg ((p : ℝ)-3)]

/-- Even squarefree moduli can lose a factor of two at the prime 2. -/
theorem coefficient_frequency_energy (q n : ℕ) : (q : ℝ) * ‖coefficient q n‖^2 ≤ parityFactor q := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => simp [parityFactor]
  | one => simp [coefficient_one, parityFactor]
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => simpa using coeffPrime_size n p hp
      | succ j => simp only [show j+1+1 = j+2 by omega, coefficient_higher_power hp, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]; unfold parityFactor; split <;> norm_num
  | coprime u v hu hv huv iu iv =>
    rw [coefficient_mul (by omega) (by omega) huv, Nat.cast_mul, norm_mul, mul_pow, parityFactor_coprime huv]
    calc _ = ((u:ℝ) * ‖coefficient u n‖^2) * ((v:ℝ) * ‖coefficient v n‖^2) := by ring
         _ ≤ parityFactor u * parityFactor v := mul_le_mul iu iv (by positivity) (by unfold parityFactor; split <;> norm_num)

/-- Summing the absolute coefficient values costs only a square root of the cutoff. -/
theorem sum_norm_coefficient_le_sqrt (Q n : ℕ) :
    ∑ q ∈ Finset.Icc 1 Q, ‖coefficient q n‖ ≤ 4 * Real.sqrt Q := by
  have hs (q : ℕ) : ‖coefficient (q+1) n‖ ≤
      4 * (Real.sqrt (q+1 : ℕ) - Real.sqrt q) := by
    let X := Real.sqrt (q+1 : ℕ)
    let Y := Real.sqrt q
    have hX : 0 < X := Real.sqrt_pos.mpr (by positivity)
    have hY : 0 ≤ Y := Real.sqrt_nonneg _
    have hXY : Y ≤ X := Real.sqrt_le_sqrt (by exact_mod_cast (Nat.le_succ q))
    have hX2 : X^2 = (q : ℝ) + 1 := by dsimp only [X]; push_cast; exact Real.sq_sqrt (by positivity)
    have hY2 : Y^2 = (q : ℝ) := Real.sq_sqrt (by positivity)
    have hh : (q+1 : ℝ) * ‖coefficient (q+1) n‖^2 ≤ 2 := by
      exact_mod_cast (coefficient_frequency_energy (q+1) n).trans (show parityFactor (q+1) ≤ 2 by unfold parityFactor; split <;> norm_num)
    have hb : ‖coefficient (q+1) n‖ * X ≤ 2 := by
      have : (‖coefficient (q+1) n‖ * X)^2 ≤ 2 := by rw [mul_pow, hX2, mul_comm]; exact hh
      nlinarith
    have hprod : (X-Y)*(X+Y) = 1 := by nlinarith [hX2,hY2]
    apply (le_of_mul_le_mul_right (a := X+Y) _ (by linarith : 0 < X+Y))
    change ‖coefficient (q+1) n‖ * (X+Y) ≤ 4 * (X-Y)*(X+Y)
    nlinarith [mul_le_mul_of_nonneg_left hXY (norm_nonneg (coefficient (q+1) n))]
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ Q+1)]
    linarith [hs Q]

end
end GoldbachMajorArc

/-! A change-of-frequency bound for the major-arc Dirichlet kernel. The centered-square
identity uses the reflection argument from DFQDZZ, goldbach-proofs PR #316 (Apache 2.0), and the
mode integral uses the argument from TranswarpDrive's PR #158. Taking the difference of
the two exact Fourier coefficients bounds the loss on any subinterval of one period. -/
namespace GoldbachEstermannKernel
noncomputable section
open Finset MeasureTheory
open scoped ComplexConjugate

def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
def kernel (M : ℕ) (t : ℝ) := ∑ k ∈ range (M + 1), phase ((k : ℝ) * t)
def twisted (M n : ℕ) (t : ℝ) := kernel M t ^ 2 * phase (-(n : ℝ) * t)

private lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase; rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma norm_phase (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private lemma phase_int (j : ℤ) : phase (j : ℝ) = 1 := by
  unfold phase
  convert Complex.exp_int_mul_two_pi_mul_I j using 2
  push_cast; ring

private lemma centered_mode (j : ℤ) :
    (∫ t in (-(1/2) : ℝ)..1/2, phase ((j : ℝ) * t)) = if j = 0 then 1 else 0 := by
  have hp : Function.Periodic (fun t : ℝ => phase ((j : ℝ) * t)) 1 := by
    intro t; simp only [mul_add, mul_one, phase_add, phase_int, mul_one]
  have hshift := hp.intervalIntegral_add_eq (-(1/2)) 0
  norm_num only [show (-(1/2) : ℝ) + 1 = 1/2 by norm_num, zero_add] at hshift
  rw [hshift]
  by_cases hj : j = 0
  · subst j; simp [phase]
  let c : ℂ := (j : ℂ) * (2 * Real.pi * Complex.I)
  have he (t : ℝ) : phase ((j : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
    unfold phase c; congr 1; push_cast; ring
  have hc : c ≠ 0 := mul_ne_zero (by exact_mod_cast hj)
    (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  simp_rw [he]; rw [integral_exp_mul_complex hc]; simp [hj, c, Complex.exp_int_mul_two_pi_mul_I]

/-- The coefficient of the square of a length M+1 kernel at every n up to M. -/
theorem full_coefficient (M n : ℕ) (hn : n ≤ M) :
    (∫ t in (-(1/2) : ℝ)..1/2, twisted M n t) = (n : ℂ) + 1 := by
  let I := range (M+1)
  let f (k j : ℕ) (t : ℝ) := phase (((k : ℤ) + (j : ℤ) - n : ℤ) * (t : ℝ))
  have hcont (k j : ℕ) : Continuous (f k j) := by dsimp [f, phase]; fun_prop
  have hex (t : ℝ) : twisted M n t = ∑ k ∈ I, ∑ j ∈ I, f k j t := by
    dsimp [twisted, kernel, I]
    simp only [sq, Finset.sum_mul, Finset.mul_sum]
    refine sum_congr rfl fun k _ => sum_congr rfl fun j _ => ?_
    dsimp [f]; push_cast; rw [← phase_add, ← phase_add]; congr 1; ring
  have hrow (k : ℕ) : (∫ t in (-(1/2) : ℝ)..1/2, ∑ j ∈ I, f k j t) = if k ≤ n then 1 else 0 := by
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont k j).intervalIntegrable _ _)]
    simp only [f, centered_mode]
    by_cases hk : k ≤ n
    · rw [ite_eq_left hk, sum_eq_single_of_mem (n-k) (show n-k ∈ I by apply mem_range.mpr; omega)]
      · simp [show (k : ℤ) + ↑(n-k) - ↑n = 0 by omega]
      · intro j _ hdiff; simp [show (k : ℤ) + ↑j - ↑n ≠ 0 by omega]
    · rw [ite_eq_right hk]; apply sum_eq_zero; intro j _; simp [show (k : ℤ) + ↑j - ↑n ≠ 0 by omega]
  simp_rw [hex]
  rw [intervalIntegral.integral_finsetSum (fun k _ => (continuous_finsetSum I fun j _ => hcont k j).intervalIntegrable _ _)]
  simp_rw [hrow]
  rw [← Finset.sum_filter]
  have hset : I.filter (fun k => k ≤ n) = range (n+1) := by ext k; simp [I]; omega
  simp [hset]

private lemma centered (M : ℕ) (t : ℝ) : twisted M M t = ((‖kernel M t‖^2 : ℝ) : ℂ) := by
  have hc (x : ℝ) : conj (phase x) = phase (-x) := by
    unfold phase; rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 1; push_cast; ring
  have hsym : kernel M t * phase (-(M : ℝ) * t) = conj (kernel M t) := by
    unfold kernel; rw [sum_mul, map_sum]
    calc
      _ = ∑ k ∈ range (M+1), conj (phase (((M-k : ℕ) : ℝ)*t)) := by
        apply sum_congr rfl
        intro k hk
        rw [hc, ← phase_add, Nat.cast_sub (Nat.lt_succ_iff.mp (mem_range.mp hk))]; congr 1; ring
      _ = _ := by simpa only [Nat.add_sub_cancel] using
                    (Finset.sum_range_reflect (fun k => conj (phase ((k : ℝ)*t))) (M+1))
  calc
    _ = kernel M t * (kernel M t * phase (-(M : ℝ) * t)) := by dsimp [twisted]; ring
    _ = _ := by rw [hsym, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private lemma cont (M n : ℕ) : Continuous (twisted M n) := by unfold twisted kernel phase; fun_prop

set_option maxHeartbeats 1200000 in
/-- On any subinterval of the centered period, changing the target M to n costs at most M−n. -/
theorem loss_on_interval (M n : ℕ) (hn : n ≤ M) {a b : ℝ} (ha : -(1/2) ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1/2) :
    0 ≤ (∫ t in a..b, ‖kernel M t‖ ^ 2) - (∫ t in a..b, (twisted M n t).re) ∧
      (∫ t in a..b, ‖kernel M t‖ ^ 2) - (∫ t in a..b, (twisted M n t).re) ≤ (M : ℝ) - n := by
  let loss (t : ℝ) := (twisted M M t).re - (twisted M n t).re
  have hnn (t : ℝ) : 0 ≤ loss t := by
    dsimp only [loss]; rw [centered, Complex.ofReal_re]; apply sub_nonneg.mpr
    apply (Complex.re_le_norm _).trans_eq
    simp [twisted, norm_pow, norm_phase]
  have hreal (j : ℕ) : Continuous (fun t => (twisted M j t).re) := Complex.continuous_re.comp (cont M j)
  have hcont : Continuous loss := (hreal M).sub (hreal n)
  have hex (c d : ℝ) : (∫ t in c..d, loss t) =
      (∫ t in c..d, (twisted M M t).re) - (∫ t in c..d, (twisted M n t).re) :=
    intervalIntegral.integral_sub ((hreal M).intervalIntegrable c d) ((hreal n).intervalIntegrable c d)
  have hre (j : ℕ) : (∫ t in (-(1/2) : ℝ)..1/2, (twisted M j t).re) =
      (∫ t in (-(1/2) : ℝ)..1/2, twisted M j t).re :=
    intervalIntegral.intervalIntegral_re (𝕜 := ℂ) ((cont M j).intervalIntegrable _ _)
  have hwhole : (∫ t in (-(1/2) : ℝ)..1/2, loss t) = (M : ℝ) - n := by
    rw [hex, hre, hre, full_coefficient M M le_rfl, full_coefficient M n hn]; simp
  have hlocal := hex a b
  simp only [centered, Complex.ofReal_re] at hlocal
  rw [← hlocal]
  exact ⟨intervalIntegral.integral_nonneg hab (fun t _ => hnn t),
    (intervalIntegral.integral_mono_interval ha hab hb (Filter.Eventually.of_forall hnn)
      (hcont.intervalIntegrable ..)).trans_eq hwhole⟩

end
end GoldbachEstermannKernel

namespace GoldbachMajorArc
noncomputable section
open Finset MeasureTheory

/-- Common rational arc radii for a block of frequencies near M. -/
def blockWidth (M Q q : ℕ) : ℝ := (Q : ℝ) / ((q : ℝ) * M)

def blockModel (M Q n : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 Q, (coefficient q n).re *
    ∫ t in -(blockWidth M Q q)..blockWidth M Q q, (GoldbachEstermannKernel.twisted M n t).re

/-- The spectrum length, cutoff and arc widths are uniform in the target n. -/
theorem block_model_floor (M Q n : ℕ) (hM : 0 < M) (hQ : 1 ≤ Q)
    (hdis : 2*Q ≤ M) (hn : n ≤ M) (heven : Even n) :
    (M : ℝ) / 72 - 4 * Real.sqrt Q * ((M : ℝ) - n) ≤ blockModel M Q n := by
  let W (q : ℕ) := if q ≤ Q then kernelMass M (blockWidth M Q q) else 0
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hQr : 1 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hwr (q : ℕ) : 0 ≤ blockWidth M Q q := by unfold blockWidth; positivity
  have hn' : 0 ≤ (M : ℝ) - n := sub_nonneg.mpr (by exact_mod_cast hn)
  have hnon (q : ℕ) : 0 ≤ W q := by
    dsimp only [W]; split_ifs
    · apply intervalIntegral.integral_nonneg (by linarith [hwr q]); intro t _; exact sq_nonneg _
    · rfl
  have hmono (i j : ℕ) (hi : 0 < i) (hij : i ≤ j) : W j ≤ W i := by
    by_cases hj : j ≤ Q
    · simp only [W, ite_eq_left hj, ite_eq_left (hij.trans hj)]
      apply kernelMass_mono (hwr j)
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos (by exact_mod_cast hi) hMr)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hMr.le
    · simp only [W, ite_eq_right hj]; exact hnon i
  have hsum := arithmetic_floor (Q := Q) heven W hnon hmono (by intro q hq; simp [W, not_le.mpr hq])
  have h1 : 1 / (6*(M : ℝ)) ≤ blockWidth M Q 1 := by
    unfold blockWidth; simp only [Nat.cast_one, one_mul]
    rw [div_le_div_iff₀ (by positivity) hMr]; nlinarith [mul_le_mul_of_nonneg_right hQr hMr.le]
  have hmodel : (M : ℝ) / 72 ≤ ∑ q ∈ Icc 1 Q, (coefficient q n).re * W q := by
    rw [show W 1 = kernelMass M (blockWidth M Q 1) by simp [W, hQ]] at hsum
    linarith [kernelMass_floor hM h1]
  have hdiff (q : ℕ) (hq : q ∈ Icc 1 Q) :
      (coefficient q n).re * W q - (coefficient q n).re *
        (∫ t in -(blockWidth M Q q)..blockWidth M Q q, (GoldbachEstermannKernel.twisted M n t).re) ≤
      ‖coefficient q n‖ * ((M : ℝ) - n) := by
    have hle : blockWidth M Q q ≤ 1/2 := by
      have hq' : (1 : ℝ) ≤ q := by exact_mod_cast (mem_Icc.mp hq).1
      have hdis' : 2 * (Q : ℝ) ≤ M := by exact_mod_cast hdis
      unfold blockWidth
      apply (div_le_iff₀ (mul_pos (by linarith) hMr)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hq' hMr.le]
    obtain ⟨hpos,hloss⟩ := GoldbachEstermannKernel.loss_on_interval M n hn
      (neg_le_neg hle) (by linarith [hwr q] : -(blockWidth M Q q) ≤ blockWidth M Q q) hle
    rw [← mul_sub, show W q = kernelMass M (blockWidth M Q q) by simp [W, (mem_Icc.mp hq).2]]
    exact mul_le_mul (Complex.re_le_norm _) hloss hpos (norm_nonneg _)
  have htot := Finset.sum_le_sum hdiff
  rw [sum_sub_distrib, ← sum_mul] at htot
  have hcoef := mul_le_mul_of_nonneg_right (sum_norm_coefficient_le_sqrt Q n) hn'
  unfold blockModel
  linarith

theorem coefficient_im_zero {q : ℕ} (n : ℕ) (hq : 0 < q) : (coefficient q n).im = 0 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => simp [coefficient_one]
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => simp [coefficient_prime hp]
      | succ j => rw [coefficient_higher_power hp]; rfl
  | coprime u v hu hv huv iu iv =>
    simp [coefficient_mul (by omega : 0 < u) (by omega : 0 < v) huv,
      Complex.mul_im, iu (by omega), iv (by omega)]

/-- Reassemble the unscaled complex coefficient and pass real parts through its integral. -/
theorem block_model_complex_re (M Q n : ℕ) :
    (∑ q ∈ Icc 1 Q, coefficient q n *
      ∫ t in -(blockWidth M Q q)..blockWidth M Q q, GoldbachEstermannKernel.twisted M n t).re =
    blockModel M Q n := by
  rw [Complex.re_sum]
  unfold blockModel
  apply sum_congr rfl
  intro q hq
  have hc : Continuous (GoldbachEstermannKernel.twisted M n) := by
    unfold GoldbachEstermannKernel.twisted GoldbachEstermannKernel.kernel GoldbachEstermannKernel.phase
    fun_prop
  rw [Complex.mul_re, coefficient_im_zero n (by have := (mem_Icc.mp hq).1; omega),
    zero_mul, sub_zero]
  exact congrArg ((coefficient q n).re * ·)
    (intervalIntegral.intervalIntegral_re (𝕜 := ℂ) (hc.intervalIntegrable _ _)).symm

end
end GoldbachMajorArc



/-!
Uniform square-model errors on full major arcs for any fixed logarithmic exponent.
The starting finite inequalities and Siegel--Walfisz application are from DFQDZZ's
goldbach-proofs PR #316 at e4ab24712555ae8c2c926adf19d368a9fb392c35 (Apache-2.0).
Its Siegel--Walfisz proof is adapted from OpenAI/math, as recorded in the attribution above.
The arbitrary cutoff exponent, arbitrary target twist and log-power savings below
are the new generalizations.
-/
namespace GoldbachMajorArc.Polylog
open Finset Filter MeasureTheory
open scoped Topology
noncomputable section

def cutoff (B n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ B

private theorem nat_log_two_le {u : ℕ} (hu : 1 ≤ u) :
    (Nat.log 2 u : ℝ) ≤ 2 * Real.log u := by
  have hL : 0 ≤ Real.log u := Real.log_nonneg (by exact_mod_cast hu)
  have h₂ := Real.log_two_gt_d9
  have h := Real.natLog_le_logb u 2
  simp only [Nat.cast_ofNat, Real.logb] at h
  refine h.trans ((div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr ?_)
  nlinarith only [mul_nonneg hL (show 0 ≤ 2 * Real.log 2 - 1 by linarith)]
theorem cutoff_le_log (B : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    (cutoff B n : ℝ) ≤ (4 * Real.log n) ^ B := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have harg : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hl := Real.log_le_log (by positivity : 0 < (n : ℝ) + 2) harg
  rw [Real.log_pow] at hl
  norm_num1 at hl
  have hnat := nat_log_two_le (u := n + 2) (by omega)
  push_cast at hnat
  have h : (Nat.log 2 (n + 2) : ℝ) ≤ 4 * Real.log n := by linarith
  simpa only [cutoff, Nat.cast_pow] using
    pow_le_pow_left₀ (Nat.cast_nonneg (Nat.log 2 (n + 2)) (α := ℝ)) h B

private theorem class_error_trivial (u q b : ℕ) (hq : 0 < q) :
    |classError (u + 1) q b| ≤ (Real.log 4 + 1) * ((u : ℝ) + 1) := by
  have hw (k : ℕ) : 0 ≤ primeWeight k := by
    unfold primeWeight
    split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_le)
    · exact le_rfl
  have hmass : classMass (u + 1) q b ≤ Real.log 4 * u := by
    unfold classMass
    calc
      _ ≤ ∑ k ∈ range (u + 1), primeWeight k :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k _ _ => hw k)
      _ = Chebyshev.theta u := by
        rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range, sum_filter]; rfl
      _ ≤ _ := Chebyshev.theta_le_log4_mul_x (by positivity)
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hfrac : ((u + 1 : ℕ) : ℝ) / q.totient ≤ (u : ℝ) + 1 := by
    push_cast
    exact div_le_self (by positivity) hφ
  push_cast at hfrac
  have hm : 0 ≤ classMass (u + 1) q b := sum_nonneg (fun k _ => hw k)
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold classError
  split_ifs
  · apply abs_le.mpr
    constructor <;> push_cast <;> nlinarith [show 0 ≤ ((u : ℝ) + 1) / q.totient by positivity,
      mul_nonneg hlog (Nat.cast_nonneg (α := ℝ) u)]
  · rw [sub_zero, abs_of_nonneg hm]
    linarith [Nat.cast_nonneg (α := ℝ) u]

def errorEnvelope (B K : ℕ) (M : ℝ) (n : ℕ) : ℝ :=
  M * 2 ^ (K+1) * n / (Real.log n) ^ (K+1) + (2 * 4 ^ B) * (Real.log n) ^ (B+1) +
    2 * Real.sqrt n * Real.log n + 1 + (Real.log 4 + 1) * (Real.sqrt n + 1)

theorem uniform_prefix_error (B K : ℕ) (hB : 0 < B) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop, ∀ q a : ℕ, 0 < q → q ≤ cutoff B n →
      prefixError n ((a : ℝ) / q) (unitMean q a) ≤ q * errorEnvelope B K M n := by
  obtain ⟨M, hM, x₀, hx₀, hAP⟩ := all_class_error ((K+1 : ℕ) : ℝ) ((2*B : ℕ) : ℝ) (by positivity) (by positivity)
  refine ⟨M, hM, ?_⟩
  have hlim := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hroot := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2 : ℕ), hlim.eventually_ge_atTop 16,
    hroot.eventually_ge_atTop x₀] with n hn hL hrootN
  change (16 : ℝ) ≤ Real.log n at hL
  change x₀ ≤ Real.sqrt n at hrootN
  intro q a hq hQ
  have hnL : 0 < Real.log n := by linarith
  have hQ' : (q : ℝ) ≤ (4 * Real.log n) ^ B :=
    (show (q : ℝ) ≤ cutoff B n by exact_mod_cast hQ).trans (cutoff_le_log B hn)
  have hconst : 0 < Real.log 4 + 1 := by positivity
  have henv : 0 ≤ errorEnvelope B K M n := by unfold errorEnvelope; positivity
  unfold prefixError
  apply Finset.sup'_le
  intro m hm
  refine (center_prefix_bound hq a m).trans ?_
  calc
    _ ≤ ∑ _b ∈ range q, errorEnvelope B K M n := by
      apply sum_le_sum
      intro b hb
      cases m with
      | zero => simpa [classError, classMass] using henv
      | succ u =>
        have hun : u ≤ n := by have := mem_range.mp hm; omega
        have hun' : (u : ℝ) ≤ n := by exact_mod_cast hun
        by_cases hs : (u : ℝ) < Real.sqrt n
        · refine (class_error_trivial u q b hq).trans ?_
          have hsmall := mul_le_mul_of_nonneg_left (add_le_add hs.le (le_refl (1 : ℝ))) hconst.le
          unfold errorEnvelope
          linarith [show 0 ≤ M * 2 ^ (K+1) * n / (Real.log n) ^ (K+1) by positivity,
            show 0 ≤ (2 * 4 ^ B) * (Real.log n) ^ (B+1) by positivity, show 0 ≤ 2 * Real.sqrt n * Real.log n by positivity]
        · have hsu := le_of_not_gt hs
          have hux : x₀ ≤ (u : ℝ) := hrootN.trans hsu
          have hu1 : (1 : ℝ) < u := hx₀.trans_le hux
          have huL := Real.log_pos hu1
          have hhalf := Real.log_le_log (by linarith : 0 < Real.sqrt n) hsu
          rw [Real.log_sqrt (Nat.cast_nonneg n)] at hhalf
          have hupper := Real.log_le_log (by linarith : 0 < (u : ℝ)) hun'
          have hu8 : 8 ≤ Real.log u := by linarith
          have hbase : 4 * Real.log n ≤ (Real.log u) ^ 2 := by
            nlinarith only [hhalf, hu8, mul_nonneg huL.le (sub_nonneg.mpr hu8)]
          have hmod : (q : ℝ) ≤ (Real.log u) ^ (2*B : ℕ) := by
            rw [pow_mul]
            exact hQ'.trans (pow_le_pow_left₀ (by positivity) hbase B)
          have hraw := hAP u q b hux hq (by simpa only [Real.rpow_natCast] using hmod) (mem_range.mp hb)
          have hrpow : (Real.log u) ^ (-((K+1 : ℕ) : ℝ)) = 1 / (Real.log u) ^ (K+1) := by
            rw [Real.rpow_neg huL.le, Real.rpow_natCast, one_div]
          rw [hrpow, ← div_eq_mul_one_div] at hraw
          have hpow := pow_le_pow_left₀ hnL.le (show Real.log n ≤ 2 * Real.log u by linarith) (K+1)
          rw [mul_pow] at hpow
          have hmain : M * (u : ℝ) / (Real.log u) ^ (K+1) ≤ M * 2 ^ (K+1) * n / (Real.log n) ^ (K+1) := by
            apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
            calc
              _ ≤ (M * n) * (2 ^ (K+1) * (Real.log u) ^ (K+1)) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hun' hM.le) hpow (by positivity) (by positivity)
              _ = _ := by ring
          have hNat := (nat_log_two_le (u := u) (by exact_mod_cast hu1.le)).trans
            (mul_le_mul_of_nonneg_left hupper (by norm_num : (0 : ℝ) ≤ 2))
          have hlogq : Real.log q ≤ (4 * Real.log n) ^ B :=
            (Real.log_le_self (Nat.cast_nonneg q)).trans hQ'
          have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
          have herr := mul_le_mul hNat hlogq hlogq0 (by positivity)
          have hsqrt := mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hun') (by norm_num : (0 : ℝ) ≤ 2))
            hupper huL.le (by positivity)
          have herr' : (Nat.log 2 u : ℝ) * Real.log q ≤ (2 * 4 ^ B) * (Real.log n) ^ (B+1) := by
            refine herr.trans_eq ?_
            rw [mul_pow, pow_succ]
            ring
          unfold errorEnvelope
          linarith only [hraw, hmain, herr', hsqrt,
            mul_nonneg hconst.le (show 0 ≤ Real.sqrt n + 1 by positivity)]
    _ = _ := by simp

private theorem log_power_over_power (k : ℕ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => (Real.log n) ^ k / (n : ℝ) ^ s) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Real.rpow_natCast] using
    ((isLittleO_log_rpow_rpow_atTop (k : ℝ) hs).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))

theorem envelope_saving (B K : ℕ) (M : ℝ) :
    Tendsto (fun n : ℕ => (Real.log n) ^ K * errorEnvelope B K M n / n) atTop (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmain : Tendsto (fun n : ℕ => M * 2 ^ (K+1) / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hself (k : ℕ) : Tendsto (fun n : ℕ => (Real.log n) ^ k / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using log_power_over_power k (show (0:ℝ) < 1 by norm_num)
  have hsqrt (k : ℕ) : Tendsto (fun n : ℕ => (Real.log n) ^ k / Real.sqrt n) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using log_power_over_power k (show (0:ℝ) < 1 / 2 by norm_num)

  have hsum := (((hmain.add ((hself (K+(B+1))).const_mul (2 * 4 ^ B))).add
    ((hsqrt (K+1)).const_mul 2)).add (hself K)).add
    (((hsqrt K).add (hself K)).const_mul (Real.log 4 + 1))
  simp only [mul_zero, add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hL := (Real.log_pos hn').ne'
  have hv := (Real.sqrt_pos.mpr (zero_lt_one.trans hn')).ne'
  have alg (L v : ℝ) (hL : L ≠ 0) (hv : v ≠ 0) :
      M * 2 ^ (K+1) / L + (2 * 4 ^ B) * (L ^ (K+(B+1)) / v ^ 2) +
        2 * (L ^ (K+1) / v) + L ^ K / v ^ 2 + (Real.log 4 + 1) * (L ^ K / v + L ^ K / v ^ 2) =
      L ^ K * (M * 2 ^ (K+1) * v ^ 2 / L ^ (K+1) + (2 * 4 ^ B) * L ^ (B+1) +
        2 * v * L + 1 + (Real.log 4 + 1) * (v + 1)) / v ^ 2 := by
    simp only [pow_add, pow_one]
    field_simp
  have h := alg (Real.log n) (Real.sqrt n) hL hv
  rw [Real.sq_sqrt (Nat.cast_nonneg n)] at h
  simpa [errorEnvelope] using h

end
end GoldbachMajorArc.Polylog

namespace GoldbachMajorArc.Polylog
open Finset Filter MeasureTheory
open scoped Topology
noncomputable section

def width (Q n q : ℕ) : ℝ := (Q : ℝ) / ((q : ℝ) * n)

/-- Absolute square-model error at frequency m, centered at a/q. -/
def modelError (n q a : ℕ) (m β : ℝ) : ℝ :=
  let t := (a : ℝ) / q + β
  ‖(primeSum n t)^2 * phase (-m*t) - (unitMean q a * kernel n β)^2 * phase (-m*t)‖

theorem modelError_eq (n q a : ℕ) (m β : ℝ) :
    modelError n q a m β =
      ‖(primeSum n ((a : ℝ) / q + β))^2 - (unitMean q a * kernel n β)^2‖ := by
  unfold modelError
  dsimp only
  rw [← sub_mul, norm_mul, show ∀ x, ‖phase x‖ = 1 from fun _ => Complex.norm_exp_ofReal_mul_I _, mul_one]

def totalArcError (Q n : ℕ) (m : ℝ) : ℝ :=
  ∑ q ∈ Icc 1 Q, ∑ a ∈ range (q + 1),
    ∫ β in -(width Q n q)..(width Q n q), modelError n q a m β

theorem totalArcError_frequency_independent (Q n : ℕ) (m m' : ℝ) :
    totalArcError Q n m = totalArcError Q n m' := by
  simp only [totalArcError, modelError_eq]
private theorem primeWeight_nonneg (k : ℕ) : 0 ≤ primeWeight k := by
  unfold primeWeight
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_le)
  · exact le_rfl

private theorem sum_primeWeight (n : ℕ) :
    ∑ k ∈ range (n + 1), primeWeight k = Chebyshev.theta n := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range, sum_filter]
  rfl
private theorem prefix_le {m n : ℕ} (hm : m ≤ n + 1) (r : ℝ) (A : ℂ) :
    ‖∑ k ∈ range m, centerErrorTerm r A k‖ ≤ prefixError n r A :=
  Finset.le_sup' (fun m => ‖∑ k ∈ range m, centerErrorTerm r A k‖) (mem_range.mpr (by omega))

private theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I _
theorem rational_arc_error {Q n q a : ℕ} (hn : 0 < n) (hq : 0 < q) {β : ℝ}
    (hβ : |β| ≤ (Q : ℝ) / ((q : ℝ) * n)) :
    ‖primeSum n ((a : ℝ) / q + β) - unitMean q a * kernel n β‖ ≤
      prefixError n ((a : ℝ) / q) (unitMean q a) * (1 + 2 * Real.pi * ((Q : ℝ) / q)) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hscale : (n : ℝ) * |β| ≤ (Q : ℝ) / q := by
    apply (le_div_iff₀ hq').mpr
    calc
      _ = |β| * ((q : ℝ) * n) := by ring
      _ ≤ _ := (le_div_iff₀ (mul_pos hq' hn')).mp hβ
  have hD : 0 ≤ prefixError n ((a : ℝ) / q) (unitMean q a) :=
    (norm_nonneg _).trans (prefix_le (m := 0) (n := n) (by omega) _ _)
  refine (shifted_sum_error n ((a : ℝ) / q) β (unitMean q a)).trans ?_
  apply mul_le_mul_of_nonneg_left _ hD
  apply add_le_add_right
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hscale (by positivity)
theorem squared_arc_error {Q n q a : ℕ} (m : ℝ) (hn : 0 < n) (hq : 0 < q) {β : ℝ}
    (hβ : |β| ≤ (Q : ℝ) / ((q : ℝ) * n)) :
    let r : ℝ := (a : ℝ) / q
    let A := unitMean q a
    modelError n q a m β ≤
      prefixError n r A * (1 + 2 * Real.pi * ((Q : ℝ) / q)) *
        (Chebyshev.theta n + ‖A‖ * (n + 1 : ℕ)) := by
  intro r A
  have hsum : ‖primeSum n (r + β)‖ ≤ Chebyshev.theta n := by
    rw [primeSum, ← sum_primeWeight]
    refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (primeWeight_nonneg k)]
  have hkernel : ‖kernel n β‖ ≤ (n + 1 : ℕ) := by
    unfold kernel
    refine (norm_sum_le _ _).trans ?_
    simp [norm_phase]
  have hplus : ‖primeSum n (r + β) + A * kernel n β‖ ≤ Chebyshev.theta n + ‖A‖ * (n + 1 : ℕ) := by
    refine (norm_add_le _ _).trans (add_le_add hsum ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hkernel (norm_nonneg _)
  rw [modelError_eq,
    show (primeSum n (r + β)) ^ 2 - (A * kernel n β) ^ 2 =
      (primeSum n (r + β) - A * kernel n β) * (primeSum n (r + β) + A * kernel n β) by ring,
    norm_mul]
  exact mul_le_mul (rational_arc_error (a := a) hn hq hβ) hplus (norm_nonneg _)
    ((norm_nonneg _).trans (rational_arc_error (a := a) hn hq hβ))
private theorem unitMean_norm (q a : ℕ) (hq : 0 < q) : ‖unitMean q a‖ ≤ 1 := by
  let U := (range q).filter (fun r => r.Coprime q)
  have hcard : U.card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    have h : U = (range q).filter (fun r => q.Coprime r) := by ext k; simp [U, Nat.coprime_comm]
    rw [h]
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  unfold unitMean
  rw [norm_div, Complex.norm_natCast, div_le_one hφ]
  refine (norm_sum_le _ _).trans ?_
  change ∑ r ∈ U, ‖phase ((r : ℝ) * ((a : ℝ) / q))‖ ≤ _
  simp only [phase, Complex.norm_exp_ofReal_mul_I, sum_const, nsmul_eq_mul, mul_one, hcard, le_refl]
private theorem integral_error_bound {Q n q : ℕ} (m : ℝ) (hn : 1 ≤ n) (hq : 0 < q) (hQ : q ≤ Q)
    (a : ℕ) {E : ℝ} (hE : 0 ≤ E)
    (hp : prefixError n ((a : ℝ) / q) (unitMean q a) ≤ q * E) :
    (∫ β in -(width Q n q)..(width Q n q), modelError n q a m β) ≤
      2 * (Q : ℝ) ^ 2 * E * ((1 + 2 * Real.pi) * (Real.log 4 + 2)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hQ' : (q : ℝ) ≤ Q := by exact_mod_cast hQ
  have npos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn'
  have qpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq'
  let B := E * ((1 + 2 * Real.pi) * (Q : ℝ)) * ((Real.log 4 + 2) * (n : ℝ))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have wpos : 0 ≤ width Q n q := by unfold width; positivity
  have hlength : width Q n q ≤ (Q : ℝ) / n := by
    unfold width
    apply div_le_div_of_nonneg_left (by positivity) npos
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right hq' npos.le)
  have hpoint {β : ℝ} (hβ : β ∈ Set.Icc (-(width Q n q)) (width Q n q)) :
      modelError n q a m β ≤ B := by
    have hp' := squared_arc_error (a := a) m hn hq (abs_le.mpr hβ)
    have hscale :
        prefixError n ((a : ℝ) / q) (unitMean q a) * (1 + 2 * Real.pi * ((Q : ℝ) / q)) ≤
        E * ((1 + 2 * Real.pi) * (Q : ℝ)) := by
      calc
        _ ≤ ((q : ℝ) * E) * (1 + 2 * Real.pi * ((Q : ℝ) / q)) :=
          mul_le_mul_of_nonneg_right hp (by positivity)
        _ = E * ((q : ℝ) + 2 * Real.pi * Q) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith only [hQ']) hE
    have hU := unitMean_norm q a hq
    have hcap : Chebyshev.theta n + ‖unitMean q a‖ * (n + 1 : ℕ) ≤ (Real.log 4 + 2) * (n : ℝ) := by
      have hcard := mul_le_mul_of_nonneg_right hU (show 0 ≤ (n : ℝ) + 1 by positivity)
      push_cast
      nlinarith only [Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n), hcard, hn']
    exact hp'.trans (mul_le_mul hscale hcap (by positivity) (by positivity))
  have hc : Continuous (modelError n q a m) := by
    unfold modelError primeSum kernel phase
    fun_prop
  calc
    _ ≤ ∫ _β in -(width Q n q)..(width Q n q), B :=
      intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _)
        (by simp) (fun β hβ => hpoint hβ)
    _ = (2 * width Q n q) * B := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    _ ≤ (2 * ((Q : ℝ) / n)) * B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlength (by norm_num)) hB
    _ = _ := by dsimp [B]; field_simp

private theorem totalArcError_nonneg (Q n : ℕ) (m : ℝ) : 0 ≤ totalArcError Q n m := by
  refine sum_nonneg fun q _ => sum_nonneg fun a _ => ?_
  have hw : 0 ≤ width Q n q := by unfold width; positivity
  exact intervalIntegral.integral_nonneg (by linarith) fun _ _ => norm_nonneg _

/-- Finite absolute error estimate, with arbitrary cutoff and twist. -/
theorem totalArcError_le {Q n : ℕ} (hn1 : 1 ≤ n) (hQ1 : 1 ≤ Q) (m : ℝ)
    {E : ℝ} (hE : 0 ≤ E) (hp : ∀ q a : ℕ, 0 < q → q ≤ Q →
      prefixError n ((a : ℝ) / q) (unitMean q a) ≤ q * E) :
    totalArcError Q n m ≤
      (4 * ((1 + 2 * Real.pi) * (Real.log 4 + 2))) * (Q : ℝ)^4 * E := by
  have hQ' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
  let C : ℝ := 4 * ((1 + 2 * Real.pi) * (Real.log 4 + 2))
  let B : ℝ := 2 * (Q : ℝ) ^ 2 * E * ((1 + 2 * Real.pi) * (Real.log 4 + 2))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have htot : totalArcError Q n m ≤ C * (Q : ℝ) ^ 4 * E := by
    unfold totalArcError
    calc
      _ ≤ ∑ _q ∈ Icc 1 Q, (((Q : ℝ) + 1) * B) := by
        refine sum_le_sum fun q hq => ?_
        have hq' := mem_Icc.mp hq
        calc
          _ ≤ ∑ _a ∈ range (q + 1), B := sum_le_sum fun a _ =>
            integral_error_bound m hn1 hq'.1 hq'.2 a hE (hp q a hq'.1 hq'.2)
          _ = ((q : ℝ) + 1) * B := by simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hq'.2 1) hB
      _ = (Q : ℝ) * (((Q : ℝ) + 1) * B) := by simp [Nat.card_Icc]
      _ ≤ (Q : ℝ) * ((2 * (Q : ℝ)) * B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hB) (Nat.cast_nonneg _)
      _ = _ := by dsimp [B, C]; ring
  exact htot

/-- The sum of the absolute errors on all full arcs is o(n/log(n)^S), for every
fixed natural S and every positive exponent B in Q=(log₂(n+2))^B. The target
frequency may vary arbitrarily with n. -/
theorem totalArcError_log_saving (B S : ℕ) (hB : 0 < B) (freq : ℕ → ℝ) :
    Tendsto (fun n : ℕ => (Real.log n)^S * totalArcError (cutoff B n) n (freq n) / n)
      atTop (𝓝 0) := by
  obtain ⟨M, hM, hpre⟩ := uniform_prefix_error B (S+B*4) hB
  let C : ℝ := 4 * ((1 + 2 * Real.pi) * (Real.log 4 + 2))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlimit := (envelope_saving B (S+B*4) M).const_mul (C * (4^B)^4)
  simp only [mul_zero] at hlimit
  apply squeeze_zero' (Eventually.of_forall fun n => div_nonneg (mul_nonneg
    (pow_nonneg (Real.log_natCast_nonneg n) _) (totalArcError_nonneg _ _ _)) (Nat.cast_nonneg n)) _ hlimit
  filter_upwards [hpre, eventually_ge_atTop (2 : ℕ)] with n hp hn
  have hn1 : 1 ≤ n := by omega
  have hQ1 : 1 ≤ cutoff B n := Nat.one_le_iff_ne_zero.mpr
    (pow_ne_zero B (Nat.log_pos (by decide : 1 < 2) (by omega : 2 ≤ n + 2)).ne')
  have hL : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hE : 0 ≤ errorEnvelope B (S+B*4) M n := by unfold errorEnvelope; positivity
  have htot := totalArcError_le hn1 hQ1 (freq n) hE hp
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (cutoff B n)) (cutoff_le_log B hn) 4
  have hcomp : (cutoff B n : ℝ)^4 ≤ (4^B)^4 * (Real.log n)^(B*4) := by
    simpa only [mul_pow, pow_mul] using hpow
  calc
    _ ≤ (Real.log n)^S * (C * (cutoff B n : ℝ)^4 * errorEnvelope B (S+B*4) M n) / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htot (pow_nonneg hL _)) (Nat.cast_nonneg n)
    _ ≤ (Real.log n)^S * (C * ((4^B)^4 * (Real.log n)^(B*4)) * errorEnvelope B (S+B*4) M n) / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcomp hC) hE) (pow_nonneg hL _)) (Nat.cast_nonneg n)
    _ = _ := by simp only [pow_add]; ring

theorem totalArcError_sublinear (B : ℕ) (hB : 0 < B) (freq : ℕ → ℝ) :
    Tendsto (fun n : ℕ => totalArcError (cutoff B n) n (freq n) / n) atTop (𝓝 0) := by
  simpa only [pow_zero, one_mul] using totalArcError_log_saving B 0 hB freq

/-- With one threshold uniform in the target frequency. -/
theorem eventually_totalArcError_lt (B S : ℕ) (hB : 0 < B) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℝ, (Real.log n)^S * totalArcError (cutoff B n) n m < ε * n := by
  have h := (tendsto_order.1 (totalArcError_log_saving B S hB (fun _ => 0))).2 ε hε
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with n hn hnpos m
  rw [totalArcError_frequency_independent _ _ m 0]
  exact (div_lt_iff₀ (show (0 : ℝ) < n by exact_mod_cast hnpos)).mp hn

end
end GoldbachMajorArc.Polylog
end

section GoldbachDeepFourthPrimeDenominator

namespace GoldbachFourthMoment
open Finset

noncomputable def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

-- Finite character calculation adapted from DFQDZZ, goldbach-proofs PR 316.
theorem full_phase_sum (q h : ℕ) (hq : 0 < q) :
    (∑ a ∈ range q, phase ((h : ℝ) * a / q)) = if q ∣ h then (q : ℂ) else 0 := by
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
        dsimp [phase]
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

theorem prime_phase_sum {q : ℕ} (hq : q.Prime) (h : ℕ) :
    (∑ a ∈ (range q).filter (fun a => a.Coprime q), phase ((h : ℝ) * a / q)) =
      (if q ∣ h then (q : ℂ) else 0) - 1 := by
  have hF : (range q).filter (fun a => a.Coprime q) = range q \ {0} := by
    ext a
    simp only [mem_filter, mem_sdiff, mem_singleton]
    constructor
    · rintro ⟨ha, hc⟩
      refine ⟨ha, ?_⟩
      rintro rfl
      exact hq.ne_one (by simpa using hc)
    · rintro ⟨ha, hz⟩
      refine ⟨ha, (hq.coprime_iff_not_dvd.mpr ?_).symm⟩
      exact fun hd => hz (Nat.eq_zero_of_dvd_of_lt hd (mem_range.mp ha))
  have hsub : ({0} : Finset ℕ) ⊆ range q := by simpa using hq.pos
  rw [hF]
  calc
    _ = (∑ a ∈ range q, phase ((h : ℝ) * a / q)) -
        (∑ a ∈ ({0} : Finset ℕ), phase ((h : ℝ) * a / q)) :=
      eq_sub_of_add_eq (sum_sdiff hsub)
    _ = _ := by rw [full_phase_sum q h hq.pos]; simp [phase]

noncomputable def primeWeight (k : ℕ) : ℝ := if k.Prime then Real.log (k : ℝ) else 0

noncomputable def primeSum (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), (primeWeight k : ℂ) * phase ((k : ℝ) * t)

theorem sum_prime_centers {n q : ℕ} (hq : q.Prime) (hqn : q ≤ n) (β : ℝ) :
    ∑ a ∈ (range q).filter (fun a => a.Coprime q), primeSum n ((a : ℝ) / q + β) =
      -primeSum n β + (q : ℂ) * (Real.log (q : ℝ) : ℂ) * phase ((q : ℝ) * β) := by
  let centers := (range q).filter (fun a => a.Coprime q)
  let term (k : ℕ) := (primeWeight k : ℂ) * phase ((k : ℝ) * β)
  have hphase (k a : ℕ) : (primeWeight k : ℂ) * phase ((k : ℝ) * (a / q + β)) =
      term k * phase ((k : ℝ) * a / q) := by
    rw [show (k : ℝ) * (a / q + β) = (k : ℝ) * a / q + k * β by ring, phase_add]
    dsimp [term]
    ring
  have hterm (k : ℕ) :
      term k * (∑ a ∈ centers, phase ((k : ℝ) * a / q)) =
        -term k + if k = q then (q : ℂ) * term q else 0 := by
    rw [prime_phase_sum hq]
    by_cases hk : k.Prime
    · have hd : q ∣ k ↔ k = q := by
        constructor
        · intro h
          exact ((Nat.dvd_prime hk).mp h).resolve_left hq.ne_one |>.symm
        · rintro rfl
          exact dvd_refl _
      by_cases h : k = q
      · subst k
        rw [ite_eq_left (dvd_refl _), ite_eq_left rfl]
        ring
      · rw [ite_eq_right (fun hh => h (hd.mp hh)), ite_eq_right h]
        ring
    · have hne : k ≠ q := by
        rintro rfl
        exact hk hq
      simp [term, primeWeight, hk, hne]
  unfold primeSum
  simp_rw [hphase]
  rw [sum_comm]
  simp_rw [← mul_sum]
  change (∑ k ∈ range (n + 1), term k * ∑ a ∈ centers, phase ((k : ℝ) * a / q)) = _
  simp_rw [hterm, sum_add_distrib, sum_neg_distrib]
  have hqmem : q ∈ range (n + 1) := mem_range.mpr (by omega)
  simp [hqmem, term, primeWeight, hq, mul_assoc]

theorem fourth_power_of_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖f i‖ ^ 4 := by
  let x := ∑ i ∈ s, ‖f i‖
  let y := ∑ i ∈ s, ‖f i‖ ^ 2
  let z := ∑ i ∈ s, ‖f i‖ ^ 4
  let k : ℝ := s.card
  have hx : ‖∑ i ∈ s, f i‖ ≤ x := norm_sum_le _ _
  have h₁ : x ^ 2 ≤ k * y := by
    simpa [x, y, k] using sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖f i‖)
  have h₂ : y ^ 2 ≤ k * z := by
    calc
      y ^ 2 ≤ k * ∑ i ∈ s, (‖f i‖ ^ 2) ^ 2 := by
        simpa [y, k] using sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖f i‖ ^ 2)
      _ = k * z := by
        congr 1
        exact sum_congr rfl (fun i _ => by ring)
  change _ ≤ k ^ 3 * z
  calc
    _ ≤ x ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hx 4
    _ = (x ^ 2) ^ 2 := by ring
    _ ≤ (k * y) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h₁ 2
    _ = k ^ 2 * y ^ 2 := by ring
    _ ≤ k ^ 2 * (k * z) := mul_le_mul_of_nonneg_left h₂ (sq_nonneg _)
    _ = _ := by ring


theorem reduced_eq_Ico {q : ℕ} (hq : q.Prime) :
    (range q).filter (fun a => a.Coprime q) = Ico 1 q := by
  ext a
  simp only [mem_filter, mem_range, mem_Ico]
  constructor
  · rintro ⟨ha, hc⟩
    refine ⟨?_, ha⟩
    by_contra! hz
    obtain rfl : a = 0 := by omega
    exact hq.ne_one (by simpa using hc)
  · rintro ⟨ha₁, ha₂⟩
    refine ⟨ha₂, (hq.coprime_iff_not_dvd.mpr ?_).symm⟩
    intro hd
    have := Nat.eq_zero_of_dvd_of_lt hd ha₂
    omega

private theorem primeWeight_nonneg (k : ℕ) : 0 ≤ primeWeight k := by
  unfold primeWeight
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_le)
  · exact le_rfl

private theorem primeSum_re (n : ℕ) (β : ℝ) : (primeSum n β).re =
    ∑ k ∈ range (n + 1), primeWeight k * Real.cos (2 * Real.pi * (k : ℝ) * β) := by
  unfold primeSum
  rw [Complex.re_sum]
  apply sum_congr rfl
  intro k _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    phase, Complex.exp_ofReal_mul_I_re, mul_assoc]

theorem one_prime_denominator {n q : ℕ} (hq : q.Prime) (hqn : q ≤ n)
    (β : ℝ) (hβ : |β| ≤ 1 / (20 * (n : ℝ)))
    (hθ : (n : ℝ) / 4 ≤ ∑ k ∈ range (n + 1), primeWeight k)
    (hsmall : (q : ℝ) * Real.log q ≤ (n : ℝ) / 16) :
    ((n : ℝ) / 16) ^ 4 / (q : ℝ) ^ 3 ≤
      ∑ a ∈ Ico 1 q, ‖primeSum n ((a : ℝ) / q + β)‖ ^ 4 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hq.pos.trans_le hqn
  have hcos (k : ℕ) (hk : k ∈ range (n + 1)) :
      (1 / 2 : ℝ) ≤ Real.cos (2 * Real.pi * (k : ℝ) * β) := by
    have hkN : (k : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hk)
    have hangle : |2 * Real.pi * (k : ℝ) * β| ≤ Real.pi / 3 := by
      calc
        _ = 2 * Real.pi * (k : ℝ) * |β| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
        _ ≤ 2 * Real.pi * (n : ℝ) * (1 / (20 * (n : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hkN (by positivity)) hβ
            (abs_nonneg _) (by positivity)
        _ = Real.pi / 10 := by
          field_simp
          ring
        _ ≤ Real.pi / 3 := by linarith [Real.pi_pos]
    calc
      _ = Real.cos (Real.pi / 3) := Real.cos_pi_div_three.symm
      _ ≤ Real.cos |2 * Real.pi * (k : ℝ) * β| :=
        Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hangle
      _ = _ := Real.cos_abs _
  have hs : (n : ℝ) / 8 ≤ (primeSum n β).re := by
    rw [primeSum_re]
    calc
      _ ≤ (∑ k ∈ range (n + 1), primeWeight k) * (1 / 2 : ℝ) := by linarith
      _ = ∑ k ∈ range (n + 1), primeWeight k * (1 / 2 : ℝ) := by rw [sum_mul]
      _ ≤ _ := sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hcos k hk) (primeWeight_nonneg k)
  let C := Ico 1 q
  let F (a : ℕ) := primeSum n ((a : ℝ) / q + β)
  let Z : ℂ := (q : ℂ) * (Real.log (q : ℝ) : ℂ) * phase ((q : ℝ) * β)
  have hsum : (∑ a ∈ C, F a) = -primeSum n β + Z := by
    simpa only [C, F, ← reduced_eq_Ico hq, Z] using sum_prime_centers hq hqn β
  have hZ : ‖Z‖ = (q : ℝ) * Real.log q := by
    have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq.one_le)
    have hphase : ‖phase ((q : ℝ) * β)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    simp only [Z, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlog, hphase, mul_one]
  have hback : ‖primeSum n β‖ ≤ ‖-primeSum n β + Z‖ + ‖Z‖ := by
    simpa only [add_sub_cancel_right, norm_neg] using norm_sub_le (-primeSum n β + Z) Z
  have hnorm : (n : ℝ) / 16 ≤ ‖∑ a ∈ C, F a‖ := by
    have hre : (primeSum n β).re ≤ ‖primeSum n β‖ :=
      (le_abs_self _).trans (Complex.abs_re_le_norm _)
    rw [hZ] at hback
    rw [hsum]
    linarith
  have hC : C.card ≤ q := by
    calc
      _ ≤ (range q).card := card_le_card fun a ha => mem_range.mpr (mem_Ico.mp ha).2
      _ = _ := card_range _
  have hnonneg : 0 ≤ ∑ a ∈ C, ‖F a‖ ^ 4 := sum_nonneg fun _ _ => by positivity
  apply (div_le_iff₀ (pow_pos hqR 3)).2
  change ((n : ℝ) / 16) ^ 4 ≤ (∑ a ∈ C, ‖F a‖ ^ 4) * (q : ℝ) ^ 3
  calc
    _ ≤ ‖∑ a ∈ C, F a‖ ^ 4 := pow_le_pow_left₀ (by positivity) hnorm 4
    _ ≤ (C.card : ℝ) ^ 3 * ∑ a ∈ C, ‖F a‖ ^ 4 := fourth_power_of_sum_le C F
    _ ≤ (q : ℝ) ^ 3 * ∑ a ∈ C, ‖F a‖ ^ 4 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hC) 3) hnonneg
    _ = _ := mul_comm _ _

end GoldbachFourthMoment

end GoldbachDeepFourthPrimeDenominator

section GoldbachDeepFourthPrimeCount

open Filter Finset
open scoped BigOperators

namespace GoldbachFourthMoment

theorem theta_eq_prime_log_sum (n : ℕ) :
    Chebyshev.theta n =
      ∑ k ∈ Finset.range (n + 1), if Nat.Prime k then Real.log (k : ℝ) else 0 := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, Finset.sum_filter,
    Nat.range_succ_eq_Icc_zero]

theorem eventually_theta_half : ∀ᶠ n : ℕ in atTop, (n : ℝ) / 2 ≤ Chebyshev.theta n := by
  have h := Chebyshev.isLittleO_psi_sub_theta_id.def (by norm_num : (0 : ℝ) < 1 / 10)
  filter_upwards [h.natCast_atTop, eventually_ge_atTop 7] with n hn h7
  have hn' : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs, abs_of_nonneg hn'] at hn
  have hlog : (3 / 5 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlo := mul_le_mul_of_nonneg_left hlog hn'
  linarith [Chebyshev.psi_ge_of_seven_le h7, (abs_le.mp hn).2]

theorem eventually_theta_quarter : ∀ᶠ n : ℕ in atTop, (n : ℝ) / 4 ≤ Chebyshev.theta n := by
  filter_upwards [eventually_theta_half] with n hn
  have hnn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

private theorem prime_denominators_log_floor :
    ∀ᶠ R : ℕ in atTop,
      (R : ℝ) / 2 ≤
        (((Finset.Ioc R (4 * R)).filter Nat.Prime).card : ℝ) * Real.log (4 * (R : ℝ)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 eventually_theta_half
  filter_upwards [eventually_ge_atTop N] with R hR
  have hR4 : R ≤ 4 * R := by omega
  have hhigh := hN (4 * R) (hR.trans hR4)
  push_cast at hhigh
  have hlow := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg R)
  have hlog : Real.log 4 ≤ (3 / 2 : ℝ) := by
    rw [Real.log_four_eq]
    linarith [Real.log_two_lt_d9]
  have hlow' := mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg R : 0 ≤ (R : ℝ))
  have hsplit : Chebyshev.theta (R : ℝ) +
      (∑ p ∈ (Finset.Ioc R (4 * R)).filter Nat.Prime, Real.log (p : ℝ)) =
        Chebyshev.theta ((4 * R : ℕ) : ℝ) := by
    simp only [Chebyshev.theta, Nat.floor_natCast, Finset.sum_filter]
    exact Finset.sum_Ioc_consecutive
      (fun p : ℕ => if Nat.Prime p then Real.log (p : ℝ) else 0) (Nat.zero_le R) hR4
  push_cast at hsplit
  have hupper :
      (∑ p ∈ (Finset.Ioc R (4 * R)).filter Nat.Prime, Real.log (p : ℝ)) ≤
        (((Finset.Ioc R (4 * R)).filter Nat.Prime).card : ℝ) * Real.log (4 * (R : ℝ)) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hpI, hpPrime⟩ := Finset.mem_filter.mp hp
    apply Real.log_le_log (by exact_mod_cast hpPrime.pos)
    exact_mod_cast (Finset.mem_Ioc.mp hpI).2
  linarith

private theorem eventually_log_le_mul_rpow (s c : ℝ) (hs : 0 < s) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ c * (n : ℝ) ^ s := by
  have h := (isLittleO_log_rpow_atTop hs).def hc
  filter_upwards [h.natCast_atTop] with n hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s)]
    using (le_abs_self (Real.log (n : ℝ))).trans hn

private theorem cube_root_floor_tendsto :
    Tendsto (fun n : ℕ => ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊) atTop atTop := by
  have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  exact tendsto_atTop.2 fun m =>
    ((tendsto_atTop.1 h) (m : ℝ)).mono fun n hn => Nat.le_floor hn

theorem eventually_many_prime_denominators : ∀ᶠ n : ℕ in atTop,
    let R := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
    (n : ℝ) ^ (1 / 4 : ℝ) ≤ (((Finset.Ioc R (4*R)).filter Nat.Prime).card : ℝ) := by
  filter_upwards [cube_root_floor_tendsto.eventually prime_denominators_log_floor,
    eventually_log_le_mul_rpow (1 / 12) (1 / 8) (by norm_num) (by norm_num),
    eventually_ge_atTop 4] with n hc hlog hn
  let R := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
  change (R : ℝ) / 2 ≤ _ at hc
  change (n : ℝ) ^ (1 / 4 : ℝ) ≤ _
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hnPos : 0 < (n : ℝ) := by linarith
  have hR1 : 1 ≤ R := Nat.le_floor (by simpa using Real.one_le_rpow hn1 (by norm_num : (0:ℝ) ≤ 1/3))
  have hR1' : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
  have hRlo : (n : ℝ) ^ (1 / 3 : ℝ) / 2 ≤ (R : ℝ) := by
    have h := Nat.lt_floor_add_one ((n : ℝ) ^ (1 / 3 : ℝ))
    change (n : ℝ) ^ (1 / 3 : ℝ) < (R : ℝ) + 1 at h
    linarith
  have hRhi : (R : ℝ) ≤ (n : ℝ) := by
    calc
      _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Nat.floor_le (Real.rpow_nonneg hnPos.le _)
      _ ≤ _ := by simpa using
        Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1/3 : ℝ) ≤ 1)
  have hlogR : Real.log (4 * (R : ℝ)) ≤ 2 * Real.log (n : ℝ) := by
    calc
      _ ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log (by linarith)
        (by nlinarith only [hRhi, hnR, sq_nonneg ((n : ℝ) - 4)])
      _ = _ := by rw [Real.log_pow]; norm_num
  have hpow : (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ) =
      (n : ℝ) ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add hnPos]
    congr 1
    norm_num
  apply le_of_mul_le_mul_right _ (Real.log_pos (by linarith : 1 < 4 * (R : ℝ)))
  calc
    _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) * (2 * Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogR (Real.rpow_nonneg hnPos.le _)
    _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) * (2 * ((1 / 8 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by norm_num)) (by positivity)
    _ = (n : ℝ) ^ (1 / 3 : ℝ) / 4 := by rw [← hpow]; ring
    _ ≤ (R : ℝ) / 2 := by linarith
    _ ≤ _ := hc

theorem eventually_small_denominator_log : ∀ᶠ n : ℕ in atTop,
    ∀ q : ℕ, q ≤ 4 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ →
      (q : ℝ) * Real.log (q : ℝ) ≤ (n : ℝ) / 16 := by
  filter_upwards [eventually_log_le_mul_rpow (2 / 3) (1 / 128) (by norm_num) (by norm_num),
    eventually_ge_atTop 4] with n hlog hn
  intro q hq
  rcases q.eq_zero_or_pos with rfl | hqPos
  · simp
    positivity
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hnPos : 0 < (n : ℝ) := by linarith
  have hqPos' : 0 < (q : ℝ) := by exact_mod_cast hqPos
  have hqHi : (q : ℝ) ≤ 4 * (n : ℝ) ^ (1 / 3 : ℝ) := calc
    _ ≤ 4 * (⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ : ℝ) := by exact_mod_cast hq
    _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.floor_le (Real.rpow_nonneg hnPos.le _)) (by norm_num)
  have hqHi' : (q : ℝ) ≤ 4 * (n : ℝ) := hqHi.trans <|
    mul_le_mul_of_nonneg_left
      (by simpa using Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1/3 : ℝ) ≤ 1))
      (by norm_num)
  have hlogq : Real.log (q : ℝ) ≤ 2 * Real.log (n : ℝ) := calc
    _ ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log hqPos'
      (by nlinarith only [hqHi', hnR, sq_nonneg ((n : ℝ) - 4)])
    _ = _ := by rw [Real.log_pow]; norm_num
  have hpow : (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) := by
    rw [← Real.rpow_add hnPos]
    norm_num
  calc
    _ ≤ (4 * (n : ℝ) ^ (1 / 3 : ℝ)) * (2 * Real.log (n : ℝ)) := by
      apply mul_le_mul hqHi hlogq
      · exact Real.log_nonneg (by exact_mod_cast hqPos)
      · positivity
    _ ≤ (4 * (n : ℝ) ^ (1 / 3 : ℝ)) * (2 * ((1 / 128 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by norm_num)) (by positivity)
    _ = ((n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ)) / 16 := by ring
    _ = _ := congrArg (fun x : ℝ => x / 16) hpow

end GoldbachFourthMoment

end GoldbachDeepFourthPrimeCount

section GoldbachWideArcSeparation

open Filter
open scoped Topology

namespace GoldbachWideArcs

/-- The triangle inequality and spacing of rational centers give this general width condition.
    This uses the rational-separation argument from goldbach-proofs PR 153. -/
theorem reduced_centers_eq_of_common_point {n H B q r a b : ℕ} {t : ℝ}
    (hn : 2 * H * B < n) (hq : 1 ≤ q) (hr : 1 ≤ r) (hqB : q ≤ B) (hrB : r ≤ B)
    (hca : a.Coprime q) (hcb : b.Coprime r)
    (ha : |t - (a : ℝ)/q| ≤ (H : ℝ)/((q : ℝ)*n))
    (hb : |t - (b : ℝ)/r| ≤ (H : ℝ)/((r : ℝ)*n)) : q = r ∧ a = b := by
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  have hrr : 0 < (r : ℝ) := by exact_mod_cast hr
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsmall : H*r + H*q < n := by
    nlinarith only [hn, Nat.mul_le_mul_left H hrB, Nat.mul_le_mul_left H hqB]
  have hradii : (H : ℝ)/(q*n) + H/(r*n) < 1/(q*r) := calc
    _ = ((H : ℝ)*r+H*q)/(q*r*n) := by field_simp
    _ < (n : ℝ)/(q*r*n) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hsmall)
    _ = _ := by field_simp
  have he : a*r = b*q := by
    by_contra hne
    have hsep : 1/((q : ℝ)*r) ≤ |(a : ℝ)/q - b/r| := by
      rw [show (a:ℝ)/q - b/r = (a*r-b*q)/(q*r) by field_simp, abs_div, abs_of_pos (mul_pos hqr hrr)]
      apply (div_le_div_iff_of_pos_right (mul_pos hqr hrr)).mpr
      rcases lt_or_gt_of_ne hne with hab | hba
      · have hgap : (a:ℝ)*r + 1 ≤ b*q := by exact_mod_cast Nat.succ_le_of_lt hab
        linarith [neg_le_abs ((a:ℝ)*r - b*q)]
      · have hgap : (b:ℝ)*q + 1 ≤ a*r := by exact_mod_cast Nat.succ_le_of_lt hba
        linarith [le_abs_self ((a:ℝ)*r - b*q)]
    have htriangle := abs_sub_le ((a:ℝ)/q) t ((b:ℝ)/r)
    rw [abs_sub_comm ((a:ℝ)/q) t] at htriangle
    linarith
  have hdiv₁ : q ∣ r := hca.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q b)
  have hdiv₂ : r ∣ q := hcb.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left r a)
  obtain rfl := Nat.dvd_antisymm hdiv₁ hdiv₂
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq he⟩

theorem eventually_wide_arc_budget :
    ∃ N : ℕ, ∀ n ≥ N,
      let Q := (Nat.log 2 (n+2))^2
      let Q₁ := ⌊(n : ℝ)^(1/3 : ℝ)⌋₊
      let H := 256 * Q₁ * Q
      2 * H * Q₁ < n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c : ℝ := Real.log 2 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hlim : Tendsto (fun x : ℝ => Real.log x ^ (2 : ℕ) / x^(1/3 : ℝ)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := 1/3) 2 (by norm_num)).tendsto_div_nhds_zero
    have heq (x : ℝ) : Real.log x ^ (2 : ℝ) = Real.log x ^ (2 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast (Real.log x) 2
    simpa only [heq] using h
  have hseq := hlim.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hε : 0 < c^2/512 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hseq.eventually_lt_const hε)
  refine ⟨max N 2, ?_⟩
  intro n hn Q Q₁ H
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  let z := (n : ℝ)^(1/3 : ℝ)
  have hz : 0 < z := Real.rpow_pos_of_pos hnpos _
  have hpow : (2 : ℝ) ^ Nat.log 2 (n+2) ≤ ((n+2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2 ≠ 0)
  have hlogbase := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 (n+2)) hpow
  rw [Real.log_pow] at hlogbase
  have hlogplus : Real.log ((n+2 : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hcomp : ((n+2 : ℕ) : ℝ) ≤ (n : ℝ)^2 := by
      push_cast
      nlinarith only [hnR, sq_nonneg ((n : ℝ) - 2)]
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by positivity : 0 < ((n+2 : ℕ) : ℝ)) hcomp
  have hnatlog : (Nat.log 2 (n+2) : ℝ) ≤ Real.log (n : ℝ) / c := by
    apply (le_div_iff₀ hc).2
    dsimp [c]
    linarith only [hlogbase, hlogplus]
  have hsmall : Real.log (n : ℝ)^2 / z < c^2/512 := hN n hnN
  have hscaled : 512 * (Real.log (n : ℝ) / c)^2 < z := by
    have h1 := (div_lt_iff₀ hz).1 hsmall
    have h2 := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 512)).1
      (show Real.log (n : ℝ)^2 < c^2*z/512 by simpa only [div_mul_eq_mul_div] using h1)
    rw [div_pow, ← mul_div_assoc]
    apply (div_lt_iff₀ (sq_pos_of_pos hc)).2
    simpa only [mul_comm] using h2
  have hQ : (512 : ℝ) * (Q : ℝ) < z := by
    have hsq : (Q : ℝ) ≤ (Real.log (n : ℝ) / c)^2 := by
      dsimp [Q]
      push_cast
      exact pow_le_pow_left₀ (by positivity) hnatlog _
    exact (mul_le_mul_of_nonneg_left hsq (by norm_num)).trans_lt hscaled
  have hB : (Q₁ : ℝ) ≤ z := Nat.floor_le hz.le
  have hz3 : z * z^2 = (n : ℝ) := by
    have heq : z^2 = (n : ℝ)^(2/3 : ℝ) := by
      dsimp [z]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      norm_num
    rw [heq]
    dsimp [z]
    rw [← Real.rpow_add hnpos]
    norm_num
  have hr : (512 : ℝ) * (Q : ℝ) * (Q₁ : ℝ)^2 < (n : ℝ) := calc
    _ ≤ 512 * (Q : ℝ) * z^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hB _) (by positivity)
    _ < z * z^2 := mul_lt_mul_of_pos_right hQ (sq_pos_of_pos hz)
    _ = _ := hz3
  have hnat : 512 * Q * Q₁^2 < n := by exact_mod_cast hr
  change 2 * (256 * Q₁ * Q) * Q₁ < n
  rw [show 2 * (256 * Q₁ * Q) * Q₁ = 512 * Q * Q₁^2 by ring]
  exact hnat

end GoldbachWideArcs

end GoldbachWideArcSeparation

section GoldbachDeepFourthGeometry

open Filter
open scoped Topology

private theorem eventuallyExtendedBudget :
    ∃ N : ℕ, ∀ n ≥ N,
      let Q := (Nat.log 2 (n+2))^2
      let Q₁ := ⌊(n : ℝ)^(1/3 : ℝ)⌋₊
      let H := 256 * Q₁ * Q
      2 * H * (4*Q₁) < n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c : ℝ := Real.log 2 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hlim : Tendsto (fun x : ℝ => Real.log x ^ (2 : ℕ) / x^(1/3 : ℝ)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := 1/3) 2 (by norm_num)).tendsto_div_nhds_zero
    have heq (x : ℝ) : Real.log x ^ (2 : ℝ) = Real.log x ^ (2 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast (Real.log x) 2
    simpa only [heq] using h
  have hseq := hlim.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hε : 0 < c^2/2048 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hseq.eventually_lt_const hε)
  refine ⟨max N 2, ?_⟩
  intro n hn Q Q₁ H
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  let z := (n : ℝ)^(1/3 : ℝ)
  have hz : 0 < z := Real.rpow_pos_of_pos hnpos _
  have hpow : (2 : ℝ) ^ Nat.log 2 (n+2) ≤ ((n+2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2 ≠ 0)
  have hlogbase := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 (n+2)) hpow
  rw [Real.log_pow] at hlogbase
  have hlogplus : Real.log ((n+2 : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hcomp : ((n+2 : ℕ) : ℝ) ≤ (n : ℝ)^2 := by
      push_cast
      nlinarith only [hnR, sq_nonneg ((n : ℝ) - 2)]
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by positivity : 0 < ((n+2 : ℕ) : ℝ)) hcomp
  have hnatlog : (Nat.log 2 (n+2) : ℝ) ≤ Real.log (n : ℝ) / c := by
    apply (le_div_iff₀ hc).2
    dsimp [c]
    linarith only [hlogbase, hlogplus]
  have hsmall : Real.log (n : ℝ)^2 / z < c^2/2048 := hN n hnN
  have hscaled : 2048 * (Real.log (n : ℝ) / c)^2 < z := by
    have h1 := (div_lt_iff₀ hz).1 hsmall
    have h2 := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2048)).1
      (show Real.log (n : ℝ)^2 < c^2*z/2048 by simpa only [div_mul_eq_mul_div] using h1)
    rw [div_pow, ← mul_div_assoc]
    apply (div_lt_iff₀ (sq_pos_of_pos hc)).2
    simpa only [mul_comm] using h2
  have hQ : (2048 : ℝ) * (Q : ℝ) < z := by
    have hsq : (Q : ℝ) ≤ (Real.log (n : ℝ) / c)^2 := by
      dsimp [Q]
      push_cast
      exact pow_le_pow_left₀ (by positivity) hnatlog _
    exact (mul_le_mul_of_nonneg_left hsq (by norm_num)).trans_lt hscaled
  have hB : (Q₁ : ℝ) ≤ z := Nat.floor_le hz.le
  have hz3 : z * z^2 = (n : ℝ) := by
    have heq : z^2 = (n : ℝ)^(2/3 : ℝ) := by
      dsimp [z]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      norm_num
    rw [heq]
    dsimp [z]
    rw [← Real.rpow_add hnpos]
    norm_num
  have hr : (2048 : ℝ) * (Q : ℝ) * (Q₁ : ℝ)^2 < (n : ℝ) := calc
    _ ≤ 2048 * (Q : ℝ) * z^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hB _) (by positivity)
    _ < z * z^2 := mul_lt_mul_of_pos_right hQ (sq_pos_of_pos hz)
    _ = _ := hz3
  have hnat : 2048 * Q * Q₁^2 < n := by exact_mod_cast hr
  change 2 * (256 * Q₁ * Q) * (4*Q₁) < n
  rw [show 2 * (256 * Q₁ * Q) * (4*Q₁) = 2048 * Q * Q₁^2 by ring]
  exact hnat

open Set

namespace GoldbachFourthGeometry

noncomputable def strip (n q a : ℕ) : Set ℝ :=
  Set.Icc ((a:ℝ)/q - 1/(20*(n:ℝ))) ((a:ℝ)/q + 1/(20*(n:ℝ)))

noncomputable def wide (n R H : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤R ∧ a≤q ∧ Nat.Coprime a q ∧
    |t - (a:ℝ)/q| ≤ (H:ℝ)/((q:ℝ)*n)}

theorem mem_strip {n q a : ℕ} {t : ℝ} :
    t ∈ strip n q a ↔ |t-(a:ℝ)/q| ≤ 1/(20*(n:ℝ)) := by
  unfold strip
  rw [Set.mem_Icc, abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem center_coprime {q a : ℕ} (hq : q.Prime) (ha : a ∈ Finset.Ico 1 q) :
    a.Coprime q := by
  obtain ⟨ha₀,ha₁⟩ := Finset.mem_Ico.mp ha
  exact (hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ha₀ ha₁)).symm

theorem bigger_radius {n q H : ℕ} (hn : 0 < n) (hq : 0 < q) (hqH : q ≤ H) :
    1/(20*(n:ℝ)) ≤ (H:ℝ)/((q:ℝ)*n) := by
  have hnr : 0 < (n:ℝ) := by exact_mod_cast hn
  have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
  have hq' : (q:ℝ) ≤ (H:ℝ) := by exact_mod_cast hqH
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hs := mul_le_mul_of_nonneg_right hq' hnr.le
  nlinarith only [hs, mul_nonneg (Nat.cast_nonneg H) hnr.le]

theorem point_in_unit {n q a : ℕ} (hn : 0 < n) (hqn : q ≤ n) (ha : a ∈ Finset.Ico 1 q)
    {t : ℝ} (ht : t ∈ strip n q a) : t ∈ Set.Icc (0:ℝ) 1 := by
  obtain ⟨ha₀,ha₁⟩ := Finset.mem_Ico.mp ha
  have hq : 0 < (q:ℝ) := by exact_mod_cast (show 0<q by omega)
  have hnr : 0 < (n:ℝ) := by exact_mod_cast hn
  have hqn' : (q:ℝ) ≤ (n:ℝ) := by exact_mod_cast hqn
  have hδ : 1/(20*(n:ℝ)) ≤ 1/(q:ℝ) := by
    apply (div_le_div_iff₀ (by positivity) hq).2
    linarith
  have hlow : 1/(q:ℝ) ≤ (a:ℝ)/q :=
    div_le_div_of_nonneg_right (by exact_mod_cast ha₀) hq.le
  have hhigh : (a:ℝ)/q ≤ 1-1/(q:ℝ) := by
    have ht : (a:ℝ)+1≤(q:ℝ) := by exact_mod_cast Nat.succ_le_of_lt ha₁
    calc
      _ ≤ ((q:ℝ)-1)/q := div_le_div_of_nonneg_right (by linarith) hq.le
      _ = _ := by rw [sub_div, div_self hq.ne']
  obtain ⟨h₁,h₂⟩ := abs_le.mp (mem_strip.mp ht)
  exact ⟨by linarith, by linarith⟩

theorem point_outside_wide {n R H q a : ℕ} (hcut : 2*H*(4*R)<n) (hH : 4*R ≤ H)
    (hq : q.Prime) (hqR : R < q) (hq4 : q ≤ 4*R) (ha : a ∈ Finset.Ico 1 q)
    {t : ℝ} (ht : t ∈ strip n q a) : t ∈ (wide n R H)ᶜ := by
  intro hw
  obtain ⟨r,b,hr,hrR,_,hcb,hradius⟩ := hw
  have hnr : 0 < n := by omega
  have hqa := center_coprime hq ha
  have hδ := (mem_strip.mp ht).trans (bigger_radius hnr hq.pos (hq4.trans hH))
  have ⟨heq,_⟩ := GoldbachWideArcs.reduced_centers_eq_of_common_point hcut hq.pos hr
    hq4 (hrR.trans (by omega)) hqa hcb hδ hradius
  omega

theorem strip_index_unique {n R H q r a b : ℕ} (hcut : 2*H*(4*R)<n) (hH : 4*R ≤ H)
    (hq : q.Prime) (hr : r.Prime) (hq4 : q ≤ 4*R) (hr4 : r ≤ 4*R)
    (ha : a ∈ Finset.Ico 1 q) (hb : b ∈ Finset.Ico 1 r) {t : ℝ}
    (htq : t ∈ strip n q a) (htr : t ∈ strip n r b) : q=r ∧ a=b := by
  have hnr : 0 < n := by omega
  exact GoldbachWideArcs.reduced_centers_eq_of_common_point hcut hq.pos hr.pos hq4 hr4
    (center_coprime hq ha) (center_coprime hr hb)
    ((mem_strip.mp htq).trans (bigger_radius hnr hq.pos (hq4.trans hH)))
    ((mem_strip.mp htr).trans (bigger_radius hnr hr.pos (hr4.trans hH)))

theorem eventually_strip_budget :
    ∃ N : ℕ, ∀ n ≥ N,
      let R := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
      let H := 256 * R * (Nat.log 2 (n+2))^2
      2*H*(4*R) < n ∧ 4*R ≤ H ∧ 4*R ≤ n := by
  obtain ⟨N,hN⟩ := eventuallyExtendedBudget
  refine ⟨N, ?_⟩
  intro n hn R H
  have hbudget : 2*H*(4*R) < n := hN n hn
  have hlog : 1 ≤ Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
  have hH : 4*R ≤ H := calc
    _ ≤ 256*R := Nat.mul_le_mul_right _ (by decide)
    _ = 256*R*1 := by simp
    _ ≤ H := Nat.mul_le_mul_left _ (by
      have hx := Nat.pow_le_pow_left hlog 2
      simpa using hx)
  have hsize : 4*R ≤ n := by
    by_cases hzero : R=0
    · simp [hzero]
    · have hHp : 1 ≤ H := by omega
      exact (Nat.le_mul_of_pos_left _ (show 0<2*H by omega)).trans hbudget.le
  exact ⟨hbudget,hH,hsize⟩

end GoldbachFourthGeometry

end GoldbachDeepFourthGeometry

section GoldbachDiscreteWindowEstimate

open Finset MeasureTheory
open scoped ComplexConjugate Interval

namespace GoldbachWindow

open GoldbachFourthMoment (phase phase_add)

/-- The finite Fourier series with coefficient list indexed by `range N`. -/
noncomputable def poly (N : ℕ) (b : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ j ∈ range N, b j * phase ((j : ℝ) * t)

private theorem phase_cont : Continuous phase := by unfold phase; fun_prop

private theorem poly_cont (N : ℕ) (b : ℕ → ℂ) : Continuous (poly N b) := by
  unfold poly
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (phase_cont.comp (by fun_prop))

private theorem phase_int (m : ℤ) : phase (m : ℝ) = 1 := by
  unfold phase
  have h : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) =
      (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

-- The mode integral uses the same orthogonality as Clrs17, Goldbach PR 158.
private theorem mode_integral (m : ℤ) :
    (∫ t in (0 : ℝ)..1, phase ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [phase]
  let c : ℂ := (m : ℂ) * (2 * Real.pi * Complex.I)
  have he (t : ℝ) : phase ((m : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
    unfold phase c
    congr 1
    push_cast
    ring
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by exact_mod_cast hm)
      (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
        Complex.I_ne_zero)
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp [hm, c, Complex.exp_int_mul_two_pi_mul_I]

private theorem phase_conj (t : ℝ) : conj (phase t) = phase (-t) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem parseval (N : ℕ) (b : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..1, ‖poly N b t‖^2) = ∑ k ∈ range N, ‖b k‖^2 := by
  let term (k j : ℕ) (t : ℝ) :=
    (conj (b k) * b j) * phase ((((j : ℤ) - (k : ℤ)) : ℝ) * t)
  let cross (t : ℝ) := ∑ k ∈ range N, ∑ j ∈ range N, term k j t
  have hc (k j : ℕ) : Continuous (term k j) := by
    unfold term phase
    fun_prop
  have hcross : Continuous cross := continuous_finsetSum _ fun k _ =>
    continuous_finsetSum _ fun j _ => hc k j
  have hexpand (t : ℝ) : ((‖poly N b t‖^2 : ℝ) : ℂ) = cross t := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    simp only [poly, cross, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    dsimp [term]
    simp only [map_mul, phase_conj]
    simp only [Int.cast_natCast]
    rw [show ((j : ℝ) - (k : ℝ)) * t =
      -((k : ℝ) * t) + (j : ℝ) * t by ring, phase_add]
    ring
  have hint : (∫ t in (0 : ℝ)..1, cross t) = (↑(∑ k ∈ range N, ‖b k‖^2) : ℂ) := by
    dsimp only [cross]
    rw [intervalIntegral.integral_finsetSum
      (fun k _ => (continuous_finsetSum _ fun j _ => hc k j).intervalIntegrable _ _),
      Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_finsetSum fun j _ => (hc k j).intervalIntegrable _ _]
    have hmode (j : ℕ) : (∫ t in (0 : ℝ)..1, term k j t) =
        (conj (b k) * b j) * (if j = k then 1 else 0) := by
      have hm : (∫ t in (0 : ℝ)..1, phase (((j : ℝ) - (k : ℝ)) * t)) =
          if j = k then 1 else 0 := by
        simpa only [Int.cast_sub, Int.cast_natCast, sub_eq_zero, Int.ofNat_inj]
          using mode_integral ((j : ℤ) - (k : ℤ))
      unfold term
      rw [intervalIntegral.integral_const_mul]
      exact congrArg ((conj (b k) * b j) * ·) hm
    simp only [hmode]
    rw [Finset.sum_eq_single_of_mem k hk]
    · simp [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    · intro j _ hne
      simp [hne]
  have hre :
      (∫ t in (0 : ℝ)..1, (cross t).re) = (∫ t in (0 : ℝ)..1, cross t).re := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact integral_re (hcross.intervalIntegrable (0 : ℝ) 1).1
  calc
    _ = ∫ t in (0 : ℝ)..1, (cross t).re := by
      apply intervalIntegral.integral_congr
      intro t _
      simpa only [Complex.ofReal_re] using congrArg Complex.re (hexpand t)
    _ = _ := by rw [hre, hint, Complex.ofReal_re]

/-- The coefficient at frequency `m` after multiplying by the length-`h` box. -/
noncomputable def moving (N h : ℕ) (b : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ x ∈ ((range N) ×ˢ (range h)).filter (fun x => x.1 + x.2 = m), b x.1

theorem moving_eq_sum (N h : ℕ) (b : ℕ → ℂ) (m : ℕ) :
    moving N h b m = ∑ k ∈ (range N).filter (fun k => m + 1 - h ≤ k ∧ k ≤ m), b k := by
  classical
  unfold moving
  refine Finset.sum_bij (fun x _ => x.1) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x hx
    obtain ⟨⟨hk, hj⟩, heq⟩ := (Finset.mem_filter.mp hx).imp (fun hp => Finset.mem_product.mp hp) id
    have hj' := mem_range.mp hj
    exact Finset.mem_filter.mpr ⟨hk, by omega, by omega⟩
  · intro x hx y hy hxy
    have heqx := (Finset.mem_filter.mp hx).2
    have heqy := (Finset.mem_filter.mp hy).2
    exact Prod.ext hxy (by omega)
  · intro k hk
    obtain ⟨hk', hlo, hhi⟩ := Finset.mem_filter.mp hk
    refine ⟨(k, m - k), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hk', mem_range.mpr (by omega)⟩, by omega⟩

theorem poly_moving_mul (N h : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    poly (N + h) (moving N h b) t = poly N b t * poly h (fun _ => 1) t := by
  unfold poly
  have hmaps (x : ℕ × ℕ) (hx : x ∈ (range N) ×ˢ (range h)) :
      x.1 + x.2 ∈ range (N + h) := by
    obtain ⟨hk, hj⟩ := Finset.mem_product.mp hx
    simp only [Finset.mem_range] at hk hj
    exact mem_range.mpr (by omega)
  calc
    _ = ∑ m ∈ range (N + h), ∑ x ∈ ((range N) ×ˢ (range h)).filter
        (fun x => x.1 + x.2 = m), b x.1 * phase ((x.1 : ℝ) * t + (x.2 : ℝ) * t) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [moving, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      have hsum := (Finset.mem_filter.mp hx).2
      have hsumR : (x.1 : ℝ) + x.2 = m := by exact_mod_cast hsum
      rw [← add_mul, hsumR]
    _ = ∑ x ∈ (range N) ×ˢ (range h), b x.1 * phase ((x.1 : ℝ) * t + (x.2 : ℝ) * t) :=
      Finset.sum_fiberwise_of_maps_to hmaps _
    _ = _ := by
      rw [Finset.sum_product, Finset.sum_mul_sum]
      simp only [one_mul, phase_add, mul_assoc]

private theorem box_lower {h : ℕ} {t : ℝ} (ht : 6 * (h : ℝ) * |t| ≤ 1) :
    (h : ℝ) / 2 ≤ ‖poly h (fun _ => 1) t‖ := by
  apply le_trans _ (Complex.re_le_norm _)
  unfold poly
  simp only [one_mul, Complex.re_sum, phase, Complex.exp_ofReal_mul_I_re]
  calc
    _ = ∑ _ ∈ range h, (1 / 2 : ℝ) := by rw [Finset.sum_const, card_range, nsmul_eq_mul]; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      have hjh : (j : ℝ) ≤ h := by exact_mod_cast (mem_range.mp hj).le
      have hfac := mul_le_mul_of_nonneg_right hjh (abs_nonneg t)
      have hangle : |2 * Real.pi * ((j : ℝ) * t)| ≤ Real.pi / 3 := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi), abs_mul,
          abs_of_nonneg (Nat.cast_nonneg j : 0 ≤ (j : ℝ))]
        calc
          _ ≤ (2 * Real.pi) * ((h : ℝ) * |t|) := mul_le_mul_of_nonneg_left hfac (by positivity)
          _ ≤ _ := by
            have h' : (h : ℝ) * |t| ≤ 1 / 6 := by linarith only [ht]
            have h'' := mul_le_mul_of_nonneg_left h' (show 0 ≤ 2 * Real.pi by positivity)
            linarith only [h'']
      rw [← Real.cos_pi_div_three, ← Real.cos_abs (2 * Real.pi * ((j : ℝ) * t))]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hangle

set_option maxHeartbeats 600000 in
/-- A finite version of the low-frequency window estimate, using exact Parseval on one period. -/
theorem low_frequency_le (N h : ℕ) (b : ℕ → ℂ) (δ : ℝ)
    (hpos : 0 < h) (hδ : 0 ≤ δ) (hwidth : 6 * (h : ℝ) * δ ≤ 1) :
    (h : ℝ)^2 / 4 * (∫ t in (-δ)..δ, ‖poly N b t‖^2) ≤
      ∑ m ∈ range (N + h), ‖moving N h b m‖^2 := by
  have hδsmall : δ ≤ 1 / 2 := by
    have hh : (1 : ℝ) ≤ h := by exact_mod_cast hpos
    have hmul := mul_le_mul_of_nonneg_right hh hδ
    nlinarith only [hmul, hwidth]
  have hre : -δ ≤ δ := by linarith
  have hline (t : ℝ) (ht : t ∈ Set.Icc (-δ) δ) :
      (h : ℝ)^2 / 4 * ‖poly N b t‖^2 ≤ ‖poly (N + h) (moving N h b) t‖^2 := by
    have ht' : |t| ≤ δ := abs_le.mpr ht
    have hb := box_lower ((mul_le_mul_of_nonneg_left ht'
      (by positivity : 0 ≤ 6 * (h : ℝ))).trans hwidth)
    rw [poly_moving_mul, norm_mul, mul_pow]
    have hb' := pow_le_pow_left₀ (by positivity : 0 ≤ (h : ℝ) / 2) hb 2
    rw [show (h : ℝ)^2 / 4 = ((h : ℝ) / 2)^2 by ring, mul_comm]
    exact mul_le_mul_of_nonneg_left hb' (by positivity)
  let F (t : ℝ) := ‖poly (N + h) (moving N h b) t‖^2
  have hF : Continuous F := (poly_cont _ _).norm.pow 2
  have hpolyper : Function.Periodic (poly (N + h) (moving N h b)) 1 := by
    intro t
    unfold poly
    apply Finset.sum_congr rfl
    intro m _
    have hm : phase (m : ℝ) = 1 := by
      simpa only [Int.cast_natCast] using phase_int (m : ℤ)
    rw [mul_add, phase_add, mul_one, hm, mul_one]
  have hper : Function.Periodic F 1 := by
    intro t
    dsimp only [F]
    rw [hpolyper t]
  calc
    _ = ∫ t in (-δ)..δ, (h : ℝ)^2 / 4 * ‖poly N b t‖^2 :=
      (intervalIntegral.integral_const_mul _ (fun t : ℝ => ‖poly N b t‖^2)).symm
    _ ≤ ∫ t in (-δ)..δ, F t :=
      intervalIntegral.integral_mono_on hre
        ((continuous_const.mul ((poly_cont _ _).norm.pow 2)).intervalIntegrable _ _)
        (hF.intervalIntegrable _ _) hline
    _ ≤ ∫ t in (-(1/2):ℝ)..(-(1/2)+1), F t :=
      intervalIntegral.integral_mono_interval (by linarith) hre (by linarith)
        (Filter.Eventually.of_forall (fun _ => by dsimp [F]; positivity)) (hF.intervalIntegrable _ _)
    _ = ∫ t in (0 : ℝ)..1, F t := by
      simpa only [zero_add] using hper.intervalIntegral_add_eq (-(1/2)) 0
    _ = _ := parseval _ _

end GoldbachWindow

end GoldbachDiscreteWindowEstimate

section GoldbachMinorArcAbelTail

open scoped BigOperators

theorem goldbach_geometric_sum_le_inv_twice_round_distance (θ : ℝ) (K : ℕ)
    (hθ : 0 < |θ - (round θ : ℝ)|) :
    ‖∑ j ∈ Finset.range K, Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖ ≤
      1 / (2 * |θ - (round θ : ℝ)|) := by
  let k : ℤ := round θ
  let d : ℝ := θ - (k : ℝ)
  let z : ℂ := Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I)
  have hpos : 0 < |d| := hθ
  have habs : |d| ≤ 1 / 2 := abs_sub_round θ
  have hphase : z = Complex.exp (Complex.I * ((2 * Real.pi * d : ℝ) : ℂ)) := by
    have hsplit :
        (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I) =
          Complex.I * ((2 * Real.pi * d : ℝ) : ℂ) +
            (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      dsimp [d]
      push_cast
      ring
    dsimp only [z]
    rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have harg : |Real.pi * d| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos, show Real.pi / 2 = Real.pi * (1 / 2) by ring]
    exact mul_le_mul_of_nonneg_left habs Real.pi_pos.le
  have hsin : 2 * |d| ≤ |Real.sin (Real.pi * d)| := calc
    _ = 2 / Real.pi * |Real.pi * d| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      field_simp [Real.pi_pos.ne']
    _ ≤ _ := Real.mul_abs_le_abs_sin harg
  have hdenom : 4 * |d| ≤ ‖z - 1‖ := by
    rw [hphase, Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show (2 * Real.pi * d) / 2 = Real.pi * d by ring,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith only [hsin]
  have hunit : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hprod : ‖∑ j ∈ Finset.range K, z ^ j‖ * ‖z - 1‖ ≤ 2 := by
    rw [← norm_mul, geom_sum_mul]
    calc
      _ ≤ ‖z ^ K‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, hunit]
  have hscaled : ‖∑ j ∈ Finset.range K, z ^ j‖ * (4 * |d|) ≤ 2 :=
    (mul_le_mul_of_nonneg_left hdenom (norm_nonneg _)).trans hprod
  have hterm (j : ℕ) :
      Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I) = z^j := by
    have he : (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I) =
      (j : ℂ) * ((((2 * Real.pi * θ : ℝ) : ℂ)) * Complex.I) := by
      push_cast
      ring
    simpa only [z, he] using Complex.exp_nat_mul
      ((((2 * Real.pi * θ : ℝ) : ℂ)) * Complex.I) j
  simp_rw [hterm]
  change ‖∑ j ∈ Finset.range K, z ^ j‖ ≤ 1 / (2 * |d|)
  apply (le_div_iff₀ (mul_pos (by norm_num) hpos)).2
  nlinarith only [hscaled]


open MeasureTheory

theorem goldbach_periodic_integral_mul_nat
    (g : ℝ → ℝ) (hg : Function.Periodic g 1)
    (hi : IntervalIntegrable g volume 0 1) (m : ℕ) (hm : 0 < m) :
    (∫ t in (0 : ℝ)..1, g ((m : ℝ) * t)) = ∫ t in (0 : ℝ)..1, g t := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hperiod := hg.intervalIntegral_add_zsmul_eq (m : ℤ) 0
    (fun a b => hg.intervalIntegrable₀ (by norm_num) hi a b)
  have hscaled : (∫ t in (0 : ℝ)..(m : ℝ), g t) =
      (m : ℝ) * ∫ t in (0 : ℝ)..1, g t := by
    simpa only [zsmul_eq_mul, Int.cast_natCast, mul_one, zero_add] using hperiod
  rw [intervalIntegral.integral_comp_mul_left g hmR, mul_zero, mul_one, hscaled,
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hmR, one_mul]


open Set

noncomputable def goldbach_round_tail (δ x : ℝ) : ℝ :=
  if δ ≤ |x - (round x : ℝ)| then 1 / |x - (round x : ℝ)| ^ 2 else 0

theorem goldbach_round_tail_periodic (δ : ℝ) : Function.Periodic (goldbach_round_tail δ) 1 := by
  intro x
  simp only [goldbach_round_tail, round_add_one, Int.cast_add, Int.cast_one, add_sub_add_right_eq_sub]

theorem goldbach_round_tail_integral (δ : ℝ) (hδ : 0 < δ) (hd : δ ≤ 1 / 2) :
    IntervalIntegrable (goldbach_round_tail δ) volume 0 1 ∧
      (∫ x in (0 : ℝ)..1, goldbach_round_tail δ x) = 2 / δ - 4 := by
  let g := goldbach_round_tail δ
  let f : ℝ → ℝ := fun x => x ^ (-2 : ℤ)
  have hr {x : ℝ} (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) : round x = 0 :=
    round_eq_zero_iff.2 ⟨hx.1.le, hx.2⟩
  have hpow (x : ℝ) : f x = 1 / |x| ^ 2 := by
    simp [f, zpow_neg, sq_abs, one_div]
  have heL : (Ioo (-(1 / 2 : ℝ)) (-δ)).EqOn g f := by
    intro x hx
    have hxr : x < 1 / 2 := by linarith only [hx.2, hδ]
    have hx0 : x < 0 := by linarith only [hx.2, hδ]
    have hxd : δ ≤ |x| := by rw [abs_of_neg hx0]; linarith only [hx.2]
    rw [hpow]
    simp only [g, goldbach_round_tail, hr ⟨hx.1,hxr⟩, Int.cast_zero, sub_zero, ite_eq_left hxd]
  have heR : (Ioo δ (1 / 2 : ℝ)).EqOn g f := by
    intro x hx
    have hxl : -(1 / 2 : ℝ) < x := by linarith only [hx.1, hδ]
    have hx0 : 0 < x := by linarith only [hx.1, hδ]
    have hxd : δ ≤ |x| := by rw [abs_of_pos hx0]; exact hx.1.le
    rw [hpow]
    simp only [g, goldbach_round_tail, hr ⟨hxl,hx.2⟩, Int.cast_zero, sub_zero, ite_eq_left hxd]
  have heC : (Ioo (-δ) δ).EqOn g (fun _ : ℝ => (0 : ℝ)) := by
    intro x hx
    have hx₁ : -(1 / 2 : ℝ) < x := by linarith only [hd, hx.1]
    have hx₂ : x < (1 / 2 : ℝ) := hx.2.trans_le hd
    have hxd : |x| < δ := abs_lt.2 ⟨hx.1, hx.2⟩
    simp only [g, goldbach_round_tail, hr ⟨hx₁,hx₂⟩, Int.cast_zero, sub_zero,
      ite_eq_right hxd.not_ge]
  have hAway (l r : ℝ) (hab : l ≤ r) (h0 : (0 : ℝ) ∉ Icc l r) (he : (Ioo l r).EqOn g f) :
      IntervalIntegrable g volume l r ∧ (∫ x in l..r, g x) = l⁻¹ - r⁻¹ := by
    have hz : (0 : ℝ) ∉ uIcc l r := by simpa only [uIcc_of_le hab] using h0
    have hIf : IntervalIntegrable f volume l r :=
      intervalIntegral.intervalIntegrable_zpow (n := -2) (Or.inr hz)
    refine ⟨hIf.congr_uIoo (by simpa only [uIoo_of_le hab] using he.symm), ?_⟩
    rw [intervalIntegral.integral_congr_Ioo_of_le hab he]
    change (∫ x in l..r, x ^ (-2 : ℤ)) = _
    rw [integral_zpow (Or.inr ⟨by norm_num, hz⟩)]
    norm_num
    ring
  obtain ⟨hIL,hVL⟩ := hAway (-(1/2)) (-δ) (by linarith only [hd])
    (by intro hz; have hh := (mem_Icc.mp hz).2; linarith only [hh,hδ]) heL
  obtain ⟨hIR,hVR⟩ := hAway δ (1/2) hd
    (by intro hz; have hh := (mem_Icc.mp hz).1; linarith only [hh,hδ]) heR
  have hcent : -δ ≤ δ := by linarith only [hδ]
  have hIC : IntervalIntegrable g volume (-δ) δ :=
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (-δ) δ).congr_uIoo
      (by simpa only [uIoo_of_le hcent] using heC.symm)
  have hVC : (∫ x in -δ..δ, g x) = 0 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hcent heC]
    exact intervalIntegral.integral_zero
  have hp := goldbach_round_tail_periodic δ
  have hiBase : IntervalIntegrable g volume (-(1/2)) (1/2) := hIL.trans (hIC.trans hIR)
  have hBaseEnd : -(1/2 : ℝ) + 1 = 1/2 := by norm_num
  have hInt : IntervalIntegrable g volume 0 1 :=
    hp.intervalIntegrable (by norm_num) (t := -(1/2 : ℝ)) (by simpa only [hBaseEnd] using hiBase) 0 1
  refine ⟨hInt, ?_⟩
  have hperiod := hp.intervalIntegral_add_eq (-(1/2 : ℝ)) 0
  change (∫ x in (0 : ℝ)..1, g x) = _
  rw [show (∫ x in (0 : ℝ)..1, g x) = ∫ x in (-(1/2 : ℝ))..(1/2), g x by
      simpa only [hBaseEnd, zero_add] using hperiod.symm,
      ← intervalIntegral.integral_add_adjacent_intervals hIL (hIC.trans hIR),
      ← intervalIntegral.integral_add_adjacent_intervals hIC hIR,
      hVL, hVC, hVR]
  norm_num [inv_neg, div_eq_mul_inv]
  ring

theorem goldbach_sum_Icc_one_eq_shifted_range {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) (K : ℕ) :
    (∑ j ∈ Finset.Icc 1 K, f j) = ∑ j ∈ Finset.range K, f (j+1) := by
  symm
  refine Finset.sum_bij (fun j _ => j+1) ?_ ?_ ?_ ?_
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i _ j _ hij
    omega
  · intro j hj
    obtain ⟨hj₁,hj₂⟩ := Finset.mem_Icc.mp hj
    exact ⟨j-1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro j _
    rfl

theorem goldbach_exponential_shifted_range_norm (θ : ℝ) (K : ℕ) :
    ‖∑ j ∈ Finset.range K, Complex.exp (((2 * Real.pi * ((j+1 : ℕ) : ℝ) * θ : ℝ) : ℂ) *
        Complex.I)‖ =
      ‖∑ j ∈ Finset.range K, Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) *
        Complex.I)‖ := by
  let e : ℕ → ℂ := fun j => Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I)
  have hshift (j : ℕ) : e (j+1) = e 1 * e j := by
    dsimp [e]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hunit : ‖e 1‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hs : (∑ j ∈ Finset.range K, e (j+1)) = e 1 * (∑ j ∈ Finset.range K, e j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => hshift j)
  change ‖∑ j ∈ Finset.range K, e (j+1)‖ = ‖∑ j ∈ Finset.range K, e j‖
  rw [hs, norm_mul, hunit, one_mul]

theorem goldbach_positive_exponential_prefix_norm (θ : ℝ) (K : ℕ) :
    ‖∑ j ∈ Finset.Icc 1 K, Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) *
        Complex.I)‖ =
      ‖∑ j ∈ Finset.range K, Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) *
        Complex.I)‖ := by
  rw [goldbach_sum_Icc_one_eq_shifted_range]
  exact goldbach_exponential_shifted_range_norm θ K

theorem goldbach_norm_weighted_prefix_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℕ → E) (w : ℕ → ℝ) (K : ℕ) (B : ℝ)
    (hw : Monotone w) (hw₀ : ∀ j, 0 ≤ w j) (hB : 0 ≤ B)
    (hprefix : ∀ n ≤ K, ‖∑ j ∈ Finset.range n, a j‖ ≤ B) :
    ‖∑ j ∈ Finset.range K, w j • a j‖ ≤ 2 * w (K-1) * B := by
  have htel (N : ℕ) :
      (∑ j ∈ Finset.range N, (w (j+1) - w j)) = w N - w 0 := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; ring
  have hlead :
      ‖w (K-1) • (∑ j ∈ Finset.range K, a j)‖ ≤ w (K-1) * B := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw₀ _)]
    exact mul_le_mul_of_nonneg_left (hprefix K le_rfl) (hw₀ _)
  have hrest :
      ‖∑ j ∈ Finset.range (K-1), (w (j+1) - w j) • (∑ i ∈ Finset.range (j+1), a i)‖
        ≤ (w (K-1)-w 0) * B := by
    calc
      _ ≤ ∑ j ∈ Finset.range (K-1),
          ‖(w (j+1)-w j) • (∑ i ∈ Finset.range (j+1), a i)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (K-1), (w (j+1)-w j)*B := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : j + 1 ≤ K := by
          have := Finset.mem_range.mp hj
          omega
        have hdiff : 0 ≤ w (j+1)-w j := sub_nonneg.mpr (hw (Nat.le_succ j))
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdiff]
        exact mul_le_mul_of_nonneg_left (hprefix (j+1) hj') hdiff
      _ = _ := by rw [← Finset.sum_mul, htel]
  rw [Finset.sum_range_by_parts]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ w (K-1)*B + (w (K-1)-w 0)*B := by exact add_le_add hlead hrest
    _ = (2*w (K-1)-w 0)*B := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (sub_le_self _ (hw₀ 0)) hB

theorem goldbach_log_exponential_prefix_bound (θ B : ℝ) (K : ℕ) (hB : 0 ≤ B)
    (hprefix : ∀ n ≤ K,
      ‖∑ j ∈ Finset.range n, Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖ ≤ B) :
    ‖∑ j ∈ Finset.Icc 1 K,
      (Real.log (j : ℝ) : ℂ) * Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖
      ≤ 2 * Real.log (K : ℝ) * B := by
  let e : ℕ → ℂ := fun j => Complex.exp (((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ) * Complex.I)
  let w : ℕ → ℝ := fun j => Real.log ((j+1 : ℕ) : ℝ)
  have hw : Monotone w := by
    intro i j hij
    dsimp [w]
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.succ_le_succ hij)
  have hw₀ (j : ℕ) : 0 ≤ w j :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ j + 1))
  have hshifted (n : ℕ) (hn : n ≤ K) :
      ‖∑ j ∈ Finset.range n, e (j+1)‖ ≤ B := by
    calc
      _ = ‖∑ j ∈ Finset.range n, e j‖ := goldbach_exponential_shifted_range_norm θ n
      _ ≤ _ := hprefix n hn
  have hreindex :
      (∑ j ∈ Finset.Icc 1 K, (Real.log (j : ℝ) : ℂ) * e j) =
        ∑ j ∈ Finset.range K, w j • e (j+1) := by
    simpa only [w, Complex.real_smul] using
      goldbach_sum_Icc_one_eq_shifted_range (fun j => (Real.log (j : ℝ) : ℂ) * e j) K
  change ‖∑ j ∈ Finset.Icc 1 K, (Real.log (j : ℝ) : ℂ) * e j‖ ≤ _
  rw [hreindex]
  by_cases hK : K = 0
  · simp [hK]
  · have hterm : w (K-1) = Real.log (K : ℝ) := by
      dsimp [w]
      rw [Nat.sub_add_cancel (by omega : 1 ≤ K)]
    simpa only [hterm] using
      goldbach_norm_weighted_prefix_le (fun j => e (j+1)) w K B hw hw₀ hB hshifted

theorem goldbach_truncated_square_comparison (F : ℝ → ℝ) (hF : Continuous F)
    (A : ℝ) (hA : 0 ≤ A) (m : ℕ) (hm : 0 < m) (δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ 1 / 2) (s : Set ℝ) (hs : MeasurableSet s)
    (hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      δ ≤ |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)|)
    (hpoint : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      F t ≤ A * (1 / |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)| ^ 2)) :
    (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ A * (2/δ - 4) := by
  let g := goldbach_round_tail δ
  have hi : IntervalIntegrable F volume 0 1 := hF.intervalIntegrable 0 1
  have hiind : IntervalIntegrable (s.indicator F) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hi).indicator hs
  obtain ⟨hiUnit, hvalue⟩ := goldbach_round_tail_integral δ hδ hd
  have hp := goldbach_round_tail_periodic δ
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hiWide : IntervalIntegrable g volume 0 (m : ℝ) :=
    hp.intervalIntegrable₀ one_ne_zero hiUnit 0 (m : ℝ)
  have hiScaled : IntervalIntegrable (fun t => g ((m : ℝ) * t)) volume 0 1 := by
    simpa only [zero_div, div_self hmR] using hiWide.comp_mul_left (c := (m : ℝ))
  have hnonneg (t : ℝ) : 0 ≤ g t := by dsimp [g, goldbach_round_tail]; split <;> positivity
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, A * g ((m : ℝ)*t) := by
      apply intervalIntegral.integral_mono_on zero_le_one hiind (hiScaled.const_mul A)
      intro t ht
      by_cases hb : t ∈ s
      · rw [indicator_of_mem hb]
        dsimp [g]
        rw [goldbach_round_tail, ite_eq_left (hcut t ht hb)]
        exact hpoint t ht hb
      · rw [indicator_of_notMem hb]
        exact mul_nonneg hA (hnonneg _)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        goldbach_periodic_integral_mul_nat g hp hiUnit m hm, hvalue]

theorem goldbach_geometric_tail_l2 (K m : ℕ) (hm : 0 < m) (δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ 1 / 2) (s : Set ℝ) (hs : MeasurableSet s)
    (hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      δ ≤ |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)|) :
    (∫ t in (0 : ℝ)..1, s.indicator (fun t =>
      ‖∑ j ∈ Finset.range K,
        Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2) t)
      ≤ 1 / (2 * δ) := by
  let F : ℝ → ℝ := fun t =>
    ‖∑ j ∈ Finset.range K,
      Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hI : (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ (1/4 : ℝ) * (2/δ - 4) := by
    apply goldbach_truncated_square_comparison F hF (1/4) (by norm_num) m hm δ hδ hd s hs hcut
    intro t ht hb
    have hpos := hδ.trans_le (hcut t ht hb)
    have hgeo := goldbach_geometric_sum_le_inv_twice_round_distance ((m : ℝ)*t) K hpos
    let d : ℝ := |(m : ℝ)*t - (round ((m : ℝ)*t) : ℝ)|
    have hn : 0 < d := hpos
    calc
      _ ≤ (1 / (2 * d)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hgeo 2
      _ = (1/4 : ℝ) * (1 / d^2) := by
        field_simp [hn.ne']
        ring
  change (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ _
  have hEq : (1/4 : ℝ) * (2/δ - 4) = 1/(2*δ) - 1 := by
    field_simp [hδ.ne']
    ring
  rw [hEq] at hI
  linarith only [hI]

theorem goldbach_positive_exponential_tail_l2 (K m : ℕ) (hm : 0 < m) (δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ 1 / 2) (s : Set ℝ) (hs : MeasurableSet s)
    (hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      δ ≤ |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)|) :
    (∫ t in (0 : ℝ)..1, s.indicator (fun t =>
      ‖∑ j ∈ Finset.Icc 1 K,
        Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2) t)
      ≤ 1 / (2 * δ) := by
  simp_rw [goldbach_positive_exponential_prefix_norm]
  exact goldbach_geometric_tail_l2 K m hm δ hδ hd s hs hcut

theorem goldbach_log_exponential_tail_l2 (K m : ℕ) (hm : 0 < m) (δ : ℝ)
    (hδ : 0 < δ) (hd : δ ≤ 1 / 2) (s : Set ℝ) (hs : MeasurableSet s)
    (hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ s →
      δ ≤ |(m : ℝ) * t - (round ((m : ℝ) * t) : ℝ)|) :
    (∫ t in (0 : ℝ)..1, s.indicator (fun t =>
      ‖∑ j ∈ Finset.Icc 1 K, (Real.log (j : ℝ) : ℂ) *
        Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2) t)
      ≤ 2 * Real.log (K : ℝ)^2 / δ := by
  let F : ℝ → ℝ := fun t =>
    ‖∑ j ∈ Finset.Icc 1 K, (Real.log (j : ℝ) : ℂ) *
      Complex.exp (((2 * Real.pi * (j : ℝ) * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2
  let A : ℝ := Real.log (K : ℝ)^2
  have hA : 0 ≤ A := sq_nonneg _
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hI : (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ A * (2/δ - 4) := by
    apply goldbach_truncated_square_comparison F hF A hA m hm δ hδ hd s hs hcut
    intro t ht hb
    have hpos := hδ.trans_le (hcut t ht hb)
    let d : ℝ := |(m : ℝ)*t - (round ((m : ℝ)*t) : ℝ)|
    have hn : 0 < d := hpos
    have hgeo := goldbach_log_exponential_prefix_bound ((m : ℝ)*t) (1/(2*d)) K
      (by positivity) (fun n _ => goldbach_geometric_sum_le_inv_twice_round_distance ((m : ℝ)*t) n hpos)
    have hEq : 2 * Real.log (K : ℝ) * (1/(2*d)) = Real.log (K : ℝ)/d := by
      field_simp [hn.ne']
    rw [hEq] at hgeo
    calc
      _ ≤ (Real.log (K : ℝ)/d)^2 := pow_le_pow_left₀ (norm_nonneg _) hgeo 2
      _ = A * (1/d^2) := by dsimp [A]; rw [div_pow,one_div,div_eq_mul_inv]
  change (∫ t in (0 : ℝ)..1, s.indicator F t) ≤ _
  calc
    _ ≤ A * (2/δ - 4) := hI
    _ ≤ A * (2/δ) := mul_le_mul_of_nonneg_left (sub_le_self _ (by norm_num)) hA
    _ = _ := by dsimp [A]; ring

end GoldbachMinorArcAbelTail

section FrontierMedcoreModelHelpers

open scoped BigOperators ComplexConjugate

theorem frontierMedcoreWeightedPrefixLower (a w : ℕ → ℝ) (K : ℕ) (B : ℝ)
    (hw : Antitone w) (hw₀ : ∀ j, 0 ≤ w j)
    (hPrefix : ∀ m ≤ K, -B ≤ ∑ j ∈ Finset.range m, a j) :
    -(B * w 0) ≤ ∑ j ∈ Finset.range K, w j * a j := by
  have hTel (N : ℕ) :
      (∑ j ∈ Finset.range N, (w (j+1) - w j)) = w N - w 0 := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; ring
  have hLast : -B * w (K-1) ≤ w (K-1) * (∑ j ∈ Finset.range K, a j) := by
    rw [mul_comm (-B)]
    exact mul_le_mul_of_nonneg_left (hPrefix K le_rfl) (hw₀ _)
  have hRest :
      (∑ j ∈ Finset.range (K-1),
        (w (j+1) - w j) * (∑ i ∈ Finset.range (j+1), a i)) ≤ (w (K-1) - w 0) * -B := by
    calc
      _ ≤ ∑ j ∈ Finset.range (K-1), (w (j+1) - w j) * -B := by
        apply Finset.sum_le_sum
        intro j hj
        have hjK : j + 1 ≤ K := by
          have := Finset.mem_range.mp hj
          omega
        exact mul_le_mul_of_nonpos_left (hPrefix (j+1) hjK)
          (sub_nonpos.mpr (hw (Nat.le_succ j)))
      _ = _ := by rw [← Finset.sum_mul, hTel]
  change -(B * w 0) ≤ ∑ j ∈ Finset.range K, w j • a j
  rw [Finset.sum_range_by_parts]
  simp only [smul_eq_mul]
  calc
    _ = -B * w (K-1) - (w (K-1) - w 0) * -B := by ring
    _ ≤ _ := sub_le_sub hLast hRest

private noncomputable def frontierMedcorePhase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

theorem frontierMedcoreKernelReflection (n : ℕ) (β : ℝ) :
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
    let K := ∑ k ∈ Finset.range (n+1), E ((k : ℝ) * β)
    K^2 * E (-(n : ℝ) * β) = (Complex.normSq K : ℂ) := by
  dsimp only
  let F : ℕ → ℂ := fun k => frontierMedcorePhase ((k : ℝ) * β)
  change (∑ k ∈ Finset.range (n+1), F k)^2 * frontierMedcorePhase (-(n : ℝ) * β) =
    (Complex.normSq (∑ k ∈ Finset.range (n+1), F k) : ℂ)
  have hPhaseAdd (x y : ℝ) : frontierMedcorePhase (x + y) =
      frontierMedcorePhase x * frontierMedcorePhase y := by
    unfold frontierMedcorePhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hPhaseConj (x : ℝ) : conj (frontierMedcorePhase x) = frontierMedcorePhase (-x) := by
    unfold frontierMedcorePhase
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hConj : (∑ k ∈ Finset.range (n+1), F k) * frontierMedcorePhase (-(n : ℝ) * β) =
      conj (∑ k ∈ Finset.range (n+1), F k) := by
    rw [Finset.sum_mul, map_sum, ← Finset.sum_range_reflect (fun k => F k * _)]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    have hIdx : n + 1 - 1 - k = n - k := by omega
    rw [hIdx]
    dsimp only [F]
    rw [← hPhaseAdd, hPhaseConj, Nat.cast_sub hk']
    congr 1
    ring
  rw [pow_two, mul_assoc, hConj, Complex.normSq_eq_conj_mul_self, mul_comm]

end FrontierMedcoreModelHelpers

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

namespace GoldbachExplicitModeledMajor

open Finset

noncomputable section
theorem coefficient_not_squarefree {q : ℕ} (n : ℕ) (hq : 0 < q)
    (hs : ¬ Squarefree q) : coefficient q n = 0 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => exact (hs squarefree_one).elim
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => exact (hs (by simpa using hp.squarefree)).elim
      | succ j => exact coefficient_higher_power hp j n
  | coprime a b ha hb hab ia ib =>
    rw [coefficient_mul (by omega) (by omega) hab]
    by_cases h : Squarefree a
    · rw [ib (by omega) (fun h' => hs ((Nat.squarefree_mul hab).mpr ⟨h,h'⟩)), mul_zero]
    · rw [ia (by omega) h, zero_mul]

theorem coefficient_prime_product (n : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    coefficient (∏ p ∈ s, p) n = ((∏ p ∈ s, localCoefficient p n : ℝ) : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficient_one]
  | @insert p s hp ih =>
    have hprime := hs p (mem_insert_self _ _)
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (mem_insert_of_mem hr)
    have hcop : p.Coprime (∏ r ∈ s, r) := Nat.coprime_prod_right_iff.mpr fun r hr =>
      (Nat.coprime_primes hprime (hs' r hr)).mpr fun he => hp (he ▸ hr)
    rw [prod_insert hp, prod_insert hp, coefficient_mul hprime.pos (prod_pos fun r hr => (hs' r hr).pos) hcop,
      coefficient_prime hprime, ih hs', Complex.ofReal_mul]


end
end GoldbachExplicitModeledMajor

end

section

namespace BandTail
open Finset GoldbachExplicitModeledMajor
noncomputable section

private theorem coprime_prod_factors {p : ℕ} {s : Finset ℕ} (hp : p.Prime)
    (hs : ∀ r∈s, r.Prime) (hps : p∉s) : p.Coprime (∏ r∈s, r) :=
  Nat.coprime_prod_right_iff.mpr (fun r hr => (Nat.coprime_primes hp (hs r hr)).mpr (fun e => hps (e ▸ hr)))

theorem coeff_norm_le (q n : ℕ) (hq : 0<q) :
    ‖coefficient q n‖ ≤ 1/(q.totient:ℝ) := by
  by_cases hsf : Squarefree q
  · suffices H : ∀ s : Finset ℕ, (∀ p∈s, p.Prime) →
        ‖coefficient (∏ p∈s, p) n‖ ≤ 1/((∏ p∈s, p).totient:ℝ) by
      simpa only [Nat.prod_primeFactors_of_squarefree hsf] using H q.primeFactors
        (fun _ h => Nat.prime_of_mem_primeFactors h)
    intro s
    induction s using Finset.induction_on with
    | empty => simp [coefficient_one]
    | @insert p s hp ih =>
      intro hs
      have hprime := hs p (mem_insert_self ..)
      have hs' (r : ℕ) (hr : r∈s) := hs r (mem_insert_of_mem hr)
      have hc := coprime_prod_factors hprime hs' hp
      have hpos : 0<∏ r∈s, r := prod_pos fun i hi => (hs' i hi).pos
      rw [prod_insert hp,coefficient_mul hprime.pos hpos hc,Nat.totient_mul hc,Nat.cast_mul,norm_mul,
        coefficient_prime hprime, Complex.norm_real,Real.norm_eq_abs]
      have hR : (2:ℝ)≤p := by exact_mod_cast hprime.two_le
      have hp1 : 0≤(p:ℝ)-1 := by linarith
      have hf : |localCoefficient p n| ≤ 1/(p.totient:ℝ) := by
        rw [Nat.totient_prime hprime,Nat.cast_sub hprime.one_le,Nat.cast_one]
        dsimp [localCoefficient]
        split_ifs
        · rw [abs_of_nonneg (by positivity)]
        · rw [abs_neg,abs_of_nonneg (by positivity)]
          apply one_div_le_one_div_of_le (by linarith)
          nlinarith [mul_nonneg (show 0≤(p:ℝ)-1 by linarith) (show 0≤(p:ℝ)-2 by linarith)]
      exact (mul_le_mul hf (ih hs') (norm_nonneg _) (by positivity)).trans_eq (by ring)
  · rw [coefficient_not_squarefree n hq hsf, norm_zero]; positivity

theorem coeff_bad_prime (p r n : ℕ) (hp : p.Prime) (hpn : ¬p∣n) (hr : 0<r) :
    ‖coefficient (p*r) n‖ ≤ 1/((p:ℝ)-1)^2 * (1/(r.totient:ℝ)) := by
  by_cases hc : p.Coprime r
  · rw [coefficient_mul hp.pos hr hc,norm_mul,coefficient_prime hp,Complex.norm_real,Real.norm_eq_abs,
      localCoefficient,if_neg hpn,abs_neg,abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (coeff_norm_le r n hr) (by positivity)
  · have hpr : p∣r := by simpa [hp.coprime_iff_not_dvd] using hc
    have hsf : ¬Squarefree (p*r) := fun h =>
      Nat.squarefree_iff_prime_squarefree.mp h p hp (Nat.mul_dvd_mul_left _ hpr)
    rw [coefficient_not_squarefree n (Nat.mul_pos hp.pos hr) hsf,norm_zero]
    positivity

theorem good_product {s : Finset ℕ} {n : ℕ} (hs : ∀ p∈s, p.Prime ∧ p∣n) :
    coefficient (∏ p∈s, p) n = ((1/((∏ p∈s, p).totient:ℝ):ℝ):ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficient_one]
  | @insert p s hp ih =>
    have hprime := (hs p (mem_insert_self ..)).1
    have hpn := (hs p (mem_insert_self ..)).2
    have hs' (r : ℕ) (hr : r∈s) := hs r (mem_insert_of_mem hr)
    have hc := coprime_prod_factors hprime (fun r hr => (hs' r hr).1) hp
    have hpos : 0<∏ r∈s, r := prod_pos fun i hi => (hs' i hi).1.pos
    rw [prod_insert hp,coefficient_mul hprime.pos hpos hc,Nat.totient_mul hc,ih hs',coefficient_prime hprime,
      localCoefficient,if_pos hpn,Nat.totient_prime hprime,Nat.cast_mul,Nat.cast_sub hprime.one_le,Nat.cast_one,←Complex.ofReal_mul]
    congr 1
    simp only [div_eq_mul_inv, mul_inv, mul_pow, inv_pow]; ring

theorem bad_product {s : Finset ℕ} {n : ℕ} (hs : ∀ p∈s, p.Prime ∧ ¬p∣n) :
    coefficient (∏ p∈s, p) n =
      (((ArithmeticFunction.moebius (∏ p∈s, p):ℝ)/((∏ p∈s, p).totient:ℝ)^2:ℝ):ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficient_one]
  | @insert p s hp ih =>
    have hprime := (hs p (mem_insert_self ..)).1
    have hpn := (hs p (mem_insert_self ..)).2
    have hs' (r : ℕ) (hr : r∈s) := hs r (mem_insert_of_mem hr)
    have hc := coprime_prod_factors hprime (fun r hr => (hs' r hr).1) hp
    have hpos : 0<∏ r∈s, r := prod_pos fun i hi => (hs' i hi).1.pos
    rw [prod_insert hp,coefficient_mul hprime.pos hpos hc,Nat.totient_mul hc,ih hs',coefficient_prime hprime,
      localCoefficient,if_neg hpn,Nat.totient_prime hprime,Nat.cast_mul,Nat.cast_sub hprime.one_le,Nat.cast_one,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc,ArithmeticFunction.moebius_apply_prime hprime,←Complex.ofReal_mul]
    push_cast
    simp only [div_eq_mul_inv, mul_inv, mul_pow, inv_pow]; ring

theorem coefficient_factorization (q n : ℕ) (hsq : Squarefree q) (hn : 0<n) :
    ∃ d m : ℕ, q=d*m ∧ d∣n ∧ m.Coprime n ∧
      coefficient q n = (((ArithmeticFunction.moebius m:ℝ)/((d.totient:ℝ)*(m.totient:ℝ)^2):ℝ):ℂ) := by
  classical
  let G := q.primeFactors.filter (fun p => p∣n)
  let B := q.primeFactors \ G
  let d := ∏ p∈G, p
  let m := ∏ p∈B, p
  have hG (p : ℕ) (hp : p∈G) : p.Prime ∧ p∣n := by
    obtain ⟨h1,h2⟩ := mem_filter.mp hp
    exact ⟨Nat.prime_of_mem_primeFactors h1,h2⟩
  have hB (p : ℕ) (hp : p∈B) : p.Prime ∧ ¬p∣n := by
    obtain ⟨h1,h2⟩ := mem_sdiff.mp hp
    exact ⟨Nat.prime_of_mem_primeFactors h1,fun hd => h2 (mem_filter.mpr ⟨h1,hd⟩)⟩
  have hqm : q=d*m := by
    have h := Finset.prod_sdiff (f:=id) (s₁:=G) (s₂:=q.primeFactors) (Finset.filter_subset ..)
    simpa [d,m,B,Nat.prod_primeFactors_of_squarefree hsq,mul_comm] using h.symm
  have hdn : d∣n := by
    have hsub : G ⊆ n.primeFactors := fun p hp => Nat.mem_primeFactors.mpr ⟨(hG p hp).1,(hG p hp).2,hn.ne'⟩
    exact dvd_trans (Finset.prod_dvd_prod_of_subset G n.primeFactors id hsub) (Nat.prod_primeFactors_dvd n)
  have hmn : m.Coprime n := Nat.coprime_prod_left_iff.mpr fun p hp => (hB p hp).1.coprime_iff_not_dvd.mpr (hB p hp).2
  refine ⟨d,m,hqm,hdn,hmn,?_⟩
  rw [hqm,coefficient_mul (prod_pos (fun p hp => (hG p hp).1.pos)) (prod_pos (fun p hp => (hB p hp).1.pos))
    (hmn.of_dvd_right hdn).symm, show coefficient d n = _ from good_product hG,
    show coefficient m n = _ from bad_product hB,←Complex.ofReal_mul]
  congr 1
  simp only [div_eq_mul_inv, mul_inv, mul_pow, inv_pow]; ring
end
end BandTail

end

section

namespace BandTail
open Finset ArithmeticFunction GoldbachExplicitModeledMajor
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
noncomputable section

def smooth (n k : ℕ) : Prop := ∀ p ∈ k.primeFactors, p∣n
instance smoothDec (n k : ℕ) : Decidable (smooth n k) := by unfold smooth; infer_instance

def g (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun k => if k=0 then 0 else if smooth n k then 1 else 0,by simp⟩

@[simp] theorem g_one (n : ℕ) : g n 1=1 := by simp [g,smooth]
theorem g_mul (n a b : ℕ) : g n (a*b)=g n a*g n b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hs : smooth n (a*b) ↔ smooth n a ∧ smooth n b := by
    simp only [smooth,Nat.primeFactors_mul ha hb,mem_union]
    constructor
    · intro h; exact ⟨fun p hp => h p (Or.inl hp),fun p hp => h p (Or.inr hp)⟩
    · rintro ⟨x,y⟩ p (h|h)
      · exact x p h
      · exact y p h
  simp only [g,coe_mk, mul_ne_zero ha hb,ha,hb,ite_false]
  by_cases h1 : smooth n a <;> by_cases h2 : smooth n b <;> simp [hs,h1,h2]
theorem g_mult (n : ℕ) : IsMultiplicative (g n) := ⟨g_one n, fun {_ _} _ => g_mul n _ _⟩
theorem g_prime (n p : ℕ) (hp : p.Prime) : g n p=if p∣n then 1 else 0 := by
  simp [g,smooth,hp.ne_zero,hp.primeFactors]

def F (n : ℕ) : ArithmeticFunction ℝ := ⟨fun q => (q:ℝ)*(coefficient q n).re,by simp⟩

theorem coeff_real {q : ℕ} (hq : 0<q) (n : ℕ) : coefficient q n = (((coefficient q n).re:ℝ):ℂ) := by
  by_cases hsf : Squarefree q
  · have he := coefficient_prime_product n q.primeFactors (fun _ hp => Nat.prime_of_mem_primeFactors hp)
    rw [Nat.prod_primeFactors_of_squarefree hsf] at he
    rw [he]; rfl
  · rw [coefficient_not_squarefree n hq hsf]; simp
theorem F_mult (n : ℕ) : IsMultiplicative (F n) := by
  refine ⟨by simp [F,coefficient_one],fun {a b} hab => ?_⟩
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hzero : (coefficient a n).im=0 := by rw [coeff_real ha.bot_lt n]; rfl
  simp [F,coefficient_mul ha.bot_lt hb.bot_lt hab,Complex.mul_re,hzero]
  ring
theorem F_prime (n p : ℕ) (hp : p.Prime) : F n p=(p:ℝ)*localCoefficient p n := by simp [F,coefficient_prime hp]
theorem F_higher (n p j : ℕ) (hp : p.Prime) : F n (p^(j+2))=0 := by simp [F,coefficient_higher_power hp j n]

def invG (n : ℕ) : ArithmeticFunction ℝ := pmul (μ : ArithmeticFunction ℝ) (g n)
def h (n : ℕ) : ArithmeticFunction ℝ := invG n * F n

theorem h_mult (n : ℕ) : IsMultiplicative (h n) :=
  (isMultiplicative_moebius.intCast.pmul (g_mult n)).mul (F_mult n)

theorem inverse_id (n : ℕ) : g n * invG n = 1 := by
  ext k
  have heq : (g n*invG n) k = g n k * (((ζ : ArithmeticFunction ℝ)*μ) k) := by
    simp only [ArithmeticFunction.mul_apply,Finset.mul_sum,invG,pmul_apply]
    apply Finset.sum_congr rfl
    intro ab hab
    have h0 : 0<ab.1 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hab)
    have hG : g n k=g n ab.1*g n ab.2 := (Nat.mem_divisorsAntidiagonal.mp hab).1 ▸ g_mul n ab.1 ab.2
    rw [hG]
    simp [zeta_apply,h0.ne']; ring
  rw [heq,coe_zeta_mul_coe_moebius]
  by_cases hk : k=1 <;> simp [ArithmeticFunction.one_apply,hk]
theorem convolution (n : ℕ) : F n = g n*h n := by rw [h,←mul_assoc,inverse_id,one_mul]

theorem h_prime_recurrence (n p j : ℕ) (hp : p.Prime) :
    h n (p^(j+1))=F n (p^(j+1))-g n p*F n (p^j) := by
  let q := p^(j+1)
  have hq : q≠0 := pow_ne_zero _ hp.ne_zero
  let v := fun d : ℕ => invG n d * F n (q/d)
  have hv : h n q = ∑ d ∈ q.divisors, v d := by
    rw [h,ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun a b : ℕ => invG n a * F n b)]
  have h1 : ({1,p}:Finset ℕ) ⊆ q.divisors := by
    intro a ha
    simp only [mem_insert,mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨one_dvd _,hq⟩
    · exact Nat.mem_divisors.mpr ⟨dvd_pow_self _ (by omega),hq⟩
  have hsum : ∑ d ∈ q.divisors,v d = ∑ d ∈ ({1,p}:Finset ℕ),v d := by
    symm; apply sum_subset h1
    intro d hd hn
    obtain ⟨i,hi,he⟩ := (Nat.dvd_prime_pow hp).mp (Nat.dvd_of_mem_divisors hd)
    by_cases hi0 : i=0
    · exfalso; apply hn; simp [he,hi0]
    by_cases hi1 : i=1
    · exfalso; apply hn; simp [he,hi1]
    have hm : μ d=0 := by rw [he, moebius_apply_prime_pow hp hi0,if_neg hi1]
    simp [v,invG,pmul_apply,intCoe_apply,hm]
  have hdiv : q/p=p^j := by dsimp [q]; rw [pow_succ,Nat.mul_div_cancel _ hp.pos]
  change h n q = _
  rw [hv,hsum,Finset.sum_insert (by simpa using hp.ne_one.symm : (1:ℕ)∉({p}:Finset ℕ)),Finset.sum_singleton]
  simp [v,invG,pmul_apply,intCoe_apply,moebius_apply_prime hp,hdiv,q]
  ring

theorem h_prime (n p : ℕ) (hp : p.Prime) : h n p =
    if p∣n then 1/((p:ℝ)-1) else -(p:ℝ)/((p:ℝ)-1)^2 := by
  have he := h_prime_recurrence n p 0 hp
  have he1 : F n 1=1 := (F_mult n).map_one
  simp only [Nat.zero_add,pow_one,pow_zero,he1,F_prime n p hp,g_prime n p hp,mul_one] at he
  rw [he]; dsimp [localCoefficient]
  have hr1 : (p:ℝ)-1≠0 := by
    have ht : (2:ℝ)≤p := by exact_mod_cast hp.two_le
    linarith
  split_ifs <;> field_simp <;> ring
theorem h_square (n p : ℕ) (hp : p.Prime) : h n (p^2) =
    if p∣n then -(p:ℝ)/((p:ℝ)-1) else 0 := by
  have he := h_prime_recurrence n p 1 hp
  rw [F_higher n p 0 hp,pow_one,g_prime n p hp,F_prime n p hp] at he
  rw [he]; dsimp [localCoefficient]; split_ifs <;> ring
theorem h_cube (n p j : ℕ) (hp : p.Prime) : h n (p^(j+3))=0 := by
  have he := h_prime_recurrence n p (j+2) hp
  rw [F_higher n p j hp,show j+2+1=(j+1)+2 by omega,F_higher n p (j+1) hp] at he
  simpa [show j+2+1=j+3 by omega] using he

end
end BandTail

end

section

namespace BandTail
open Finset
noncomputable section

private theorem pairPos {q : ℕ} {v : ℕ × ℕ} (hv : v ∈ q.divisorsAntidiagonal) : 0<v.1 ∧ 0<v.2 :=
  ⟨Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hv),
   Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hv)⟩

theorem unpair (U : ℕ) (F : ℕ×ℕ → ℝ) (hF : ∀ x, 0 ≤ F x) :
    (∑ q ∈ Icc 1 U, ∑ v ∈ q.divisorsAntidiagonal, F v) ≤
      ∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 U, F (a,b) := by
  classical
  let S := Icc 1 U
  have hf (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal = (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    obtain ⟨hq0,hqQ⟩ := mem_Icc.mp hq
    ext ab
    constructor
    · intro hab
      have hm (a : ℕ) (ha : a ∈ q.divisors) : a ∈ S :=
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,(Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors ha)).trans hqQ⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ (Nat.fst_mem_divisors_of_mem_antidiagonal hab),
        hm _ (Nat.snd_mem_divisors_of_mem_antidiagonal hab)⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
    · intro h; exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp h).2,by omega⟩
  calc
    _ = ∑ q ∈ S, ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), F v :=
      sum_congr rfl (fun q hq => by rw [hf q hq])
    _ = ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), F v :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ v ∈ S ×ˢ S, F v := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun v _ _ => hF v)
    _ = _ := Finset.sum_product _ _ _

theorem invSquares (U : ℕ) : (∑ k ∈ Icc 1 U, ((k:ℝ)^2)⁻¹) ≤ 2 := by
  rcases U with _ | u
  · simp
  · have hUU : 1≤u+1 := by omega
    have H := sum_Ioc_inv_sq_le_sub (α:=ℝ) (by decide : 1 ≠ 0) hUU
    rw [← Finset.sum_Ioc_add_eq_sum_Icc hUU]
    norm_num at H ⊢
    linarith [show 0 ≤ ((u:ℝ)+1)⁻¹ by positivity]

theorem scaledInvSquares (X v U : ℕ) (hv : 0<v) :
    (X:ℝ) * (∑ k ∈ Icc 1 U, if X<v*k then ((k:ℝ)^2)⁻¹ else 0) ≤ 2*v := by
  by_cases h : X<v
  · have hc : (∑ k ∈ Icc 1 U, if X<v*k then ((k:ℝ)^2)⁻¹ else 0) ≤ 2 :=
      (sum_le_sum fun k _ => by split_ifs <;> first | rfl | positivity).trans (invSquares U)
    exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans (by exact_mod_cast (by omega : X*2 ≤ 2*v))
  have hm : 0<X/v := Nat.div_pos (by omega) hv
  have he : ∑ k ∈ Icc 1 U, (if X<v*k then ((k:ℝ)^2)⁻¹ else 0) =
      ∑ k ∈ Ioc (X/v) U, ((k:ℝ)^2)⁻¹ := by
    rw [← sum_filter]
    congr 1
    ext k
    simp only [mem_filter,mem_Icc,mem_Ioc,Nat.div_lt_iff_lt_mul hv]
    constructor <;> rintro h
    · exact ⟨by simpa [mul_comm] using h.2,h.1.2⟩
    · exact ⟨⟨by cases k <;> simp_all, h.2⟩,by simpa [mul_comm] using h.1⟩
  rw [he]
  by_cases hU : X/v≤U
  · have H := sum_Ioc_inv_sq_le_sub (α:=ℝ) hm.ne' hU
    have hc := H.trans (sub_le_self _ (by positivity))
    have hlim := Nat.div_add_mod X v
    have hmod := Nat.mod_lt X hv
    have hle : X ≤ 2*v*(X/v) := by nlinarith only [hlim,hmod,Nat.mul_le_mul_left v hm]
    have hr : 0<((X/v:ℕ):ℝ) := by exact_mod_cast hm
    refine (mul_le_mul_of_nonneg_left hc (by positivity : 0≤(X:ℝ))).trans ?_
    rw [←div_eq_mul_inv,div_le_iff₀ hr]
    exact_mod_cast hle
  · simp [Finset.Ioc_eq_empty_of_le (by omega : U≤X/v)]

theorem totient_series (U : ℕ) : (∑ q ∈ Icc 1 U, 1/((q:ℝ)*q.totient)) ≤ 4 := by
  let F := fun ab : ℕ×ℕ => ((ab.1:ℝ)^2)⁻¹ * ((ab.2:ℝ)^2)⁻¹
  calc
    _ ≤ ∑ q ∈ Icc 1 U, ∑ ab ∈ q.divisorsAntidiagonal, F ab := by
      apply sum_le_sum
      intro q hq
      have hq0 := (mem_Icc.mp hq).1
      have hφ := Nat.totient_pos.mpr hq0
      have hcount : q ≤ q.divisors.card*q.totient := calc
        _ = ∑ d ∈ q.divisors, d.totient := (Nat.sum_totient q).symm
        _ ≤ ∑ _ ∈ q.divisors, q.totient := sum_le_sum fun d hd => Nat.le_of_dvd hφ (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
        _ = _ := by simp
      calc
        _ ≤ (q.divisors.card:ℝ)/(q:ℝ)^2 := by
          have hr : (0:ℝ)<q := by exact_mod_cast hq0
          have hφr : (0:ℝ)<q.totient := by exact_mod_cast hφ
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          have hc : (q:ℝ)≤q.divisors.card*q.totient := by exact_mod_cast hcount
          nlinarith only [mul_le_mul_of_nonneg_left hc hr.le]
        _ = ∑ ab ∈ q.divisorsAntidiagonal, ((q:ℝ)^2)⁻¹ := by
          rw [Nat.sum_divisorsAntidiagonal (fun _ _ => ((q:ℝ)^2)⁻¹)]; simp [div_eq_mul_inv]
        _ = _ := by
          apply sum_congr rfl; intro ab hab
          dsimp [F]
          rw [←(Nat.mem_divisorsAntidiagonal.mp hab).1,Nat.cast_mul,mul_pow,mul_inv]
    _ ≤ ∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 U, F (a,b) := unpair U F (by intro x; dsimp [F]; positivity)
    _ = (∑ a ∈ Icc 1 U, ((a:ℝ)^2)⁻¹)^2 := by dsimp [F]; rw [sq,Finset.sum_mul_sum]
    _ ≤ 4 := by
      have h := pow_le_pow_left₀ (by exact sum_nonneg (fun _ _ => by positivity)) (invSquares U) 2
      norm_num at h ⊢; exact h

theorem totient_tail (X v U : ℕ) (hv : 0<v) :
    (X:ℝ)*(∑ q ∈ Icc 1 U, if X<v*q then 1/((q:ℝ)*q.totient) else 0) ≤ 8*v := by
  let F := fun ab : ℕ×ℕ => (1 / ((ab.1:ℝ)^2*ab.1.totient)) *
      (if X<v*ab.1*ab.2 then ((ab.2:ℝ)^2)⁻¹ else 0)
  have hF (x : ℕ×ℕ) : 0≤F x := by dsimp [F]; split_ifs <;> positivity
  have hh (q : ℕ) (hq : q ∈ Icc 1 U) :
      (if X<v*q then 1/((q:ℝ)*q.totient) else 0) ≤ ∑ ab ∈ q.divisorsAntidiagonal, F ab := by
    by_cases h : X<v*q
    · rw [if_pos h]
      have hq0 := (mem_Icc.mp hq).1
      have hqR : (0:ℝ)<q := by exact_mod_cast hq0
      have hφR : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
      have he : ∑ ab ∈ q.divisorsAntidiagonal, (ab.2.totient:ℝ) = (q:ℝ) := by
        exact_mod_cast (by rw [Nat.sum_divisorsAntidiagonal (fun (_ : ℕ) (b : ℕ) => b.totient), Nat.sum_div_divisors]; exact Nat.sum_totient q : ∑ ab ∈ q.divisorsAntidiagonal, ab.2.totient=q)
      calc
        _ = (∑ ab ∈ q.divisorsAntidiagonal, (ab.2.totient:ℝ))/((q:ℝ)^2*q.totient) := by rw [he]; field_simp
        _ = ∑ ab ∈ q.divisorsAntidiagonal, (ab.2.totient:ℝ)/((q:ℝ)^2*q.totient) := Finset.sum_div _ _ _
        _ ≤ _ := by
          apply sum_le_sum
          intro ab hab
          obtain ⟨ha,hb⟩ := pairPos hab
          have hprod := (Nat.mem_divisorsAntidiagonal.mp hab).1
          have habR : (ab.1:ℝ)*ab.2=q := by exact_mod_cast hprod
          have hφa : (0:ℝ)<ab.1.totient := by exact_mod_cast Nat.totient_pos.mpr ha
          have hbR : (0:ℝ)<ab.2 := by exact_mod_cast hb
          have haR : (0:ℝ)<ab.1 := by exact_mod_cast ha
          have hs := Nat.totient_super_multiplicative ab.1 ab.2
          rw [hprod] at hs
          have hs' : (ab.1.totient:ℝ)*ab.2.totient≤q.totient := by exact_mod_cast hs
          dsimp [F]
          rw [mul_assoc,hprod,if_pos h]
          rw [←habR,mul_pow]
          field_simp
          nlinarith only [hs']
    · rw [if_neg h]; exact sum_nonneg fun ab _ => hF ab
  calc
    _ ≤ (X:ℝ)*(∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 U, F (a,b)) :=
      mul_le_mul_of_nonneg_left ((sum_le_sum hh).trans (unpair U F hF)) (by positivity)
    _ = ∑ a ∈ Icc 1 U, (1 / ((a:ℝ)^2*a.totient)) *
        ((X:ℝ) * ∑ b ∈ Icc 1 U, if X<(v*a)*b then ((b:ℝ)^2)⁻¹ else 0) := by
      rw [Finset.mul_sum]
      apply sum_congr rfl; intro a _
      dsimp [F]
      rw [←Finset.mul_sum]; ring
    _ ≤ ∑ a ∈ Icc 1 U, 2*(v:ℝ)*(1/((a:ℝ)*a.totient)) := by
      apply sum_le_sum; intro a ha
      have ha0 := (Finset.mem_Icc.mp ha).1
      have hs := scaledInvSquares X (v*a) U (Nat.mul_pos hv ha0)
      refine (mul_le_mul_of_nonneg_left hs (by positivity : 0≤1/((a:ℝ)^2*a.totient))).trans_eq ?_
      push_cast
      have haR : (0:ℝ)<a := by exact_mod_cast ha0
      have hφR : (0:ℝ)<a.totient := by exact_mod_cast Nat.totient_pos.mpr ha0
      field_simp
    _ = 2*(v:ℝ)*(∑ a ∈ Icc 1 U, 1/((a:ℝ)*a.totient)) := (Finset.mul_sum ..).symm
    _ ≤ 8*v := by nlinarith only [mul_le_mul_of_nonneg_left (totient_series U) (show 0≤(v:ℝ) by positivity)]

end
end BandTail

end

section

/- The finite phase and Ramanujan identities in this section are adapted from
DFQDZZ's Apache-2.0 proof in goldbach-proofs PR #316,
commit e4ab24712555ae8c2c926adf19d368a9fb392c35. -/
namespace GoldbachExplicitModeledMajor
open Finset MeasureTheory
open scoped ComplexConjugate
noncomputable section

private theorem windowPhaseAdd (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

private theorem windowConjPhase (x : ℝ) : conj (phase x) = phase (-x) := by
  unfold phase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- Centering the square of the geometric sum makes its phase cancel exactly. -/
theorem windowKernelSquare (n : ℕ) (β : ℝ) :
    kernel n β ^ 2 * phase (-(n : ℝ) * β) = ((‖kernel n β‖ ^ 2 : ℝ) : ℂ) := by
  have hsym : kernel n β * phase (-(n : ℝ) * β) = conj (kernel n β) := by
    unfold kernel
    rw [sum_mul, map_sum]
    calc
      _ = ∑ k ∈ range (n + 1), conj (phase (((n - k : ℕ) : ℝ) * β)) := by
        refine sum_congr rfl fun k hk => ?_
        rw [windowConjPhase, ← windowPhaseAdd, Nat.cast_sub (Nat.lt_succ_iff.mp (mem_range.mp hk))]
        congr 1
        ring
      _ = _ := by
        simpa only [Nat.add_sub_cancel] using
          (Finset.sum_range_reflect (fun k => conj (phase ((k : ℝ) * β))) (n + 1))
  calc
    _ = kernel n β * (kernel n β * phase (-(n : ℝ) * β)) := by ring
    _ = _ := by rw [hsym, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem windowRamPower {p : ℕ} (hp : p.Prime) (j h : ℕ) (hc : h.Coprime p) :
    ram (p ^ (j + 1)) h = if j = 0 then -1 else 0 := by
  have hd := hp.coprime_iff_not_dvd.mp hc.symm
  have hpow (k : ℕ) : ¬ p ^ (k + 1) ∣ h :=
    fun hh => hd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans hh)
  rw [ram_primePower p j h hp, ite_eq_right (hpow j)]
  cases j with
  | zero => simp
  | succ k => simp [hpow k]

theorem windowRamUnit (q h : ℕ) (hc : h.Coprime q) : ram q h = ram q 1 := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ k =>
      have hc' := (Nat.coprime_pow_right_iff (Nat.succ_pos k) h p).mp hc
      rw [windowRamPower hp k h hc', windowRamPower hp k 1 (by simp)]
  | coprime q r hq hr hqr iq ir =>
    obtain ⟨h₁,h₂⟩ := Nat.coprime_mul_iff_right.mp hc
    rw [ram_mul (by omega) (by omega) hqr, ram_mul (by omega) (by omega) hqr, iq h₁, ir h₂]

def windowAvg (q a : ℕ) : ℂ := (∑ r ∈ (range q).filter (fun r => r.Coprime q),
  phase ((r:ℝ)*a/q))/(q.totient:ℂ)

private theorem avg_const (q a : ℕ) (ha : a.Coprime q) :
    windowAvg q a = ram q 1/(q.totient:ℂ) := by
  have hm : (∑ r ∈ (range q).filter (fun r => r.Coprime q), phase ((r:ℝ)*a/q)) = ram q a := by
    unfold ram; apply sum_congr rfl; intro r _; congr 1; ring
  rw [windowAvg,hm,windowRamUnit q a ha]

def windowModel (n A B : ℕ) : ℂ :=
  ∑ q ∈ Ioc A B, ∑ a ∈ (range (q+1)).filter (fun a => a.Coprime q),
    ∫ t in (a:ℝ)/q-width n q..(a:ℝ)/q+width n q,
      (windowAvg q a * kernel n (t-(a:ℝ)/q))^2 * phase (-(n:ℝ)*t)

private theorem windowIntegral (n : ℕ) (c b : ℝ) (z : ℂ) :
    (∫ t in c-b..c+b, (z*kernel n (t-c))^2*phase (-(n:ℝ)*t)) =
      z^2*phase (-(n:ℝ)*c)*(kernelMass n b:ℂ) := by
  have ht := intervalIntegral.integral_comp_add_left
    (fun t => (z*kernel n (t-c))^2*phase (-(n:ℝ)*t)) (a := -b) (b := b) c
  rw [sub_eq_add_neg,← ht]
  calc
    _ = ∫ x in -b..b, (z^2*phase (-(n:ℝ)*c))*((‖kernel n x‖^2:ℝ):ℂ) := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [add_sub_cancel_left,mul_add,windowPhaseAdd,← windowKernelSquare]
      ring
    _ = _ := by rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_ofReal]; rfl

theorem windowModel_re (n A B : ℕ) (hA : 1≤A) :
    (windowModel n A B).re = ∑ q ∈ Ioc A B, (coefficient q n).re * kernelMass n (width n q) := by
  unfold windowModel
  simp_rw [windowIntegral]
  rw [Complex.re_sum]
  apply sum_congr rfl
  intro q hq
  have hq' : 1<q := lt_of_le_of_lt hA (mem_Ioc.mp hq).1
  have hrange : (range (q+1)).filter (fun a => a.Coprime q) = (range q).filter (fun a => a.Coprime q) := by
    ext a
    simp only [mem_filter,mem_range]
    constructor
    · rintro ⟨ha,hc⟩
      have hne : a ≠ q := by
        rintro rfl
        simp [Nat.Coprime] at hc
        omega
      exact ⟨by omega,hc⟩
    · rintro ⟨ha,hc⟩; exact ⟨by omega,hc⟩
  rw [hrange,← sum_mul]
  have hc : (∑ a ∈ (range q).filter (fun a => a.Coprime q),
      windowAvg q a ^ 2 * phase (-(n:ℝ)*((a:ℝ)/q))) = coefficient q n := by
    unfold coefficient ram
    rw [map_sum,mul_sum]
    apply sum_congr rfl
    intro a ha
    rw [avg_const _ _ (mem_filter.mp ha).2,windowConjPhase]
    congr 2
    ring
  rw [hc,Complex.mul_re]; simp

end
end GoldbachExplicitModeledMajor

end

section

namespace BandTail
open Finset GoldbachExplicitModeledMajor MeasureTheory Filter Topology
noncomputable section

private theorem mass_nonneg (n q : ℕ) : 0 ≤ kernelMass n (width n q) := by
  apply intervalIntegral.integral_nonneg
  · linarith only [width_nonneg n q]
  · intro t _; positivity

theorem mass_upper (n q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q) :
    kernelMass n (width n q) ≤ 8*(n:ℝ)*(cutoff n:ℝ)/q := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hK (x : ℝ) : ‖kernel n x‖ ≤ (n:ℝ)+1 := by
    unfold kernel
    exact (norm_sum_le ..).trans (by simp [phase,Complex.norm_exp])
  have hnn := mass_nonneg n q
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -(width n q)) (b := width n q)
    (f := fun x : ℝ => ‖kernel n x‖^2) (C := ((n:ℝ)+1)^2) (fun t _ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hK t) 2)
  change |kernelMass n (width n q)| ≤ _ at h
  rw [abs_of_nonneg hnn,abs_of_nonneg (by linarith only [width_nonneg n q])] at h
  refine h.trans ?_
  unfold width
  have hnpos : (0:ℝ) < n := by linarith
  have hQ : 0 ≤ (cutoff n:ℝ) := by positivity
  have hsq : ((n:ℝ)+1)^2 ≤ 4*(n:ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn') (show 0 ≤ 3*(n:ℝ)+1 by positivity)]
  field_simp
  nlinarith only [mul_le_mul_of_nonneg_right hsq hQ]

private def bandWeight (n q : ℕ) : ℝ := kernelMass n (width n q)/(q:ℝ)

private theorem weight_mono (n i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) : bandWeight n j ≤ bandWeight n i := by
  have hi' : (0:ℝ) < i := by exact_mod_cast hi
  have hj' : (0:ℝ) < j := by exact_mod_cast hi.trans hij
  have hr : (i:ℝ) ≤ j := by exact_mod_cast hij
  have hw : width n j ≤ width n i := by
    by_cases hn : n=0
    · simp [width,hn]
    · unfold width
      gcongr
  unfold bandWeight
  apply div_le_div₀ (mass_nonneg n i) (kernelMass_mono (width_nonneg n j) hw n) hi' hr

theorem weighted_prefix_lower (A B : ℕ) (f w : ℕ → ℝ) (k : ℝ)
    (hab : A ≤ B) (hk : 0 ≤ k) (hw : ∀ i ≥ A,0 ≤ w i) (hm : ∀ i ≥ A,w (i+1) ≤ w i)
    (hp : ∀ i ≥ A,i ≤ B → -k ≤ ∑ j ∈ Ioc A i,f j) :
    -(k*w A) ≤ ∑ j ∈ Ioc A B,f j*w j := by
  have strong (i : ℕ) (hi : A ≤ i) (hiB : i ≤ B) :
      w i*((∑ j ∈ Ioc A i,f j)+k) ≤ (∑ j ∈ Ioc A i,f j*w j)+k*w A := by
    induction i,hi using Nat.le_induction with
    | base => simp [mul_comm]
    | succ i hi ih =>
      have h := ih (by omega)
      have hmono := hm i hi
      have hx := hp i hi (by omega)
      rw [sum_Ioc_succ_top hi,sum_Ioc_succ_top hi]
      nlinarith only [h,mul_nonneg (sub_nonneg.mpr hmono) (show 0 ≤ (∑ j ∈ Ioc A i,f j)+k by linarith)]
  have h := strong B hab le_rfl
  have v := hp B hab le_rfl
  nlinarith only [h,mul_nonneg (hw B hab) (show 0 ≤ (∑ j ∈ Ioc A B, f j)+k by linarith)]

theorem model_from_prefix (n B R : ℕ) (δ : ℝ) (hn : 1 ≤ n) (hR : 1 ≤ R) (hδ : 0 ≤ δ)
    (hprefix : ∀ i ≥ cutoff n,i ≤ R*cutoff n → -(δ*(cutoff n:ℝ)) ≤ ∑ q ∈ Ioc (cutoff n) i, F n q) :
    -((8*δ + 64/(R:ℝ))*(n:ℝ)) ≤ (windowModel n (cutoff n) B).re := by
  let A := cutoff n
  have ha : 1 ≤ A := cutoff_positive n
  have ha' : (0:ℝ) < A := by exact_mod_cast ha
  have hr' : (0:ℝ) < R := by exact_mod_cast hR
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [windowModel_re _ _ _ ha]
  change _ ≤ ∑ q ∈ Ioc A B, _
  by_cases hab : A ≤ B
  · let T := min B (R*A)
    have hT : A ≤ T := le_min hab (by dsimp [A]; nlinarith [Nat.mul_le_mul_right (cutoff n) hR])
    have hind := weighted_prefix_lower A T (F n) (bandWeight n) (δ*(A:ℝ)) hT (by positivity)
      (fun i _ => div_nonneg (mass_nonneg n i) (by positivity)) (fun i hi => weight_mono n _ _ (ha.trans hi) (by omega))
      (fun i hi hmax => hprefix i hi (hmax.trans (min_le_right _ _)))
    have hweight : bandWeight n A ≤ 8*(n:ℝ)/A := by
      have h := mass_upper n A hn ha
      change kernelMass n (width n A) ≤ 8*(n:ℝ)*A/A at h
      rw [mul_div_cancel_right₀ _ ha'.ne'] at h
      exact div_le_div_of_nonneg_right h ha'.le
    have hs : -(8*δ*(n:ℝ)) ≤ ∑ q ∈ Ioc A T, (coefficient q n).re * kernelMass n (width n q) := by
      calc
        _ ≤ -(δ*(A:ℝ)*bandWeight n A) := by
          have h := mul_le_mul_of_nonneg_left hweight (show 0 ≤ δ*(A:ℝ) by positivity)
          field_simp at h
          nlinarith only [h]
        _ ≤ _ := hind
        _ = _ := sum_congr rfl (fun q hq => by
          have hq' : (q:ℝ)≠0 := by exact_mod_cast (show q≠0 by have := (mem_Ioc.mp hq).1; omega)
          change (q:ℝ)*_ * (_/(q:ℝ)) = _
          field_simp)
    have ht : -(64*(n:ℝ)/R) ≤ ∑ q ∈ Ioc T B, (coefficient q n).re * kernelMass n (width n q) := by
      by_cases hB : B ≤ R*A
      · simp [T,min_eq_left hB]; positivity
      · rw [show T = R*A from min_eq_right (by omega)]
        have hsum := totient_tail (R*A) 1 B (by decide)
        let S := Ioc (R*A) B
        have he : ∑ q ∈ S, 1/((q:ℝ)*q.totient) ≤
          ∑ q ∈ Icc 1 B, if R*A < 1*q then 1/((q:ℝ)*q.totient) else 0 := by
          rw [← sum_filter]
          apply le_of_eq
          congr 1
          ext q; simp only [S,mem_Ioc,mem_filter,mem_Icc,one_mul]
          constructor <;> rintro h <;> omega
        have hsz : ((R:ℝ)*A)*(∑ q ∈ S,1/((q:ℝ)*q.totient)) ≤ 8 := by
          push_cast at hsum
          exact (mul_le_mul_of_nonneg_left he (by positivity)).trans (by simpa only [Nat.cast_one,mul_one] using hsum)
        have hterm (q : ℕ) (hq : q∈S) : -((8*(n:ℝ)*A)*(1/((q:ℝ)*q.totient))) ≤
            (coefficient q n).re * kernelMass n (width n q) := by
          have hq0 : 1 ≤ q := by have := (mem_Ioc.mp hq).1; omega
          have hq' : (0:ℝ) < q := by exact_mod_cast hq0
          have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
          have hc := (Complex.abs_re_le_norm (coefficient q n)).trans (coeff_norm_le q n hq0)
          have hmass := mass_upper n q hn hq0
          have hprod := mul_le_mul hc hmass (mass_nonneg n q) (by positivity)
          have habs : |(coefficient q n).re * kernelMass n (width n q)| ≤ (1/(q.totient:ℝ))*(8*(n:ℝ)*(cutoff n:ℝ)/q) := by
            simpa only [abs_mul,abs_of_nonneg (mass_nonneg n q)] using hprod
          have hneg := (neg_le_of_abs_le habs)
          convert hneg using 1 <;> dsimp [A] <;> ring
        have hsum' := sum_le_sum hterm
        rw [sum_neg_distrib,← mul_sum] at hsum'
        refine le_trans ?_ hsum'
        apply neg_le_neg
        apply (le_div_iff₀ hr').mpr
        nlinarith only [mul_le_mul_of_nonneg_left hsz (show 0 ≤ 8*(n:ℝ) by positivity)]
    rw [← sum_Ioc_consecutive _ hT (min_le_left _ _)]
    have hid : 64*(n:ℝ)/R = (64/(R:ℝ))*(n:ℝ) := by ring
    linarith
  · simp [Ioc_eq_empty (by omega : ¬ A < B)]
    positivity

end
end BandTail

end

section

namespace BandTail
open Finset GoldbachExplicitModeledMajor Filter Topology
noncomputable section

theorem floor_from_uniform
    (uniform : ∀ R : ℕ, 1 ≤ R → ∀ δ : ℝ, 0 < δ → ∃ A₀ : ℕ,
      ∀ A ≥ A₀, ∀ n i : ℕ, A ≤ i → i ≤ R*A → -(δ*(A:ℝ)) ≤ ∑ q ∈ Ioc A i, F n q) :
    ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ B : ℕ,
      -(e*(n:ℝ)) ≤ (windowModel n (cutoff n) B).re := by
  intro e he
  let R : ℕ := ⌈128/e⌉₊+1
  have hR : 1 ≤ R := by dsimp [R]; omega
  have hR' : (0:ℝ) < R := by exact_mod_cast hR
  have hlarge : 128 / e ≤ (R:ℝ) := by
    dsimp [R]; push_cast; linarith only [Nat.le_ceil (128/e)]
  have hratio : 64/(R:ℝ) ≤ e/2 := (div_le_iff₀ hR').mpr (by
    have h := (div_le_iff₀ he).mp hlarge
    linarith)
  obtain ⟨A₀,hA⟩ := uniform R hR (e/16) (by positivity)
  refine ⟨2^A₀+1,?_⟩
  intro n hn B
  have hn' : 1 ≤ n := (Nat.succ_le_succ (Nat.zero_le (2^A₀))).trans hn
  have hlog : A₀ ≤ Nat.log 2 (n+2) := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by omega)
  have hl : 1 ≤ Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
  have hc : A₀ ≤ cutoff n := hlog.trans (by
    dsimp [cutoff]; nlinarith [Nat.mul_le_mul_left (Nat.log 2 (n+2)) hl])
  apply le_trans _ (model_from_prefix n B R (e/16) hn' hR (by positivity) (hA _ hc n))
  have hk : 8*(e/16)+64/(R:ℝ) ≤ e := by linarith
  exact neg_le_neg (mul_le_mul_of_nonneg_right hk (by positivity))

end
end BandTail

end

section

namespace BandTail
open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta
noncomputable section
def w (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => |h n d|/(d:ℝ)^(3/4:ℝ),by simp⟩
def z (n : ℕ) : ArithmeticFunction ℝ := ⟨fun d => h n d/(d:ℝ),by simp⟩
theorem w_mult (n : ℕ) : IsMultiplicative (w n) := by
  refine ⟨by simp [w,(h_mult n).map_one],fun {a b} hab => ?_⟩
  simp only [w,coe_mk,(h_mult n).map_mul_of_coprime hab,Nat.cast_mul,abs_mul,Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
  ring
theorem z_mult (n : ℕ) : IsMultiplicative (z n) := by
  refine ⟨by simp [z,(h_mult n).map_one],fun {a b} hab => ?_⟩
  simp [z,(h_mult n).map_mul_of_coprime hab]; ring
theorem w_nonneg (n d : ℕ) : 0≤w n d := by dsimp [w]; positivity

theorem localReduce (f : ℕ → ℝ) (hf : ∀ j, f (j+3)=0) (k : ℕ) :
    (∑ i ∈ range (k+1), f i)=f 0 + (if k≥1 then f 1 else 0) + (if k≥2 then f 2 else 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ,ih]
    rcases k with _ | _ | j
    · simp
    · simp
    · simp [hf,show 2≤j+1+1 by omega,show 2≤j+1+1+1 by omega]

theorem wLocal (p n k : ℕ) (hp : p.Prime) :
    (∑ d ∈ (p^k).divisors, w n d) ≤ 1+6/((p:ℝ)^(3/2:ℝ)) := by
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hp1 : 0<(p:ℝ)-1 := by linarith
  have hpr : 0<(p:ℝ) := by linarith
  have hW1 : w n p ≤ 4/((p:ℝ)^(3/2:ℝ)) := by
    have h₁ : |h n p| ≤ 4/(p:ℝ) := by
      rw [h_prime n p hp]
      split_ifs
      · rw [abs_of_nonneg (by positivity)]; field_simp; linarith
      · rw [abs_div,abs_neg,abs_of_nonneg hpr.le,abs_of_nonneg (sq_nonneg _)]
        field_simp
        nlinarith [mul_nonneg (show 0≤(p:ℝ)-2 by linarith) (show 0≤3*(p:ℝ)-2 by linarith)]
    dsimp [w]
    calc
      _ ≤ (4/(p:ℝ))/((p:ℝ)^(3/4:ℝ)) := div_le_div_of_nonneg_right h₁ (by positivity)
      _ = 4/(p:ℝ)^(1+(3/4):ℝ) := by rw [Real.rpow_add hpr,Real.rpow_one,div_div]
      _ ≤ _ := by apply div_le_div_of_nonneg_left (by norm_num) (by positivity); exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hW2 : w n (p^2) ≤ 2/(p:ℝ)^(3/2:ℝ) := by
    have he : |h n (p^2)| ≤ 2 := by
      rw [h_square n p hp]; split_ifs
      · rw [abs_div,abs_neg,abs_of_nonneg hpr.le,abs_of_nonneg hp1.le]; apply (div_le_iff₀ hp1).mpr; linarith
      · norm_num
    change |h n (p^2)| / ((p^2:ℕ):ℝ)^(3/4:ℝ) ≤ _
    rw [Nat.cast_pow,←Real.rpow_natCast_mul hpr.le,show (↑(2:ℕ):ℝ)*(3/4)=3/2 by norm_num]
    exact div_le_div_of_nonneg_right he (by positivity)
  rw [Nat.sum_divisors_prime_pow hp,localReduce (fun j => w n (p^j)) (fun j => by simp [w,h_cube n p j hp])]
  simp only [pow_zero,pow_one,(w_mult n).map_one]
  simp only [div_eq_mul_inv] at hW1 hW2 ⊢
  split_ifs <;> linarith [w_nonneg n p,w_nonneg n (p^2)]

theorem zLocal (p n k : ℕ) (hp : p.Prime) : 0≤∑ d ∈ (p^k).divisors,z n d := by
  rw [Nat.sum_divisors_prime_pow hp,localReduce (fun j => z n (p^j)) (fun j => by simp [z,h_cube n p j hp])]
  simp only [pow_zero,pow_one,(z_mult n).map_one]
  have h2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hp1 : 0<(p:ℝ)-1 := by linarith
  have hpr : 0<(p:ℝ) := by linarith
  have hsq : 1≤((p:ℝ)-1)^2 := by nlinarith [mul_nonneg (show 0≤(p:ℝ)-2 by linarith) (show 0≤(p:ℝ) by linarith)]
  simp only [z,coe_mk,h_prime n p hp,h_square n p hp,Nat.cast_pow]
  by_cases hpn : p∣n
  · simp only [hpn,ite_true]
    split_ifs with hk hk2
    · field_simp; nlinarith [mul_pos hpr hp1]
    · positivity
    · omega
    · norm_num
  · simp only [hpn,ite_false,zero_div,ite_self,add_zero]
    split_ifs
    · field_simp; nlinarith [mul_le_mul_of_nonneg_right hsq hpr.le]
    · norm_num

def universal : ℝ := Real.exp (6*∑' j : ℕ, ((j:ℝ)^(3/2:ℝ))⁻¹)

theorem uniformDivisors (n M : ℕ) (hM : 0<M) :
    (∑ d ∈ M.divisors, w n d) ≤ universal := by
  let A : ArithmeticFunction ℝ := w n * (ζ : ArithmeticFunction ℝ)
  have hA : IsMultiplicative A := (w_mult n).mul isMultiplicative_zeta.natCast
  have he (m : ℕ) : A m = ∑ d ∈ m.divisors,w n d := coe_mul_zeta_apply
  have hprod := hA.multiplicative_factorization A hM.ne'
  rw [he] at hprod
  rw [hprod,Finsupp.prod]
  calc
    _ ≤ ∏ p ∈ M.factorization.support, Real.exp (6/((p:ℝ)^(3/2:ℝ))) := by
      refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
      · rw [he]; exact sum_nonneg fun d _ => w_nonneg n d
      · rw [he]
        have hh : p ∈ M.primeFactors := M.support_factorization ▸ hp
        exact (wLocal p n _ (Nat.prime_of_mem_primeFactors hh)).trans (by linarith [Real.add_one_le_exp (6/((p:ℝ)^(3/2:ℝ)))])
    _ ≤ universal := by
      rw [←Real.exp_sum,universal]
      apply Real.exp_le_exp.mpr
      simp_rw [div_eq_mul_inv,←mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤6)
      exact (Real.summable_nat_rpow_inv.mpr (by norm_num : (1:ℝ)<3/2)).sum_le_tsum _ (by intro _ _; positivity)

theorem signedDivisors (n M : ℕ) (hM : 0<M) :
    0 ≤ ∑ d ∈ M.divisors, z n d := by
  let A : ArithmeticFunction ℝ := z n * (ζ : ArithmeticFunction ℝ)
  have hA : IsMultiplicative A := (z_mult n).mul isMultiplicative_zeta.natCast
  have he (m : ℕ) : A m = ∑ d ∈ m.divisors,z n d := coe_mul_zeta_apply
  have hh := hA.multiplicative_factorization A hM.ne'
  rw [he] at hh
  rw [hh,Finsupp.prod]
  apply Finset.prod_nonneg
  intro p hp
  rw [he]
  exact zLocal p n _ (Nat.prime_of_mem_primeFactors (M.support_factorization ▸ hp))

theorem prefixDiv (J : ℕ) : Icc 1 J ⊆ J.factorial.divisors := by
  intro d hd
  obtain ⟨hd1, hdJ⟩ := mem_Icc.mp hd
  exact Nat.mem_divisors.mpr ⟨Nat.dvd_factorial hd1 hdJ,J.factorial_pos.ne'⟩

theorem uniformPrefix (n J : ℕ) : (∑ d ∈ Icc 1 J, w n d)≤universal :=
  (sum_le_sum_of_subset_of_nonneg (prefixDiv J) (fun d _ _ => w_nonneg n d)).trans
    (uniformDivisors n _ J.factorial_pos)

theorem tailTerm (n J d : ℕ) (hJ : 0<J) (hJd : J≤d) :
    |z n d| ≤ w n d / ((J:ℝ)^(1/4:ℝ)) := by
  have hd : 0<(d:ℝ) := by exact_mod_cast hJ.trans_le hJd
  have hJr : 0<(J:ℝ) := by exact_mod_cast hJ
  have he : (d:ℝ)^(3/4:ℝ)*(d:ℝ)^(1/4:ℝ)=d := by
    rw [←Real.rpow_add hd,show (3/4:ℝ)+1/4=1 by norm_num,Real.rpow_one]
  change |h n d / (d:ℝ)| ≤ |h n d| / _ / _
  rw [abs_div,abs_of_pos hd,div_div]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos (Real.rpow_pos_of_pos hd _) (Real.rpow_pos_of_pos hJr _))
  apply le_trans _ he.le
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hJd) (by norm_num)) (by positivity)

theorem uniformTail (n J : ℕ) (s : Finset ℕ) (hJ : 0<J) (hs : ∀ d ∈ s,J≤d) :
    (∑ d ∈ s, |z n d|) ≤ universal / (J:ℝ)^(1/4:ℝ) := by
  have hb : s⊆Icc 1 (s.sup id) := by
    intro d hd
    exact mem_Icc.mpr ⟨by have := hs d hd; omega, le_sup (f:=id) hd⟩
  calc
    _ ≤ ∑ d ∈ s, w n d / (J:ℝ)^(1/4:ℝ) := sum_le_sum fun d hd => tailTerm n J d hJ (hs d hd)
    _ = _ := (sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right ((sum_le_sum_of_subset_of_nonneg hb (fun d _ _ => w_nonneg n d)).trans (uniformPrefix n _)) (by positivity)

theorem signedPrefix (n J : ℕ) (hJ : 0<J) :
    -(universal / (J:ℝ)^(1/4:ℝ)) ≤ ∑ d ∈ Icc 1 J, z n d := by
  have hu := uniformTail n J (J.factorial.divisors \ Icc 1 J) hJ (by
    intro d hd
    obtain ⟨hd,hd'⟩ := mem_sdiff.mp hd
    have hpos := Nat.pos_of_mem_divisors hd
    simp only [mem_Icc,not_and] at hd'
    omega)
  have hh := signedDivisors n J.factorial J.factorial_pos
  rw [←sum_sdiff (s₁:=Icc 1 J) (s₂:=J.factorial.divisors) (prefixDiv J)] at hh
  have ht := sum_le_sum (s:=J.factorial.divisors \ Icc 1 J) (fun d _ => le_abs_self (z n d))
  linarith

end
end BandTail

end

section

namespace BandTail
open Finset ArithmeticFunction
noncomputable section

def gSum (n X : ℕ) : ℝ := ∑ k ∈ Icc 1 X, g n k
def gAvg (n X : ℕ) : ℝ := gSum n X / X
def fSum (n X : ℕ) : ℝ := ∑ k ∈ Icc 1 X, F n k

theorem g_sum_bounds (n X : ℕ) : 0≤gSum n X ∧ gSum n X≤X := by
  constructor
  · apply sum_nonneg
    intro k hk
    simp [g]; split_ifs <;> norm_num
  · calc
      _ ≤ ∑ k ∈ Icc 1 X,(1:ℝ) := by
        apply sum_le_sum
        intro k hk
        simp [g]; split_ifs <;> norm_num
      _ = _ := by simp

theorem g_avg_bounds (n X : ℕ) : 0≤gAvg n X ∧ gAvg n X≤1 := by
  have hb := g_sum_bounds n X
  exact ⟨div_nonneg hb.1 (Nat.cast_nonneg _),div_le_one_of_le₀ hb.2 (Nat.cast_nonneg _)⟩

theorem fSum_convolution (n X : ℕ) :
    fSum n X = ∑ d ∈ Icc 1 X,h n d * gSum n (X/d) := by
  classical
  let S := Icc 1 X
  let f := fun v : ℕ × ℕ => h n v.1 * g n v.2
  have hf (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal = (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    obtain ⟨hq0,hqQ⟩ := mem_Icc.mp hq
    ext ab
    constructor
    · intro hab
      have hm (a : ℕ) (ha : a ∈ q.divisors) : a ∈ S :=
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,(Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors ha)).trans hqQ⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ (Nat.fst_mem_divisors_of_mem_antidiagonal hab),
        hm _ (Nat.snd_mem_divisors_of_mem_antidiagonal hab)⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
    · intro hh; exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hh).2,by omega⟩
  calc
    _ = ∑ q ∈ S,∑ v ∈ q.divisorsAntidiagonal,f v := by
      simp [fSum,S,convolution n,mul_comm (g n) (h n),ArithmeticFunction.mul_apply,f]
    _ = ∑ q ∈ S, ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), f v :=
      sum_congr rfl (fun q hq => by rw [hf q hq])
    _ = ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), f v :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ = _ := by
      rw [sum_filter,sum_product]
      apply sum_congr rfl
      intro d hd
      have hd0 := (mem_Icc.mp hd).1
      have hkd : (S.filter fun k => d*k∈S)=Icc 1 (X/d) := by
        ext k
        simp only [S,mem_filter,mem_Icc]
        constructor
        · rintro ⟨⟨hk,_⟩,_,hdk⟩
          exact ⟨hk,(Nat.le_div_iff_mul_le hd0).mpr (by simpa [mul_comm] using hdk)⟩
        · rintro ⟨hk,hkx⟩
          exact ⟨⟨hk,hkx.trans (Nat.div_le_self _ _)⟩,Nat.mul_pos hd0 hk, by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd0).mp hkx⟩
      simp only [f,gSum,mul_sum]
      rw [←sum_filter,hkd]

theorem prefix_split (f : ℕ→ℝ) {J X : ℕ} (hJX : J≤X) :
    (∑ d ∈ Icc 1 X,f d)=(∑ d ∈ Icc 1 J,f d)+(∑ d ∈ Ioc J X,f d) := by
  have he : Icc 1 X=Icc 1 J ∪ Ioc J X := by ext k; simp only [mem_union,mem_Icc,mem_Ioc]; omega
  rw [he,sum_union (by rw [Finset.disjoint_left]; intro k hk hj; have := (mem_Icc.mp hk).2; have := (mem_Ioc.mp hj).1; omega)]

def scaleFactor (X d : ℕ) : ℝ := (d:ℝ)*(X/d:ℕ)/X

theorem scale_bounds (X d : ℕ) (hX : 0<X) (hd : 0<d) :
    0≤ scaleFactor X d ∧ scaleFactor X d ≤ 1 ∧ 1-scaleFactor X d ≤ (d:ℝ)/X := by
  have hx : 0<(X:ℝ) := by exact_mod_cast hX
  have hx0 : (d:ℝ)*(X/d:ℕ) ≤ X := by exact_mod_cast Nat.mul_div_le X d
  have hx1 : (X:ℝ) < (d:ℝ)*((X/d:ℕ)+1:ℝ) := by exact_mod_cast Nat.lt_mul_div_succ X hd
  unfold scaleFactor
  refine ⟨by positivity,(div_le_iff₀ hx).mpr (by linarith),?_⟩
  rw [sub_div' hx.ne',div_le_div_iff_of_pos_right hx]
  linarith

theorem scaled_piece (n X d : ℕ) (hd : 0<d) :
    h n d * gSum n (X/d) / X = z n d * (scaleFactor X d * gAvg n (X/d)) := by
  have hdr : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  by_cases hy : X/d=0
  · simp [gSum,gAvg,scaleFactor,hy]
  · have hyr : ((X/d:ℕ):ℝ)≠0 := by exact_mod_cast hy
    simp only [z,coe_mk,scaleFactor,gAvg]
    field_simp

theorem piece_approx (n X d : ℕ) (hX : 0<X) (hd : 0<d) (t e : ℝ)
    (he : |gAvg n (X/d)-t|≤e) (hdX : (d:ℝ)/X≤e) :
    |h n d * gSum n (X/d) / X - z n d * t| ≤ |z n d| *(2*e) := by
  obtain ⟨_,hs,hs'⟩ := scale_bounds X d hX hd
  have hg := g_avg_bounds n (X/d)
  have hc : |scaleFactor X d * gAvg n (X/d)-gAvg n (X/d)| ≤ e := by
    rw [←sub_one_mul,abs_mul,abs_of_nonpos (sub_nonpos.mpr hs),abs_of_nonneg hg.1]
    calc
      _ ≤ -(scaleFactor X d-1)*1 := mul_le_mul_of_nonneg_left hg.2 (by linarith)
      _ ≤ e := by linarith
  rw [scaled_piece n X d hd,←mul_sub,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (abs_sub_le _ (gAvg n (X/d)) _).trans (by linarith)

theorem dyadic_approx (n X J : ℕ) (hX : 0<X) (hJ : 0<J) (hJX : J≤X) (t e : ℝ) (he : 0≤e)
    (hne : ∀ d ∈ Icc 1 J,|gAvg n (X/d)-t|≤e) (hJr : (J:ℝ)/X ≤ e) :
    |fSum n X / X - (∑ d ∈ Icc 1 J,z n d)*t| ≤
      universal*(2*e)+universal/(J:ℝ)^(1/4:ℝ) := by
  let a := fun d => h n d * gSum n (X/d) / X
  have hsmall : |∑ d ∈ Icc 1 J,(a d-z n d*t)|≤universal*(2*e) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ d ∈ Icc 1 J, |z n d| *(2*e) := by
        refine sum_le_sum fun d hd => piece_approx n X d hX (mem_Icc.mp hd).1 t e (hne _ hd) ?_
        exact (div_le_div_of_nonneg_right (by exact_mod_cast (mem_Icc.mp hd).2) (Nat.cast_nonneg _)).trans hJr
      _ = _ := (sum_mul _ _ _).symm
      _ ≤ _ := by
        have hu := uniformTail n 1 (Icc 1 J) (by decide) (fun d hd => (mem_Icc.mp hd).1)
        norm_num at hu
        exact mul_le_mul_of_nonneg_right hu (by positivity)
  have hlarge : |∑ d ∈ Ioc J X,a d| ≤ universal/(J:ℝ)^(1/4:ℝ) := by
    apply (abs_sum_le_sum_abs _ _).trans
    apply le_trans _ (uniformTail n J (Ioc J X) hJ (fun d hd => (mem_Ioc.mp hd).1.le))
    apply sum_le_sum
    intro d hd
    have hd0 : 0<d := hJ.trans (mem_Ioc.mp hd).1
    obtain ⟨hs,hs',_⟩ := scale_bounds X d hX hd0
    have hg := g_avg_bounds n (X/d)
    dsimp only [a]; rw [scaled_piece n X d hd0,abs_mul,abs_of_nonneg (mul_nonneg hs hg.1)]
    exact mul_le_of_le_one_right (abs_nonneg _) (mul_le_one₀ hs' hg.1 hg.2)
  have htotal : fSum n X / X = (∑ d ∈ Icc 1 J,a d)+(∑ d ∈ Ioc J X,a d) := by
    rw [fSum_convolution,sum_div]
    exact prefix_split a hJX
  rw [htotal,sum_mul]
  rw [show (∑ d ∈ Icc 1 J,a d)+(∑ d ∈ Ioc J X,a d)-(∑ d ∈ Icc 1 J,z n d*t)=
      (∑ d ∈ Icc 1 J,(a d-z n d*t))+(∑ d ∈ Ioc J X,a d) by rw [sum_sub_distrib]; ring]
  exact (abs_add_le _ _).trans (add_le_add hsmall hlarge)

end
end BandTail

end

section

namespace GoldbachModelMean

open Finset Filter Topology

private def modProd (s : Finset Nat.Primes) : ℕ := ∏ p ∈ s, (p:ℕ)

private theorem modProd_pos (s : Finset Nat.Primes) : 0 < modProd s :=
  Finset.prod_pos (fun p _ => p.property.pos)

private theorem totientProd (s : Finset Nat.Primes) :
    ((modProd s).totient:ℝ)*(1+∑ p ∈ s, 1/(p:ℝ)) ≤ modProd s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [modProd]
  | @insert p s hps ih =>
    have hcop : (p:ℕ).Coprime (modProd s) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      apply (Nat.coprime_primes p.property q.property).mpr
      intro h
      exact hps ((Subtype.ext h : p=q) ▸ hq)
    have heq : modProd (insert p s) = (p:ℕ)*modProd s := Finset.prod_insert hps
    have hp : (1:ℕ)≤p.val := p.property.one_lt.le
    have hp' : (0:ℝ)<p := by exact_mod_cast p.property.pos
    have hsum : 0 ≤ ∑ q ∈ s, (1:ℝ)/(q:ℝ) := sum_nonneg fun q _ => by positivity
    rw [heq,Nat.totient_mul hcop,Nat.totient_prime p.property,Finset.sum_insert hps]
    push_cast [Nat.cast_sub hp]
    calc
      _ ≤ (p:ℝ)*(((modProd s).totient:ℝ)*(1+∑ q ∈ s, 1/(q:ℝ))) := by
        have : ((p:ℝ)-1)*(1+(1/(p:ℝ)+∑ q ∈ s, 1/(q:ℝ))) ≤ (p:ℝ)*(1+∑ q ∈ s, 1/(q:ℝ)) := by
          field_simp
          nlinarith [mul_nonneg hp'.le hsum]
        nlinarith only [mul_le_mul_of_nonneg_right this (Nat.cast_nonneg (modProd s).totient (α:=ℝ))]
      _ ≤ _ := mul_le_mul_of_nonneg_left ih hp'.le

theorem exists_thin_modulus (e : ℝ) (he : 0<e) :
    ∃ D : ℕ, 0<D ∧ (D.totient:ℝ)/(D:ℝ)<e := by
  classical
  have hs : ∃ s : Finset Nat.Primes, (1/e:ℝ) < ∑ p ∈ s, 1/(p:ℝ) := by
    by_contra! h
    exact Nat.Primes.not_summable_one_div (summable_of_sum_le (fun p => by positivity) h)
  obtain ⟨s,hs⟩ := hs
  refine ⟨modProd s,modProd_pos s,(div_lt_iff₀ (by exact_mod_cast modProd_pos s)).mpr ?_⟩
  have h := totientProd s
  have ht : (0:ℝ) < (modProd s).totient := by exact_mod_cast Nat.totient_pos.mpr (modProd_pos s)
  have h1 := (div_lt_iff₀ he).mp hs
  nlinarith only [mul_le_mul_of_nonneg_right h he.le,
    mul_lt_mul_of_pos_right h1 ht,mul_pos he ht]

def fewFactors (k X : ℕ) : Finset ℕ :=
  (range X).filter fun n => 0 < n ∧ n.primeFactorsList.length ≤ k

private theorem few_step (k X D : ℕ) (hD : 0<D) :
    (fewFactors (k+1) X).card ≤ D.totient*(X/D+1)+(D+1)*(fewFactors k X).card := by
  classical
  let R := (range X).filter fun n => D.Coprime n
  let cover := (range (D+1)).biUnion fun p => (fewFactors k X).image fun y => p*y
  have hsub : fewFactors (k+1) X ⊆ R ∪ cover := by
    intro x hx
    obtain ⟨hxX,hxp,hxk⟩ := mem_filter.mp hx
    by_cases hc : D.Coprime x
    · exact mem_union_left _ (mem_filter.mpr ⟨hxX,hc⟩)
    obtain ⟨p,hp,hpd,hpx⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    obtain ⟨y,rfl⟩ := hpx
    have hy : y ≠ 0 := by intro hz; simp [hz] at hxp
    have hlen := (Nat.perm_primeFactorsList_mul hp.ne_zero hy).length_eq
    simp [Nat.primeFactorsList_prime hp] at hlen
    have hyX : y < X := lt_of_le_of_lt (by simpa [Nat.mul_comm] using Nat.le_mul_of_pos_left y hp.pos) (mem_range.mp hxX)
    exact mem_union_right _ (mem_biUnion.mpr ⟨p,mem_range.mpr (by have := Nat.le_of_dvd hD hpd; omega),
      mem_image.mpr ⟨y,mem_filter.mpr ⟨mem_range.mpr hyX,by omega,by omega⟩,rfl⟩⟩)
  have hR : R.card ≤ D.totient*(X/D+1) := by
    simpa only [R,zero_add,← range_eq_Ico] using Nat.Ico_filter_coprime_le 0 X hD.ne'
  have hc : cover.card ≤ (D+1)*(fewFactors k X).card := calc
    _ ≤ ∑ p ∈ range (D+1), ((fewFactors k X).image fun y => p*y).card := card_biUnion_le
    _ ≤ ∑ _ ∈ range (D+1), (fewFactors k X).card := by exact Finset.sum_le_sum (fun p _ => card_image_le)
    _ = _ := by simp
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add hR hc))

theorem fewFactors_eventually (k : ℕ) (e : ℝ) (he : 0<e) :
    ∀ᶠ X : ℕ in atTop, ((fewFactors k X).card:ℝ) ≤ e*X := by
  induction k generalizing e with
  | zero =>
    filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (1/e)] with X hX
    have hsub : fewFactors 0 X ⊆ {1} := by
      intro x hx
      obtain ⟨_,hp,hl⟩ := mem_filter.mp hx
      have hn := (Nat.primeFactorsList_eq_nil x).mp (List.length_eq_zero_iff.mp (by omega))
      simp only [mem_singleton]
      omega
    have hc : (fewFactors 0 X).card ≤ 1 := by simpa using card_le_card hsub
    change 1/e ≤ (X:ℝ) at hX
    have hh := (div_le_iff₀ he).mp hX
    exact (by exact_mod_cast hc : ((fewFactors 0 X).card:ℝ) ≤ 1) |>.trans (by linarith)
  | succ k ih =>
    obtain ⟨D,hD,hphi⟩ := exists_thin_modulus (e/4) (by positivity)
    have hD' : (0:ℝ)<D := by exact_mod_cast hD
    filter_upwards [ih (e/(4*(D+1))) (by positivity),
      (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (4*(D.totient:ℝ)/e)] with X hprev hlarge
    change 4*(D.totient:ℝ)/e ≤ X at hlarge
    have hr := (div_le_iff₀ he).mp hlarge
    have hp := (div_lt_iff₀ hD').mp hphi
    have hquot : ((X/D:ℕ):ℝ) ≤ (X:ℝ)/D := by
      apply (le_div_iff₀ hD').mpr
      exact_mod_cast Nat.div_mul_le_self X D
    have h := few_step k X D hD
    have h' : ((fewFactors (k+1) X).card:ℝ) ≤ D.totient*(((X/D:ℕ):ℝ)+1)+((D:ℝ)+1)*(fewFactors k X).card := by exact_mod_cast h
    have hf : ((D:ℝ)+1)*((fewFactors k X).card:ℝ) ≤ (e/4)*X := by
      calc
        _ ≤ ((D:ℝ)+1)*(e/(4*(D+1))*X) := mul_le_mul_of_nonneg_left hprev (by positivity)
        _ = _ := by field_simp
    have hg : (D.totient:ℝ)*((X/D:ℕ):ℝ) ≤ (e/4)*X := calc
      _ ≤ (D.totient:ℝ)*((X:ℝ)/D) := mul_le_mul_of_nonneg_left hquot (by positivity)
      _ = ((D.totient:ℝ)/D)*X := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hphi.le (by positivity)
    nlinarith only [h',hf,hg,hr,mul_nonneg he.le (Nat.cast_nonneg X (α:=ℝ))]

end GoldbachModelMean

end

section

noncomputable section
namespace GoldbachModelMean.Brun
open Finset Filter

def product (s : Finset ℕ) := ∏ p ∈ s, p
def hits (P : Finset ℕ) (m : ℕ) := P.filter (fun p => p ∣ m)
def count (P : Finset ℕ) (X : ℕ) : ℝ := ∑ m ∈ Ioc 0 X, if (hits P m).card=0 then 1 else 0
def harmonic (P : Finset ℕ) : ℝ := ∑ p ∈ P, 1/(p:ℝ)
def divisCount (P : Finset ℕ) (j X : ℕ) : ℝ :=
  ∑ s ∈ P.powersetCard j, ((X / product s : ℕ):ℝ)
def trunc (P : Finset ℕ) (r X : ℕ) : ℝ :=
  ∑ j ∈ range (r+1), (-1:ℝ)^j*divisCount P j X

lemma prodPos (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) : 0<product s :=
  prod_pos (fun p h => (hp p h).pos)

lemma prodDvd (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) (m : ℕ) :
    product s ∣ m ↔ ∀ p ∈ s, p ∣ m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [product]
  | @insert p s hps ih =>
    have hp' := hp p (mem_insert_self _ _)
    have hs := fun q (hq : q∈s) => hp q (mem_insert_of_mem hq)
    have hc : p.Coprime (product s) := Nat.coprime_prod_right_iff.mpr (fun q hq =>
      (Nat.coprime_primes hp' (hs q hq)).mpr fun he => hps (he ▸ hq))
    rw [product,prod_insert hps,forall_mem_insert]
    change p*product s ∣ m ↔ _
    exact ⟨fun h => ⟨(dvd_mul_right p _).trans h,(ih hs).mp ((dvd_mul_left (product s) p).trans h)⟩,
      fun h => hc.mul_dvd_of_dvd_of_dvd h.1 ((ih hs).mpr h.2)⟩

lemma omegaProd (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) : (product s).primeFactorsList.length=s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [product]
  | @insert p s hps ih =>
    have hp' := hp p (mem_insert_self _ _)
    have hs := fun q (hq : q∈s) => hp q (mem_insert_of_mem hq)
    have he := (Nat.perm_primeFactorsList_mul hp'.ne_zero (prodPos s hs).ne').length_eq
    change (∏ q ∈ insert p s,q).primeFactorsList.length=_
    rw [prod_insert hps,card_insert_of_notMem hps]
    change (p*product s).primeFactorsList.length=_
    simpa [Nat.primeFactorsList_prime hp',ih hs,Nat.add_comm] using he

theorem divisAsChoose (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (j X : ℕ) :
    divisCount P j X = ∑ m ∈ Ioc 0 X, (((hits P m).card.choose j:ℕ):ℝ) := by
  classical
  have hs (m : ℕ) :
      (P.powersetCard j).filter (fun s => product s ∣ m) = (hits P m).powersetCard j := by
    ext s
    simp only [mem_filter,mem_powersetCard]
    constructor
    · rintro ⟨⟨hsub,hj⟩,hd⟩
      exact ⟨fun q hq => mem_filter.mpr ⟨hsub hq,(prodDvd s (fun p h => hp p (hsub h)) m).mp hd q hq⟩,hj⟩
    · rintro ⟨hsub,hj⟩
      have hP (q) (hq:q∈s) := (mem_filter.mp (hsub hq)).1
      exact ⟨⟨fun q hq => hP q hq,hj⟩,(prodDvd s (fun p h => hp p (hP p h)) m).mpr
        (fun q hq => (mem_filter.mp (hsub hq)).2)⟩
  unfold divisCount
  simp_rw [←Nat.Ioc_filter_dvd_card_eq_div, ←Finset.sum_boole]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro m _
  rw [Finset.sum_boole,hs,card_powersetCard]

private theorem localTrunc (k r : ℕ) :
    |(if k=0 then (1:ℝ) else 0) - ∑ j ∈ range (r+1), (-1:ℝ)^j*(k.choose j:ℕ)| ≤ k.choose r := by
  cases k with
  | zero =>
    have hy : (∑ j ∈ range (r+1), (-1:ℝ)^j*(((0:ℕ).choose j):ℕ))=1 := by
      rw [sum_eq_single 0]
      · simp
      · intro j _ hj
        have hh : (0:ℕ).choose j=0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [hh];simp
      · simp
    simp [hy]
  | succ k =>
    have hi := @Int.alternating_sum_range_choose_eq_choose k r
    have hr : (∑ j ∈ range (r+1), (-1:ℝ)^j*(((k+1).choose j):ℕ))=(-1:ℝ)^r*(k.choose r:ℕ) := by exact_mod_cast hi
    rw [if_neg (by omega),zero_sub,abs_neg,hr,abs_mul,abs_pow]
    simpa using (show ((k.choose r:ℕ):ℝ) ≤ ((k+1).choose r:ℕ) by exact_mod_cast Nat.choose_le_succ k r)

theorem truncateError (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (r X : ℕ) :
    |count P X-trunc P r X| ≤ divisCount P r X := by
  unfold count trunc
  simp_rw [divisAsChoose P hp,Finset.mul_sum]
  rw [Finset.sum_comm (s:=range (r+1)),←sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun m _ => localTrunc (hits P m).card r))

theorem reciprocalLayer (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (r : ℕ) :
    (∑ s ∈ P.powersetCard r, 1/(product s:ℝ)) ≤ Real.exp (2*harmonic P)/(2:ℝ)^r := by
  apply (le_div_iff₀ (by positivity)).mpr
  rw [Finset.sum_mul]
  calc
    _ = ∑ s ∈ P.powersetCard r, ∏ p ∈ s, (2/(p:ℝ)) := by
      apply sum_congr rfl
      intro s hs
      rw [prod_div_distrib,prod_const,(mem_powersetCard.mp hs).2]
      simp [product,div_eq_mul_inv,mul_comm]
    _ ≤ ∑ s ∈ P.powerset, ∏ p ∈ s, (2/(p:ℝ)) :=
      sum_le_sum_of_subset_of_nonneg (fun s hs => mem_powerset.mpr (mem_powersetCard.mp hs).1)
        (fun s _ _ => prod_nonneg (fun _ _ => by positivity))
    _ = ∏ p ∈ P, (1+2/(p:ℝ)) := (prod_one_add ..).symm
    _ ≤ ∏ p ∈ P, Real.exp (2/(p:ℝ)) := by
      apply Finset.prod_le_prod₀ (fun p _ => by positivity)
      intro p hp
      simpa [add_comm] using (Real.add_one_le_exp (2/(p:ℝ)))
    _ = _ := by rw [←Real.exp_sum]; congr 1;unfold harmonic;rw [mul_sum];apply sum_congr rfl;intros;ring

theorem errorEnvelope (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (r X : ℕ) :
    |count P X-trunc P r X| ≤ (X:ℝ)*Real.exp (2*harmonic P)/(2:ℝ)^r := by
  apply (truncateError P hp r X).trans
  calc
    divisCount P r X ≤ (X:ℝ)*(∑ s ∈ P.powersetCard r, 1/(product s:ℝ)) := by
      unfold divisCount
      rw [mul_sum]
      apply sum_le_sum
      intro s _
      simpa only [mul_one_div] using (Nat.cast_div_le (m:=X) (n:=product s) : ((X/product s:ℕ):ℝ)≤X/(product s:ℝ))
    _ ≤ (X:ℝ)*(Real.exp (2*harmonic P)/(2:ℝ)^r) :=
      mul_le_mul_of_nonneg_left (reciprocalLayer P hp r) (Nat.cast_nonneg _)
    _ = _ := by ring
end GoldbachModelMean.Brun

end

section

noncomputable section
namespace GoldbachModelMean.Brun
open Finset Filter

private lemma floorIneq (m d : ℕ) (hd : 0<d) :
    (m:ℝ)/d-1 ≤ ((m/d:ℕ):ℝ) ∧ ((m/d:ℕ):ℝ) ≤ m/(d:ℝ) := by
  refine ⟨?_,Nat.cast_div_le⟩
  have h : (m:ℝ) < d * (((m/d:ℕ):ℝ)+1) := by exact_mod_cast Nat.lt_mul_div_succ m hd
  have hh : (m:ℝ)/d < ((m/d:ℕ):ℝ)+1 := (div_lt_iff₀ (by exact_mod_cast hd)).mpr (by linarith)
  linarith

private lemma floorDiff (X Y d : ℕ) (hd : 0<d) (hY : 0<Y) :
    |((X/d:ℕ):ℝ)-(X:ℝ)/Y*((Y/d:ℕ):ℝ)| ≤ 1+(X:ℝ)/Y := by
  have hY' : (0:ℝ)<Y := by exact_mod_cast hY
  have hpos : 0≤(X:ℝ)/Y := by positivity
  obtain ⟨a,b⟩ := floorIneq X d hd
  obtain ⟨c,e⟩ := floorIneq Y d hd
  have h : (X:ℝ)/Y*(Y/(d:ℝ))=X/(d:ℝ) := by field_simp
  have h1 := mul_le_mul_of_nonneg_left c hpos
  have h2 := mul_le_mul_of_nonneg_left e hpos
  rw [h] at h2
  rw [mul_sub,h,mul_one] at h1
  rw [abs_le]
  constructor <;> linarith

private lemma layerCard (P : Finset ℕ) (hp : ∀ p∈P,p.Prime) (r j X : ℕ) (hj : j≤r) :
    ((P.powersetCard j).filter (fun s => product s ≤ X)).card ≤
      (GoldbachModelMean.fewFactors r (X+1)).card := by
  apply Finset.card_le_card_of_injOn product
  · intro s hs
    obtain ⟨hP,hX⟩ := mem_filter.mp hs
    obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hP
    have hPrime (q) (hq:q∈s) := hp q (hsub hq)
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),prodPos s hPrime,(omegaProd s hPrime).trans_le (hcard.trans_le hj)⟩
  · intro s hs t ht e
    have h1 := (mem_powersetCard.mp (mem_filter.mp hs).1).1
    have h2 := (mem_powersetCard.mp (mem_filter.mp ht).1).1
    have hs' : (product s).primeFactors=s := Nat.primeFactors_prod (fun q hq => hp q (h1 hq))
    have ht' : (product t).primeFactors=t := Nat.primeFactors_prod (fun q hq => hp q (h2 hq))
    rw [←hs',e,ht']

private lemma layerDiff (P : Finset ℕ) (hp : ∀ p∈P,p.Prime) (r j X Y : ℕ)
    (hj : j≤r) (hY : 0<Y) (hYX : Y≤X) :
    |divisCount P j X-(X:ℝ)/Y*divisCount P j Y| ≤
      ((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) := by
  classical
  unfold divisCount
  rw [mul_sum,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ s ∈ P.powersetCard j, if product s≤X then 1+(X:ℝ)/Y else 0 := by
      apply sum_le_sum
      intro s hs
      split_ifs with h
      · exact floorDiff X Y (product s) (prodPos s (fun q hq => hp q ((mem_powersetCard.mp hs).1 hq))) hY
      · have hx : X<product s := by omega
        simp [Nat.div_eq_of_lt hx,Nat.div_eq_of_lt (hYX.trans_lt hx)]
    _ = (((P.powersetCard j).filter (fun s => product s ≤ X)).card:ℝ)*(1+(X:ℝ)/Y) := by
      rw [←sum_filter];simp;ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast layerCard P hp r j X hj) (by positivity)

theorem truncDiff (P : Finset ℕ) (hp : ∀ p∈P,p.Prime) (r X Y : ℕ)
    (hY : 0<Y) (hYX : Y≤X) :
    |trunc P r X-(X:ℝ)/Y*trunc P r Y| ≤
      ((r:ℝ)+1)*((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) := by
  unfold trunc
  rw [mul_sum,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j ∈ range (r+1), ((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) := by
      apply sum_le_sum
      intro j hj
      have hh := layerDiff P hp r j X Y (by have := mem_range.mp hj;omega) hY hYX
      rw [show (X:ℝ)/Y*((-1:ℝ)^j*divisCount P j Y)=(-1:ℝ)^j*((X:ℝ)/Y*divisCount P j Y) by ring,
        ←mul_sub,abs_mul,abs_pow]
      simpa using hh
    _ = _ := by simp [mul_assoc]

end GoldbachModelMean.Brun

end

section

noncomputable section
namespace GoldbachModelMean.Brun
open Finset Filter

theorem uniform_lowH (H C e : ℝ) (hC : 1≤C) (he : 0<e) :
    ∀ᶠ X : ℕ in atTop, ∀ Y : ℕ, 0<Y → Y≤X → (X:ℝ)≤C*Y →
    ∀ P : Finset ℕ, (∀ p∈P,p.Prime) → harmonic P≤H →
    |count P X/X - count P Y/Y| ≤ e := by
  obtain ⟨r,hr⟩ := pow_unbounded_of_one_lt (4*Real.exp (2*H)/e) (show (1:ℝ)<2 by norm_num)
  let A : ℝ := ((r:ℝ)+1)*(1+C)
  have hA : 0<A := by dsimp [A];positivity
  have heps : 0<e/(4*A) := by positivity
  obtain ⟨x₀,hx⟩ := eventually_atTop.mp (GoldbachModelMean.fewFactors_eventually r (e/(4*A)) heps)
  filter_upwards [eventually_ge_atTop x₀,eventually_ge_atTop 1] with X hX hX1
  intro Y hY hYX hscale P hp hH
  have hY' : (0:ℝ)<Y := by exact_mod_cast hY
  have hX' : (0:ℝ)<X := by exact_mod_cast hX1
  have hx1 : (1:ℝ)≤X := by exact_mod_cast hX1
  have hRatio : (X:ℝ)/Y≤C := (div_le_iff₀ hY').mpr hscale
  have hR : 0≤(X:ℝ)/Y := by positivity
  have hExp := Real.exp_le_exp.mpr (show 2*harmonic P≤2*H by linarith)
  have hcoeff : Real.exp (2*harmonic P)/(2:ℝ)^r ≤ e/4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have := (div_lt_iff₀ he).mp hr
    nlinarith
  have err (W : ℕ) : |count P W-trunc P r W| ≤ (W:ℝ)*(e/4) := by
    refine (errorEnvelope P hp r W).trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg _)
  have hf := hx (X+1) (by omega)
  push_cast at hf
  have hL : ((r:ℝ)+1)*((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) ≤ (X:ℝ)*(e/2) := by
    calc
      _ ≤ ((r:ℝ)+1)*((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+C) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = A*((GoldbachModelMean.fewFactors r (X+1)).card:ℝ) := by dsimp [A];ring
      _ ≤ A*(e/(4*A)*((X:ℝ)+1)) := mul_le_mul_of_nonneg_left hf hA.le
      _ = e/4*((X:ℝ)+1) := by field_simp
      _ ≤ _ := by nlinarith [mul_nonneg he.le (sub_nonneg.mpr hx1)]
  have ht := (truncDiff P hp r X Y hY hYX).trans hL
  have hE : |(X:ℝ)/Y*trunc P r Y-(X:ℝ)/Y*count P Y| ≤ (X:ℝ)*(e/4) := by
    rw [←mul_sub,abs_mul,abs_of_nonneg hR,abs_sub_comm]
    calc
      _ ≤ ((X:ℝ)/Y)*(Y*(e/4)) := mul_le_mul_of_nonneg_left (err _) hR
      _ = _ := by field_simp
  have hT := abs_sub_le (count P X) (trunc P r X) ((X:ℝ)/Y*count P Y)
  have hU := abs_sub_le (trunc P r X) ((X:ℝ)/Y*trunc P r Y) ((X:ℝ)/Y*count P Y)
  have hab : |count P X-(X:ℝ)/Y*count P Y|≤e*X := by linarith [err X]
  rw [show count P X/(X:ℝ)-count P Y/Y=(count P X-(X:ℝ)/Y*count P Y)/X by field_simp,
    abs_div,abs_of_pos hX']
  exact (div_le_iff₀ hX').mpr hab

end GoldbachModelMean.Brun

end

section

noncomputable section
namespace BandTail
open Finset Filter GoldbachModelMean.Brun

def exceptionalPrimes (n X : ℕ) : Finset ℕ := (Icc 1 X).filter (fun p => p.Prime ∧ ¬p∣n)
def meanG (n X : ℕ) : ℝ := (∑ k ∈ Icc 1 X,g n k)/X

theorem count_eq_g (n X T : ℕ) (hT : T≤X) :
    count (exceptionalPrimes n X) T = ∑ k ∈ Icc 1 T,g n k := by
  unfold count
  have hset : Ioc 0 T=Icc 1 T := by ext k;simp;omega
  rw [hset]
  apply sum_congr rfl
  intro k hk
  obtain ⟨hk1,hkT⟩ := mem_Icc.mp hk
  have h0 : k≠0 := by omega
  have he : (hits (exceptionalPrimes n X) k).card=0 ↔ smooth n k := by
    rw [Finset.card_eq_zero]
    constructor
    · intro h p hp
      by_contra hn
      obtain ⟨hp',hpk,_⟩ := Nat.mem_primeFactors.mp hp
      have hpX := (Nat.le_of_dvd (by omega : 0<k) hpk).trans (hkT.trans hT)
      have hmem : p ∈ hits (exceptionalPrimes n X) k := mem_filter.mpr
        ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hp'.one_lt.le,hpX⟩,hp',hn⟩,hpk⟩
      simp [h] at hmem
    · intro hs
      apply eq_empty_iff_forall_notMem.mpr
      intro p hpm
      obtain ⟨hP,hpk⟩ := mem_filter.mp hpm
      obtain ⟨_,hp,hn⟩ := mem_filter.mp hP
      exact hn (hs p (Nat.mem_primeFactors.mpr ⟨hp,hpk,h0⟩))
  simp [g,h0,he]

theorem meanG_nonneg (n X : ℕ) : 0≤ meanG n X := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply sum_nonneg
  intro k _
  simp only [g,ArithmeticFunction.coe_mk];split_ifs <;> norm_num

theorem meanG_le_one (n X : ℕ) : meanG n X≤1 := by
  rcases eq_or_ne X 0 with rfl|hx
  · simp [meanG]
  · apply (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hx)).mpr
    calc
      _ ≤ ∑ k ∈ Icc 1 X, (1:ℝ) := by
        apply sum_le_sum
        intro k _
        simp only [g,ArithmeticFunction.coe_mk];split_ifs <;> norm_num
      _ = _ := by simp

end BandTail

end

section

namespace BandTail
open Finset
noncomputable section

def frequency (P : Finset ℕ) : ℝ := ∑ p ∈ P, (p:ℝ)⁻¹
def hit (p k : ℕ) : ℝ := if p ∣ k then 1 else 0
def hitCount (P : Finset ℕ) (k : ℕ) : ℝ := ∑ p ∈ P, hit p k

theorem hit_sum (p X : ℕ) : (∑ k ∈ Icc 1 X, hit p k) = (X/p : ℕ) := by
  have he : Icc 1 X=Ioc 0 X := by ext k; simp only [mem_Icc,mem_Ioc]; omega
  unfold hit
  rw [he,Finset.sum_boole,Nat.Ioc_filter_dvd_card_eq_div]

theorem firstMoment (P : Finset ℕ) (X : ℕ) (hP : ∀ p ∈ P, 0<p) :
    (X:ℝ)*frequency P-P.card ≤ ∑ k ∈ Icc 1 X,hitCount P k := by
  simp only [hitCount,Finset.sum_comm (s:=Icc 1 X) (t:=P),hit_sum]
  calc
    _ = ∑ p ∈ P, ((X:ℝ)*(p:ℝ)⁻¹-1) := by simp [frequency,mul_sum,sum_sub_distrib]
    _ ≤ _ := by
      apply sum_le_sum
      intro p hp
      have hpr : 0<(p:ℝ) := by exact_mod_cast hP p hp
      have hc : (X:ℝ) < (p:ℝ)*((X/p:ℕ)+1:ℝ) := by exact_mod_cast Nat.lt_mul_div_succ X (hP p hp)
      have hh : (X:ℝ)/(p:ℝ) ≤ ((X/p:ℕ):ℝ)+1 := (div_le_iff₀ hpr).mpr (by linarith)
      linarith [show (X:ℝ)*(p:ℝ)⁻¹ = X/p by rw [div_eq_mul_inv]]

theorem hitPair (X p r : ℕ) (hp : p.Prime) (hr : r.Prime) :
    (∑ k ∈ Icc 1 X,hit p k * hit r k) ≤
      (X:ℝ)*((p:ℝ)⁻¹*(r:ℝ)⁻¹) + (if p=r then (X:ℝ)*(p:ℝ)⁻¹ else 0) := by
  by_cases he : p=r
  · subst r
    have hh (k : ℕ) : hit p k*hit p k=hit p k := by by_cases hk : p∣k <;> simp [hit,hk]
    simp only [hh,hit_sum,ite_true]
    exact (Nat.cast_div_le (α:=ℝ)).trans (by rw [div_eq_mul_inv]; exact le_add_of_nonneg_left (by positivity))
  · have hh (k : ℕ) : hit p k*hit r k=hit (p*r) k := by
      have hc := (Nat.coprime_primes hp hr).mpr he
      have eqv : p*r∣k ↔ p∣k ∧ r∣k := ⟨fun hk => ⟨(dvd_mul_right p r).trans hk,(dvd_mul_left r p).trans hk⟩,fun hk => hc.mul_dvd_of_dvd_of_dvd hk.1 hk.2⟩
      by_cases ha : p∣k <;> by_cases hb : r∣k <;> simp [hit,eqv,ha,hb]
    simp only [hh,hit_sum,if_neg he,add_zero]
    exact (Nat.cast_div_le (α:=ℝ)).trans_eq (by simp [div_eq_mul_inv,mul_comm])

theorem secondMoment (P : Finset ℕ) (X : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ k ∈ Icc 1 X,(hitCount P k)^2) ≤ (X:ℝ)*(frequency P)^2+X*frequency P := by
  have hswap (f : ℕ → ℕ → ℕ → ℝ) :
      (∑ k ∈ Icc 1 X,∑ p ∈ P,∑ r ∈ P,f k p r)=∑ p ∈ P,∑ r ∈ P,∑ k ∈ Icc 1 X,f k p r := by
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_comm
  simp only [hitCount,sq,sum_mul_sum,hswap]
  calc
    _ ≤ ∑ p ∈ P,∑ r ∈ P, ((X:ℝ)*((p:ℝ)⁻¹*(r:ℝ)⁻¹)+(if p=r then (X:ℝ)*(p:ℝ)⁻¹ else 0)) :=
      sum_le_sum fun p hp => sum_le_sum fun r hr => hitPair X p r (hP p hp) (hP r hr)
    _ = _ := by
      simp only [sum_add_distrib,←mul_sum,sum_ite_eq]
      unfold frequency
      congr 1
      · rw [←Finset.sum_mul]
      · rw [mul_sum]
        exact sum_congr rfl fun p hp => by simp [hp]

theorem highH (n X : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ ¬p∣n) :
    frequency P * (∑ k ∈ Icc 1 X, g n k) ≤ (X:ℝ) + 2*P.card := by
  let H := frequency P
  have hH : 0≤H := sum_nonneg fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p)
  rcases hH.eq_or_lt with hz | hpos
  · change H*_ ≤ _
    rw [←hz,zero_mul]; positivity
  have h1 := firstMoment P X (fun p hp => (hP p hp).1.pos)
  have h2 := secondMoment P X (fun p hp => (hP p hp).1)
  have hdom : (∑ k ∈ Icc 1 X, g n k * H^2) ≤ ∑ k ∈ Icc 1 X, (hitCount P k-H)^2 := by
    apply sum_le_sum
    intro k hk
    have hk0 : k≠0 := by have := (mem_Icc.mp hk).1; omega
    by_cases hsm : smooth n k
    · have h0 : hitCount P k=0 := by
        apply sum_eq_zero
        intro p hp
        have hn := (hP p hp).2
        have hpk : ¬p∣k := fun hpk => hn (hsm p (Nat.mem_primeFactors.mpr ⟨(hP p hp).1,hpk,hk0⟩))
        simp [hit,hpk]
      simp [g,hk0,hsm,h0]
    · simp [g,hk0,hsm,sq_nonneg]
  have he (k : ℕ) : (hitCount P k-H)^2=(hitCount P k)^2 - hitCount P k*(2*H)+ H^2 := by ring
  simp only [he,sum_add_distrib,sum_sub_distrib,←sum_mul,sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel] at hdom
  change (X:ℝ)*H-_≤_ at h1
  change _≤(X:ℝ)*H^2+X*H at h2
  have h3 := mul_le_mul_of_nonneg_right h1 (mul_nonneg (by norm_num : (0:ℝ)≤2) hpos.le)
  apply le_of_mul_le_mul_right (a:=H) _ hpos
  nlinarith only [hdom,h3,h2]
end
end BandTail

end

section

noncomputable section
namespace BandTail
open Finset Filter GoldbachModelMean.Brun

theorem mean_slow (C e : ℝ) (hC : 1≤C) (he : 0<e) :
    ∀ᶠ X : ℕ in atTop, ∀ Y : ℕ, 0<Y → Y≤X → (X:ℝ)≤C*Y →
    ∀ n, |meanG n X-meanG n Y|≤e := by
  let H : ℝ := (1+2*C)/e
  have hHpos : 0<H := by dsimp [H];positivity
  filter_upwards [uniform_lowH H C e hC he] with X hlow
  intro Y hY hYX hscale n
  let P := exceptionalPrimes n X
  have hprime (p) (hp : p∈P) : p.Prime ∧ ¬p∣n := (mem_filter.mp hp).2
  have hh : harmonic P=frequency P := by simp [GoldbachModelMean.Brun.harmonic,frequency,one_div]
  by_cases hc : harmonic P≤H
  · have hh := hlow Y hY hYX hscale P (fun p h => (hprime p h).1) hc
    rwa [count_eq_g n X X le_rfl,count_eq_g n X Y hYX] at hh
  · have hPH := lt_of_not_ge hc
    rw [hh] at hPH
    have hPcard : P.card≤X := (card_filter_le ..).trans_eq (by simp)
    have hX' : (0:ℝ)<X := by exact_mod_cast hY.trans_le hYX
    have hyp : (0:ℝ)<Y := by exact_mod_cast hY
    have hscaleX : (X:ℝ)≤C*X := by simpa using (mul_le_mul_of_nonneg_right hC hX'.le)
    have hb (T : ℕ) (ht : (0:ℝ)<T) (hscaleT : (X:ℝ)≤C*T) : meanG n T≤e := by
      have hcard' : (P.card:ℝ) ≤ C*T := (show (P.card:ℝ)≤X by exact_mod_cast hPcard).trans hscaleT
      have hbound := highH n T P hprime
      have hp : 0≤∑ k ∈ Icc 1 T,g n k := by
        have hh := meanG_nonneg n T
        unfold meanG at hh
        simpa [ht.ne'] using mul_nonneg hh ht.le
      have hlo := mul_le_mul_of_nonneg_right hPH.le hp
      have hHS : H*(∑ k ∈ Icc 1 T,g n k) ≤ (1+2*C)*T := by linarith
      have hid : (1+2*C)*T=H*(e*T) := by dsimp [H];field_simp
      rw [hid] at hHS
      exact (div_le_iff₀ ht).mpr ((mul_le_mul_iff_right₀ hHpos).mp hHS)
    have hx := hb X hX' hscaleX
    have hy := hb Y hyp hscale
    rw [abs_le]
    constructor <;> linarith [meanG_nonneg n X, meanG_nonneg n Y]

end BandTail

end

section

namespace BandTail
open Finset Filter
noncomputable section

theorem uniform_prefix_floor (R : ℕ) (hR : 1 ≤ R) (δ : ℝ) (hδ : 0<δ) :
    ∃ A₀ : ℕ, ∀ A ≥ A₀, ∀ n i : ℕ, A ≤ i → i ≤ R*A →
      -(δ*(A:ℝ))  ≤  ∑ q ∈ Finset.Ioc A i,F n q := by
  have hr : (1:ℝ) ≤ R := by exact_mod_cast hR
  have hu : 0<universal := Real.exp_pos _
  let τ : ℝ := δ/(8*((R:ℝ)+1))
  have hτ : 0<τ := by dsimp [τ]; positivity
  let e : ℝ := τ/(universal+1)
  have he : 0<e := by dsimp [e]; positivity
  have heu : universal*e  ≤  τ := by
    have heq : e*(universal+1)=τ := by dsimp [e]; field_simp
    nlinarith
  obtain ⟨N,hN⟩ := exists_nat_ge (universal/τ)
  let J := (N+1)^4
  have hJ : 0<J := by dsimp [J]; positivity
  have hj : (J:ℝ)^(1/4:ℝ)=(N:ℝ)+1 := by
    dsimp [J]; push_cast
    rw [←Real.rpow_natCast_mul (by positivity),show (↑(4:ℕ):ℝ)*(1/4)=1 by norm_num,Real.rpow_one]
  have ht : universal/(J:ℝ)^(1/4:ℝ)  ≤  τ := by
    rw [hj]
    apply (div_le_iff₀ (by positivity)).mpr
    have := (div_le_iff₀ hτ).mp hN
    nlinarith
  let C : ℝ := 2*(R:ℝ)*J
  have hjr : (1:ℝ) ≤ J := by exact_mod_cast hJ
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [mul_le_mul hr hjr (by norm_num) (by positivity)]
  obtain ⟨M,hM⟩ := eventually_atTop.mp (mean_slow C e hC he)
  obtain ⟨L,hL⟩ := exists_nat_ge ((J:ℝ)/e)
  refine ⟨max J (max M L),?_⟩
  intro A hA n i hAi hiA
  have hJA : J ≤ A := by omega
  have hA0 : 0<A := hJ.trans_le hJA
  have hAr : (0:ℝ)<A := by exact_mod_cast hA0
  have hi0 : 0 < i := hA0.trans_le hAi
  have hir : (0:ℝ) < i := by exact_mod_cast hi0
  have hscale : (i:ℝ) ≤ R*(A:ℝ) := by exact_mod_cast hiA
  let t := gAvg n i
  let Z := ∑ d ∈ Icc 1 J,z n d
  have ht01 : 0 ≤ t ∧ t ≤ 1 := g_avg_bounds n i
  have hz : -τ ≤ Z := by have hz' := signedPrefix n J hJ; dsimp [Z]; linarith
  have hlin (X : ℕ) (hAX : A ≤ X) (hXi : X ≤ i) :
      |fSum n X-(X:ℝ)*(Z*t)|  ≤  X*(3*τ) := by
    have hX : 0<X := hA0.trans_le hAX
    have hxr : (0:ℝ)<X := by exact_mod_cast hX
    have hjx : (J:ℝ)/X ≤ e := by
      apply (div_le_iff₀ hxr).mpr
      have hLX : (L:ℝ) ≤ X := by exact_mod_cast (show L ≤ X by omega)
      have := (div_le_iff₀ he).mp (hL.trans hLX)
      linarith
    have hnear (d : ℕ) (hd : d∈Icc 1 J) : |gAvg n (X/d)-t| ≤ e := by
      obtain ⟨hd0,hdJ⟩ := mem_Icc.mp hd
      have hdX : d ≤ X := by omega
      have hy : 0<X/d := Nat.div_pos hdX hd0
      have hii : i ≤ R*X := hiA.trans (Nat.mul_le_mul_left R hAX)
      have hratio : X ≤ (2*J)*(X/d) := by
        calc
          X  ≤  d*(X/d+1) := (Nat.lt_mul_div_succ X hd0).le
          _  ≤  J*(2*(X/d)) := Nat.mul_le_mul hdJ (by omega)
          _ = _ := by ring
      have hcxy : (i:ℝ) ≤ C*(X/d:ℕ) := by
        dsimp [C]
        exact_mod_cast (show i ≤ 2*R*J*(X/d) from hii.trans (by calc
          R*X  ≤  R*((2*J)*(X/d)) := Nat.mul_le_mul_left R hratio
          _ = _ := by ring))
      rw [abs_sub_comm]
      exact hM i (by omega) (X/d) hy ((Nat.div_le_self X d).trans hXi) hcxy n
    have h := dyadic_approx n X J hX hJ (by omega) t e he.le hnear hjx
    have ha : |fSum n X / X - Z*t| ≤ 3*τ := h.trans (by linarith)
    have eqv : fSum n X-(X:ℝ)*(Z*t)=(X:ℝ)*(fSum n X/X-Z*t) := by field_simp
    rw [eqv,abs_mul,abs_of_pos hxr]
    exact mul_le_mul_of_nonneg_left ha hxr.le
  have ha := abs_le.mp (hlin A le_rfl hAi)
  have hb := abs_le.mp (hlin i hAi le_rfl)
  have htZ : -τ  ≤  Z*t := by
    calc
      -τ  ≤  -τ*t := by nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr ht01.2)]
      _  ≤  _ := mul_le_mul_of_nonneg_right hz ht01.1
  have hia : (A:ℝ) ≤ i := by exact_mod_cast hAi
  have hdiff := mul_le_mul_of_nonneg_left htZ (sub_nonneg.mpr hia)
  have heqτ : (8*((R:ℝ)+1))*τ=δ := by dsimp [τ]; field_simp
  have htot : (i:ℝ)*τ  ≤  R*A*τ := mul_le_mul_of_nonneg_right hscale hτ.le
  have hgood : -(δ*(A:ℝ)) ≤ fSum n i-fSum n A := by
    have δeq : δ*(A:ℝ)=(8*((R:ℝ)+1))*τ*A := by rw [heqτ]
    nlinarith only [ha.1,ha.2,hb.1,hb.2,hdiff,htot,δeq,
      mul_nonneg (Nat.cast_nonneg R) (mul_nonneg hAr.le hτ.le),mul_nonneg hAr.le hτ.le]
  have hsplit := prefix_split (fun q => F n q) hAi
  change fSum n i=fSum n A+_ at hsplit
  linarith

end
end BandTail

end

end
end
end
end
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

end GoldbachGRHRamanujanMobius

section GoldbachGRHKernel

open MeasureTheory Set Finset
open scoped Interval

namespace GoldbachGRHKernel

open GoldbachFourthMoment (phase phase_add)

noncomputable def kernel (n : ℕ) : ℝ → ℂ :=
  GoldbachWindow.poly (n + 1) fun _ => 1

noncomputable def mass (n : ℕ) (r : ℝ) : ℝ :=
  ∫ t in (-r)..r, ‖kernel n t‖ ^ 2

theorem kernel_eq_sum (n : ℕ) (t : ℝ) :
    kernel n t = ∑ k ∈ range (n + 1), phase ((k : ℝ) * t) := by
  simp [kernel, GoldbachWindow.poly]

theorem phase_nat (k : ℕ) : phase (k : ℝ) = 1 := by
  unfold phase
  have h : (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) =
      (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h]
  exact_mod_cast Complex.exp_int_mul_two_pi_mul_I (k : ℤ)

theorem kernel_periodic (n : ℕ) : Function.Periodic (kernel n) 1 := by
  intro t
  simp only [kernel_eq_sum, mul_add, mul_one, phase_add, phase_nat, mul_one]

theorem kernel_continuous (n : ℕ) : Continuous (kernel n) := by
  rw [show kernel n = fun t => ∑ k ∈ range (n + 1), phase ((k : ℝ) * t) from
    funext (kernel_eq_sum n)]
  unfold phase
  fun_prop

theorem reflect (n : ℕ) (t : ℝ) :
    kernel n t ^ 2 * phase (-(n : ℝ) * t) = (↑(‖kernel n t‖ ^ 2) : ℂ) := by
  simp only [kernel_eq_sum, ← Complex.normSq_eq_norm_sq]
  exact frontierMedcoreKernelReflection n t

theorem full_parseval (n : ℕ) :
    (∫ t in (0 : ℝ)..1, ‖kernel n t‖ ^ 2) = (n : ℝ) + 1 := by
  simpa [kernel] using GoldbachWindow.parseval (n + 1) (fun _ => (1 : ℂ))

theorem mass_nonneg (n : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ mass n r :=
  intervalIntegral.integral_nonneg_of_forall (by linarith) fun _ => sq_nonneg _

theorem mass_mono (n : ℕ) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    mass n r ≤ mass n s := by
  apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) hrs
  · exact Filter.Eventually.of_forall fun _ => sq_nonneg _
  · exact ((kernel_continuous n).norm.pow 2).intervalIntegrable _ _

theorem mass_loss (n : ℕ) {r : ℝ} (hr : 0 < r) (hh : r ≤ 1 / 2) :
    0 ≤ (n : ℝ) + 1 - mass n r ∧
      (n : ℝ) + 1 - mass n r ≤ 1 / (2 * r) := by
  let F : ℝ → ℝ := fun t => ‖kernel n t‖ ^ 2
  have hF : Continuous F := (kernel_continuous n).norm.pow 2
  have hp : Function.Periodic F 1 := by
    intro t
    simp only [F, kernel_periodic n t]
  have hfull : (∫ t in (-r)..(1 - r), F t) = (n : ℝ) + 1 := by
    have h := hp.intervalIntegral_add_eq (-r) 0
    rw [show -r + 1 = 1 - r by ring, zero_add] at h
    exact h.trans (full_parseval n)
  have hsplit :
      mass n r + (∫ t in r..(1 - r), F t) = (n : ℝ) + 1 := by
    have h := intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable (μ := volume) (-r) r) (hF.intervalIntegrable r (1 - r))
    exact h.trans hfull
  have htail : (n : ℝ) + 1 - mass n r = ∫ t in r..(1 - r), F t := by
    linarith only [hsplit]
  have hordered : r ≤ 1 - r := by linarith only [hh]
  have hrepr : (∫ t in (0 : ℝ)..1, (Ioc r (1 - r)).indicator F t) =
      ∫ t in r..(1 - r), F t := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le hordered,
      MeasureTheory.integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc]
    rw [inter_eq_left.mpr (Ioc_subset_Ioc hr.le (by linarith only [hr]))]
  have hcut : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Ioc r (1 - r) →
      r ≤ |(1 : ℝ) * t - (round ((1 : ℝ) * t) : ℝ)| := by
    intro t ht hz
    rw [one_mul]
    by_cases hhalf : t < 1 / 2
    · have hround : round t = 0 :=
        round_eq_zero_iff.mpr ⟨by linarith only [ht.1], hhalf⟩
      simp only [hround, Int.cast_zero, sub_zero, abs_of_nonneg ht.1]
      exact hz.1.le
    · have hround : round t = 1 := round_eq_iff.mpr (by
        change ((1 : ℤ) : ℝ) - 1 / 2 ≤ t ∧ t < ((1 : ℤ) : ℝ) + 1 / 2
        push_cast
        constructor <;> linarith only [hhalf, ht.2])
      simp only [hround, Int.cast_one, abs_of_nonpos (sub_nonpos.mpr ht.2)]
      linarith only [hz.2]
  have hbound := goldbach_geometric_tail_l2 (n + 1) 1 Nat.one_pos r hr hh
    (Ioc r (1 - r)) measurableSet_Ioc hcut
  simp only [Nat.cast_one, one_mul] at hbound
  have hboundF : (∫ t in (0 : ℝ)..1, (Ioc r (1 - r)).indicator F t) ≤ 1 / (2 * r) := by
    simpa only [F, kernel_eq_sum, phase, mul_assoc] using hbound
  rw [hrepr] at hboundF
  rw [htail]
  exact ⟨intervalIntegral.integral_nonneg_of_forall hordered (fun _ => sq_nonneg _), hboundF⟩

end GoldbachGRHKernel

end GoldbachGRHKernel

section GoldbachGRHArcs

open Finset MeasureTheory Set
open scoped Interval

namespace GoldbachGRHArcs

noncomputable abbrev cap := GoldbachFourthGeometry.wide

/-- Indices of reduced fractions in the closed unit interval. The two endpoints are both
present when the denominator is one. -/
def centers (U : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 U) ×ˢ (Finset.range (U+1))).filter
    (fun i => i.2 ≤ i.1 ∧ Nat.Coprime i.2 i.1)

theorem mem_centers {U : ℕ} {i : ℕ × ℕ} :
    i ∈ centers U ↔ 1 ≤ i.1 ∧ i.1 ≤ U ∧ i.2 ≤ i.1 ∧ Nat.Coprime i.2 i.1 := by
  simp only [centers, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨⟨h₁, h₂⟩, _⟩, h₃, h₄⟩
    exact ⟨h₁,h₂,h₃,h₄⟩
  · rintro ⟨h₁,h₂,h₃,h₄⟩
    exact ⟨⟨⟨h₁,h₂⟩, by omega⟩,h₃,h₄⟩

theorem centers_mono {Q U : ℕ} (h : Q ≤ U) : centers Q ⊆ centers U := by
  intro i hi
  obtain ⟨h₁,h₂,h₃,h₄⟩ := mem_centers.mp hi
  exact mem_centers.mpr ⟨h₁,h₂.trans h,h₃,h₄⟩

noncomputable def radius (n H q : ℕ) : ℝ := (H : ℝ) / ((q : ℝ) * (n : ℝ))

noncomputable def center (i : ℕ × ℕ) : ℝ := (i.2 : ℝ) / (i.1 : ℝ)

noncomputable def arc (n H : ℕ) (i : ℕ × ℕ) : Set ℝ :=
  {t | |t - center i| ≤ radius n H i.1}

theorem measurable_arc (n H : ℕ) (i : ℕ × ℕ) : MeasurableSet (arc n H i) := by
  unfold arc
  exact measurableSet_le (show Continuous (fun t : ℝ => |t - center i|) by fun_prop).measurable
    measurable_const

theorem arc_eq_Icc (n H : ℕ) (i : ℕ × ℕ) :
    arc n H i = Set.Icc (center i - radius n H i.1) (center i + radius n H i.1) := by
  ext t
  change |t - center i| ≤ radius n H i.1 ↔ _
  rw [abs_le, Set.mem_Icc]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem mem_cap {n U H : ℕ} {t : ℝ} :
    t ∈ cap n U H ↔ ∃ i ∈ centers U, t ∈ arc n H i := by
  constructor
  · rintro ⟨q,a,h₁,h₂,h₃,h₄,h₅⟩
    exact ⟨(q,a),mem_centers.mpr ⟨h₁,h₂,h₃,h₄⟩,h₅⟩
  · rintro ⟨⟨q,a⟩,hi,ht⟩
    obtain ⟨h₁,h₂,h₃,h₄⟩ := mem_centers.mp hi
    exact ⟨q,a,h₁,h₂,h₃,h₄,ht⟩

theorem measurable_cap (n U H : ℕ) : MeasurableSet (cap n U H) := by
  have h : cap n U H = ⋃ i ∈ centers U, arc n H i := by
    ext t
    rw [mem_cap]
    simp only [Set.mem_iUnion]
    constructor <;> rintro ⟨i,hi,ht⟩ <;> exact ⟨i,hi,ht⟩
  rw [h]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => measurable_arc n H i

theorem arc_mono {n R H : ℕ} (h : R ≤ H) (i : ℕ × ℕ) : arc n R i ⊆ arc n H i := by
  intro t ht
  change |t - center i| ≤ radius n R i.1 at ht
  change |t - center i| ≤ radius n H i.1
  exact ht.trans (div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity))

theorem cap_mono {n Q U R H : ℕ} (hQ : Q ≤ U) (hH : R ≤ H) :
    cap n Q R ⊆ cap n U H := by
  intro t ht
  obtain ⟨i,hi,hit⟩ := mem_cap.mp ht
  exact mem_cap.mpr ⟨i,centers_mono hQ hi,arc_mono hH i hit⟩

theorem common_arc_unique {n U H : ℕ} (hbudget : 2 * H * U < n)
    {i j : ℕ × ℕ} (hi : i ∈ centers U) (hj : j ∈ centers U) {t : ℝ}
    (hti : t ∈ arc n H i) (htj : t ∈ arc n H j) : i = j := by
  obtain ⟨hi₁,hi₂,_,hi₄⟩ := mem_centers.mp hi
  obtain ⟨hj₁,hj₂,_,hj₄⟩ := mem_centers.mp hj
  obtain ⟨h₁,h₂⟩ := GoldbachWideArcs.reduced_centers_eq_of_common_point
    hbudget hi₁ hj₁ hi₂ hj₂ hi₄ hj₄ hti htj
  exact Prod.ext h₁ h₂

/-- A wide arc clipped to the unit interval, with its narrow interval removed when appropriate. -/
noncomputable def cell (n Q H : ℕ) (i : ℕ × ℕ) : Set ℝ :=
  (arc n H i \ (if i.1 ≤ Q then arc n Q i else ∅)) ∩ Set.Ioc 0 1

theorem measurable_cell (n Q H : ℕ) (i : ℕ × ℕ) : MeasurableSet (cell n Q H i) := by
  unfold cell
  apply MeasurableSet.inter _ measurableSet_Ioc
  apply (measurable_arc n H i).diff
  split
  · exact measurable_arc n Q i
  · exact MeasurableSet.empty

theorem cell_disjoint {n Q U H : ℕ} (hbudget : 2 * H * U < n) :
    (↑(centers U) : Set (ℕ × ℕ)).PairwiseDisjoint (cell n Q H) := by
  intro i hi j hj hij
  apply Set.disjoint_left.mpr
  intro t hti htj
  exact hij (common_arc_unique hbudget hi hj hti.1.1 htj.1.1)

theorem cells_eq {n Q U H : ℕ} (hQ : Q ≤ U) (hH : Q ≤ H) (hbudget : 2 * H * U < n) :
    (⋃ i ∈ centers U, cell n Q H i) = (cap n U H \ cap n Q Q) ∩ Set.Ioc 0 1 := by
  ext t
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨i,hi,ht⟩
    refine ⟨⟨mem_cap.mpr ⟨i,hi,ht.1.1⟩,?_⟩, ht.2⟩
    intro hN
    obtain ⟨j,hj,htj⟩ := mem_cap.mp hN
    have he := common_arc_unique hbudget hi (centers_mono hQ hj) ht.1.1 (arc_mono hH j htj)
    subst j
    apply ht.1.2
    rw [ite_eq_left (mem_centers.mp hj).2.1]
    exact htj
  · rintro ⟨⟨ht,hnot⟩,hunit⟩
    obtain ⟨i,hi,hti⟩ := mem_cap.mp ht
    refine ⟨i,hi,⟨⟨hti,?_⟩,hunit⟩⟩
    by_cases hic : i.1 ≤ Q
    · rw [ite_eq_left hic]
      intro hnarrow
      apply hnot
      obtain ⟨h₁,_,h₃,h₄⟩ := mem_centers.mp hi
      exact mem_cap.mpr ⟨i,mem_centers.mpr ⟨h₁,hic,h₃,h₄⟩,hnarrow⟩
    · simp [hic]

theorem integrate_difference_eq_sum {n Q U H : ℕ}
    (hQ : Q ≤ U) (hH : Q ≤ H) (hbudget : 2 * H * U < n) (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ t in (0 : ℝ)..1, (cap n U H \ cap n Q Q).indicator F t) =
      ∑ i ∈ centers U, ∫ t in cell n Q H i, F t := by
  have hm := (measurable_cap n U H).diff (measurable_cap n Q Q)
  have hint : IntegrableOn F (Set.Ioc (0 : ℝ) 1) volume :=
    (hF.intervalIntegrable (0 : ℝ) 1).1
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), setIntegral_indicator hm,
    inter_comm, ← cells_eq hQ hH hbudget]
  exact integral_biUnion_finset (centers U) (fun i _ => measurable_cell n Q H i)
    (cell_disjoint hbudget) (fun i _ => hint.mono_set inter_subset_right)

theorem integrate_middle_split {n Q U H : ℕ}
    (hQ : Q ≤ U) (hH : Q ≤ H) (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ t in (0 : ℝ)..1, (cap n U Q \ cap n Q Q).indicator F t) +
      (∫ t in (0 : ℝ)..1, (cap n U H \ cap n U Q).indicator F t) =
        ∫ t in (0 : ℝ)..1, (cap n U H \ cap n Q Q).indicator F t := by
  let L := cap n Q Q
  let M := cap n U Q
  let W := cap n U H
  have hLM : L ⊆ M := cap_mono hQ le_rfl
  have hMW : M ⊆ W := cap_mono le_rfl hH
  have hm := (measurable_cap n U Q).diff (measurable_cap n Q Q)
  have hw := (measurable_cap n U H).diff (measurable_cap n U Q)
  have hint : IntegrableOn F (Set.Ioc (0 : ℝ) 1) volume :=
    (hF.intervalIntegrable (0 : ℝ) 1).1
  have hmi : IntervalIntegrable ((M \ L).indicator F) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 (hint.indicator hm)
  have hwi : IntervalIntegrable ((W \ M).indicator F) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 (hint.indicator hw)
  change (∫ t in (0 : ℝ)..1, (M \ L).indicator F t) +
    (∫ t in (0 : ℝ)..1, (W \ M).indicator F t) =
    ∫ t in (0 : ℝ)..1, (W \ L).indicator F t
  rw [← intervalIntegral.integral_add hmi hwi]
  apply intervalIntegral.integral_congr
  intro t _
  by_cases hl : t ∈ L
  · have hmt := hLM hl
    simp [hl, hmt]
  · by_cases hmt : t ∈ M
    · have hwt := hMW hmt
      simp [hl, hmt, hwt]
    · by_cases hwt : t ∈ W <;> simp [hl, hmt, hwt]

end GoldbachGRHArcs

end GoldbachGRHArcs

section GoldbachGRHCenterSums

open scoped BigOperators

namespace GoldbachGRHArcs

/-- Group the reduced arc centers by denominator. -/
theorem sum_centers_eq (U : ℕ) {A : Type*} [AddCommMonoid A] (F : ℕ × ℕ → A) :
    (∑ i ∈ centers U, F i) =
      ∑ q ∈ Finset.Icc 1 U, ∑ a ∈ (Finset.range (q + 1)).filter (fun a => a.Coprime q),
        F (q, a) := by
  rw [centers, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun q hq => ?_
  change (∑ a ∈ Finset.range (U + 1), if a ≤ q ∧ a.Coprime q then F (q, a) else 0) = _
  rw [← Finset.sum_filter]
  have hqU := (Finset.mem_Icc.mp hq).2
  have hs : (Finset.range (U + 1)).filter (fun a => a ≤ q ∧ a.Coprime q) =
      (Finset.range (q + 1)).filter (fun a => a.Coprime q) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, ha, hcop⟩
      exact ⟨Nat.lt_succ_of_le ha, hcop⟩
    · rintro ⟨ha, hcop⟩
      exact ⟨by omega, by omega, hcop⟩
  rw [hs]

/-- The least nonnegative representatives enumerate all residues once. -/
theorem sum_range_natCast_zmod (q : ℕ) [NeZero q] {A : Type*} [AddCommMonoid A]
    (f : ZMod q → A) :
    (∑ a ∈ Finset.range q, f (a : ZMod q)) = ∑ a : ZMod q, f a := by
  apply Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q))
  · intro a _
    exact Finset.mem_univ _
  · intro a ha b hb hab
    simpa only [ZMod.val_natCast_of_lt (Finset.mem_range.mp ha),
      ZMod.val_natCast_of_lt (Finset.mem_range.mp hb)] using congrArg ZMod.val hab
  · intro a _
    exact ⟨a.val, Finset.mem_range.mpr a.val_lt, ZMod.natCast_zmod_val a⟩
  · intro a _
    rfl

/-- Restrict to the reduced numerators of the closed unit interval. The factor
    two allows the endpoints \(0/1\) and \(1/1\) to share their residue. -/
theorem sum_numerators_le_real (q : ℕ) [NeZero q] (f : ZMod q → ℝ)
    (hf : ∀ a, 0 ≤ f a) :
    (∑ a ∈ (Finset.range (q + 1)).filter (fun a => a.Coprime q), f (a : ZMod q)) ≤
      2 * (∑ a : ZMod q, f a) := by
  calc
    _ ≤ ∑ a ∈ Finset.range (q + 1), f (a : ZMod q) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun a _ _ => hf a)
    _ = (∑ a ∈ Finset.range q, f (a : ZMod q)) + f (q : ZMod q) :=
      Finset.sum_range_succ _ _
    _ = (∑ a : ZMod q, f a) + f 0 := by
      rw [sum_range_natCast_zmod, ZMod.natCast_self]
    _ ≤ _ := by
      have hzero : f 0 ≤ ∑ a : ZMod q, f a :=
        Finset.single_le_sum (fun a _ => hf a) (Finset.mem_univ 0)
      linarith

end GoldbachGRHArcs

end GoldbachGRHCenterSums

section GoldbachGRHArcTransport

open MeasureTheory
open Set hiding center
open scoped Interval

namespace GoldbachGRHArcTransport

open GoldbachGRHArcs

private theorem radius_nonnegative (n H q : ℕ) : 0 ≤ radius n H q := by
  unfold radius
  positivity

private theorem continuous_translate {E : Type*} [TopologicalSpace E]
    {G : ℝ → E} (hG : Continuous G) (c : ℝ) : Continuous (fun t => G (t - c)) :=
  hG.comp (continuous_id.sub continuous_const)

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem arc_integral (n H : ℕ) (i : ℕ × ℕ) (G : ℝ → E) :
    (∫ t in arc n H i, G (t - center i)) =
      ∫ t in (-(radius n H i.1))..(radius n H i.1), G t := by
  have hr := radius_nonnegative n H i.1
  rw [arc_eq_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith only [hr] :
      center i - radius n H i.1 ≤ center i + radius n H i.1),
    intervalIntegral.integral_comp_sub_right]
  congr 2 <;> ring

private theorem clipped_arc_integral_closed (n H : ℕ) (i : ℕ × ℕ) (G : ℝ → E) :
    (∫ t in arc n H i ∩ Ioc 0 1, G (t - center i)) =
      ∫ t in arc n H i ∩ Icc 0 1, G (t - center i) := by
  apply setIntegral_congr_set
  have h : Ioc (0 : ℝ) 1 =ᵐ[volume] Icc (0 : ℝ) 1 := Ioc_ae_eq_Icc
  filter_upwards [h] with t ht
  simp only [mem_inter_iff, ht]

theorem clipped_arc_integral_of_interior (n H : ℕ) (i : ℕ × ℕ) (G : ℝ → E)
    (hleft : radius n H i.1 ≤ center i) (hright : center i + radius n H i.1 ≤ 1) :
    (∫ t in arc n H i ∩ Ioc 0 1, G (t - center i)) =
      ∫ t in (-(radius n H i.1))..(radius n H i.1), G t := by
  rw [clipped_arc_integral_closed, inter_eq_left.mpr, arc_integral]
  rw [arc_eq_Icc]
  exact Icc_subset_Icc (sub_nonneg.mpr hleft) hright

theorem clipped_arc_integral_zero (n H : ℕ) (G : ℝ → E)
    (hr : radius n H 1 ≤ 1) :
    (∫ t in arc n H (1, 0) ∩ Ioc 0 1, G (t - center (1, 0))) =
      ∫ t in (0 : ℝ)..(radius n H 1), G t := by
  have hnonneg := radius_nonnegative n H 1
  rw [clipped_arc_integral_closed, arc_eq_Icc]
  simp only [show center (1, 0) = 0 by norm_num [center], zero_sub, zero_add, sub_zero]
  rw [Icc_inter_Icc, sup_eq_right.mpr (neg_nonpos.mpr hnonneg), inf_eq_left.mpr hr,
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hnonneg]

theorem clipped_arc_integral_one (n H : ℕ) (G : ℝ → E)
    (hr : radius n H 1 ≤ 1) :
    (∫ t in arc n H (1, 1) ∩ Ioc 0 1, G (t - center (1, 1))) =
      ∫ t in (-(radius n H 1))..(0 : ℝ), G t := by
  have hnonneg := radius_nonnegative n H 1
  rw [clipped_arc_integral_closed, arc_eq_Icc]
  simp only [show center (1, 1) = 1 by norm_num [center] ]
  rw [Icc_inter_Icc, sup_eq_left.mpr (sub_nonneg.mpr hr),
    inf_eq_right.mpr (by linarith only [hnonneg] : (1 : ℝ) ≤ 1 + radius n H 1),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith only [hnonneg] :
      1 - radius n H 1 ≤ 1), intervalIntegral.integral_comp_sub_right]
  congr 2 <;> ring

theorem cell_integral_eq_clipped_sub {n Q H : ℕ} (hQH : Q ≤ H) (i : ℕ × ℕ)
    (G : ℝ → E) (hG : Continuous G) :
    (∫ t in cell n Q H i, G (t - center i)) =
      (∫ t in arc n H i ∩ Ioc 0 1, G (t - center i)) -
        if i.1 ≤ Q then (∫ t in arc n Q i ∩ Ioc 0 1, G (t - center i)) else 0 := by
  by_cases hq : i.1 ≤ Q
  · simp only [cell, ite_eq_left hq]
    rw [show (arc n H i \ arc n Q i) ∩ Ioc (0 : ℝ) 1 =
        (arc n H i ∩ Ioc 0 1) \ (arc n Q i ∩ Ioc 0 1) by
      ext t
      simp only [mem_inter_iff, mem_sdiff]
      tauto]
    apply setIntegral_sdiff ((measurable_arc n Q i).inter measurableSet_Ioc)
    · exact ((continuous_translate hG (center i)).intervalIntegrable 0 1).1.mono_set inter_subset_right
    · exact inter_subset_inter_left _ (arc_mono hQH i)
  · simp [cell, hq]

end Integral

/-- A nonnegative translated integrand on the clipped cell is bounded by its full window. -/
theorem cell_l2_le (n Q H : ℕ) (i : ℕ × ℕ) (G : ℝ → ℝ) (hG : Continuous G)
    (hG0 : ∀ t, 0 ≤ G t) :
    (∫ t in cell n Q H i, G (t - center i)) ≤
      ∫ t in (-(radius n H i.1))..(radius n H i.1), G t := by
  rw [← arc_integral]
  apply setIntegral_mono_set
  · rw [arc_eq_Icc, integrableOn_Icc_iff_integrableOn_Ioc]
    exact ((continuous_translate hG (center i)).intervalIntegrable _ _).1
  · exact Filter.Eventually.of_forall fun t => hG0 (t - center i)
  · exact (show cell n Q H i ⊆ arc n H i from fun _ ht => ht.1.1).eventuallySubset

theorem arc_interior_bounds {n H q a : ℕ} (hH : H ≤ n) (hq : 2 ≤ q) (ha : a ≤ q)
    (hcop : Nat.Coprime a q) :
    radius n H q ≤ center (q, a) ∧ center (q, a) + radius n H q ≤ 1 := by
  have ha0 : 1 ≤ a := by
    by_contra! hn
    have ha' : a = 0 := by omega
    subst a
    have h := (Nat.coprime_zero_left q).mp hcop
    omega
  have haq : a + 1 ≤ q := by
    by_contra! hn
    have ha' : a = q := by omega
    subst a
    have h : q = 1 := by simpa [Nat.Coprime] using hcop
    omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hr : radius n H q ≤ 1 / (q : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [radius]
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hHn : (H : ℝ) ≤ (n : ℝ) := by exact_mod_cast hH
    unfold radius
    apply (div_le_iff₀ (mul_pos hqR hnR)).mpr
    rw [← mul_assoc, one_div_mul_cancel hqR.ne', one_mul]
    exact hHn
  refine ⟨hr.trans ?_, (add_le_add_right hr (center (q, a))).trans ?_⟩
  · unfold center
    exact div_le_div_of_nonneg_right (by exact_mod_cast ha0) hqR.le
  · unfold center
    rw [← add_div]
    apply (div_le_iff₀ hqR).mpr
    simpa only [one_mul, Nat.cast_add, Nat.cast_one] using (show ((a + 1 : ℕ) : ℝ) ≤ q by
      exact_mod_cast haq)

theorem radius_one_le {n H : ℕ} (hH : H ≤ n) : radius n H 1 ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [radius]
  · simpa [radius] using (div_le_one (by exact_mod_cast hn : (0:ℝ) < n)).mpr
      (show (H : ℝ) ≤ n by exact_mod_cast hH)


theorem cell_integral_interior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n Q H q a : ℕ} (hQH : Q ≤ H) (hHn : H ≤ n) (hq : 2 ≤ q) (ha : a ≤ q)
    (hcop : Nat.Coprime a q) (G : ℝ → E) (hG : Continuous G) :
    (∫ t in cell n Q H (q, a), G (t - center (q, a))) =
      (∫ t in (-(radius n H q))..(radius n H q), G t) -
        if q ≤ Q then (∫ t in (-(radius n Q q))..(radius n Q q), G t) else 0 := by
  obtain ⟨hHl, hHr⟩ := arc_interior_bounds hHn hq ha hcop
  obtain ⟨hQl, hQr⟩ := arc_interior_bounds (hQH.trans hHn) hq ha hcop
  rw [cell_integral_eq_clipped_sub hQH (q, a) G hG,
    clipped_arc_integral_of_interior n H (q, a) G hHl hHr,
    clipped_arc_integral_of_interior n Q (q, a) G hQl hQr]

/-- The two denominator-one cells assemble to a full translated window. -/
theorem cell_integral_endpoints {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n Q H : ℕ} (hQH : Q ≤ H) (hHn : H ≤ n) (G : ℝ → E) (hG : Continuous G) :
    (∫ t in cell n Q H (1, 0), G (t - center (1, 0))) +
      (∫ t in cell n Q H (1, 1), G (t - center (1, 1))) =
      (∫ t in (-(radius n H 1))..(radius n H 1), G t) -
        if 1 ≤ Q then (∫ t in (-(radius n Q 1))..(radius n Q 1), G t) else 0 := by
  have hQn := hQH.trans hHn
  have hfull (R : ℕ) :
      (∫ t in (0 : ℝ)..(radius n R 1), G t) +
        (∫ t in (-(radius n R 1))..(0 : ℝ), G t) =
          ∫ t in (-(radius n R 1))..(radius n R 1), G t := by
    rw [add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals (hG.intervalIntegrable _ _)
      (hG.intervalIntegrable _ _)
  simp only [cell_integral_eq_clipped_sub hQH _ G hG,
    clipped_arc_integral_zero n H G (radius_one_le hHn),
    clipped_arc_integral_zero n Q G (radius_one_le hQn),
    clipped_arc_integral_one n H G (radius_one_le hHn),
    clipped_arc_integral_one n Q G (radius_one_le hQn)]
  by_cases h : 1 ≤ Q
  · simp only [ite_eq_left h]
    rw [← hfull H, ← hfull Q]
    abel
  · simpa only [ite_eq_right h, sub_zero] using hfull H

theorem cell_kernel_interior {n Q H q a : ℕ} (hQH : Q ≤ H) (hHn : H ≤ n)
    (hq : 2 ≤ q) (ha : a ≤ q) (hcop : Nat.Coprime a q) :
    (∫ t in cell n Q H (q, a), ‖GoldbachGRHKernel.kernel n (t - center (q, a))‖ ^ 2) =
      GoldbachGRHKernel.mass n (radius n H q) -
        if q ≤ Q then GoldbachGRHKernel.mass n (radius n Q q) else 0 :=
  cell_integral_interior hQH hHn hq ha hcop _
    ((GoldbachGRHKernel.kernel_continuous n).norm.pow 2)

theorem cell_kernel_endpoints {n Q H : ℕ} (hQH : Q ≤ H) (hHn : H ≤ n) :
    (∫ t in cell n Q H (1, 0), ‖GoldbachGRHKernel.kernel n (t - center (1, 0))‖ ^ 2) +
      (∫ t in cell n Q H (1, 1), ‖GoldbachGRHKernel.kernel n (t - center (1, 1))‖ ^ 2) =
      GoldbachGRHKernel.mass n (radius n H 1) -
        if 1 ≤ Q then GoldbachGRHKernel.mass n (radius n Q 1) else 0 :=
  cell_integral_endpoints hQH hHn _ ((GoldbachGRHKernel.kernel_continuous n).norm.pow 2)

end GoldbachGRHArcTransport

end GoldbachGRHArcTransport

section GoldbachGRHModelDef

namespace GoldbachGRHModel

/-- The principal model on a single reduced rational arc. -/
noncomputable def model (n : ℕ) (i : ℕ × ℕ) (t : ℝ) : ℂ :=
  ((ArithmeticFunction.moebius i.1 : ℂ) / (i.1.totient : ℂ)) *
    GoldbachGRHKernel.kernel n (t - GoldbachGRHArcs.center i)

theorem model_continuous (n : ℕ) (i : ℕ × ℕ) : Continuous (model n i) :=
  continuous_const.mul ((GoldbachGRHKernel.kernel_continuous n).comp
    (continuous_id.sub continuous_const))

end GoldbachGRHModel

end GoldbachGRHModelDef

section GoldbachGRHModelAssembly

open Finset MeasureTheory
open scoped ComplexConjugate

namespace GoldbachGRHModelAssembly

open GoldbachGRHArcs (cell centers center radius)
open GoldbachGRHKernel (kernel mass)
open GoldbachFourthMoment (phase phase_add)
open GoldbachGRHModel (model)
open GoldbachExplicitModeledMajor (coefficient ram ram_one_eq_moebius)

noncomputable def massDifference (n Q H q : ℕ) : ℝ :=
  mass n (radius n H q) - if q ≤ Q then mass n (radius n Q q) else 0

noncomputable def signedFactor (n q a : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 2 *
    phase (-(n : ℝ) * center (q, a))

private theorem phase_neg (x : ℝ) : phase (-x) = conj (phase x) := by
  symm
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem signedFactor_zero (n : ℕ) : signedFactor n 1 0 = 1 := by
  simp [signedFactor, center, phase]

private theorem signedFactor_one (n : ℕ) : signedFactor n 1 1 = 1 := by
  simp [signedFactor, center, phase_neg, GoldbachGRHKernel.phase_nat]

theorem model_square_eq (n q a : ℕ) (t : ℝ) :
    model n (q, a) t ^ 2 * phase (-(n : ℝ) * t) =
      signedFactor n q a * (↑(‖kernel n (t - center (q, a))‖ ^ 2) : ℂ) := by
  have hphase : -(n : ℝ) * t =
      -(n : ℝ) * center (q, a) + -(n : ℝ) * (t - center (q, a)) := by ring
  rw [← GoldbachGRHKernel.reflect n (t - center (q, a)), model, hphase, phase_add]
  unfold signedFactor
  ring

theorem cell_model_integral (n Q H q a : ℕ) :
    (∫ t in cell n Q H (q, a), model n (q, a) t ^ 2 * phase (-(n : ℝ) * t)) =
      signedFactor n q a *
        (↑(∫ t in cell n Q H (q, a), ‖kernel n (t - center (q, a))‖ ^ 2) : ℂ) := by
  simp_rw [model_square_eq]
  rw [MeasureTheory.integral_const_mul, integral_complex_ofReal]

theorem sum_signedFactor (n q : ℕ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), signedFactor n q a) =
      coefficient q n := by
  rw [coefficient, ram_one_eq_moebius, ram, map_sum, Finset.mul_sum]
  refine sum_congr rfl fun a _ => ?_
  unfold signedFactor
  congr 1
  have h : -(n : ℝ) * center (q, a) = -((n : ℝ) * a / q) := by
    simp only [center, ← mul_div_assoc, neg_mul, neg_div]
  rw [h, phase_neg]
  rfl

/-- Grouping the centered kernels by denominator recovers the exact Ramanujan model. -/
theorem sum_cell_model {n Q H U : ℕ} (_hU : 1 ≤ U) (hQH : Q ≤ H) (hHn : H ≤ n) :
    (∑ i ∈ centers U, ∫ t in cell n Q H i, model n i t ^ 2 * phase (-(n : ℝ) * t)) =
      ∑ q ∈ Icc 1 U, coefficient q n * (massDifference n Q H q : ℂ) := by
  classical
  rw [GoldbachGRHArcs.sum_centers_eq]
  refine sum_congr rfl fun q hq => ?_
  have hq1 := (mem_Icc.mp hq).1
  by_cases hqOne : q = 1
  · subst q
    have hf : ((range (1 + 1)).filter (fun a : ℕ => Nat.Coprime a 1)) =
        ({0, 1} : Finset ℕ) := by
      ext a
      simp only [mem_filter, mem_range, Nat.coprime_one_right_iff, and_true,
        mem_insert, mem_singleton]
      omega
    rw [hf, sum_pair (by decide : (0 : ℕ) ≠ 1)]
    simp only [cell_model_integral, signedFactor_zero, signedFactor_one, one_mul,
      ← Complex.ofReal_add, GoldbachGRHArcTransport.cell_kernel_endpoints hQH hHn,
      GoldbachExplicitModeledMajor.coefficient_one, massDifference]
  · have hq2 : 2 ≤ q := by omega
    have hf : ((range (q + 1)).filter (fun a => Nat.Coprime a q)) =
        (range q).filter (fun a => Nat.Coprime a q) := by
      ext a
      simp only [mem_filter, mem_range]
      constructor
      · rintro ⟨haq, hcop⟩
        have hne : a ≠ q := by
          intro heq
          subst a
          have h : q = 1 := by simpa [Nat.Coprime] using hcop
          exact hqOne h
        exact ⟨lt_of_le_of_ne (Nat.lt_succ_iff.mp haq) hne, hcop⟩
      · rintro ⟨haq, hcop⟩
        exact ⟨haq.trans (Nat.lt_succ_self q), hcop⟩
    rw [hf, ← sum_signedFactor, Finset.sum_mul]
    refine sum_congr rfl fun a ha => ?_
    obtain ⟨haq, hcop⟩ := mem_filter.mp ha
    rw [cell_model_integral, GoldbachGRHArcTransport.cell_kernel_interior hQH hHn hq2
      (mem_range.mp haq).le hcop, massDifference]

theorem sum_cell_model_re {n Q H U : ℕ} (hU : 1 ≤ U) (hQH : Q ≤ H) (hHn : H ≤ n) :
    (∑ i ∈ centers U, ∫ t in cell n Q H i, model n i t ^ 2 * phase (-(n : ℝ) * t)).re =
      ∑ q ∈ Icc 1 U, (coefficient q n).re * massDifference n Q H q := by
  rw [sum_cell_model hU hQH hHn, Complex.re_sum]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

end GoldbachGRHModelAssembly

end GoldbachGRHModelAssembly

section GoldbachGRHBudget

open Filter Finset
open scoped Topology

namespace GoldbachGRHBudget

def narrow (n : ℕ) : ℕ := (Nat.log 2 (n+2))^2
noncomputable def cutoff (n : ℕ) : ℕ := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
noncomputable def width (n : ℕ) : ℕ := 256 * cutoff n * narrow n

theorem width_ge_cutoff (n : ℕ) (h : 1 ≤ narrow n) : cutoff n ≤ width n := by
  unfold width
  have hh := Nat.mul_le_mul_left (256 * cutoff n) h
  omega

end GoldbachGRHBudget
end GoldbachGRHBudget

section GoldbachGRHSignedModel

open Filter
open scoped Topology BigOperators ComplexConjugate

namespace GoldbachGRHSignedModel

open Finset

theorem weighted_suffix_lower (f : ℕ → ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ (m A : ℕ) (w : ℕ → ℝ), Monotone w → (∀ q ≥ A, 0 ≤ w q) →
      (∀ k, A ≤ k → k ≤ A+m → -ε ≤ ∑ q ∈ Ioc k (A+m), f q) →
      -(ε * w (A+m)) ≤ ∑ q ∈ Ioc A (A+m), f q * w q := by
  intro m
  induction m with
  | zero =>
    intro A w _ hw _
    simpa using neg_nonpos.mpr (mul_nonneg hε (hw A le_rfl))
  | succ m ih =>
    intro A w hw hw₀ hfloor
    let B := A + (m+1)
    let v : ℕ → ℝ := fun q => w q-w (A+1)
    have hB : A+1+m=B := by dsimp [B]; omega
    have hv : Monotone v := by
      intro i j hij
      exact sub_le_sub_right (hw hij) _
    have hv₀ (q : ℕ) (hq : A+1 ≤ q) : 0 ≤ v q := sub_nonneg.mpr (hw hq)
    have hsub : -(ε * v B) ≤ ∑ q ∈ Ioc (A+1) B, f q * v q := by
      rw [← hB]
      apply ih (A+1) v hv hv₀
      intro k hk hkB
      simpa only [hB] using hfloor k (by omega) (show k ≤ B from hB ▸ hkB)
    have hs : Ioc A B = insert (A+1) (Ioc (A+1) B) := by
      ext k
      have hAB : A+1 ≤ B := by dsimp [B]; omega
      simp only [mem_Ioc, mem_insert]
      omega
    have hnin : A+1 ∉ Ioc (A+1) B := by simp
    have hsum :
        (∑ q ∈ Ioc A B, f q * w q) =
          w (A+1) * (∑ q ∈ Ioc A B, f q) +
            ∑ q ∈ Ioc (A+1) B, f q * v q := by
      rw [hs]
      simp only [sum_insert hnin, v, mul_sub, sum_sub_distrib, ← sum_mul]
      ring
    have hf := hfloor A le_rfl (by omega)
    have hfirst : -(ε * w (A+1)) ≤ w (A+1) * (∑ q ∈ Ioc A B, f q) := by
      simpa [B, mul_comm] using mul_le_mul_of_nonneg_left hf (hw₀ (A+1) (by omega))
    change -(ε * w B) ≤ ∑ q ∈ Ioc A B, f q * w q
    rw [hsum]
    dsimp [v] at hsub
    calc
      _ = -(ε*w (A+1)) + -(ε*(w B-w (A+1))) := by ring
      _ ≤ _ := add_le_add hfirst hsub

theorem weighted_suffix_lower_of_le_one (f w : ℕ → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    {A B : ℕ} (hAB : A ≤ B) (hw : Monotone w) (hw₀ : ∀ q ≥ A, 0 ≤ w q) (hwend : w B ≤ 1)
    (hfloor : ∀ k, A ≤ k → k ≤ B → -ε ≤ ∑ q ∈ Ioc k B, f q) :
    -ε ≤ ∑ q ∈ Ioc A B, f q * w q := by
  have hlen : A+(B-A)=B := Nat.add_sub_of_le hAB
  have hh := weighted_suffix_lower f ε hε (B-A) A w hw hw₀
  rw [hlen] at hh
  exact (by nlinarith [mul_le_mul_of_nonneg_left hwend hε] : -ε ≤ -(ε * w B)).trans (hh hfloor)

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel

open Finset Filter ArithmeticFunction
open scoped Topology ArithmeticFunction.zeta

private theorem inverse_squares_ge_two_le (X : ℕ) :
    (∑ j ∈ Icc 2 X, ((j : ℝ)^2)⁻¹) ≤ 3/4 := by
  by_cases hX : 2 ≤ X
  · rw [← sum_Ioc_add_eq_sum_Icc hX]
    have hh := sum_Ioc_inv_sq_le_sub (α := ℝ) (by decide : (2 : ℕ) ≠ 0) hX
    norm_num at hh ⊢
    linarith [show 0 ≤ ((X : ℝ))⁻¹ by positivity]
  · norm_num [Icc_eq_empty_of_lt (lt_of_not_ge hX)]

private theorem product_one_sub_ge {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) :
    1 - (∑ i ∈ s, f i) ≤ ∏ i ∈ s, (1-f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have haF := hf a (mem_insert_self _ _)
    have hs : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1 := fun i hi => hf i (mem_insert_of_mem hi)
    rw [sum_insert ha, prod_insert ha]
    have hsum : 0 ≤ ∑ i ∈ s, f i := sum_nonneg fun i hi => (hs i hi).1
    have hh := mul_le_mul_of_nonneg_left (ih hs) (sub_nonneg.mpr haF.2)
    nlinarith only [hh, mul_nonneg haF.1 hsum]

private noncomputable def correctionLoss (n p : ℕ) : ℝ :=
  if p ∣ n then 0 else (((p : ℝ)-1)^2)⁻¹

private theorem odd_prime_ge_three {n p : ℕ} (hn : Even n) (hp : p.Prime)
    (hpn : ¬ p ∣ n) : 3 ≤ p := by
  have hp2 := hp.two_le
  by_contra! hh
  have hp₂ : p = 2 := by omega
  apply hpn
  rw [hp₂]
  obtain ⟨k, hk⟩ := hn
  exact ⟨k, by omega⟩

private theorem correctionLoss_bounds {n p : ℕ} (hn : Even n) (hp : p.Prime) :
    0 ≤ correctionLoss n p ∧ correctionLoss n p ≤ 1 := by
  unfold correctionLoss
  by_cases hpN : p ∣ n
  · simp [hpN]
  · have h3 : (3 : ℝ) ≤ p := by exact_mod_cast odd_prime_ge_three hn hp hpN
    rw [ite_eq_right hpN]
    exact ⟨by positivity, inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ((p:ℝ)-2)])⟩

private theorem local_correction_floor (n p k : ℕ) (hp : p.Prime) :
    1 - correctionLoss n p ≤ ∑ d ∈ (p^k).divisors, BandTail.z n d := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  rw [Nat.sum_divisors_prime_pow hp,
    BandTail.localReduce (fun j => BandTail.z n (p^j))
      (fun j => by simp [BandTail.z,BandTail.h_cube n p j hp])]
  simp only [pow_zero,pow_one,(BandTail.z_mult n).map_one]
  simp only [correctionLoss,BandTail.z,ArithmeticFunction.coe_mk,
    BandTail.h_prime n p hp,BandTail.h_square n p hp,Nat.cast_pow]
  by_cases hpn : p ∣ n
  · simp only [hpn, ite_true, sub_zero]
    have hpos : 0 ≤ (1 / ((p : ℝ)-1)) / (p : ℝ) := by positivity
    have hcancel : (1 / ((p : ℝ)-1)) / (p : ℝ) +
        (-(p : ℝ) / ((p : ℝ)-1)) / (p : ℝ)^2 = 0 := by
      field_simp; ring
    split_ifs <;> first | omega | linarith only [hpos,hcancel]
  · simp only [hpn, ite_false, zero_div, ite_self, add_zero]
    have hneg : (-(p : ℝ) / ((p : ℝ)-1)^2) / (p : ℝ) = -(((p : ℝ)-1)^2)⁻¹ := by
      field_simp
    rw [hneg]
    split_ifs <;> linarith [show 0 ≤ (((p : ℝ)-1)^2)⁻¹ by positivity]

theorem signed_divisors_quarter (n M : ℕ) (hn : Even n) (hM : 0 < M) :
    (1/4 : ℝ) ≤ ∑ d ∈ M.divisors, BandTail.z n d := by
  classical
  let s := M.factorization.support
  let P := s.filter (fun p => ¬ p ∣ n)
  have hprime (p : ℕ) (hp : p ∈ s) : p.Prime :=
    Nat.prime_of_mem_primeFactors (M.support_factorization ▸
      (show p ∈ M.factorization.support from hp))
  have hle (p : ℕ) (hp : p ∈ s) : p ≤ M :=
    Nat.le_of_dvd hM (Nat.dvd_of_mem_primeFactors (M.support_factorization ▸
      (show p ∈ M.factorization.support from hp)))
  have hM' (p : ℕ) (hp : p ∈ P) : 3 ≤ p :=
    odd_prime_ge_three hn (hprime p (mem_filter.mp hp).1) (mem_filter.mp hp).2
  have hinj : Set.InjOn (fun p : ℕ => p-1) (↑P : Set ℕ) := by
    intro p hp q hq he
    have h1 := hM' p hp
    have h2 := hM' q hq
    change p - 1 = q - 1 at he
    omega
  have himage : P.image (fun p => p-1) ⊆ Icc 2 M := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hj
    have h1 := hM' p hp
    have h2 := hle p (mem_filter.mp hp).1
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hsum : (∑ p ∈ s, correctionLoss n p) ≤ 3/4 := by
    calc
      _ = ∑ p ∈ P, (((p : ℝ)-1)^2)⁻¹ := by
        rw [sum_filter]
        apply sum_congr rfl
        intro p hp
        by_cases hpN : p ∣ n <;> simp [correctionLoss,hpN]
      _ = ∑ p ∈ P, ((((p-1 : ℕ) : ℝ)^2))⁻¹ := by
        apply sum_congr rfl
        intro p hp
        rw [Nat.cast_sub (by have := hM' p hp; omega)]
        norm_cast
      _ = ∑ j ∈ P.image (fun p : ℕ => p-1), ((j : ℝ)^2)⁻¹ := by rw [sum_image hinj]
      _ ≤ ∑ j ∈ Icc 2 M, ((j : ℝ)^2)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg himage (fun _ _ _ => by positivity)
      _ ≤ _ := inverse_squares_ge_two_le M
  let A : ArithmeticFunction ℝ := BandTail.z n * (ζ : ArithmeticFunction ℝ)
  have hA : IsMultiplicative A := (BandTail.z_mult n).mul isMultiplicative_zeta.natCast
  have he (m : ℕ) : A m = ∑ d ∈ m.divisors,BandTail.z n d := coe_mul_zeta_apply
  have hprod := hA.multiplicative_factorization A hM.ne'
  rw [he] at hprod
  rw [hprod,Finsupp.prod]
  change _ ≤ ∏ p ∈ s, A (p^M.factorization p)
  calc
    _ ≤ 1 - ∑ p ∈ s, correctionLoss n p := by linarith
    _ ≤ ∏ p ∈ s, (1 - correctionLoss n p) :=
      product_one_sub_ge s _ (fun p hp => correctionLoss_bounds hn (hprime p hp))
    _ ≤ _ := by
      apply prod_le_prod₀
      · exact fun p hp => sub_nonneg.mpr (correctionLoss_bounds hn (hprime p hp)).2
      · intro p hp
        rw [he]
        exact local_correction_floor n p _ (hprime p hp)

theorem correction_prefix_eighth :
    ∀ᶠ J : ℕ in atTop, 0 < J ∧ ∀ n : ℕ, Even n →
      (1/8 : ℝ) ≤ ∑ d ∈ Icc 1 J, BandTail.z n d := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/4)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop (1 : ℕ), ht.eventually_ge_atTop (8 * BandTail.universal)]
    with J hJ hlarge
  refine ⟨hJ, ?_⟩
  intro n hn
  have hJ' : 0 < J := hJ
  have hu := BandTail.uniformTail n J (J.factorial.divisors \ Icc 1 J) hJ' (by
    intro d hd
    obtain ⟨hd, hd'⟩ := mem_sdiff.mp hd
    have hpos := Nat.pos_of_mem_divisors hd
    simp only [mem_Icc, not_and] at hd'
    omega)
  have hh := signed_divisors_quarter n J.factorial hn J.factorial_pos
  rw [← sum_sdiff (s₁ := Icc 1 J) (s₂ := J.factorial.divisors) (BandTail.prefixDiv J)] at hh
  have ht := sum_le_sum (s := J.factorial.divisors \ Icc 1 J) (fun d _ => le_abs_self (BandTail.z n d))
  have hsmall : BandTail.universal / (J : ℝ)^(1/4 : ℝ) ≤ 1/8 := by
    apply (div_le_iff₀ (by positivity)).mpr
    change 8 * BandTail.universal ≤ (J : ℝ)^(1/4 : ℝ) at hlarge
    linarith
  linarith

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel

open Finset Filter ArithmeticFunction
open scoped Topology

noncomputable def harmonicG (n X : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 X, BandTail.g n k / (k : ℝ)

noncomputable def harmonicF (n X : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 X, BandTail.F n q / (q : ℝ)

theorem g_unit_interval (n k : ℕ) : 0 ≤ BandTail.g n k ∧ BandTail.g n k ≤ 1 := by
  simp [BandTail.g]
  split_ifs <;> norm_num

private theorem harmonicG_sub (n : ℕ) {A B : ℕ} (hAB : A ≤ B) :
    harmonicG n B - harmonicG n A =
      ∑ k ∈ Ioc A B, BandTail.g n k / (k : ℝ) := by
  have h := BandTail.prefix_split (fun k => BandTail.g n k / (k : ℝ)) hAB
  unfold harmonicG
  linarith

theorem harmonicG_mono (n : ℕ) : Monotone (harmonicG n) := by
  intro A B hAB
  have h := harmonicG_sub n hAB
  have hn : 0 ≤ ∑ k ∈ Ioc A B, BandTail.g n k / (k : ℝ) :=
    sum_nonneg fun k _ => div_nonneg (g_unit_interval n k).1 (Nat.cast_nonneg _)
  linarith

theorem g_boundary_le_mean (n X d : ℕ) (hX : 0 < X) (hd : 0 < d) :
    harmonicG n X - harmonicG n (X/d) ≤ (d : ℝ) * BandTail.gAvg n X := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hsub : Ioc (X/d) X ⊆ Icc 1 X := by
    intro k hk
    exact mem_Icc.mpr ⟨Nat.succ_le_of_lt ((Nat.zero_le (X/d)).trans_lt (mem_Ioc.mp hk).1), (mem_Ioc.mp hk).2⟩
  rw [harmonicG_sub n (Nat.div_le_self X d)]
  calc
    _ ≤ ∑ k ∈ Ioc (X/d) X, BandTail.g n k * ((d : ℝ)/X) := by
      apply sum_le_sum
      intro k hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast Nat.zero_lt_of_lt (mem_Ioc.mp hk).1
      have hxk := (Nat.div_lt_iff_lt_mul hd).mp (mem_Ioc.mp hk).1
      have hxkR : (X : ℝ) ≤ k * d := by exact_mod_cast hxk.le
      have hcoeff : (1 : ℝ)/(k : ℝ) ≤ (d : ℝ)/X :=
        (div_le_div_iff₀ hkR hXR).mpr (by nlinarith)
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hcoeff (g_unit_interval n k).1
    _ ≤ ∑ k ∈ Icc 1 X, BandTail.g n k * ((d : ℝ)/X) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => mul_nonneg (g_unit_interval n k).1 (by positivity))
    _ = _ := by
      rw [← sum_mul]
      unfold BandTail.gAvg BandTail.gSum
      ring

theorem g_boundary_le_log (n X d : ℕ) (hd : 0 < d) :
    harmonicG n X - harmonicG n (X/d) ≤ 1 + Real.log d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlogd : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  by_cases hX : X = 0
  · simp [hX, harmonicG]
    positivity
  have hXR : (0 : ℝ) < X := by exact_mod_cast Nat.pos_of_ne_zero hX
  have hfloor := Nat.div_le_self X d
  have hQ : (0 : ℝ) < ((X / d : ℕ) : ℝ) + 1 := by positivity
  have hdiv : (X : ℝ) / (((X / d : ℕ) : ℝ) + 1) ≤ d := by
    apply (div_le_iff₀ hQ).mpr
    exact_mod_cast (Nat.lt_mul_div_succ X hd).le
  have hlogs : Real.log (X : ℝ) - Real.log (((X / d : ℕ) : ℝ) + 1) ≤ Real.log d := by
    rw [← Real.log_div hXR.ne' hQ.ne']
    exact Real.log_le_log (div_pos hXR hQ) hdiv
  have hH := harmonic_le_one_add_log X
  have hL := log_add_one_le_harmonic (X/d)
  have hsum : (∑ k ∈ Ioc (X/d) X, (k : ℝ)⁻¹) =
      (harmonic X:ℝ) - (harmonic (X/d):ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    have hp := BandTail.prefix_split (fun k : ℕ => (k : ℝ)⁻¹) hfloor
    linarith
  rw [harmonicG_sub n hfloor]
  calc
    _ ≤ ∑ k ∈ Ioc (X/d) X, (k : ℝ)⁻¹ := by
      apply sum_le_sum
      intro k _
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_nonneg.mpr (Nat.cast_nonneg k)) (g_unit_interval n k).2
    _ = _ := hsum
    _ ≤ _ := by
      rw [Nat.cast_add, Nat.cast_one] at hL
      linarith

theorem harmonic_doubling_lower (n A : ℕ) (hA : 0 < A) (t η : ℝ)
    (hlo : |BandTail.gAvg n A - t| ≤ η)
    (hhi : |BandTail.gAvg n (2*A) - t| ≤ η) :
    t/2 - (3/2)*η ≤ harmonicG n (2*A) - harmonicG n A := by
  have hAB : A ≤ 2*A := by omega
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hBA := BandTail.prefix_split (BandTail.g n) hAB
  change BandTail.gSum n (2*A) = BandTail.gSum n A + _ at hBA
  have hweak : BandTail.gAvg n (2*A) - BandTail.gAvg n A / 2 ≤
      harmonicG n (2*A) - harmonicG n A := by
    rw [harmonicG_sub n hAB]
    calc
      _ = (∑ j ∈ Ioc A (2*A), BandTail.g n j) / ((2*A : ℕ) : ℝ) := by
        unfold BandTail.gAvg
        rw [← sub_eq_of_eq_add hBA]
        push_cast
        field_simp; ring
      _ ≤ _ := by
        rw [sum_div]
        apply sum_le_sum
        intro k hk
        apply div_le_div_of_nonneg_left (g_unit_interval n k).1
        · exact_mod_cast hA.trans (mem_Ioc.mp hk).1
        · exact_mod_cast (mem_Ioc.mp hk).2
  linarith [(abs_le.mp hlo).2, (abs_le.mp hhi).1]

theorem harmonic_dyadic_lower (n : ℕ) (t η : ℝ) :
    ∀ (L A : ℕ), 0 < A →
      (∀ j ≤ L, |BandTail.gAvg n (2^j*A) - t| ≤ η) →
      (L : ℝ) * (t/2 - (3/2)*η) ≤ harmonicG n (2^L*A) - harmonicG n A := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    intro A hA hnear
    have hm := ih A hA (fun j hj => hnear j (by omega))
    have ht : 0 < 2^L*A := Nat.mul_pos (pow_pos (by decide) _) hA
    have hh := harmonic_doubling_lower n (2^L*A) ht t η (hnear L (by omega)) (by
      simpa only [pow_succ', mul_assoc] using hnear (L+1) le_rfl)
    push_cast
    rw [pow_succ', mul_assoc]
    linarith

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel

open Finset Filter ArithmeticFunction
open scoped Topology

private theorem sum_divisors_reindex (X : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ q ∈ Icc 1 X, ∑ v ∈ q.divisorsAntidiagonal, f v) =
      ∑ d ∈ Icc 1 X, ∑ k ∈ Icc 1 (X/d), f (d,k) := by
  classical
  let S := Icc 1 X
  have hf (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal = (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    obtain ⟨hq0,hqQ⟩ := mem_Icc.mp hq
    ext ab
    constructor
    · intro hab
      have hm (a : ℕ) (ha : a ∈ q.divisors) : a ∈ S :=
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,(Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors ha)).trans hqQ⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ (Nat.fst_mem_divisors_of_mem_antidiagonal hab),
        hm _ (Nat.snd_mem_divisors_of_mem_antidiagonal hab)⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
    · intro hh; exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hh).2,by omega⟩
  calc
    _ = ∑ q ∈ S, ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), f v :=
      sum_congr rfl (fun q hq => by rw [hf q hq])
    _ = ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), f v :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ = _ := by
      rw [sum_filter,sum_product]
      apply sum_congr rfl
      intro d hd
      have hd0 := (mem_Icc.mp hd).1
      have hkd : (S.filter fun k => d*k∈S)=Icc 1 (X/d) := by
        ext k
        simp only [S,mem_filter,mem_Icc]
        constructor
        · rintro ⟨⟨hk,_⟩,_,hdk⟩
          exact ⟨hk,(Nat.le_div_iff_mul_le hd0).mpr (by simpa [mul_comm] using hdk)⟩
        · rintro ⟨hk,hkx⟩
          exact ⟨⟨hk,hkx.trans (Nat.div_le_self _ _)⟩,Nat.mul_pos hd0 hk,by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd0).mp hkx⟩
      rw [←sum_filter,hkd]

theorem harmonicF_convolution (n X : ℕ) :
    harmonicF n X = ∑ d ∈ Icc 1 X, BandTail.z n d * harmonicG n (X/d) := by
  let f := fun v : ℕ × ℕ => BandTail.z n v.1 * (BandTail.g n v.2 / (v.2 : ℝ))
  calc
    _ = ∑ q ∈ Icc 1 X, ∑ v ∈ q.divisorsAntidiagonal, f v := by
      apply sum_congr rfl
      intro q _
      rw [BandTail.convolution n,mul_comm (BandTail.g n) (BandTail.h n),ArithmeticFunction.mul_apply,sum_div]
      apply sum_congr rfl
      intro v hv
      change BandTail.h n v.1*BandTail.g n v.2/(q:ℝ) =
        (BandTail.h n v.1/(v.1:ℝ))*(BandTail.g n v.2/(v.2:ℝ))
      rw [←(Nat.mem_divisorsAntidiagonal.mp hv).1, Nat.cast_mul,div_eq_mul_inv,mul_inv]
      simp only [div_eq_mul_inv]
      ring
    _ = ∑ d ∈ Icc 1 X, ∑ k ∈ Icc 1 (X/d), f (d,k) := sum_divisors_reindex X f
    _ = _ := by simp [f,harmonicG,mul_sum]

theorem absolute_prefix_le (n X : ℕ) :
    (∑ q ∈ Icc 1 X, |BandTail.F n q|) ≤ BandTail.universal * (X:ℝ) := by
  classical
  let f : ℕ × ℕ → ℝ := fun v => |BandTail.h n v.1|
  calc
    _ ≤ ∑ q ∈ Icc 1 X, ∑ v ∈ q.divisorsAntidiagonal, f v := by
      apply sum_le_sum
      intro q _
      rw [BandTail.convolution n,mul_comm (BandTail.g n) (BandTail.h n),ArithmeticFunction.mul_apply]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      apply sum_le_sum
      intro v _
      rw [abs_mul,abs_of_nonneg (g_unit_interval n v.2).1]
      exact mul_le_of_le_one_right (abs_nonneg _) (g_unit_interval n v.2).2
    _ = ∑ d ∈ Icc 1 X, ∑ k ∈ Icc 1 (X/d), f (d,k) := sum_divisors_reindex X f
    _ ≤ ∑ d ∈ Icc 1 X, |BandTail.z n d| * (X:ℝ) := by
      apply sum_le_sum
      intro d hd
      have hd0 := (mem_Icc.mp hd).1
      have hdR : (0:ℝ)<d := by exact_mod_cast hd0
      have hdiv : ((X/d:ℕ):ℝ) ≤ (X:ℝ)/(d:ℝ) := by
        apply (le_div_iff₀ hdR).2
        exact_mod_cast Nat.div_mul_le_self X d
      calc
        _ = ((X/d:ℕ):ℝ)*|BandTail.h n d| := by
          simp [f,Nat.card_Icc,nsmul_eq_mul]
        _ ≤ ((X:ℝ)/(d:ℝ))*|BandTail.h n d| := mul_le_mul_of_nonneg_right hdiv (abs_nonneg _)
        _ = _ := by
          rw [BandTail.z,ArithmeticFunction.coe_mk,abs_div,abs_of_pos hdR]
          ring
    _ = (∑ d ∈ Icc 1 X, |BandTail.z n d|) * (X:ℝ) := (sum_mul ..).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa using BandTail.uniformTail n 1 (Icc 1 X) (by decide) (fun d hd => (mem_Icc.mp hd).1)

theorem harmonic_convolution_interval (n K X : ℕ) (hKX : K ≤ X) :
    (∑ q ∈ Ioc K X, BandTail.F n q / (q:ℝ)) =
      ∑ d ∈ Icc 1 X, BandTail.z n d * (harmonicG n (X/d)-harmonicG n (K/d)) := by
  have hsub := BandTail.prefix_split (fun q => BandTail.F n q / (q:ℝ)) hKX
  have hsub' : (∑ q ∈ Ioc K X, BandTail.F n q / (q:ℝ)) = harmonicF n X-harmonicF n K := by
    unfold harmonicF
    linarith
  have hK :
      ∑ d ∈ Icc 1 K, BandTail.z n d * harmonicG n (K/d) =
        ∑ d ∈ Icc 1 X, BandTail.z n d * harmonicG n (K/d) := by
    apply sum_subset (Icc_subset_Icc_right hKX)
    intro d hd hnot
    have hdK : K<d := by
      simp only [mem_Icc,not_and] at hnot
      have hd' := mem_Icc.mp hd
      omega
    simp [Nat.div_eq_of_lt hdK,harmonicG]
  rw [hsub',harmonicF_convolution n X,harmonicF_convolution n K,hK,←sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  ring

theorem uniform_log_tail (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ J : ℕ in atTop, 0 < J ∧ ∀ n : ℕ, ∀ s : Finset ℕ, (∀ d ∈ s, J ≤ d) →
      (∑ d ∈ s, |BandTail.z n d| *(1+Real.log d)) ≤ ε := by
  have hC : 0 < BandTail.universal := Real.exp_pos _
  let τ := ε/(2*BandTail.universal)
  have hτ : 0<τ := by dsimp [τ]; positivity
  have hc := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hm := ((isLittleO_log_rpow_rpow_atTop (1:ℝ) (by norm_num : (0:ℝ)<1/4)).comp_tendsto hc).bound hτ
  have hlog := (Real.tendsto_log_atTop.comp hc).eventually_ge_atTop (1:ℝ)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hm.and hlog)
  filter_upwards [eventually_ge_atTop (max N 1)] with J hJ
  have hJ' : 0<J := lt_of_lt_of_le (by decide : 0<1) ((le_max_right N 1).trans hJ)
  refine ⟨hJ',?_⟩
  intro n s hs
  have hbound (d : ℕ) (hd : d ∈ s) : |BandTail.z n d| *(1+Real.log d) ≤
      (ε/BandTail.universal)*BandTail.w n d := by
    have hdJ := hs d hd
    have hd0 := hJ'.trans_le hdJ
    have hz : (0:ℝ)<(d:ℝ)^(1/4:ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hd0) _
    obtain ⟨ha,hb⟩ := hN d ((le_max_left N 1).trans (hJ.trans hdJ))
    change ‖(Real.log (d:ℝ))^(1:ℝ)‖ ≤ τ*‖(d:ℝ)^(1/4:ℝ)‖ at ha
    change 1 ≤ Real.log (d:ℝ) at hb
    rw [Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤Real.log (d:ℝ)),
      Real.norm_eq_abs,abs_of_pos hz] at ha
    have hh : 1+Real.log (d:ℝ) ≤ (ε/BandTail.universal)*(d:ℝ)^(1/4:ℝ) := by
      have hτ' : 2*τ=ε/BandTail.universal := by dsimp [τ]; ring
      rw [←hτ',mul_assoc]
      linarith
    calc
      _ ≤ (BandTail.w n d/(d:ℝ)^(1/4:ℝ))*(1+Real.log d) :=
        mul_le_mul_of_nonneg_right (BandTail.tailTerm n d d hd0 le_rfl) (by linarith)
      _ ≤ (BandTail.w n d/(d:ℝ)^(1/4:ℝ))*((ε/BandTail.universal)*(d:ℝ)^(1/4:ℝ)) :=
        mul_le_mul_of_nonneg_left hh (div_nonneg (BandTail.w_nonneg n d) hz.le)
      _ = _ := by field_simp
  have hu : ∑ d ∈ s, BandTail.w n d ≤ BandTail.universal := by
    apply le_trans _ (BandTail.uniformPrefix n (s.sup id))
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      exact mem_Icc.mpr ⟨hJ'.trans_le (hs d hd),le_sup (f:=id) hd⟩
    · intro d _ _
      exact BandTail.w_nonneg n d
  calc
    _ ≤ ∑ d ∈ s, (ε/BandTail.universal)*BandTail.w n d := sum_le_sum hbound
    _ = (ε/BandTail.universal)*(∑ d ∈ s,BandTail.w n d) := (mul_sum ..).symm
    _ ≤ (ε/BandTail.universal)*BandTail.universal := mul_le_mul_of_nonneg_left hu (by positivity)
    _ = _ := by field_simp

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel

open Finset Filter
open scoped Topology

private theorem harmonic_diff_boundary (n K X d : ℕ) :
    harmonicG n (X/d) - harmonicG n (K/d) -
      (harmonicG n X - harmonicG n K) =
      (harmonicG n K - harmonicG n (K/d)) -
      (harmonicG n X - harmonicG n (X/d)) := by ring

private theorem harmonic_diff_abs (n K X d : ℕ) :
    |harmonicG n (X/d) - harmonicG n (K/d) -
      (harmonicG n X - harmonicG n K)| ≤
      (harmonicG n K - harmonicG n (K/d)) +
      (harmonicG n X - harmonicG n (X/d)) := by
  rw [harmonic_diff_boundary]
  have hK := sub_nonneg.mpr (harmonicG_mono n (Nat.div_le_self K d))
  have hX := sub_nonneg.mpr (harmonicG_mono n (Nat.div_le_self X d))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem gAvg_nonneg (n X : ℕ) : 0 ≤ BandTail.gAvg n X := by
  unfold BandTail.gAvg BandTail.gSum
  exact div_nonneg (sum_nonneg fun k _ => (g_unit_interval n k).1) (by positivity)

theorem harmonic_convolution_lower (n K X J : ℕ) (hK : 0 < K) (hKX : K ≤ X)
    (hJX : J ≤ X) (e : ℝ)
    (hZ : (1/8 : ℝ) ≤ ∑ d ∈ Icc 1 X, BandTail.z n d)
    (hlog : (∑ d ∈ Ioc J X, |BandTail.z n d| * (1 + Real.log d)) ≤ e) :
    (1/8 : ℝ) * (harmonicG n X - harmonicG n K) -
      (J : ℝ) * BandTail.universal * (BandTail.gAvg n K + BandTail.gAvg n X) - 2*e ≤
      ∑ q ∈ Ioc K X, BandTail.F n q / (q:ℝ) := by
  let A := harmonicG n X - harmonicG n K
  let D (d : ℕ) := harmonicG n (X/d) - harmonicG n (K/d) - A
  let t := BandTail.gAvg n K + BandTail.gAvg n X
  have ht := add_nonneg (gAvg_nonneg n K) (gAvg_nonneg n X)
  have hpos := sub_nonneg.mpr (harmonicG_mono n hKX)
  have hlow (d : ℕ) : -(abs (BandTail.z n d) * abs (D d)) ≤ BandTail.z n d * D d := by
    rw [← abs_mul]
    exact neg_abs_le _
  have hsmall : -((J : ℝ) * BandTail.universal * t) ≤ ∑ d ∈ Icc 1 J, BandTail.z n d * D d := by
    have habs (d : ℕ) (hd : d ∈ Icc 1 J) : |D d| ≤ (J : ℝ) * t := by
      have hd0 := (mem_Icc.mp hd).1
      calc
        _ ≤ _ := harmonic_diff_abs n K X d
        _ ≤ (d : ℝ) * t := by
          dsimp [t]
          rw [mul_add]
          exact add_le_add (g_boundary_le_mean n K d hK hd0)
            (g_boundary_le_mean n X d (hK.trans_le hKX) hd0)
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (mem_Icc.mp hd).2) ht
    have hU : (∑ d ∈ Icc 1 J, |BandTail.z n d|) ≤ BandTail.universal := by
      simpa using BandTail.uniformTail n 1 (Icc 1 J) (by decide) (fun d hd => (mem_Icc.mp hd).1)
    calc
      _ = -(BandTail.universal * ((J : ℝ) * t)) := by ring
      _ ≤ -((∑ d ∈ Icc 1 J, |BandTail.z n d|) * ((J : ℝ) * t)) :=
        neg_le_neg (mul_le_mul_of_nonneg_right hU (mul_nonneg (Nat.cast_nonneg J) ht))
      _ = ∑ d ∈ Icc 1 J, -(|BandTail.z n d| * ((J : ℝ) * t)) := by rw [sum_neg_distrib, sum_mul]
      _ ≤ _ := sum_le_sum fun d hd =>
        (neg_le_neg (mul_le_mul_of_nonneg_left (habs d hd) (abs_nonneg _))).trans (hlow d)
  have hlarge : -(2*e) ≤ ∑ d ∈ Ioc J X, BandTail.z n d * D d := by
    have habs (d : ℕ) (hd : d ∈ Ioc J X) : |D d| ≤ 2 * (1 + Real.log d) := by
      have hd0 := (Nat.zero_le J).trans_lt (mem_Ioc.mp hd).1
      calc
        _ ≤ _ := harmonic_diff_abs n K X d
        _ ≤ (1 + Real.log d) + (1 + Real.log d) := by
          exact add_le_add (g_boundary_le_log n K d hd0) (g_boundary_le_log n X d hd0)
        _ = _ := by ring
    calc
      _ ≤ -(2*(∑ d ∈ Ioc J X, |BandTail.z n d| * (1 + Real.log d))) :=
        neg_le_neg (mul_le_mul_of_nonneg_left hlog (by norm_num))
      _ = ∑ d ∈ Ioc J X, -(|BandTail.z n d| * (2 * (1 + Real.log d))) := by
        rw [sum_neg_distrib, mul_sum]
        congr 1
        apply sum_congr rfl
        intro d _
        ring
      _ ≤ _ := sum_le_sum fun d hd =>
        (neg_le_neg (mul_le_mul_of_nonneg_left (habs d hd) (abs_nonneg _))).trans (hlow d)
  have hsplit := BandTail.prefix_split (fun d => BandTail.z n d * D d) hJX
  rw [harmonic_convolution_interval n K X hKX]
  have hrewrite : (∑ d ∈ Icc 1 X, BandTail.z n d *
      (harmonicG n (X/d) - harmonicG n (K/d))) =
      (∑ d ∈ Icc 1 X, BandTail.z n d) * A + ∑ d ∈ Icc 1 X, BandTail.z n d * D d := by
    rw [sum_mul, ←sum_add_distrib]
    apply sum_congr rfl
    intro d _
    dsimp [D]
    ring
  rw [hrewrite, hsplit]
  change (1/8 : ℝ) * A - (J : ℝ)*BandTail.universal*t - 2*e ≤ _
  linarith [mul_le_mul_of_nonneg_right hZ hpos]

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel

open Finset Filter
open scoped Topology

theorem harmonic_suffix_floor (ε : ℝ) (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ n X : ℕ, Even n → K ≤ X →
      -ε ≤ ∑ q ∈ Ioc K X, BandTail.F n q / (q:ℝ) := by
  obtain ⟨J,hJ⟩ := eventually_atTop.mp
    (correction_prefix_eighth.and (uniform_log_tail (ε/4) (by positivity)))
  obtain ⟨hJ₀,_⟩ := (hJ J le_rfl).1
  obtain ⟨m,hm⟩ := exists_nat_ge (16 * ((J:ℝ) * BandTail.universal))
  let L := m+1
  let T : ℕ := 2^L
  have hT : 0 < T := pow_pos (by decide) _
  have hC : (1:ℝ) ≤ 2*(T:ℝ) := by
    have ht' : (1:ℝ) ≤ T := by exact_mod_cast hT
    linarith
  have hL : (0:ℝ) < L := by exact_mod_cast (Nat.zero_lt_succ m)
  have hLJ : (J:ℝ)*BandTail.universal ≤ (L:ℝ)/16 := by
    change (J:ℝ)*BandTail.universal ≤ ((m+1:ℕ):ℝ)/16
    push_cast
    linarith
  let η := ε/(L:ℝ)
  have hη : 0 < η := div_pos hε hL
  have hLη : (L:ℝ)*η=ε := by dsimp [η]; field_simp
  obtain ⟨M,hM⟩ := eventually_atTop.mp (BandTail.mean_slow (2*(T:ℝ)) η hC hη)
  have hR : 1 ≤ T*T := Nat.mul_pos hT hT
  obtain ⟨N,hN⟩ := BandTail.uniform_prefix_floor (T*T) hR ε hε
  refine ⟨max J (max M N),?_⟩
  intro K hK₀ n X hn hKX
  have hJK : J ≤ K := (le_max_left J (max M N)).trans hK₀
  have hMK : M ≤ K := ((le_max_left M N).trans (le_max_right J (max M N))).trans hK₀
  have hNK : N ≤ K := ((le_max_right M N).trans (le_max_right J (max M N))).trans hK₀
  have hK : 0 < K := hJ₀.trans_le hJK
  have hKR : (0:ℝ)<K := by exact_mod_cast hK
  by_cases hnear : X ≤ (T*T)*K
  · have hh := BandTail.weighted_prefix_lower K X (BandTail.F n)
      (fun q => (q:ℝ)⁻¹) (ε*(K:ℝ)) hKX (by positivity)
      (fun i _ => by positivity)
      (fun i hi => by
        apply inv_anti₀
        · exact_mod_cast hK.trans_le hi
        · exact_mod_cast Nat.le_succ i)
      (fun i hi hiX => hN K hNK n i hi (hiX.trans hnear))
    have hEq : -(ε*(K:ℝ)*(K:ℝ)⁻¹) = -ε := by field_simp
    rw [hEq] at hh
    simpa [div_eq_mul_inv] using hh
  · let B := X/T
    have hfar : (T*T)*K ≤ X := le_of_lt (lt_of_not_ge hnear)
    have hKB : T*K ≤ B := by
      apply (Nat.le_div_iff_mul_le hT).2
      calc
        T*K*T = (T*T)*K := by ring
        _ ≤ X := hfar
    have hB : 0<B := (Nat.mul_pos hT hK).trans_le hKB
    have hBX : T*B ≤ X := Nat.mul_div_le X T
    have hXT : X ≤ 2*T*B := by
      have hmod := Nat.mod_lt X hT
      have hdiv : X % T + T * B = X := Nat.mod_add_div X T
      have hTB : T ≤ T*B := by
        simpa using Nat.mul_le_mul_left T (show 1≤B from hB)
      have he : 2*T*B=T*B+T*B := by ring
      rw [he]
      omega
    have hdT (j : ℕ) (hj : j≤L) : (2:ℕ)^j≤T := Nat.pow_le_pow_right (by decide) hj
    have hd1 (j : ℕ) : 1≤(2:ℕ)^j := pow_pos (by decide : 0<(2:ℕ)) j
    have hKm (j : ℕ) : K ≤ 2^j*K := by simpa using Nat.mul_le_mul_right K (hd1 j)
    have hBm (j : ℕ) : B ≤ 2^j*B := by simpa using Nat.mul_le_mul_right B (hd1 j)
    have hslowK (j : ℕ) (hj : j≤L) : |BandTail.gAvg n (2^j*K)-BandTail.gAvg n K| ≤ η := by
      apply hM (2^j*K) (hMK.trans (hKm j)) K hK (hKm j) _ n
      have hx : (2:ℕ)^j*K≤T*K := Nat.mul_le_mul_right K (hdT j hj)
      have hx' : (((2:ℕ)^j*K : ℕ):ℝ) ≤ (T:ℝ)*(K:ℝ) := by exact_mod_cast hx
      nlinarith [show (0:ℝ)≤(T:ℝ)*(K:ℝ) by positivity]
    have hslowX (j : ℕ) (hj : j≤L) : |BandTail.gAvg n (2^j*B)-BandTail.gAvg n X| ≤ η := by
      rw [abs_sub_comm]
      apply hM X (hMK.trans hKX) (2^j*B) (hB.trans_le (hBm j))
        ((Nat.mul_le_mul_right B (hdT j hj)).trans hBX) _ n
      have hXj : X ≤ 2*T*(2^j*B) := hXT.trans (Nat.mul_le_mul_left (2*T) (hBm j))
      exact_mod_cast hXj
    have hnearK := harmonic_dyadic_lower n (BandTail.gAvg n K) η L K hK hslowK
    have hnearX := harmonic_dyadic_lower n (BandTail.gAvg n X) η L B hB hslowX
    have hmid := harmonicG_mono n hKB
    have hlast := harmonicG_mono n hBX
    change (L:ℝ)*(BandTail.gAvg n K/2 - (3/2)*η) ≤ harmonicG n (T*K)-harmonicG n K at hnearK
    change (L:ℝ)*(BandTail.gAvg n X/2 - (3/2)*η) ≤ harmonicG n (T*B)-harmonicG n B at hnearX
    have hlong : ((L:ℝ)/2)*(BandTail.gAvg n K+BandTail.gAvg n X)-3*ε ≤
      harmonicG n X-harmonicG n K := by linarith
    have hJX := hJK.trans hKX
    have hZ := (hJ X hJX).1.2 n hn
    have hlog := (hJ J le_rfl).2.2 n (Ioc J X) (fun d hd => (mem_Ioc.mp hd).1.le)
    have hlower := harmonic_convolution_lower n K X J hK hKX hJX (ε/4) hZ hlog
    have hdom := mul_le_mul_of_nonneg_right hLJ
      (add_nonneg (gAvg_nonneg n K) (gAvg_nonneg n X))
    linarith

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel

open Finset

theorem coefficient_re_eq (n q : ℕ) (hq : 0 < q) :
    (GoldbachExplicitModeledMajor.coefficient q n).re = BandTail.F n q / (q:ℝ) := by
  have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  simp [BandTail.F,hqR]

/-- A monotone weight that is at most q/Q near the origin preserves the asymptotic
lower floor of the full initial Ramanujan sum. -/
theorem harmonic_tapered_prefix_floor (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, ∀ Q ≥ Q₀, ∀ n : ℕ, Even n → ∀ w : ℕ → ℝ, Monotone w →
      (∀ q, 0 ≤ w q) → w Q ≤ 2 →
      (∀ q ∈ Icc 1 Q, w q ≤ (q:ℝ)/(Q:ℝ)) →
      -ε ≤ ∑ q ∈ Icc 1 Q, (BandTail.F n q / (q:ℝ)) * w q := by
  have hδ : 0 < ε/4 := by positivity
  obtain ⟨K₀,hK₀⟩ := harmonic_suffix_floor (ε/4) hδ
  let K := max K₀ 1
  have hK₁ : 1 ≤ K := le_max_right _ _
  obtain ⟨M,hM⟩ := exists_nat_ge (2 * (BandTail.universal * (K:ℝ)) / ε)
  refine ⟨max K M, ?_⟩
  intro Q hQ n hn w hw hw₀ hwQ hweight
  have hKQ : K ≤ Q := (le_max_left _ _).trans hQ
  have hMQ : M ≤ Q := (le_max_right _ _).trans hQ
  have hQR : (0:ℝ) < Q := by exact_mod_cast hK₁.trans hKQ
  have hQM : 2 * (BandTail.universal * (K:ℝ)) / ε ≤ (Q:ℝ) :=
    hM.trans (by exact_mod_cast hMQ)
  have hcut : BandTail.universal * (K:ℝ) / (Q:ℝ) ≤ ε/2 := by
    have hs := (div_le_iff₀ hε).1 hQM
    apply (div_le_iff₀ hQR).2
    linarith
  have hterm (q : ℕ) (hq : q ∈ Icc 1 K) :
      -(|BandTail.F n q| / (Q:ℝ)) ≤ (BandTail.F n q / (q:ℝ)) * w q := by
    have hqR : (0:ℝ) < q := by exact_mod_cast (mem_Icc.mp hq).1
    have hh := hweight q ((Icc_subset_Icc_right hKQ) hq)
    calc
      _ = -((|BandTail.F n q| / (q:ℝ)) * ((q:ℝ)/(Q:ℝ))) := by field_simp
      _ ≤ -((|BandTail.F n q| / (q:ℝ)) * w q) :=
        neg_le_neg (mul_le_mul_of_nonneg_left hh (div_nonneg (abs_nonneg _) hqR.le))
      _ ≤ _ := by
        have he : |(BandTail.F n q / (q:ℝ)) * w q| =
            (|BandTail.F n q| / (q:ℝ)) * w q := by
          rw [abs_mul, abs_div, abs_of_pos hqR, abs_of_nonneg (hw₀ q)]
        rw [←he]
        exact neg_abs_le _
  have hsmall :
      -(ε/2) ≤ ∑ q ∈ Icc 1 K, (BandTail.F n q / (q:ℝ)) * w q := by
    calc
      _ ≤ -(BandTail.universal * (K:ℝ) / (Q:ℝ)) := neg_le_neg hcut
      _ ≤ -((∑ q ∈ Icc 1 K, |BandTail.F n q|) / (Q:ℝ)) :=
        neg_le_neg (div_le_div_of_nonneg_right (absolute_prefix_le n K) hQR.le)
      _ = ∑ q ∈ Icc 1 K, -(|BandTail.F n q| / (Q:ℝ)) := by
        rw [sum_neg_distrib, sum_div]
      _ ≤ _ := sum_le_sum hterm
  have hlen : K+(Q-K)=Q := Nat.add_sub_of_le hKQ
  have htail := weighted_suffix_lower (fun q => BandTail.F n q/(q:ℝ)) (ε/4) hδ.le
    (Q-K) K w hw (fun q _ => hw₀ q)
  rw [hlen] at htail
  have hrest := htail (fun k hk hkQ => hK₀ k ((le_max_left _ _).trans hk) n Q hn hkQ)
  have hrest' : -(ε/2) ≤ ∑ q ∈ Ioc K Q, (BandTail.F n q/(q:ℝ))*w q := by
    exact (by linarith [mul_le_mul_of_nonneg_left hwQ hδ.le] : -(ε/2) ≤ -(ε/4 * w Q)).trans hrest
  rw [BandTail.prefix_split (fun q => (BandTail.F n q/(q:ℝ))*w q) hKQ]
  linarith

end GoldbachGRHSignedModel

namespace GoldbachGRHSignedModel

open Finset

/-- Uniform lower floor for the two model sums after separating the common kernel
mass, the low-denominator taper, and a uniformly small truncation error. -/
theorem medium_model_floor (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, ∀ Q ≥ Q₀, ∀ n U : ℕ, Even n → Q ≤ U →
      ∀ mass defect : ℝ, mass ∈ Set.Icc 0 2 → 0 ≤ defect →
      defect * (BandTail.universal * (U:ℝ)) ≤ ε/4 →
      ∀ wide taper : ℕ → ℝ, Monotone taper → (∀ q, 0 ≤ taper q) → taper Q ≤ 2 →
      (∀ q ∈ Icc 1 Q, taper q ≤ (q:ℝ)/(Q:ℝ)) →
      (∀ q ∈ Icc 1 U, |wide q-mass| ≤ defect*(q:ℝ)) →
      -ε ≤ (∑ q ∈ Ioc Q U, (GoldbachExplicitModeledMajor.coefficient q n).re * wide q) +
        ∑ q ∈ Icc 1 Q, (GoldbachExplicitModeledMajor.coefficient q n).re *
          (wide q-mass+taper q) := by
  have hδ : 0 < ε/4 := by positivity
  obtain ⟨Q₁,hQ₁⟩ := harmonic_suffix_floor (ε/4) hδ
  obtain ⟨Q₂,hQ₂⟩ := harmonic_tapered_prefix_floor (ε/4) hδ
  refine ⟨max Q₁ Q₂,?_⟩
  intro Q hQ n U hn hQU mass defect hmass hdefect hcost wide taper hmono hnonneg
    hcap hscale hwide
  let a (q : ℕ) := (GoldbachExplicitModeledMajor.coefficient q n).re
  have hite (q : ℕ) (hq : q ∈ Ioc Q U) : 0 < q := (Nat.zero_le Q).trans_lt (mem_Ioc.mp hq).1
  have hlarge : -(ε/4) ≤ ∑ q ∈ Ioc Q U, a q := by
    have hh := hQ₁ Q ((le_max_left _ _).trans hQ) n U hn hQU
    refine hh.trans (le_of_eq (sum_congr rfl ?_))
    intro q hq
    exact (coefficient_re_eq n q (hite q hq)).symm
  have hmain : -(ε/2) ≤ (∑ q ∈ Ioc Q U, a q)*mass := by
    exact (by linarith [mul_le_mul_of_nonneg_left hmass.2 hδ.le] :
      -(ε/2) ≤ -(ε/4)*mass).trans (mul_le_mul_of_nonneg_right hlarge hmass.1)
  have hsmall : -(ε/4) ≤ ∑ q ∈ Icc 1 Q, a q*taper q := by
    have hh := hQ₂ Q ((le_max_right _ _).trans hQ) n hn taper hmono hnonneg hcap hscale
    refine hh.trans (le_of_eq (sum_congr rfl ?_))
    intro q hq
    exact congrArg (fun x : ℝ => x*taper q) (coefficient_re_eq n q (mem_Icc.mp hq).1).symm
  have herror : -(ε/4) ≤ ∑ q ∈ Icc 1 U, a q*(wide q-mass) := by
    have hterm (q : ℕ) (hq : q ∈ Icc 1 U) :
        -(defect*|BandTail.F n q|) ≤ a q*(wide q-mass) := by
      have hq0 := (mem_Icc.mp hq).1
      have hqR : (0:ℝ)<q := by exact_mod_cast hq0
      have hAbs : |a q*(wide q-mass)| ≤ defect*|BandTail.F n q| := by
        dsimp [a]
        rw [abs_mul, coefficient_re_eq n q hq0, abs_div, abs_of_pos hqR]
        calc
          _ ≤ (|BandTail.F n q|/(q:ℝ))*(defect*(q:ℝ)) :=
            mul_le_mul_of_nonneg_left (hwide q hq) (div_nonneg (abs_nonneg _) hqR.le)
          _ = _ := by field_simp
      exact (neg_le_neg hAbs).trans (neg_abs_le _)
    calc
      _ ≤ -(defect*(BandTail.universal*(U:ℝ))) := neg_le_neg hcost
      _ ≤ -(defect*(∑ q ∈ Icc 1 U, |BandTail.F n q|)) :=
        neg_le_neg (mul_le_mul_of_nonneg_left (absolute_prefix_le n U) hdefect)
      _ = ∑ q ∈ Icc 1 U, -(defect*|BandTail.F n q|) := by rw [sum_neg_distrib,mul_sum]
      _ ≤ _ := sum_le_sum hterm
  change -ε ≤ (∑ q ∈ Ioc Q U, a q * wide q) +
    ∑ q ∈ Icc 1 Q, a q * (wide q-mass+taper q)
  have H :
      (∑ q ∈ Ioc Q U, a q * wide q) =
        (∑ q ∈ Ioc Q U, a q)*mass + ∑ q ∈ Ioc Q U, a q*(wide q-mass) := by
    rw [sum_mul,←sum_add_distrib]
    apply sum_congr rfl
    intro q _
    ring
  have E := BandTail.prefix_split (fun q => a q*(wide q-mass)) hQU
  rw [H]
  simp only [mul_add,sum_add_distrib]
  linarith

end GoldbachGRHSignedModel

end GoldbachGRHSignedModel

section GoldbachGRHConcreteFloor

open Filter Finset MeasureTheory
open scoped Topology Interval Classical

namespace GoldbachGRHConcreteFloor

open GoldbachGRHBudget (narrow cutoff width)
open GoldbachGRHArcs (radius centers cell)
open GoldbachGRHKernel (mass)
open GoldbachExplicitModeledMajor (coefficient)

theorem eventually_narrow_ge (m : ℕ) : ∀ᶠ n : ℕ in atTop, m ≤ narrow n := by
  filter_upwards [eventually_ge_atTop (2^m : ℕ)] with n hn
  have h := Nat.le_log_of_pow_le (by decide : 1 < 2) (hn.trans (by omega : n≤n+2))
  have h₁ : 1 ≤ Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
  have h₂ := Nat.mul_le_mul_left (Nat.log 2 (n+2)) h₁
  exact h.trans (by simpa [narrow,pow_two] using h₂)

noncomputable def normalized (n T q : ℕ) : ℝ :=
  mass n (radius n T (max 1 q)) / (n:ℝ)

theorem normalized_loss (n T q : ℕ) (hn : 0 < n) (hT : 0 < T) (hbudget : 24*T≤n) :
    0 ≤ ((n:ℝ)+1)/(n:ℝ)-normalized n T q ∧
     ((n:ℝ)+1)/(n:ℝ)-normalized n T q ≤ (max 1 q:ℕ)/(2*(T:ℝ)) := by
  let r := radius n T (max 1 q)
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hTR : 0 < (T:ℝ) := by exact_mod_cast hT
  have hqR : (1:ℝ) ≤ (max 1 q:ℕ) := by exact_mod_cast le_max_left 1 q
  have hqpos : (0:ℝ) < ((max 1 q:ℕ):ℝ) := by linarith
  have hbn : 24*(T:ℝ) ≤ (n:ℝ) := by exact_mod_cast hbudget
  have hqp := mul_le_mul_of_nonneg_right hqR hnR.le
  have hr : 0 < r := by unfold r radius; positivity
  have hr' : r ≤ 1/2 := by
    apply (div_le_iff₀ (mul_pos hqpos hnR)).2
    nlinarith only [hqp,hbn,hTR]
  have hmass := GoldbachGRHKernel.mass_loss n hr hr'
  change 0 ≤ ((n:ℝ)+1)/(n:ℝ) - mass n r/(n:ℝ) ∧
    ((n:ℝ)+1)/(n:ℝ) - mass n r/(n:ℝ) ≤ _
  rw [← sub_div]
  constructor
  · exact div_nonneg hmass.1 hnR.le
  · calc
      _ ≤ (1/(2*r))/(n:ℝ) := div_le_div_of_nonneg_right hmass.2 hnR.le
      _ = _ := by
        unfold r radius
        field_simp [hnR.ne',hqpos.ne',hTR.ne']

end GoldbachGRHConcreteFloor
end GoldbachGRHConcreteFloor

namespace GoldbachGRHApproximation
open GoldbachFourthMoment (phase primeSum)
noncomputable def integrand (n : ℕ) (t : ℝ) : ℂ := primeSum n t ^ 2 * phase (-(n:ℝ)*t)
end GoldbachGRHApproximation

open Filter Finset MeasureTheory
open scoped Topology Interval Classical
namespace GoldbachLowSkirt7
open GoldbachGRHBudget (narrow cutoff width)
open GoldbachGRHArcs (cap)
open GoldbachGRHApproximation (integrand)
theorem eventually_narrow_ge (m : ℕ) : ∀ᶠ n : ℕ in atTop, m ≤ narrow n := by
  filter_upwards [eventually_ge_atTop (2^m : ℕ)] with n hn
  have h := Nat.le_log_of_pow_le (by decide : 1 < 2) (hn.trans (by omega : n≤n+2))
  have h₁ : 1 ≤ Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
  have h₂ := Nat.mul_le_mul_left (Nat.log 2 (n+2)) h₁
  exact h.trans (by simpa [narrow,pow_two] using h₂)
noncomputable def lowIntegral (n : ℕ) : ℂ :=
  ∫ t in (0:ℝ)..1,
    (cap n (narrow n) (width n) \ cap n (narrow n) (narrow n)).indicator (integrand n) t
end GoldbachLowSkirt7

/- The signed denominator floor and its application to the narrow modulus range
   are adapted from LogTruSoul, goldbach-proofs PR 2829, revision
   cfde193e18afc4e0ffac53868d514142e908cd36.  Here the upper width is
   independent of the cube-root cutoff and the statement is unconditional. -/
namespace GBInner
open Filter Finset MeasureTheory
open scoped Topology Interval Classical
open GoldbachGRHArcs (radius centers cell cap)
open GoldbachGRHConcreteFloor (normalized normalized_loss)
open GoldbachExplicitModeledMajor (coefficient)

theorem model_floor_at_width (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, ∀ (n Q H : ℕ), Q₀ ≤ Q → 1 ≤ Q → Q*Q ≤ H → 24*H ≤ n →
      Even n → -ε*(n:ℝ) ≤
      (∑ i ∈ centers Q, ∫ t in cell n Q H i,
        GoldbachGRHModel.model n i t^2 * GoldbachFourthMoment.phase (-(n:ℝ)*t)).re := by
  obtain ⟨R,hfloor⟩ := GoldbachGRHSignedModel.medium_model_floor ε hε
  obtain ⟨P,hP⟩ := exists_nat_ge (4*(|BandTail.universal|+1)/ε)
  refine ⟨max R P,?_⟩
  intro n Q H hQR hQ hwide hbudget hEven
  have hQ₀ := (le_max_left R P).trans hQR
  have hP' := (le_max_right R P).trans hQR
  have hbig : 4*(|BandTail.universal|+1)/ε ≤ (Q:ℝ) := hP.trans (by exact_mod_cast hP')
  have hn : 1 ≤ n := by nlinarith [Nat.mul_le_mul_left Q hQ]
  let full := ((n:ℝ)+1)/(n:ℝ)
  let d := 1/(2*(H:ℝ))
  let wide := normalized n H
  let taper (q : ℕ) := full - normalized n Q q
  have hn₀ : 0 < n := by omega
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn₀
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (show 1≤n by omega)
  have hQH : Q ≤ H := by nlinarith [Nat.mul_le_mul_left Q hQ]
  have hH₀ : 0 < H := hQ.trans hQH
  have hHn : H ≤ n := by omega
  have hH' : 0 < (H:ℝ) := by exact_mod_cast hH₀
  have hQ' : 0 < (Q:ℝ) := by exact_mod_cast hQ
  have hQbudget : 24*Q≤n := (Nat.mul_le_mul_left 24 hQH).trans hbudget
  have hfull : full ∈ Set.Icc 0 2 := ⟨by unfold full; positivity,
    (div_le_iff₀ hnR).2 (by linarith)⟩
  have hC : 0 ≤ BandTail.universal := (Real.exp_pos _).le
  have hcostLow : d*(BandTail.universal*(Q:ℝ)) ≤ ε/4 := by
    have threshold := (div_le_iff₀ hε).mp hbig
    have sq : (Q:ℝ)*(Q:ℝ) ≤ H := by exact_mod_cast hwide
    have smallQ : BandTail.universal ≤ (ε/2)*(Q:ℝ) := by linarith [le_abs_self BandTail.universal]
    have mult := mul_le_mul_of_nonneg_right smallQ hQ'.le
    have widthcost := mul_le_mul_of_nonneg_left sq hε.le
    unfold d
    rw [one_div_mul_eq_div,div_le_iff₀ (by positivity)]
    nlinarith only [mult,widthcost]
  have htaper : ∀ q, 0≤taper q := fun q =>
    (normalized_loss n Q q hn₀ hQ hQbudget).1
  have hmono : Monotone taper := by
    intro q r hqr
    apply sub_le_sub_left
    unfold normalized
    apply div_le_div_of_nonneg_right _ hnR.le
    apply GoldbachGRHKernel.mass_mono
    · unfold radius
      positivity
    · unfold radius
      apply div_le_div_of_nonneg_left (by positivity)
        (mul_pos (by exact_mod_cast (show 0 < max 1 q by omega)) hnR)
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast max_le_max (le_refl 1) hqr) hnR.le
  have htcap : taper Q≤2 := by
    have hnon : 0≤normalized n Q Q := by
      unfold normalized
      apply div_nonneg _ hnR.le
      exact GoldbachGRHKernel.mass_nonneg _ (by unfold radius; positivity)
    unfold taper
    linarith [hfull.2]
  have htbound : ∀ q∈Icc 1 Q, taper q ≤ (q:ℝ)/(Q:ℝ) := by
    intro q hq
    have hh := (normalized_loss n Q q hn₀ hQ hQbudget).2
    rw [max_eq_right (Finset.mem_Icc.mp hq).1] at hh
    exact hh.trans (div_le_div_of_nonneg_left (by positivity) hQ' (by linarith))
  have hwbound : ∀ q∈Icc 1 Q, |wide q-full|≤d*(q:ℝ) := by
    intro q hq
    obtain ⟨h₁,h₂⟩ := normalized_loss n H q hn₀ hH₀ hbudget
    rw [max_eq_right (Finset.mem_Icc.mp hq).1] at h₂
    change 0≤full-wide q at h₁
    change full-wide q ≤ _ at h₂
    rw [abs_sub_comm, abs_of_nonneg h₁]
    unfold d
    exact h₂.trans_eq (by ring)
  have hm := hfloor Q hQ₀ n Q hEven le_rfl full d hfull (by unfold d; positivity)
    hcostLow wide taper hmono htaper htcap htbound hwbound
  simp only [Finset.Ioc_self, Finset.sum_empty, zero_add] at hm
  rw [GoldbachGRHModelAssembly.sum_cell_model_re hQ hQH hHn]
  have hrew :
      (∑ q ∈ Icc 1 Q, (coefficient q n).re * GoldbachGRHModelAssembly.massDifference n Q H q)
      = (∑ q ∈ Icc 1 Q, (coefficient q n).re * (wide q-full+taper q)) * (n:ℝ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    obtain ⟨hqL,hqU⟩ := Finset.mem_Icc.mp hq
    simp only [GoldbachGRHModelAssembly.massDifference, ite_eq_left hqU, taper,
      wide, normalized, max_eq_right hqL]
    field_simp [hnR.ne']
    ring
  rw [hrew]
  exact mul_le_mul_of_nonneg_right hm hnR.le

end GBInner

namespace GBInner
open Finset MeasureTheory GoldbachGRHArcs
open GoldbachFourthMoment (phase primeSum)
open GoldbachGRHModel (model model_continuous)
open GoldbachGRHApproximation (integrand)
open scoped Interval
noncomputable section

def actual (n Q H : ℕ) := ∫ t in (0:ℝ)..1,
  (cap n Q H \ cap n Q Q).indicator (integrand n) t

def approx (n Q H : ℕ) := ∑ i ∈ centers Q, ∫ t in cell n Q H i,
  model n i t ^ 2 * phase (-(n:ℝ)*t)

def cellCost (n H q a : ℕ) : ℝ :=
  ∫ β in -(radius n H q)..(radius n H q), GoldbachMajorArc.Polylog.modelError n q a n β

theorem unit_agrees {q a : ℕ} (h : a.Coprime q) :
    GoldbachMajorArc.unitMean q a = (ArithmeticFunction.moebius q : ℂ)/(q.totient:ℂ) := by
  rw [GoldbachMajorArc.unitMean_eq_ram h,←GoldbachExplicitModeledMajor.ram_one_eq_moebius q]
  rfl

theorem kernel_agrees (n : ℕ) (t : ℝ) : GoldbachGRHKernel.kernel n t = GoldbachMajorArc.kernel n t := by
  rw [GoldbachGRHKernel.kernel_eq_sum]
  rfl

def loss (n : ℕ) (i : ℕ × ℕ) (t : ℝ) : ℂ :=
  integrand n t - model n i t ^ 2 * phase (-(n:ℝ)*t)

theorem continuous_integrand (n : ℕ) : Continuous (integrand n) := by
  unfold integrand primeSum phase
  fun_prop

theorem continuous_loss (n : ℕ) (i : ℕ×ℕ) : Continuous (loss n i) := by
  unfold loss
  apply (continuous_integrand n).sub
  apply ((model_continuous n i).pow 2).mul
  unfold phase
  fun_prop

theorem loss_at {i : ℕ×ℕ} (hi : i.2.Coprime i.1) (n : ℕ) (β : ℝ) :
    ‖loss n i (center i+β)‖ = GoldbachMajorArc.Polylog.modelError n i.1 i.2 n β := by
  simp only [loss,integrand,model,add_sub_cancel_left,kernel_agrees,
    GoldbachMajorArc.Polylog.modelError,unit_agrees hi]
  rfl

theorem cellCost_nonneg (n H q a : ℕ) : 0 ≤ cellCost n H q a := by
  have hr : 0 ≤ radius n H q := by unfold radius; positivity
  exact intervalIntegral.integral_nonneg (by linarith only [hr]) (fun _ _ => norm_nonneg _)

theorem cell_error {Q H n : ℕ} {i : ℕ×ℕ} (hi : i ∈ centers Q) :
    ‖∫ t in cell n Q H i, loss n i t‖ ≤ cellCost n H i.1 i.2 := by
  let r := radius n H i.1
  let c := center i
  have hr : 0 ≤ r := by dsimp [r,radius]; positivity
  have con := (continuous_loss n i).norm
  have integr : IntegrableOn (fun t => ‖loss n i t‖) (arc n H i) := by
    rw [arc_eq_Icc]
    exact con.integrableOn_Icc
  have subset : cell n Q H i ⊆ arc n H i := fun _ ht => ht.1.1
  have bound := setIntegral_mono_set integr (Filter.Eventually.of_forall (fun t => norm_nonneg (loss n i t)))
    (Filter.Eventually.of_forall subset)
  refine (norm_integral_le_integral_norm _).trans (bound.trans_eq ?_)
  rw [arc_eq_Icc,integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by dsimp only [c,r] at hr ⊢; linarith only [hr])]
  change (∫ t in c-r..c+r, ‖loss n i t‖) = _
  rw [show c-r = c+ -r by ring,←intervalIntegral.integral_comp_add_left]
  apply intervalIntegral.integral_congr
  intro β _
  exact loss_at (mem_centers.mp hi).2.2.2 n β

theorem all_cell_error {n Q H : ℕ} (hQH : Q ≤ H) (hbudget : 2*H*Q < n) :
    ‖actual n Q H - approx n Q H‖ ≤ GoldbachMajorArc.Polylog.totalArcError H n n := by
  let g i t := model n i t^2*phase (-(n:ℝ)*t)
  have hg i : Continuous (g i) := by
    apply ((model_continuous n i).pow 2).mul
    unfold phase
    fun_prop
  have eq i : (∫ t in cell n Q H i, integrand n t) - (∫ t in cell n Q H i,g i t) =
      ∫ t in cell n Q H i, loss n i t := by
    apply (integral_sub _ _).symm
    · exact ((continuous_integrand n).intervalIntegrable 0 1).1.mono_set Set.inter_subset_right
    · exact ((hg i).intervalIntegrable 0 1).1.mono_set Set.inter_subset_right
  rw [actual,integrate_difference_eq_sum le_rfl hQH hbudget _ (continuous_integrand n),approx,←sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ centers Q, ‖(∫ t in cell n Q H i, integrand n t)-(∫ t in cell n Q H i,g i t)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ centers Q, cellCost n H i.1 i.2 := sum_le_sum (fun i hi => by rw [eq i]; exact cell_error hi)
    _ ≤ ∑ q ∈ Icc 1 Q, ∑ a ∈ range (q+1), cellCost n H q a := by
      rw [sum_centers_eq]
      exact sum_le_sum (fun q _ => sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun a _ _ => cellCost_nonneg ..))
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hQH)
      (fun q _ _ => sum_nonneg (fun a _ => cellCost_nonneg ..))

end
end GBInner

namespace GBInner
open Filter Finset MeasureTheory
open scoped Topology
open GoldbachGRHBudget (narrow cutoff width)
open GoldbachGRHArcs (cap cap_mono measurable_cap)
open GoldbachGRHApproximation (integrand)
noncomputable section

def upper (b n : ℕ) := GoldbachMajorArc.Polylog.cutoff (b+4) n

theorem polylog_geometry (b : ℕ) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ narrow n ∧ narrow n*narrow n ≤ upper b n ∧
      24*upper b n ≤ n ∧ 2*upper b n*narrow n < n ∧ upper b n ≤ width n := by
  let p := b+4
  have hp : 0 < p := by dsimp [p]; omega
  have ht : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have slim := ((isLittleO_log_rpow_rpow_atTop (p:ℝ) (by norm_num : (0:ℝ)<1/3)).comp_tendsto ht).bound
      (by positivity : 0<(1/(2*4^p):ℝ))
  have van := ((isLittleO_log_rpow_rpow_atTop ((p+2:ℕ):ℝ) (by norm_num : (0:ℝ)<1)).comp_tendsto ht).bound
      (by positivity : 0<(1/(48*4^(p+2)):ℝ))
  filter_upwards [eventually_ge_atTop (2:ℕ),slim,van] with n hn hs hv
  have lp : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  let l := Nat.log 2 (n+2)
  have hl : 1 ≤ l := Nat.log_pos (by decide) (by omega : 2 ≤ n+2)
  have hq : 1 ≤ narrow n := one_le_pow₀ hl
  have hlow : narrow n*narrow n ≤ upper b n := by
    change l^2*l^2 ≤ l^p
    rw [←pow_add]
    exact Nat.pow_le_pow_right hl (by dsimp [p]; omega)
  have hH : (upper b n:ℝ) ≤ (4*Real.log n)^p := GoldbachMajorArc.Polylog.cutoff_le_log p hn
  have root : (upper b n:ℝ) ≤ (n:ℝ)^(1/3:ℝ) := by
    change ‖(Real.log (n:ℝ))^(p:ℝ)‖ ≤ _ * ‖(n:ℝ)^(1/3:ℝ)‖ at hs
    rw [Real.rpow_natCast,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg lp _),Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at hs
    rw [mul_pow] at hH
    have m := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ 4^p)
    calc
      _ ≤ _ := hH.trans m
      _ = (n:ℝ)^(1/3:ℝ)/2 := by field_simp <;> ring
      _ ≤ _ := by linarith [Real.rpow_nonneg (Nat.cast_nonneg n) (1/3:ℝ)]
  have hU : upper b n ≤ cutoff n := (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr root
  have hh : 48*(upper b n*narrow n) ≤ n := by
    have cmp := GoldbachMajorArc.Polylog.cutoff_le_log (p+2) hn
    change ((l^(p+2):ℕ):ℝ) ≤ _ at cmp
    have id : upper b n*narrow n = l^(p+2) := (pow_add l p 2).symm
    change ‖(Real.log (n:ℝ))^((p+2:ℕ):ℝ)‖ ≤ _*‖(n:ℝ)^(1:ℝ)‖ at hv
    rw [Real.rpow_natCast,Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg lp _),
      Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg n)] at hv
    rw [mul_pow] at cmp
    have m := mul_le_mul_of_nonneg_left hv (by positivity : (0:ℝ) ≤ 4^(p+2))
    have e : (4:ℝ)^(p+2)*(1/(48*4^(p+2))*(n:ℝ)) = (n:ℝ)/48 := by field_simp <;> ring
    have v := cmp.trans (m.trans_eq e)
    rw [id]
    exact_mod_cast (show (48:ℝ)*((l^(p+2):ℕ):ℝ) ≤ (n:ℝ) by linarith only [v])
  have qpos : 0<narrow n := hq
  have Hpos : 0<upper b n := (Nat.mul_pos qpos qpos).trans_le hlow
  obtain ⟨hHn,hd⟩ : 24*upper b n ≤ n ∧ 2*upper b n*narrow n<n := by
    have t := Nat.mul_le_mul_left (upper b n) hq
    simp only [mul_one] at t
    rw [Nat.mul_assoc]
    omega
  exact ⟨hq,hlow,hHn,hd,hU.trans (GoldbachGRHBudget.width_ge_cutoff n hq)⟩

theorem inner_floor (b : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      -(ε*(n:ℝ)) ≤ (actual n (narrow n) (upper b n)).re := by
  obtain ⟨Q₀,hm⟩ := model_floor_at_width (ε/2) (by positivity)
  apply eventually_atTop.mp
  filter_upwards [polylog_geometry b, GoldbachLowSkirt7.eventually_narrow_ge Q₀,
    GoldbachMajorArc.Polylog.eventually_totalArcError_lt (b+4) 0 (by omega) (ε:=ε/2) (by positivity)]
    with n geom hQ hE
  intro even
  obtain ⟨qpos,hwide,hHn,hd,_⟩ := geom
  have qsq : narrow n ≤ narrow n*narrow n := by simpa using Nat.mul_le_mul_left (narrow n) qpos
  have qH := qsq.trans hwide
  have comp := all_cell_error qH hd
  have e := hE n
  simp only [pow_zero,one_mul] at e
  have model := hm n (narrow n) (upper b n) hQ qpos hwide hHn even
  change - (ε/2)*(n:ℝ) ≤ (approx n (narrow n) (upper b n)).re at model
  have d := Complex.re_le_norm (approx n (narrow n) (upper b n) - actual n (narrow n) (upper b n))
  rw [norm_sub_rev,Complex.sub_re] at d
  change _ < ε/2*(n:ℝ) at e
  change _ ≤ GoldbachMajorArc.Polylog.totalArcError (GoldbachMajorArc.Polylog.cutoff (b+4) n) n n at comp
  linarith

end
end GBInner

namespace GBInner
open Filter Finset MeasureTheory
open scoped Topology
open GoldbachGRHBudget (narrow width)
open GoldbachGRHArcs (cap cap_mono measurable_cap)
open GoldbachGRHApproximation (integrand)
noncomputable section

def outer (b n : ℕ) := ∫ t in (0:ℝ)..1,
    (cap n (narrow n) (width n) \ cap n (narrow n) (upper b n)).indicator (integrand n) t

theorem split (b : ℕ) : ∀ᶠ n : ℕ in atTop,
    GoldbachLowSkirt7.lowIntegral n = actual n (narrow n) (upper b n) + outer b n := by
  filter_upwards [polylog_geometry b] with n h
  obtain ⟨hp,hl,_,_,hH⟩ := h
  let A := cap n (narrow n) (narrow n)
  let B := cap n (narrow n) (upper b n)
  let C := cap n (narrow n) (width n)
  have qsq : narrow n ≤ narrow n*narrow n := by simpa using Nat.mul_le_mul_left (narrow n) hp
  have hAB : A ⊆ B := cap_mono le_rfl (qsq.trans hl)
  have hBC : B ⊆ C := cap_mono le_rfl hH
  have hI := (continuous_integrand n).intervalIntegrable (μ:=volume) 0 1
  have hF : (C \ A).indicator (integrand n) =
      fun t => (B \ A).indicator (integrand n) t + (C \ B).indicator (integrand n) t := by
    funext t
    by_cases a : t ∈ A
    · have b := hAB a
      simp [Set.indicator,Set.mem_diff,a,b]
    · by_cases b : t ∈ B
      · have c := hBC b
        simp [Set.indicator,Set.mem_diff,a,b,c]
      · by_cases c : t ∈ C <;> simp [Set.indicator,Set.mem_diff,a,b,c]
  unfold GoldbachLowSkirt7.lowIntegral actual outer
  change (∫ t in (0:ℝ)..1, (C\A).indicator (integrand n) t) = _
  rw [hF]
  apply intervalIntegral.integral_add
  · apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
    exact hI.1.indicator ((measurable_cap ..).diff (measurable_cap ..))
  · apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
    exact hI.1.indicator ((measurable_cap ..).diff (measurable_cap ..))

theorem suffices_outer (b : ℕ)
    (hout : ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      -(ε*(n:ℝ)) ≤ (outer b n).re) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      -(ε*(n:ℝ)) ≤ (GoldbachLowSkirt7.lowIntegral n).re := by
  intro ε he
  obtain ⟨N,hN⟩ := inner_floor b (ε/2) (by positivity)
  obtain ⟨M,hM⟩ := hout (ε/2) (by positivity)
  apply eventually_atTop.mp
  filter_upwards [split b,eventually_ge_atTop N,eventually_ge_atTop M] with n h hn hm
  intro par
  rw [h,Complex.add_re]
  linarith only [hN n hn par,hM n hm par]

end
end GBInner

theorem Conjectures.Goldbach.LowSkirtPolylogInner :
∀ b : ℕ, let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let H := fun n : ℕ => (Nat.log 2 (n+2))^(b+4); let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowSkirt := fun n : ℕ => intervalIntegral (fun t => (lowWideArcs n \ arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (lowSkirt n).re := by
  intro b
  exact GBInner.inner_floor b
