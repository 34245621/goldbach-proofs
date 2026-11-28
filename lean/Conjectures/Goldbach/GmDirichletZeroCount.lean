import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Log
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Algebra.InfiniteSum.Field
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Monotone

namespace Conjectures.Goldbach.GmDirichletZeroCountAux

/-!
Unconditional explicit Riemann-von Mangoldt zero-count bound for N(T) when T >= 3.
High-height (100 <= T) argument adapted from Garald1/RSBounds (commit 82d7a55f, Apache-2.0)
via senamakel/schoenfeld-rh (commit 0d24a0c5) and PR 5097 (Taskf355ec8ae439e1460fa4ce50),
combined with the main-term and critical-strip assembly from PR 4914 (Cutd13e05c9a1ea668b77ce8945),
and extended down to 3 <= T < 100 via a 5-piece circle-majorant bound from norm_zetaF_le.
-/
/-
Source acknowledgements

Authors: OpenAI
Authors: Terence Tao
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Copyright (c) 2026. All rights reserved.

Adapted from Garald1/RSBounds at commit 82d7a55f02e52cd071cd8ed800cc889a23ad3e61, through the vendored copy in senamakel/schoenfeld-rh at 0d24a0c5eac14301655ed2c65163404560e07892.
The Euler constant estimate in the high-height argument uses a trapezoidal harmonic bound at sixteen.
RSBounds and the indicated Apache-licensed sources are distributed under Apache License 2.0. See the repository LICENSE.

Ternary Goldbach project
Copyright 2026 Charlie Reams

A formalization of H. A. Helfgott's proof of the ternary Goldbach conjecture
(H. A. Helfgott, “The ternary Goldbach problem”, arXiv:1501.05438).
Canonical repository: https://github.com/calr3/ternary-goldbach

TernaryGoldbach/Prelim/PNTMertens.lean is derived from the PrimeNumberTheoremAnd
project (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd), licensed under
the Apache License 2.0.

MIT License

Copyright (c) 2026 Charlie Reams and Harald Helfgott

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the “Software”), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

The original MIT and Apache-2.0 legal notices and full adaptation history can also be read at
https://github.com/senamakel/schoenfeld-rh/tree/0d24a0c5eac14301655ed2c65163404560e07892/Vendor/Rosser/licenses
-/

-- RSBounds.BacklundCircleMajorantDef
section
namespace TernaryGoldbach.RSBounds.BacklundCircleMajorant

noncomputable def radius : ℝ := 33 / 25

noncomputable def scalar (H L V σ : ℝ) : ℝ :=
  if 5 / 4 ≤ σ then Real.log ‖riemannZeta (σ : ℂ)‖
  else H + L / 2 * (max (1 - σ) 0 + max (-σ) 0) +
    if 0 ≤ σ ∧ σ < 1 then V else 0

noncomputable def heightLog (T : ℝ) : ℝ := Real.log (Real.log (T + radius))
noncomputable def powerLog (T : ℝ) : ℝ := Real.log ((T + radius) / (2 * Real.pi))
noncomputable def stripLog (T : ℝ) : ℝ :=
  Real.log ((T - radius) ^ 2 / ((T - radius) ^ 2 - 4))

noncomputable def majorant (T : ℝ) (z : ℂ) : ℝ :=
  scalar (heightLog T) (powerLog T) (stripLog T) z.re

end TernaryGoldbach.RSBounds.BacklundCircleMajorant
end

-- TernaryGoldbach.Prelim.PNTMertens
section
section EulerMaclaurin

open Finset Interval MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2

lemma abs_B1_le_half {x : ℝ} (hx : 0 ≤ x) : |B1 x| ≤ 1 / 2 := by
  unfold B1
  refine abs_le.mpr ⟨?_, ?_⟩
  · grind [Nat.floor_le hx]
  · grind [Nat.lt_succ_floor x]

lemma integral_deriv_mul_add_const (c : 𝕜) (hab : a ≤ b) (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
    ∫ t in a..b, (t + c) * deriv f t = (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have : ∀ t ∈ [[a, b]], HasDerivAt (fun (t : ℝ) ↦ t + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    convert! ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K := 𝕜)) using 1
    simp
  replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul this hf_diff (by simp) h_int]
  simp

lemma intervalIntegrable_deriv_mul_B1 (ha : 0 ≤ a) (hab : a ≤ b) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    IntervalIntegrable (fun t ↦ deriv f t * B1 t) volume a b := by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp) (by unfold B1; fun_prop) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
  norm_cast
  exact abs_B1_le_half (by linarith)

lemma integral_deriv_mul_floor_add_one (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∫ t in a..b, deriv f t * (⌊t⌋₊ + 1) = (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t) - ∫ t in a..b, deriv f t * B1 t := by
  calc
  _ = ∫ t in a..b, (deriv f t * (t + 1 / 2) -deriv f t * B1 t) := by
    congr
    ext
    simp only [B1]
    push_cast
    ring
  _ = (∫ t in a..b, deriv f t * (t + 1 / 2)) - ∫ t in a..b, deriv f t * B1 t := by
    exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop)) (intervalIntegrable_deriv_mul_B1 ha hab h_cont)
  _ = _ := by
    conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
    rw [integral_deriv_mul_add_const _ hab h_cont.intervalIntegrable hf_diff]

theorem sum_eq_integral_add_integral_deriv (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) + ∫ t in a..b, deriv f t * B1 t  := by
  have := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at this
  rw [this, ← intervalIntegral.integral_of_le hab]
  rw [integral_deriv_mul_floor_add_one ha hab hf_diff h_cont]
  unfold B1
  push_cast
  ring

end EulerMaclaurin

section Issue1584
open MeasureTheory Set Filter Topology

end Issue1584

namespace TernaryGoldbach.PNTMertens

open Real Finset Filter Asymptotics Topology
open ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa

theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]

theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

theorem sum_mangoldt_div_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d = log x + E₁Λ x := by
    grind

theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring

theorem sum_mangoldt_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x| ≤ log 4 + 4 := by
  grind [E₁Λ.le hx, E₁Λ.ge hx, log_nonneg]

theorem E₁Λ.bounded' : ∃ c > 0, ∀ x ≥ 1, |E₁Λ x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun x hx ↦ sum_mangoldt_div_eq_log hx⟩

noncomputable abbrev E₁p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]

noncomputable abbrev E₁ : ℝ := ∑' p : ℕ, if p.Prime then (log p) / (p*(p-1)) else 0

lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp; linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all; linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! summable_nat_add_iff 1|>.mpr this using 2
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq

theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast; ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]

noncomputable abbrev γ : ℝ := (∫ t in Set.Ioi 2, E₁Λ t / (t * log t^2)) + 1 - log (log 2)

noncomputable abbrev E₂Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ

lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa

private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! this.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

theorem integrable_E₁Λ_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁Λ x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁Λ.bounded'
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · have hd : Measurable (fun n : ℕ => ∑ d ∈ Ioc 0 n, (Λ d) / (d : ℝ)) := measurable_from_top
    have hn : Measurable (fun x : ℝ => ⌊x⌋₊) := by fun_prop
    have he : Measurable E₁Λ := (hd.comp hn).sub Real.measurable_log
    exact (he.div (by fun_prop)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)

theorem E₂Λ.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂Λ x = E₁Λ x / log x - ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) := by
  unfold E₂Λ
  rw [← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp)]
  conv => lhs; arg 1; arg 1; arg 2; ext n; rw [(by field : Λ n / (n * log n) = (Λ n / n) / log n)]
  rw [sum_div_log_eq hx]
  rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, Λ n / n) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁Λ t / (t * log t ^ 2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold γ
    calc
    _ = E₁Λ x / log x + (∫ (x : ℝ) in 2..x, E₁Λ x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁Λ t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁Λ_div_mul_log_sq (by rfl)) (integrable_E₁Λ_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁Λ_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp

theorem E₂Λ.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂Λ.eq hx, abs_le']
    constructor
    · grw [E₁Λ.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≥ - 2 / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2) hx)
            (integrable_E₁Λ_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2) hx
      grw [this]
      grind
    grw [E₁Λ.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁Λ_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind

theorem log_zeta_eq_sum (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = ∑' n, Λ n / (n^s * log n) := by
  have hsc : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs

  have hep := riemannZeta_eulerProduct_exp_log (s := (s : ℂ)) hsc
  set S : ℂ := ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) with hS

  have hcpow : ∀ p : Nat.Primes, (p : ℂ) ^ (-(s : ℂ)) = (((p : ℝ) ^ (-s) : ℝ) : ℂ) := by
    intro p
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf

  set z : Nat.Primes → ℝ := fun p => (p : ℝ) ^ (-s) with hz

  have hz_pos : ∀ p : Nat.Primes, 0 < z p := fun p => by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
    positivity
  have hz_lt_one : ∀ p : Nat.Primes, z p < 1 := by
    intro p
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    change (p : ℝ) ^ (-s) < 1
    rw [Real.rpow_neg (by positivity), inv_lt_one_iff₀]
    right
    exact (Real.one_lt_rpow_iff_of_pos (by positivity)).mpr (Or.inl ⟨hp1, by linarith⟩)

  have hterm : ∀ p : Nat.Primes,
      -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) = ((-Real.log (1 - z p) : ℝ) : ℂ) := by
    intro p
    rw [hcpow p]
    have h1z : (0 : ℝ) < 1 - z p := by have := hz_lt_one p; linarith
    rw [show (1 : ℂ) - ((z p : ℝ) : ℂ) = (((1 - z p : ℝ)) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_log h1z.le]
    push_cast; ring

  set Sr : ℝ := ∑' p : Nat.Primes, -Real.log (1 - z p) with hSr
  have hSeq : S = (Sr : ℂ) := by
    rw [hS, hSr, Complex.ofReal_tsum]
    exact tsum_congr hterm
  have hSim : S.im = 0 := by rw [hSeq]; exact Complex.ofReal_im _
  have hSre : S.re = Sr := by rw [hSeq]; exact Complex.ofReal_re _

  have hlog_zeta : Complex.log (riemannZeta (s : ℂ)) = S := by
    rw [← hep, Complex.log_exp (by rw [hSim]; exact neg_lt_zero.mpr Real.pi_pos)
      (by rw [hSim]; exact Real.pi_pos.le)]

  have hkey : Real.log (riemannZeta (s : ℂ)).re = Sr := by
    have hζim : (riemannZeta (s : ℂ)).im = 0 := riemannZeta_im_eq_zero_of_one_lt hs
    have hζeq : riemannZeta (s : ℂ) = ((riemannZeta (s : ℂ)).re : ℂ) := by
      apply Complex.ext <;> simp [hζim]
    have : Real.log (riemannZeta (s : ℂ)).re
        = (Complex.log (riemannZeta (s : ℂ))).re := by
      conv_rhs => rw [hζeq]
      rw [Complex.log_ofReal_re]
    rw [this, hlog_zeta, hSre]
  rw [hkey]

  have habs : ∀ p : Nat.Primes, |z p| < 1 := by
    intro p
    rw [abs_of_pos (hz_pos p)]; exact hz_lt_one p
  have htaylor : ∀ p : Nat.Primes,
      HasSum (fun n : ℕ => (z p) ^ (n + 1) / (n + 1)) (-Real.log (1 - z p)) :=
    fun p => hasSum_pow_div_log_of_abs_lt_one (habs p)
  have hSr_double : Sr = ∑' (p : Nat.Primes) (n : ℕ), (z p) ^ (n + 1) / (n + 1) := by
    rw [hSr]
    exact tsum_congr fun p => ((htaylor p).tsum_eq).symm

  have hsummable_z : Summable z := Nat.Primes.summable_rpow.mpr (by linarith)

  have hsummable_prime : Summable (fun p : Nat.Primes => -Real.log (1 - z p)) := by
    have := Real.summable_log_one_add_of_summable hsummable_z.neg
    convert! this.neg using 1

  have hg_nonneg : ∀ pk : Nat.Primes × ℕ, 0 ≤ (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1) := by
    intro pk; positivity [hz_pos pk.1]
  have hsummable_g : Summable (fun pk : Nat.Primes × ℕ => (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1)) := by
    rw [summable_prod_of_nonneg hg_nonneg]
    refine ⟨fun p => (htaylor p).summable, ?_⟩
    refine hsummable_prime.congr (fun p => ?_)
    exact ((htaylor p).tsum_eq).symm

  have hpoint : ∀ (p : Nat.Primes) (n : ℕ),
      Λ ((p : ℕ) ^ (n + 1)) /
        ((((p : ℕ) ^ (n + 1) : ℕ) : ℝ) ^ s * Real.log (((p : ℕ) ^ (n + 1) : ℕ) : ℝ))
      = (z p) ^ (n + 1) / (n + 1) := by
    intro p n
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
    rw [vonMangoldt_apply_pow (Nat.succ_ne_zero n), vonMangoldt_apply_prime p.prop]
    have hcast : (((p : ℕ) ^ (n + 1) : ℕ) : ℝ) = (p : ℝ) ^ (n + 1) := by push_cast; ring
    rw [hcast, Real.log_pow]
    rw [show (z p) ^ (n + 1) = ((p : ℝ) ^ (n + 1)) ^ (-s) by
      rw [hz]; rw [← Real.rpow_natCast ((p : ℝ) ^ (-s)) (n + 1),
        ← Real.rpow_natCast ((p : ℝ)) (n + 1), ← Real.rpow_mul (by positivity),
        ← Real.rpow_mul (by positivity)]; ring_nf]
    rw [Real.rpow_neg (by positivity)]
    field_simp
    push_cast
    ring

  set F : ℕ → ℝ := fun n => Λ n / ((n : ℝ) ^ s * Real.log n) with hF

  have hsupp : Function.support F ⊆ {n : ℕ | IsPrimePow n} := by
    intro n hn
    rw [Function.mem_support] at hn
    simp only [Set.mem_ofPred_eq]
    by_contra hpp
    apply hn
    simp only [hF, vonMangoldt_eq_zero_iff.mpr hpp, zero_div]

  have hprod_eq : (∑' pk : Nat.Primes × ℕ, (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1))
      = ∑' m : {n : ℕ // IsPrimePow n}, F m.val := by
    rw [← Equiv.tsum_eq Nat.Primes.prodNatEquiv (fun m : {n : ℕ // IsPrimePow n} => F m.val)]
    apply tsum_congr
    intro pk
    rw [Nat.Primes.coe_prodNatEquiv_apply, hF]
    exact (hpoint pk.1 pk.2).symm

  rw [hSr_double, ← hsummable_g.tsum_prod' (fun p => (htaylor p).summable), hprod_eq]
  exact tsum_subtype_eq_of_support_subset hsupp

section
open MeasureTheory Set

namespace LogZetaInteg

private noncomputable def c (d : ℕ) : ℝ := Λ d / (d * Real.log d)

private noncomputable def f (s : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
    c d * (Set.Ici (d:ℝ)).indicator (fun x => x ^ (-s)) x

@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]

end LogZetaInteg
end

section
open MeasureTheory Set

end

end TernaryGoldbach.PNTMertens
end

-- RSBounds.BacklundCenter
section
open Complex Filter
open scoped Topology

namespace TernaryGoldbach.RSBounds

private theorem center_factor_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    {z : ℂ} (hz : ‖z‖ = a) :
    ‖(1 - (a : ℂ) ^ 2)⁻¹‖ ≤
      ‖(1 - (a : ℂ))⁻¹‖ * ‖(1 - z)⁻¹‖ := by
  have h1 : 0 < 1 - a := sub_pos.mpr ha1
  have h2 : 0 < 1 - a ^ 2 := by nlinarith
  have hz1 : 0 < ‖(1 : ℂ) - z‖ := by
    apply norm_pos_iff.mpr
    intro h
    have he : z = 1 := (sub_eq_zero.mp h).symm
    have : a = 1 := by simpa [he] using hz.symm
    linarith
  have htri : ‖(1 : ℂ) - z‖ ≤ 1 + a := by
    simpa only [norm_one, hz] using norm_sub_le (1 : ℂ) z
  have hreal1 : ‖(1 : ℂ) - (a : ℂ)‖ = 1 - a := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_of_nonneg h1.le]
  have hreal2 : ‖(1 : ℂ) - (a : ℂ) ^ 2‖ = 1 - a ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_of_nonneg h2.le]
  rw [norm_inv, norm_inv, norm_inv, hreal1, hreal2, ← mul_inv]
  apply (inv_le_inv₀ h2 (mul_pos h1 hz1)).mpr
  nlinarith [mul_le_mul_of_nonneg_left htri h1.le]

theorem zeta_norm_lower_euler_ratio {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta ((2 * s.re : ℝ) : ℂ)‖ / ‖riemannZeta (s.re : ℂ)‖ ≤
      ‖riemannZeta s‖ := by
  have hσ : 1 < ((s.re : ℂ)).re := by simpa using hs
  have h2σ : 1 < (((2 * s.re : ℝ) : ℂ)).re := by simpa using (show 1 < 2 * s.re by linarith)
  have hprod := (riemannZeta_eulerProduct_hasProd hσ).norm.mul
    (riemannZeta_eulerProduct_hasProd hs).norm
  have hprod2 := (riemannZeta_eulerProduct_hasProd h2σ).norm
  have hfactor (p : Nat.Primes) :
      ‖(1 - (p : ℂ) ^ (-((2 * s.re : ℝ) : ℂ)))⁻¹‖ ≤
        ‖(1 - (p : ℂ) ^ (-(s.re : ℂ)))⁻¹‖ *
          ‖(1 - (p : ℂ) ^ (-s))⁻¹‖ := by
    have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    have hp0 : 0 < (p : ℝ) := by linarith
    let a : ℝ := (p : ℝ) ^ (-s.re)
    have ha : 0 ≤ a := Real.rpow_nonneg hp0.le _
    have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
    have hpow : (p : ℂ) ^ (-(s.re : ℂ)) = (a : ℂ) := by
      simpa only [a, Complex.ofReal_neg, Complex.ofReal_natCast] using
        (Complex.ofReal_cpow hp0.le (-s.re)).symm
    have hpow2 : (p : ℂ) ^ (-((2 * s.re : ℝ) : ℂ)) = (a : ℂ) ^ 2 := by
      rw [show -((2 * s.re : ℝ) : ℂ) = -(s.re : ℂ) * (2 : ℕ) by push_cast; ring,
        Complex.cpow_mul_nat, hpow]
    have hz : ‖(p : ℂ) ^ (-s)‖ = a := by
      simpa only [a, Complex.neg_re, Complex.ofReal_natCast] using
        Complex.norm_cpow_eq_rpow_re_of_pos hp0 (-s)
    rw [hpow, hpow2]
    exact center_factor_le ha ha1 hz
  have hlim : ‖riemannZeta ((2 * s.re : ℝ) : ℂ)‖ ≤
      ‖riemannZeta (s.re : ℂ)‖ * ‖riemannZeta s‖ := by
    apply le_of_tendsto_of_tendsto' hprod2 hprod
    intro S
    exact Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) (fun p _ => hfactor p)
  have hζ : 0 < ‖riemannZeta (s.re : ℂ)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hσ)
  exact (div_le_iff₀ hζ).mpr (by simpa only [mul_comm] using hlim)

theorem zeta_norm_lower_five_fourths_ratio (T : ℝ) :
    ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ / ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ ≤
      ‖riemannZeta (((5 / 4 : ℝ) : ℂ) + T * Complex.I)‖ := by
  have h := zeta_norm_lower_euler_ratio
    (s := ((5 / 4 : ℝ) : ℂ) + T * Complex.I) (by simp; norm_num)
  norm_num at h ⊢
  exact h

end TernaryGoldbach.RSBounds
end

-- RSBounds.BacklundCenterNumericsBase
section
open scoped BigOperators
open Finset MeasureTheory

namespace TernaryGoldbach.RSBounds.CenterNumerics

theorem norm_zeta_eq_tsum_rpow {σ : ℝ} (hσ : 1 < σ) :
    ‖riemannZeta (σ : ℂ)‖ = ∑' n : ℕ, (n : ℝ) ^ (-σ) := by
  have hc : riemannZeta (σ : ℂ) =
      Complex.ofReal (∑' n : ℕ, (n : ℝ) ^ (-σ)) := by
    rw [zeta_eq_tsum_one_div_nat_cpow (by simpa using hσ), Complex.ofReal_tsum]
    congr 1
    funext n
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_neg,
      Complex.ofReal_natCast, Complex.cpow_neg, one_div]
  rw [hc, Complex.norm_of_nonneg (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))]

noncomputable def rpowSum (σ : ℝ) (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => (n : ℝ) ^ (-σ) + rpowSum σ (n + 1) m

theorem rpowSum_eq (σ : ℝ) (n m : ℕ) :
    rpowSum σ n m = ∑ j ∈ Finset.range m, ((j + n : ℕ) : ℝ) ^ (-σ) := by
  induction m generalizing n with
  | zero => simp [rpowSum]
  | succ m ih =>
    simp [rpowSum, Finset.sum_range_succ', ih, Nat.add_assoc, add_comm, add_left_comm]

theorem zeta_tail_upper {σ : ℝ} (hσ : 1 < σ) {N : ℕ} (hN : 0 < N) :
    ‖riemannZeta (σ : ℂ)‖ ≤
      rpowSum σ 1 N + (N : ℝ) ^ (1 - σ) / (σ - 1) := by
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have anti : AntitoneOn (fun t : ℝ => t ^ (-σ)) (Set.Ici (N : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hN'.trans_le hx) hxy (by linarith)
  have ht := anti.tsum_comp_add_le_integral N
    (integrableOn_Ioi_rpow_of_lt (by linarith : -σ < -1) hN')
    (fun t ht => Real.rpow_nonneg (le_of_lt (hN'.trans ht)) _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -σ < -1) hN'] at ht
  have htail : (∑' n : ℕ, ((n + N + 1 : ℕ) : ℝ) ^ (-σ)) ≤
      (N : ℝ) ^ (1 - σ) / (σ - 1) := by
    convert ht using 1
    rw [show -σ + 1 = 1 - σ by ring, show σ - 1 = -(1 - σ) by ring,
      div_neg, neg_div]
  rw [norm_zeta_eq_tsum_rpow hσ, hsum.tsum_eq_zero_add]
  rw [Nat.cast_zero, Real.zero_rpow (by linarith : -σ ≠ 0), zero_add]
  have hs1 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-σ)) := hsum.comp_injective (fun a b h => Nat.add_right_cancel h : Function.Injective (fun n : ℕ => n + 1))
  rw [← hs1.sum_add_tsum_nat_add N, rpowSum_eq]
  exact add_le_add le_rfl htail

theorem zeta_partial_lower {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
    rpowSum σ 1 N ≤ ‖riemannZeta (σ : ℂ)‖ := by
  rw [norm_zeta_eq_tsum_rpow hσ]
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hs1 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-σ)) := hsum.comp_injective (fun a b h => Nat.add_right_cancel h : Function.Injective (fun n : ℕ => n + 1))
  rw [hsum.tsum_eq_zero_add, Nat.cast_zero, Real.zero_rpow (by linarith : -σ ≠ 0), zero_add, rpowSum_eq]
  exact hs1.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem zeta_tail_lower {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
    rpowSum σ 1 N + ((N + 1 : ℕ) : ℝ) ^ (1 - σ) / (σ - 1) ≤
      ‖riemannZeta (σ : ℂ)‖ := by
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hN' : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have anti : AntitoneOn (fun t : ℝ => t ^ (-σ)) (Set.Ici ((N + 1 : ℕ) : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hN'.trans_le hx) hxy (by linarith)
  have ht := anti.integral_le_tsum_comp_add (N + 1) hsum
    (fun t ht => Real.rpow_nonneg (le_of_lt (hN'.trans ht)) _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -σ < -1) hN'] at ht
  have htail : ((N + 1 : ℕ) : ℝ) ^ (1 - σ) / (σ - 1) ≤
      ∑' n : ℕ, ((n + (N + 1) : ℕ) : ℝ) ^ (-σ) := by
    convert ht using 1
    rw [show -σ + 1 = 1 - σ by ring, show σ - 1 = -(1 - σ) by ring,
      div_neg, neg_div]
  rw [norm_zeta_eq_tsum_rpow hσ, hsum.tsum_eq_zero_add]
  rw [Nat.cast_zero, Real.zero_rpow (by linarith : -σ ≠ 0), zero_add]
  have hs1 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-σ)) := hsum.comp_injective (fun a b h => Nat.add_right_cancel h : Function.Injective (fun n : ℕ => n + 1))
  rw [← hs1.sum_add_tsum_nat_add N, rpowSum_eq]
  apply add_le_add le_rfl
  simpa only [Nat.add_assoc] using htail

theorem rpow_root_identity {n p k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    ((n : ℝ) ^ (-(p : ℝ) / k)) ^ k = ((n : ℝ) ^ p)⁻¹ := by
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [div_mul_cancel₀ _ hk', Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_natCast]

theorem root_lower {n p k D b : ℕ} (hn : 0 < n) (hk : 0 < k) (hD : 0 < D)
    (hb : b ^ k * n ^ p ≤ D ^ k) :
    (b : ℝ) / D ≤ (n : ℝ) ^ (-(p : ℝ) / k) := by
  apply (pow_le_pow_iff_left₀ (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hk.ne').mp
  rw [div_pow, rpow_root_identity hn hk]
  have hn' : 0 < (n : ℝ) ^ p := pow_pos (by exact_mod_cast hn) _
  have hD' : 0 < (D : ℝ) ^ k := pow_pos (by exact_mod_cast hD) _
  rw [div_le_iff₀ hD', le_inv_mul_iff₀ hn']
  exact_mod_cast (by simpa [mul_comm] using hb : n ^ p * b ^ k ≤ D ^ k)

theorem root_upper {n p k D b : ℕ} (hn : 0 < n) (hk : 0 < k) (hD : 0 < D)
    (hb : D ^ k ≤ b ^ k * n ^ p) :
    (n : ℝ) ^ (-(p : ℝ) / k) ≤ (b : ℝ) / D := by
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity) hk.ne').mp
  rw [div_pow, rpow_root_identity hn hk]
  have hn' : 0 < (n : ℝ) ^ p := pow_pos (by exact_mod_cast hn) _
  have hD' : 0 < (D : ℝ) ^ k := pow_pos (by exact_mod_cast hD) _
  rw [le_div_iff₀ hD', inv_mul_le_iff₀ hn']
  exact_mod_cast (by simpa [mul_comm] using hb : D ^ k ≤ n ^ p * b ^ k)

def rootCheck (p k D n : ℕ) : List ℕ → Bool
  | [] => true
  | b :: bs => decide (b ^ k * n ^ p ≤ D ^ k ∧ D ^ k ≤ (b + 1) ^ k * n ^ p) &&
      rootCheck p k D (n + 1) bs

theorem rootCheck_sound {p k D n : ℕ} (hn : 0 < n) (hk : 0 < k) (hD : 0 < D)
    {bs : List ℕ} (hc : rootCheck p k D n bs = true) :
    (bs.sum : ℝ) / D ≤ rpowSum ((p : ℝ) / k) n bs.length ∧
    rpowSum ((p : ℝ) / k) n bs.length ≤ ((bs.sum + bs.length : ℕ) : ℝ) / D := by
  induction bs generalizing n with
  | nil => simp [rpowSum]
  | cons b bs ih =>
    simp only [rootCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hl, hu⟩ := ih (by omega) hc.2
    have hbl := root_lower hn hk hD hc.1.1
    have hbu := root_upper hn hk hD hc.1.2
    simp only [List.sum_cons, List.length_cons, rpowSum, Nat.cast_add, Nat.cast_one]
    rw [neg_div] at hbl hbu
    simp only [Nat.cast_add, Nat.cast_one, add_div] at hbu hu ⊢
    constructor <;> linarith

end TernaryGoldbach.RSBounds.CenterNumerics
end

-- RSBounds.BacklundRightArc
section
open Real Complex Set Filter MeasureTheory Finset ArithmeticFunction
open scoped Topology BigOperators

namespace TernaryGoldbach.RSBounds.BacklundRightArc

noncomputable def logZeta (σ : ℝ) : ℝ := Real.log ‖riemannZeta (σ : ℂ)‖
noncomputable def logCoeff (n : ℕ) : ℝ := Λ n / Real.log n

lemma logCoeff_nonneg (n : ℕ) : 0 ≤ logCoeff n :=
  div_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg n)

lemma logCoeff_le_one (n : ℕ) : logCoeff n ≤ 1 := by
  by_cases hn : n ≤ 1
  · interval_cases n <;> norm_num [logCoeff]
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  exact (div_le_one hl).mpr vonMangoldt_le_log

lemma summable_logCoeff {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => logCoeff n * (n : ℝ) ^ (-σ)) := by
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (logCoeff_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (fun n => ?_) (Real.summable_nat_rpow.mpr (show -σ < -1 by linarith))
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) _) (logCoeff_le_one n)

lemma logZeta_eq_tsum {σ : ℝ} (hσ : 1 < σ) :
    logZeta σ = ∑' n : ℕ, logCoeff n * (n : ℝ) ^ (-σ) := by
  have he : riemannZeta (σ : ℂ) = ((riemannZeta (σ : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [riemannZeta_im_eq_zero_of_one_lt hσ]
  unfold logZeta
  rw [he, Complex.norm_of_nonneg (riemannZeta_re_pos_of_one_lt hσ).le,
    TernaryGoldbach.PNTMertens.log_zeta_eq_sum σ hσ]
  apply tsum_congr
  intro n
  rw [logCoeff, Real.rpow_neg (Nat.cast_nonneg n)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma logZeta_nonneg {σ : ℝ} (hσ : 1 < σ) : 0 ≤ logZeta σ := by
  rw [logZeta_eq_tsum hσ]
  exact tsum_nonneg (fun n => mul_nonneg (logCoeff_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))

lemma convexOn_logZeta : ConvexOn ℝ (Ioi 1) logZeta := by
  refine ⟨convex_Ioi 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz : 1 < a • x + b • y := (convex_Ioi 1) hx hy ha hb hab
  rw [logZeta_eq_tsum hx, logZeta_eq_tsum hy, logZeta_eq_tsum hz]
  simp only [smul_eq_mul]
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← Summable.tsum_add ((summable_logCoeff hx).mul_left a) ((summable_logCoeff hy).mul_left b)]
  apply (summable_logCoeff hz).tsum_le_tsum _
    (((summable_logCoeff hx).mul_left a).add ((summable_logCoeff hy).mul_left b))
  intro n
  by_cases hn : n = 0
  · simp [hn, logCoeff]
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hh := convexOn_exp.2 (mem_univ (-x * Real.log n))
    (mem_univ (-y * Real.log n)) ha hb hab
  simp only [smul_eq_mul] at hh ⊢
  rw [Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hn0]
  have he : Real.log (n : ℝ) * -(a * x + b * y) =
      a * (-x * Real.log n) + b * (-y * Real.log n) := by ring
  rw [he, show Real.log (n : ℝ) * -x = -x * Real.log n by ring,
    show Real.log (n : ℝ) * -y = -y * Real.log n by ring]
  have hm := mul_le_mul_of_nonneg_left hh (logCoeff_nonneg n)
  nlinarith [hm]

lemma antitoneOn_logZeta : AntitoneOn logZeta (Ioi 1) := by
  intro x hx y hy hxy
  rw [logZeta_eq_tsum hx, logZeta_eq_tsum hy]
  apply (summable_logCoeff hy).tsum_le_tsum _ (summable_logCoeff hx)
  intro n
  by_cases hn : n = 0
  · simp [hn, logCoeff]
  apply mul_le_mul_of_nonneg_left _ (logCoeff_nonneg n)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)) (by linarith)

lemma continuousOn_logZeta : ContinuousOn logZeta (Ioi 1) := by
  intro σ hσ
  change 1 < σ at hσ
  unfold logZeta
  apply ContinuousWithinAt.log
  · apply ContinuousWithinAt.norm
    exact ((differentiableAt_riemannZeta (by
      intro he
      have hh := congrArg Complex.re he
      simp only [Complex.ofReal_re, Complex.one_re] at hh
      linarith [hσ])).continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  · exact norm_ne_zero_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ))

noncomputable def arcFunction (θ : ℝ) : ℝ := logZeta (5 / 4 + (33 / 25) * Real.cos θ)

lemma arc_sigma_gt_one {θ : ℝ} (hθ : θ ∈ Icc 0 (Real.pi / 2)) :
    1 < 5 / 4 + (33 / 25) * Real.cos θ := by
  have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  linarith

lemma convexOn_arcFunction : ConvexOn ℝ (Icc 0 (Real.pi / 2)) arcFunction := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz : a • x + b • y ∈ Icc 0 (Real.pi / 2) := (convex_Icc _ _) hx hy ha hb hab
  have hc := strictConcaveOn_cos_Icc.concaveOn.2
    (show x ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) by constructor <;> linarith [hx.1, hx.2, Real.pi_pos])
    (show y ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) by constructor <;> linarith [hy.1, hy.2, Real.pi_pos])
    ha hb hab
  have hsx := arc_sigma_gt_one hx
  have hsy := arc_sigma_gt_one hy
  have hsz := arc_sigma_gt_one hz
  have hsmix : 1 < a * (5 / 4 + (33 / 25) * Real.cos x) +
      b * (5 / 4 + (33 / 25) * Real.cos y) := by
    exact (convex_Ioi (1 : ℝ)) hsx hsy ha hb hab
  have hsm : a * (5 / 4 + (33 / 25) * Real.cos x) +
      b * (5 / 4 + (33 / 25) * Real.cos y) ≤
      5 / 4 + (33 / 25) * Real.cos (a • x + b • y) := by
    simp only [smul_eq_mul] at hc ⊢
    nlinarith
  have ha1 := antitoneOn_logZeta hsmix hsz hsm
  have ha2 := convexOn_logZeta.2 hsx hsy ha hb hab
  exact ha1.trans ha2

lemma continuousOn_arcFunction : ContinuousOn arcFunction (Icc 0 (Real.pi / 2)) :=
  continuousOn_logZeta.comp (by fun_prop) (fun _ hx => arc_sigma_gt_one hx)

lemma integral_unit_le_trapezoid {f : ℝ → ℝ} {a : ℝ}
    (hf : ConvexOn ℝ (Icc a (a + 1)) f) (hc : ContinuousOn f (Icc a (a + 1))) :
    (∫ x in a..a + 1, f x) ≤ (f a + f (a + 1)) / 2 := by
  let L : ℝ → ℝ := fun x => (a + 1 - x) * f a + (x - a) * f (a + 1)
  have hL : Continuous L := by dsimp [L]; fun_prop
  have hpoint : ∀ x ∈ Icc a (a + 1), f x ≤ L x := by
    intro x hx
    have hh := hf.2 (show a ∈ Icc a (a + 1) by constructor <;> linarith)
      (show a + 1 ∈ Icc a (a + 1) by constructor <;> linarith)
      (show 0 ≤ a + 1 - x by linarith [hx.2]) (show 0 ≤ x - a by linarith [hx.1])
      (show (a + 1 - x) + (x - a) = 1 by ring)
    simpa only [smul_eq_mul, show (a + 1 - x) * a + (x - a) * (a + 1) = x by ring] using hh
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by linarith : a ≤ a + 1)
    (hc.intervalIntegrable_of_Icc (by linarith)) (hL.intervalIntegrable a (a + 1)) hpoint
  have he : (∫ x in a..a + 1, L x) = (f a + f (a + 1)) / 2 := by
    dsimp [L]
    rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const, intervalIntegral.integral_const,
      integral_id]
    simp only [smul_eq_mul]
    ring
  exact hi.trans_eq he

lemma integral_nat_le_trapezoids {f : ℝ → ℝ} {N : ℕ}
    (hf : ConvexOn ℝ (Icc 0 (N : ℝ)) f) (hc : ContinuousOn f (Icc 0 (N : ℝ))) :
    (∫ x in (0 : ℝ)..N, f x) ≤
      ∑ i ∈ Finset.range N, (f i + f ((i : ℝ) + 1)) / 2 := by
  have hi (i : ℕ) (hi : i < N) : Icc (i : ℝ) (i + 1) ⊆ Icc 0 (N : ℝ) := by
    apply Set.Icc_subset_Icc (Nat.cast_nonneg i)
    exact_mod_cast (show i + 1 ≤ N by omega)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume)
    (a := fun i : ℕ => (i : ℝ)) (n := N) (fun i hi' =>
      (hc.mono (by simpa only [Nat.cast_add, Nat.cast_one] using hi i hi')).intervalIntegrable_of_Icc
        (by exact_mod_cast Nat.le_succ i))
  simp only [Nat.cast_zero] at hsum
  rw [← hsum]
  apply Finset.sum_le_sum
  intro i hi'
  simpa only [Nat.cast_add, Nat.cast_one] using integral_unit_le_trapezoid
    (hf.subset (hi i (Finset.mem_range.mp hi')) (convex_Icc _ _))
    (hc.mono (hi i (Finset.mem_range.mp hi')))

lemma right_arc_le_samples :
    (∫ θ in (0 : ℝ)..Real.pi / 2, arcFunction θ) / (2 * Real.pi) ≤
      (∑ i ∈ Finset.range 16,
        (arcFunction (Real.pi / 32 * i) + arcFunction (Real.pi / 32 * ((i : ℝ) + 1))) / 2) / 64 := by
  let F : ℝ → ℝ := fun x => arcFunction (Real.pi / 32 * x)
  have hmem {x : ℝ} (hx : x ∈ Icc 0 (16 : ℝ)) : Real.pi / 32 * x ∈ Icc 0 (Real.pi / 2) := by
    rcases hx with ⟨hx0, hx16⟩
    constructor
    · exact mul_nonneg (by positivity) hx0
    · nlinarith [mul_le_mul_of_nonneg_left hx16 Real.pi_pos.le]
  have hF : ConvexOn ℝ (Icc 0 (16 : ℝ)) F := by
    refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hh := convexOn_arcFunction.2 (hmem hx) (hmem hy) ha hb hab
    simpa only [F, smul_eq_mul, mul_add, mul_assoc, mul_left_comm] using hh
  have hc : ContinuousOn F (Icc 0 (16 : ℝ)) :=
    continuousOn_arcFunction.comp (by fun_prop) (fun _ hx => hmem hx)
  have hi := integral_nat_le_trapezoids (N := 16) hF hc
  have he := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 16) arcFunction (Real.pi / 32)
  norm_num only [smul_eq_mul, mul_zero, show Real.pi / 32 * 16 = Real.pi / 2 by ring] at he
  rw [← he]
  have hh := div_le_div_of_nonneg_right hi (show (0 : ℝ) ≤ 64 by norm_num)
  convert hh using 1 <;> dsimp [F] <;> field_simp [Real.pi_ne_zero] <;> ring

end TernaryGoldbach.RSBounds.BacklundRightArc
end

-- RSBounds.BacklundGammaBaseline
section
open Complex Real
open scoped ComplexConjugate

namespace TernaryGoldbach.RSBounds.BacklundGammaBaseline

theorem norm_Gamma_one_sub_mul_I (t : ℝ) :
    ‖Complex.Gamma (1 - (t : ℂ) * I)‖ = ‖Complex.Gamma (1 + (t : ℂ) * I)‖ := by
  have he : 1 - (t : ℂ) * I = conj (1 + (t : ℂ) * I) := by simp [sub_eq_add_neg]
  rw [he, Complex.Gamma_conj, norm_conj]

theorem norm_Gamma_one_add_mul_I_sq {t : ℝ} (ht : 0 < t) :
    ‖Complex.Gamma (1 + (t : ℂ) * I)‖ ^ 2 =
      Real.pi * t / Real.sinh (Real.pi * t) := by
  have htC : (t : ℂ) * I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne') I_ne_zero
  have hs : 0 < Real.sinh (Real.pi * t) := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)
  have hsin : ‖Complex.sin ((Real.pi : ℂ) * ((t : ℂ) * I))‖ = Real.sinh (Real.pi * t) := by
    have he : (Real.pi : ℂ) * ((t : ℂ) * I) = ((Real.pi * t : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [he, Complex.sin_mul_I, ← Complex.ofReal_sinh (Real.pi * t), norm_mul,
      norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hr := congrArg norm (Complex.Gamma_mul_Gamma_one_sub ((t : ℂ) * I))
  rw [norm_mul, norm_div, norm_Gamma_one_sub_mul_I, hsin] at hr
  have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by simp [Real.pi_pos.le]
  rw [hpi] at hr
  have hc := congrArg norm (Complex.Gamma_add_one ((t : ℂ) * I) htC)
  rw [norm_mul, norm_mul] at hc
  have harg : (t : ℂ) * I + 1 = 1 + (t : ℂ) * I := add_comm _ _
  rw [harg] at hc
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, norm_I, mul_one] at hc
  calc
    _ = t * (‖Complex.Gamma ((t : ℂ) * I)‖ * ‖Complex.Gamma (1 + (t : ℂ) * I)‖) := by
      rw [pow_two, hc]
      ring
    _ = t * (Real.pi / Real.sinh (Real.pi * t)) := by rw [hr]
    _ = _ := by ring

end TernaryGoldbach.RSBounds.BacklundGammaBaseline
end

-- RSBounds.BacklundFunctionalMultiplier
section
open Complex Real
open scoped ComplexConjugate

namespace TernaryGoldbach.RSBounds.BacklundFunctionalMultiplier

noncomputable def multiplier (s : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) * Complex.Gamma (1 - s) *
    Complex.cos ((Real.pi : ℂ) * (1 - s) / 2)

theorem functional_equation {s : ℂ} (hs : s.im ≠ 0) :
    riemannZeta s = multiplier s * riemannZeta (1 - s) := by
  have hn : ∀ n : ℕ, 1 - s ≠ -(n : ℂ) := by
    intro n he
    have hh := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.one_im, Complex.neg_im, Complex.natCast_im,
      neg_zero, zero_sub] at hh
    exact hs (neg_eq_zero.mp hh)
  have hone : 1 - s ≠ 1 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.one_im, zero_sub] at hh
    exact hs (neg_eq_zero.mp hh)
  have hh := riemannZeta_one_sub hn hone
  simpa [multiplier, sub_sub_cancel] using hh

end TernaryGoldbach.RSBounds.BacklundFunctionalMultiplier
end

-- RSBounds.BacklundHyperbolicFactor
section
open Real

namespace TernaryGoldbach.RSBounds.BacklundHyperbolicFactor

theorem exp_neg_pi_mul_le {t : ℝ} (ht : 50 ≤ t) :
    Real.exp (-Real.pi * t) ≤ 1 / (8 * t ^ 2) := by
  have ht0 : 0 < t := by linarith
  have hp := Real.pow_div_factorial_le_exp (Real.pi * t) (by positivity : 0 ≤ Real.pi * t) 3
  norm_num at hp
  have hcub : (3 * t) ^ 3 ≤ (Real.pi * t) ^ 3 := by
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_right (Real.pi_gt_three).le ht0.le
  have hbig : 8 * t ^ 2 ≤ (Real.pi * t) ^ 3 / 6 := by
    have hh := mul_nonneg (by linarith : 0 ≤ t - 2) (sq_nonneg t)
    nlinarith
  have hexp : 8 * t ^ 2 ≤ Real.exp (Real.pi * t) := hbig.trans hp
  have he : -Real.pi * t = -(Real.pi * t) := by ring
  rw [he, Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) hexp

theorem sqrt_ratio_le_exp {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    Real.sqrt ((1 + q) / (1 - q)) ≤ Real.exp (2 * q) := by
  have hd : 0 < 1 - q := by linarith
  have hr : (1 + q) / (1 - q) ≤ 1 + 4 * q := by
    rw [div_le_iff₀ hd]
    nlinarith [mul_nonneg hq0 (by linarith : 0 ≤ 1 / 2 - q)]
  have he : 1 + 4 * q ≤ Real.exp (4 * q) := by
    linarith [Real.add_one_le_exp (4 * q)]
  have heq : Real.exp (4 * q) = Real.exp (2 * q) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hs : Real.sqrt ((1 + q) / (1 - q)) ^ 2 = (1 + q) / (1 - q) :=
    Real.sq_sqrt (by positivity)
  rw [heq] at he
  nlinarith [Real.sqrt_nonneg ((1 + q) / (1 - q)), Real.exp_pos (2 * q)]

theorem sqrt_exp_ratio_le {t : ℝ} (ht : 50 ≤ t) :
    Real.sqrt ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t))) ≤
      Real.exp (1 / (4 * t ^ 2)) := by
  have ht0 : 0 < t := by linarith
  have hq := exp_neg_pi_mul_le ht
  have hu : 1 / (8 * t ^ 2) ≤ (1 / 2 : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hb := sqrt_ratio_le_exp (Real.exp_pos _).le (hq.trans hu)
  refine hb.trans (Real.exp_le_exp.mpr ?_)
  calc
    2 * Real.exp (-Real.pi * t) ≤ 2 * (1 / (8 * t ^ 2)) := by gcongr
    _ = 1 / (4 * t ^ 2) := by ring

end TernaryGoldbach.RSBounds.BacklundHyperbolicFactor
end

-- RSBounds.IEANTNGamma.GaussSeries
section
namespace GammaSolution

open Complex

noncomputable def gaussTerm (s : ℂ) (k : ℕ) : ℂ := ((k : ℂ) + 1)⁻¹ - ((k : ℂ) + s)⁻¹

theorem gaussTerm_eq {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (k : ℕ) :
    gaussTerm s k = (s - 1) / (((k : ℂ) + 1) * ((k : ℂ) + s)) := by
  have h1 : ((k : ℂ) + 1) ≠ 0 := by
    intro h
    have : ((k : ℝ) + 1) = 0 := by exact_mod_cast congrArg Complex.re h
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have h2 : ((k : ℂ) + s) ≠ 0 := fun h ↦ hs k (by linear_combination h)
  simp only [gaussTerm]
  field_simp
  ring

theorem summable_gaussTerm {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) : Summable (gaussTerm s) := by

  obtain ⟨N, hN⟩ := exists_nat_gt (2 * ‖s‖)
  have hcomp : Summable (fun k : ℕ ↦ 2 * ‖s - 1‖ / (k : ℝ) ^ 2) := by
    simpa [div_eq_mul_inv] using
      (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left (2 * ‖s - 1‖)
  refine Summable.of_norm_bounded_eventually_nat hcomp ?_
  filter_upwards [Filter.eventually_ge_atTop (max N 1)] with k hk
  have hkN : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans (le_max_left N 1) hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans (le_max_right N 1) hk
  have hks : 2 * ‖s‖ < (k : ℝ) := lt_of_lt_of_le hN hkN

  have hlow : (k : ℝ) / 2 ≤ ‖(k : ℂ) + s‖ := by
    have h := norm_sub_norm_le ((k : ℂ)) (-s)
    simp only [norm_neg, sub_neg_eq_add] at h
    have hkabs : ‖((k : ℕ) : ℂ)‖ = (k : ℝ) := by
      simp
    rw [hkabs] at h
    linarith
  have hpos : (0 : ℝ) < (k : ℝ) := by linarith
  rw [gaussTerm_eq hs k, norm_div, norm_mul]
  have hk1n : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
    have hcast : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [hk1n]
  have hs1 : (0 : ℝ) ≤ ‖s - 1‖ := norm_nonneg _
  have hnormpos : (0 : ℝ) < ‖(k : ℂ) + s‖ := by linarith
  have hden1 : (0 : ℝ) < ((k : ℝ) + 1) * ‖(k : ℂ) + s‖ :=
    mul_pos (by linarith) hnormpos
  have hden2 : (0 : ℝ) < (k : ℝ) ^ 2 := by nlinarith
  rw [div_le_div_iff₀ hden1 hden2]

  have hmul : ((k : ℝ) + 1) * ((k : ℝ) / 2) ≤ ((k : ℝ) + 1) * ‖(k : ℂ) + s‖ :=
    mul_le_mul_of_nonneg_left hlow (by linarith)
  nlinarith [hmul, hs1, hk1, hpos]

end GammaSolution
end

-- RSBounds.IEANTNGamma.Recurrence
section
namespace GammaSolution

open Complex

noncomputable def gaussSum (s : ℂ) : ℂ :=
  -(Real.eulerMascheroniConstant : ℂ) + ∑' k, gaussTerm s k

theorem hasSum_sub_succ {F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {f : ℕ → F}
    (hsum : Summable fun k ↦ f k - f (k + 1))
    (hlim : Filter.Tendsto f Filter.atTop (nhds 0)) :
    HasSum (fun k ↦ f k - f (k + 1)) (f 0) := by
  have hpart : ∀ n : ℕ, ∑ i ∈ Finset.range n, (f i - f (i + 1)) = f 0 - f n :=
    fun n ↦ Finset.sum_range_sub' f n
  have h1 := hsum.hasSum.tendsto_sum_nat
  simp only [hpart] at h1
  have h2 : Filter.Tendsto (fun n : ℕ ↦ f 0 - f n) Filter.atTop (nhds (f 0)) := by
    simpa using tendsto_const_nhds.sub hlim
  rw [← tendsto_nhds_unique h1 h2]
  exact hsum.hasSum

theorem tendsto_inv_natCast_add (s : ℂ) :
    Filter.Tendsto (fun k : ℕ ↦ ((k : ℂ) + s)⁻¹) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_inv]
  refine Filter.Tendsto.inv_tendsto_atTop ?_
  refine Filter.tendsto_atTop_mono (fun k ↦ ?_)
    (Filter.tendsto_atTop_add_const_right _ (-‖s‖) tendsto_natCast_atTop_atTop)
  have h := norm_sub_norm_le ((k : ℂ)) (-s)
  simp only [norm_neg, sub_neg_eq_add] at h
  rw [Complex.norm_natCast] at h
  exact (by linarith : (k : ℝ) + -‖s‖ ≤ ‖(k : ℂ) + s‖)

theorem gaussSum_add_one {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
    gaussSum (s + 1) = gaussSum s + s⁻¹ := by
  have hs' : ∀ n : ℕ, s + 1 ≠ -n := fun n h ↦
    hs (n + 1) (by push_cast at h ⊢; linear_combination h)
  set f : ℕ → ℂ := fun k ↦ ((k : ℂ) + s)⁻¹ with hf
  have hdiff : ∀ k : ℕ, gaussTerm (s + 1) k - gaussTerm s k = f k - f (k + 1) := by
    intro k
    simp only [gaussTerm, hf]
    push_cast
    ring
  have hsub : Summable (fun k ↦ f k - f (k + 1)) := by
    have h := (summable_gaussTerm hs').sub (summable_gaussTerm hs)
    simpa only [hdiff] using h
  have htel := hasSum_sub_succ hsub (tendsto_inv_natCast_add s)
  have hHS : HasSum (fun k ↦ gaussTerm (s + 1) k - gaussTerm s k)
      ((∑' k, gaussTerm (s + 1) k) - ∑' k, gaussTerm s k) :=
    (summable_gaussTerm hs').hasSum.sub (summable_gaussTerm hs).hasSum
  have hHS' : HasSum (fun k ↦ gaussTerm (s + 1) k - gaussTerm s k) (f 0) := by
    simpa only [hdiff] using htel
  have hkey := hHS.unique hHS'
  have hf0 : f 0 = s⁻¹ := by simp [hf]
  rw [hf0] at hkey
  simp only [gaussSum]
  linear_combination hkey

@[simp]
theorem gaussTerm_one (k : ℕ) : gaussTerm 1 k = 0 := by simp [gaussTerm]

theorem gaussSum_one : gaussSum 1 = -(Real.eulerMascheroniConstant : ℂ) := by
  simp [gaussSum]

theorem gaussSum_nat_add_one (n : ℕ) :
    gaussSum ((n : ℂ) + 1)
      = -(Real.eulerMascheroniConstant : ℂ) + ((harmonic n : ℚ) : ℂ) := by
  induction n with
  | zero => simpa using gaussSum_one
  | succ n ih =>
    have hne : ∀ m : ℕ, ((n : ℂ) + 1) ≠ -(m : ℂ) := by
      intro m h
      have hre : (n : ℝ) + 1 = -(m : ℝ) := by exact_mod_cast congrArg Complex.re h
      have h1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h2 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hstep : gaussSum (((n : ℂ) + 1) + 1) = gaussSum ((n : ℂ) + 1) + ((n : ℂ) + 1)⁻¹ :=
      gaussSum_add_one hne
    have hcast : (((n : ℕ) + 1 : ℕ) : ℂ) + 1 = ((n : ℂ) + 1) + 1 := by push_cast; ring
    rw [hcast, hstep, ih, harmonic_succ]
    push_cast
    ring

theorem digamma_eq_gaussSum_nat_add_one (n : ℕ) :
    Complex.digamma ((n : ℂ) + 1) = gaussSum ((n : ℂ) + 1) := by
  rw [Complex.digamma_nat_add_one n, gaussSum_nat_add_one n]
  ring

end GammaSolution
end

-- RSBounds.IEANTNGamma.RealAsymptotic
section
namespace GammaSolution

open Real Set

theorem differentiableAt_log_Gamma {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (fun t ↦ Real.log (Real.Gamma t)) x := by
  have hΓ : DifferentiableAt ℝ Real.Gamma x :=
    Real.differentiableAt_Gamma (fun m ↦ by
      intro hcon
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      rw [hcon] at hx
      linarith)
  exact (Real.differentiableAt_log (Real.Gamma_pos_of_pos hx).ne').comp x hΓ

theorem log_Gamma_add_one_sub {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma x) = Real.log x := by
  rw [Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']
  ring

theorem deriv_log_Gamma_add_one {x : ℝ} (hx : 0 < x) :
    deriv (fun t ↦ Real.log (Real.Gamma t)) (x + 1)
      = deriv (fun t ↦ Real.log (Real.Gamma t)) x + 1 / x := by
  have hpos : {t : ℝ | 0 < t} ∈ nhds x :=
    (isOpen_lt continuous_const continuous_id).mem_nhds hx
  have hEq : (fun t : ℝ ↦ Real.log t + Real.log (Real.Gamma t))
      =ᶠ[nhds x] (fun t : ℝ ↦ Real.log (Real.Gamma (t + 1))) := by
    filter_upwards [hpos] with t ht
    rw [Real.Gamma_add_one (ne_of_gt ht), Real.log_mul (ne_of_gt ht)
      (Real.Gamma_pos_of_pos ht).ne']

  have hL : HasDerivAt (fun t : ℝ ↦ Real.log (Real.Gamma (t + 1)))
      (deriv (fun t ↦ Real.log (Real.Gamma t)) (x + 1)) x := by
    have hshift : HasDerivAt (fun t : ℝ ↦ t + 1) 1 x := (hasDerivAt_id x).add_const 1
    have hout := (differentiableAt_log_Gamma (by linarith : (0:ℝ) < x + 1)).hasDerivAt
    simpa [Function.comp_def] using hout.comp x hshift

  have hR : HasDerivAt (fun t : ℝ ↦ Real.log t + Real.log (Real.Gamma t))
      (x⁻¹ + deriv (fun t ↦ Real.log (Real.Gamma t)) x) x :=
    (Real.hasDerivAt_log hx.ne').add (differentiableAt_log_Gamma hx).hasDerivAt
  have hLR : HasDerivAt (fun t : ℝ ↦ Real.log t + Real.log (Real.Gamma t))
      (deriv (fun t ↦ Real.log (Real.Gamma t)) (x + 1)) x := hL.congr_of_eventuallyEq hEq
  have := hLR.unique hR
  rw [this, one_div]
  ring

theorem monotoneOn_deriv_log_Gamma :
    MonotoneOn (deriv (fun t ↦ Real.log (Real.Gamma t))) (Ioi 0) :=
  Real.convexOn_log_Gamma.monotoneOn_deriv (fun _ hx ↦ differentiableAt_log_Gamma hx)

theorem deriv_log_Gamma_le_log_le {x : ℝ} (hx : 0 < x) :
    deriv (fun t ↦ Real.log (Real.Gamma t)) x ≤ Real.log x ∧
      Real.log x ≤ deriv (fun t ↦ Real.log (Real.Gamma t)) (x + 1) := by
  have hsub : Icc x (x + 1) ⊆ Ioi 0 := fun t ht ↦ lt_of_lt_of_le hx ht.1
  have hcont : ContinuousOn (fun t ↦ Real.log (Real.Gamma t)) (Icc x (x + 1)) := fun t ht ↦
    (differentiableAt_log_Gamma (hsub ht)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcs⟩ :=
    exists_deriv_eq_slope (fun t ↦ Real.log (Real.Gamma t)) (by linarith) hcont
      (fun t ht ↦ (differentiableAt_log_Gamma (lt_trans hx ht.1)).differentiableWithinAt)
  have hslope : (Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma x)) / (x + 1 - x)
      = Real.log x := by
    rw [add_sub_cancel_left, div_one, log_Gamma_add_one_sub hx]
  rw [hslope] at hcs
  have hcpos : (0 : ℝ) < c := lt_trans hx hc.1
  have h1 : deriv (fun t ↦ Real.log (Real.Gamma t)) x ≤ Real.log x := by
    rw [← hcs]
    exact monotoneOn_deriv_log_Gamma (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hcpos) hc.1.le
  have h2 : Real.log x ≤ deriv (fun t ↦ Real.log (Real.Gamma t)) (x + 1) := by
    rw [← hcs]
    exact monotoneOn_deriv_log_Gamma (Set.mem_Ioi.mpr hcpos)
      (Set.mem_Ioi.mpr (by linarith)) hc.2.le
  exact ⟨h1, h2⟩

theorem abs_deriv_log_Gamma_sub_log_le {x : ℝ} (hx : 0 < x) :
    |deriv (fun t ↦ Real.log (Real.Gamma t)) x - Real.log x| ≤ 1 / x := by
  obtain ⟨hle, hge⟩ := deriv_log_Gamma_le_log_le hx
  rw [deriv_log_Gamma_add_one hx] at hge
  rw [abs_le]
  constructor <;> linarith

end GammaSolution
end

-- RSBounds.IEANTNGamma.ComplexToReal
section
namespace GammaSolution

open Complex

theorem hasDerivAt_complex_of_real {f : ℂ → ℂ} {g : ℝ → ℝ} {g' s : ℝ}
    (hf : DifferentiableAt ℂ f s) (hg : HasDerivAt g g' s) (hfg : ∀ s : ℝ, f ↑s = ↑(g s)) :
    HasDerivAt f ↑g' s := by
  refine HasDerivAt.congr_deriv hf.hasDerivAt ?_
  rw [← (funext hfg ▸ hf.hasDerivAt.comp_ofReal.deriv :)]
  exact hg.ofReal_comp.deriv

theorem ofReal_ne_neg_natCast {x : ℝ} (hx : 0 < x) (m : ℕ) : (x : ℂ) ≠ -(m : ℂ) := by
  intro h
  have hx' : x = -(m : ℝ) := by exact_mod_cast h
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

theorem differentiableAt_real_Gamma {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ Real.Gamma x :=
  Real.differentiableAt_Gamma (fun m ↦ by
    intro hcon
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rw [hcon] at hx
    linarith)

theorem hasDerivAt_Gamma_ofReal {x : ℝ} (hx : 0 < x) :
    HasDerivAt Complex.Gamma ((deriv Real.Gamma x : ℝ) : ℂ) (x : ℂ) :=
  hasDerivAt_complex_of_real
    (Complex.differentiableAt_Gamma _ (ofReal_ne_neg_natCast hx))
    (differentiableAt_real_Gamma hx).hasDerivAt
    Complex.Gamma_ofReal

theorem deriv_log_Gamma_eq {x : ℝ} (hx : 0 < x) :
    deriv (fun t ↦ Real.log (Real.Gamma t)) x = deriv Real.Gamma x / Real.Gamma x := by
  have hpos := Real.Gamma_pos_of_pos hx
  have h := (Real.hasDerivAt_log hpos.ne').comp x (differentiableAt_real_Gamma hx).hasDerivAt
  simp only [Function.comp_def] at h
  rw [h.deriv]
  ring

theorem digamma_ofReal {x : ℝ} (hx : 0 < x) :
    Complex.digamma (x : ℂ) = ((deriv (fun t ↦ Real.log (Real.Gamma t)) x : ℝ) : ℂ) := by
  have hpos := Real.Gamma_pos_of_pos hx
  rw [Complex.digamma_def, logDeriv_apply, (hasDerivAt_Gamma_ofReal hx).deriv,
    Complex.Gamma_ofReal, deriv_log_Gamma_eq hx]
  push_cast
  ring

end GammaSolution
end

-- RSBounds.IEANTNGamma.Oscillation
section
namespace GammaSolution

open Complex

theorem summable_telescope {t : ℝ} (ht : 1 ≤ t) :
    Summable (fun k : ℕ ↦ (((k : ℝ) + t) * ((k : ℝ) + t + 1))⁻¹) := by
  have hcomp : Summable (fun k : ℕ ↦ 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  refine Summable.of_norm_bounded_eventually_nat hcomp ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsq : (0 : ℝ) < (k : ℝ) ^ 2 := by nlinarith
  have hpos : (0 : ℝ) < ((k : ℝ) + t) * ((k : ℝ) + t + 1) := by nlinarith
  rw [Real.norm_of_nonneg (by positivity), inv_eq_one_div, div_le_div_iff₀ hpos hsq]
  nlinarith

theorem tsum_telescope {t : ℝ} (ht : 1 ≤ t) :
    ∑' k : ℕ, (((k : ℝ) + t) * ((k : ℝ) + t + 1))⁻¹ = t⁻¹ := by
  set f : ℕ → ℝ := fun k ↦ ((k : ℝ) + t)⁻¹ with hf
  have hne : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + t := fun k ↦ by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hdiff : ∀ k : ℕ, f k - f (k + 1) = (((k : ℝ) + t) * ((k : ℝ) + t + 1))⁻¹ := by
    intro k
    have h1 : ((k : ℝ) + t) ≠ 0 := (hne k).ne'
    have h2 : (((k : ℕ) + 1 : ℕ) : ℝ) + t ≠ 0 := (hne (k + 1)).ne'
    simp only [hf]
    push_cast at h2 ⊢
    field_simp
    ring
  have hsum : Summable (fun k : ℕ ↦ f k - f (k + 1)) := by
    simpa only [hdiff] using summable_telescope ht
  have hlim : Filter.Tendsto f Filter.atTop (nhds 0) := by
    simp only [hf]
    exact Filter.Tendsto.inv_tendsto_atTop
      (Filter.tendsto_atTop_add_const_right _ t tendsto_natCast_atTop_atTop)
  have h := hasSum_sub_succ hsum hlim
  have hf0 : f 0 = t⁻¹ := by simp [hf]
  rw [hf0] at h
  simpa only [hdiff] using h.tsum_eq

theorem hasSum_comparison {t : ℝ} (ht : 1 ≤ t) (c : ℝ) :
    HasSum (fun k : ℕ ↦ c * (2 * (((k : ℝ) + t) * ((k : ℝ) + t + 1))⁻¹)) (c * (2 * t⁻¹)) := by
  have h : HasSum (fun k : ℕ ↦ (((k : ℝ) + t) * ((k : ℝ) + t + 1))⁻¹) t⁻¹ := by
    rw [← tsum_telescope ht]
    exact (summable_telescope ht).hasSum
  exact (h.mul_left 2).mul_left c

theorem gaussTerm_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
    gaussTerm (a : ℂ) k - gaussTerm (b : ℂ) k
      = ((a : ℂ) - b) / (((k : ℂ) + a) * ((k : ℂ) + b)) := by
  have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h1 : ((k : ℂ) + a) ≠ 0 := by
    intro h
    have : (k : ℝ) + a = 0 := by exact_mod_cast congrArg Complex.re h
    linarith
  have h2 : ((k : ℂ) + b) ≠ 0 := by
    intro h
    have : (k : ℝ) + b = 0 := by exact_mod_cast congrArg Complex.re h
    linarith
  simp only [gaussTerm]
  field_simp
  ring

theorem norm_gaussSum_sub_le {n : ℕ} (hn : 1 ≤ n) {a b : ℝ}
    (ha : (n : ℝ) ≤ a) (hb : (n : ℝ) ≤ b) :
    ‖gaussSum (a : ℂ) - gaussSum (b : ℂ)‖ ≤ |a - b| * (2 / n) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hapos : (0 : ℝ) < a := by linarith
  have hbpos : (0 : ℝ) < b := by linarith
  have habs : (0 : ℝ) ≤ |a - b| := abs_nonneg _
  have hsa : ∀ m : ℕ, (a : ℂ) ≠ -m := fun m h ↦ by
    have h' : a = -(m : ℝ) := by exact_mod_cast h
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hsb : ∀ m : ℕ, (b : ℂ) ≠ -m := fun m h ↦ by
    have h' : b = -(m : ℝ) := by exact_mod_cast h
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith

  have hHS : HasSum (fun k ↦ gaussTerm (a : ℂ) k - gaussTerm (b : ℂ) k)
      (gaussSum (a : ℂ) - gaussSum (b : ℂ)) := by
    have h := (summable_gaussTerm hsa).hasSum.sub (summable_gaussTerm hsb).hasSum
    simpa only [gaussSum, add_sub_add_left_eq_sub] using h

  have hbound : ∀ k : ℕ, ‖gaussTerm (a : ℂ) k - gaussTerm (b : ℂ) k‖
      ≤ |a - b| * (2 * (((k : ℝ) + n) * ((k : ℝ) + n + 1))⁻¹) := by
    intro k
    have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hka : (0 : ℝ) < (k : ℝ) + a := by linarith
    have hkb : (0 : ℝ) < (k : ℝ) + b := by linarith
    have hknpos : (0 : ℝ) < (k : ℝ) + n := by linarith
    have hprod : (0 : ℝ) < ((k : ℝ) + a) * ((k : ℝ) + b) := mul_pos hka hkb
    have hnprod : (0 : ℝ) < ((k : ℝ) + n) * ((k : ℝ) + n + 1) := by positivity
    rw [gaussTerm_sub hapos hbpos k, norm_div, norm_mul]
    have hna : ‖((k : ℂ) + a)‖ = (k : ℝ) + a := by
      have hc : ((k : ℂ) + a) = (((k : ℝ) + a : ℝ) : ℂ) := by push_cast; ring
      rw [hc, Complex.norm_real, Real.norm_of_nonneg hka.le]
    have hnb : ‖((k : ℂ) + b)‖ = (k : ℝ) + b := by
      have hc : ((k : ℂ) + b) = (((k : ℝ) + b : ℝ) : ℂ) := by push_cast; ring
      rw [hc, Complex.norm_real, Real.norm_of_nonneg hkb.le]
    have hnum : ‖((a : ℂ) - b)‖ = |a - b| := by
      have hc : ((a : ℂ) - b) = ((a - b : ℝ) : ℂ) := by push_cast; ring
      rw [hc, Complex.norm_real, Real.norm_eq_abs]
    rw [hna, hnb, hnum]
    have hcmp : 1 / (((k : ℝ) + a) * ((k : ℝ) + b))
        ≤ 2 / (((k : ℝ) + n) * ((k : ℝ) + n + 1)) := by
      rw [div_le_div_iff₀ hprod hnprod]
      nlinarith
    calc |a - b| / (((k : ℝ) + a) * ((k : ℝ) + b))
        = |a - b| * (1 / (((k : ℝ) + a) * ((k : ℝ) + b))) := by ring
      _ ≤ |a - b| * (2 / (((k : ℝ) + n) * ((k : ℝ) + n + 1))) :=
          mul_le_mul_of_nonneg_left hcmp habs
      _ = |a - b| * (2 * (((k : ℝ) + n) * ((k : ℝ) + n + 1))⁻¹) := by ring
  have hle := hHS.norm_le_of_bounded (hasSum_comparison hn1 |a - b|) hbound
  refine hle.trans_eq ?_
  field_simp

theorem abs_log_sub_log_le {n : ℝ} (hn : 0 < n) {a b : ℝ} (ha : n ≤ a) (hb : n ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / n := by

  have key : ∀ u v : ℝ, n ≤ u → n ≤ v → v ≤ u → Real.log u - Real.log v ≤ (u - v) / n := by
    intro u v hu hv hvu
    have hvpos : (0 : ℝ) < v := lt_of_lt_of_le hn hv
    have hupos : (0 : ℝ) < u := lt_of_lt_of_le hn hu
    rw [← Real.log_div hupos.ne' hvpos.ne']
    have h1 : Real.log (u / v) ≤ u / v - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : u / v - 1 = (u - v) / v := by field_simp
    have h3 : (u - v) / v ≤ (u - v) / n := by gcongr
    linarith
  rcases le_total b a with h | h
  · have hlog : Real.log b ≤ Real.log a := Real.log_le_log (lt_of_lt_of_le hn hb) h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact key a b ha hb h
  · have hlog : Real.log a ≤ Real.log b := Real.log_le_log (lt_of_lt_of_le hn ha) h
    rw [abs_sub_comm, abs_sub_comm a b, abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    exact key b a hb ha h

theorem abs_deriv_log_Gamma_sub_le {n : ℕ} (hn : 1 ≤ n) {a b : ℝ}
    (ha : (n : ℝ) ≤ a) (hb : (n : ℝ) ≤ b) (hab : |a - b| ≤ 1) :
    |deriv (fun t ↦ Real.log (Real.Gamma t)) a - deriv (fun t ↦ Real.log (Real.Gamma t)) b|
      ≤ 3 / n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hapos : (0 : ℝ) < a := by linarith
  have hbpos : (0 : ℝ) < b := by linarith
  have h1 := abs_deriv_log_Gamma_sub_log_le hapos
  have h2 := abs_deriv_log_Gamma_sub_log_le hbpos
  have h3 := abs_log_sub_log_le hnpos ha hb
  have h1n : (1 : ℝ) / a ≤ 1 / n := by gcongr
  have h2n : (1 : ℝ) / b ≤ 1 / n := by gcongr
  have h3n : |a - b| / n ≤ 1 / n := by gcongr

  have t1 := abs_sub_le (deriv (fun t ↦ Real.log (Real.Gamma t)) a) (Real.log a)
    (deriv (fun t ↦ Real.log (Real.Gamma t)) b)
  have t2 := abs_sub_le (Real.log a) (Real.log b)
    (deriv (fun t ↦ Real.log (Real.Gamma t)) b)
  have t3 : |Real.log b - deriv (fun t ↦ Real.log (Real.Gamma t)) b|
      = |deriv (fun t ↦ Real.log (Real.Gamma t)) b - Real.log b| := abs_sub_comm _ _
  have hthree : (3 : ℝ) / n = 1 / n + 1 / n + 1 / n := by ring
  linarith

theorem norm_error_sub_le {n : ℕ} (hn : 1 ≤ n) {a b : ℝ}
    (ha : (n : ℝ) ≤ a) (hb : (n : ℝ) ≤ b) (hab : |a - b| ≤ 1) :
    ‖(Complex.digamma (a : ℂ) - gaussSum (a : ℂ))
        - (Complex.digamma (b : ℂ) - gaussSum (b : ℂ))‖ ≤ 5 / n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hapos : (0 : ℝ) < a := by linarith
  have hbpos : (0 : ℝ) < b := by linarith

  have hsplit : (Complex.digamma (a : ℂ) - gaussSum (a : ℂ))
      - (Complex.digamma (b : ℂ) - gaussSum (b : ℂ))
      = (Complex.digamma (a : ℂ) - Complex.digamma (b : ℂ))
        - (gaussSum (a : ℂ) - gaussSum (b : ℂ)) := by ring

  have hpsi : ‖Complex.digamma (a : ℂ) - Complex.digamma (b : ℂ)‖ ≤ 3 / n := by
    rw [digamma_ofReal hapos, digamma_ofReal hbpos, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    exact abs_deriv_log_Gamma_sub_le hn ha hb hab
  have hG : ‖gaussSum (a : ℂ) - gaussSum (b : ℂ)‖ ≤ 2 / n := by
    refine (norm_gaussSum_sub_le hn ha hb).trans ?_
    have hle : |a - b| * (2 / n) ≤ 1 * (2 / n) := by gcongr
    simpa using hle
  have hfive : (5 : ℝ) / n = 3 / n + 2 / n := by ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  linarith

end GammaSolution
end

-- RSBounds.IEANTNGamma.Periodic
section
namespace GammaSolution

theorem eq_zero_of_periodic_of_nat_of_oscillation {F : Type*} [NormedAddCommGroup F]
    {E : ℝ → F} {C : ℝ}
    (hper : ∀ x : ℝ, 0 < x → E (x + 1) = E x)
    (hnat : ∀ n : ℕ, E ((n : ℝ) + 1) = 0)
    (hosc : ∀ n : ℕ, 1 ≤ n → ∀ a b : ℝ, (n : ℝ) ≤ a → (n : ℝ) ≤ b → |a - b| ≤ 1 →
      ‖E a - E b‖ ≤ C / n)
    {x : ℝ} (hx : 0 < x) : E x = 0 := by

  have hshift : ∀ n : ℕ, ∀ y : ℝ, 0 < y → E (y + n) = E y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro y hy
      have hyn : (0 : ℝ) < y + n := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hre : y + ((n + 1 : ℕ) : ℝ) = (y + (n : ℝ)) + 1 := by push_cast; ring
      rw [hre, hper (y + n) hyn, ih y hy]
  have key : ∀ n : ℕ, 1 ≤ n → ‖E x‖ ≤ C / n := by
    intro n hn
    set m : ℕ := ⌊x⌋₊ with hm
    have hmx : (m : ℝ) ≤ x := Nat.floor_le hx.le
    have hxm : x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hnnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n

    have hEx : E x = E (x + n) := (hshift n x hx).symm
    have hzero : E (((m + n : ℕ) : ℝ) + 1) = 0 := hnat (m + n)
    have hle_a : (n : ℝ) ≤ x + n := by linarith
    have hle_b : (n : ℝ) ≤ ((m + n : ℕ) : ℝ) + 1 := by push_cast; linarith
    have hclose : |(x + n) - (((m + n : ℕ) : ℝ) + 1)| ≤ 1 := by
      push_cast
      rw [abs_le]
      constructor <;> linarith
    have hb := hosc n hn (x + n) (((m + n : ℕ) : ℝ) + 1) hle_a hle_b hclose
    rwa [hzero, sub_zero, ← hEx] at hb

  have hlim : Filter.Tendsto (fun n : ℕ ↦ C / (n : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have hle : ‖E x‖ ≤ 0 :=
    ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨1, fun n hn ↦ key n hn⟩)
  exact norm_le_zero_iff.mp hle

end GammaSolution
end

-- RSBounds.IEANTNGamma.RealIdentity
section
namespace GammaSolution

open Complex

noncomputable def gaussError (x : ℝ) : ℂ :=
  Complex.digamma (x : ℂ) - gaussSum (x : ℂ)

theorem ofReal_ne_neg_nat {x : ℝ} (hx : 0 < x) (m : ℕ) : (x : ℂ) ≠ -(m : ℂ) :=
  ofReal_ne_neg_natCast hx m

theorem gaussError_add_one {x : ℝ} (hx : 0 < x) : gaussError (x + 1) = gaussError x := by
  have hne := ofReal_ne_neg_nat hx
  have hcast : ((x + 1 : ℝ) : ℂ) = (x : ℂ) + 1 := by push_cast; ring
  have hx0 : (x : ℂ) ≠ 0 := by simpa using hne 0
  simp only [gaussError, hcast]
  rw [Complex.digamma_apply_add_one _ hne, gaussSum_add_one hne]
  ring

theorem gaussError_nat_add_one (n : ℕ) : gaussError ((n : ℝ) + 1) = 0 := by
  have hcast : (((n : ℝ) + 1 : ℝ) : ℂ) = (n : ℂ) + 1 := by push_cast; ring
  simp only [gaussError, hcast]
  rw [digamma_eq_gaussSum_nat_add_one n, sub_self]

theorem norm_gaussError_sub_le {n : ℕ} (hn : 1 ≤ n) {a b : ℝ}
    (ha : (n : ℝ) ≤ a) (hb : (n : ℝ) ≤ b) (hab : |a - b| ≤ 1) :
    ‖gaussError a - gaussError b‖ ≤ 5 / n :=
  norm_error_sub_le hn ha hb hab

theorem digamma_eq_gaussSum_of_pos {x : ℝ} (hx : 0 < x) :
    Complex.digamma (x : ℂ) = gaussSum (x : ℂ) := by
  have h : gaussError x = 0 :=
    eq_zero_of_periodic_of_nat_of_oscillation
      (fun y hy ↦ gaussError_add_one hy)
      gaussError_nat_add_one
      (fun n hn a b ha hb hab ↦ norm_gaussError_sub_le hn ha hb hab)
      hx
  rwa [gaussError, sub_eq_zero] at h

end GammaSolution
end

-- RSBounds.IEANTNGamma.Analytic
section
namespace GammaSolution

open Complex

def rightHalfPlane : Set ℂ := {s : ℂ | 0 < s.re}

theorem isOpen_rightHalfPlane : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

theorem isPreconnected_rightHalfPlane : IsPreconnected rightHalfPlane :=
  (convex_halfSpace_re_gt 0).isPreconnected

theorem mem_rightHalfPlane_iff {s : ℂ} : s ∈ rightHalfPlane ↔ 0 < s.re := Iff.rfl

theorem ne_neg_natCast_of_mem {s : ℂ} (hs : s ∈ rightHalfPlane) (m : ℕ) : s ≠ -(m : ℂ) := by
  intro h
  have hre : s.re = -(m : ℝ) := by rw [h]; simp
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have := mem_rightHalfPlane_iff.mp hs
  linarith

theorem norm_gaussTerm_le_of_re {δ M : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {s : ℂ}
    (hre : δ ≤ s.re) (hM : ‖s‖ ≤ M) (k : ℕ) :
    ‖gaussTerm s k‖ ≤ (M + 1) / (δ * ((k : ℝ) + 1) ^ 2) := by
  have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hspos : (0 : ℝ) < s.re := lt_of_lt_of_le hδ0 hre
  have hne : ∀ m : ℕ, s ≠ -(m : ℂ) := ne_neg_natCast_of_mem (mem_rightHalfPlane_iff.mpr hspos)
  have hMnn : (0 : ℝ) ≤ M := le_trans (norm_nonneg s) hM

  have hk1 : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
    have hc : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hc, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hks : (k : ℝ) + δ ≤ ‖(k : ℂ) + s‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  have hkspos : (0 : ℝ) < ‖(k : ℂ) + s‖ := lt_of_lt_of_le (by linarith) hks

  have hnum : ‖s - 1‖ ≤ M + 1 := by
    refine le_trans (norm_sub_le s 1) ?_
    simpa using hM
  rw [gaussTerm_eq hne k, norm_div, norm_mul, hk1]
  have hden : (0 : ℝ) < ((k : ℝ) + 1) * ‖(k : ℂ) + s‖ := by positivity
  have hden2 : (0 : ℝ) < δ * ((k : ℝ) + 1) ^ 2 := by positivity
  rw [div_le_div_iff₀ hden hden2]

  have hstep : δ * ((k : ℝ) + 1) ≤ ‖(k : ℂ) + s‖ := by nlinarith
  have hM1 : (0 : ℝ) ≤ (M + 1) * ((k : ℝ) + 1) := by positivity
  calc ‖s - 1‖ * (δ * ((k : ℝ) + 1) ^ 2)
      = (‖s - 1‖ * ((k : ℝ) + 1)) * (δ * ((k : ℝ) + 1)) := by ring
    _ ≤ ((M + 1) * ((k : ℝ) + 1)) * ‖(k : ℂ) + s‖ :=
        mul_le_mul (mul_le_mul_of_nonneg_right hnum (by linarith)) hstep (by positivity) hM1
    _ = (M + 1) * (((k : ℝ) + 1) * ‖(k : ℂ) + s‖) := by ring

theorem summable_gaussTerm_bound {δ M : ℝ} (hδ0 : 0 < δ) :
    Summable (fun k : ℕ ↦ (M + 1) / (δ * ((k : ℝ) + 1) ^ 2)) := by
  have hbase : Summable (fun k : ℕ ↦ 1 / ((k : ℝ) + 1) ^ 2) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using h
  have hEq : ∀ k : ℕ, (M + 1) / (δ * ((k : ℝ) + 1) ^ 2)
      = ((M + 1) / δ) * (1 / ((k : ℝ) + 1) ^ 2) := by
    intro k
    field_simp
  simpa only [hEq] using hbase.mul_left ((M + 1) / δ)

theorem differentiableOn_gaussTerm (k : ℕ) {V : Set ℂ} (hV : V ⊆ rightHalfPlane) :
    DifferentiableOn ℂ (fun s ↦ gaussTerm s k) V := by
  intro s hs
  have hne : ((k : ℂ) + s) ≠ 0 := by
    intro h
    have hre : (k : ℝ) + s.re = 0 := by
      have := congrArg Complex.re h
      simpa using this
    have h1 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h2 := mem_rightHalfPlane_iff.mp (hV hs)
    linarith
  refine DifferentiableAt.differentiableWithinAt ?_
  simp only [gaussTerm]
  exact (differentiableAt_const _).sub (((differentiableAt_const _).add differentiableAt_id).inv hne)

theorem differentiableAt_gaussSum {s₀ : ℂ} (hs₀ : s₀ ∈ rightHalfPlane) :
    DifferentiableAt ℂ gaussSum s₀ := by
  have hre₀ : 0 < s₀.re := mem_rightHalfPlane_iff.mp hs₀
  set δ : ℝ := min (s₀.re / 2) 1 with hδ
  set M : ℝ := ‖s₀‖ + 1 with hM
  have hδ0 : 0 < δ := lt_min (by linarith) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδre : δ < s₀.re := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set V : Set ℂ := {s : ℂ | δ < s.re} ∩ Metric.ball 0 M with hV
  have hVopen : IsOpen V :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hs₀V : s₀ ∈ V := by
    refine ⟨hδre, ?_⟩
    simp [Metric.mem_ball, dist_zero_right, hM]
  have hVsub : V ⊆ rightHalfPlane := fun s hs ↦
    mem_rightHalfPlane_iff.mpr (lt_trans hδ0 hs.1)

  have hbound : ∀ (k : ℕ) (w : ℂ), w ∈ V → ‖gaussTerm w k‖ ≤ (M + 1) / (δ * ((k : ℝ) + 1) ^ 2) := by
    intro k w hw
    refine norm_gaussTerm_le_of_re hδ0 hδ1 (le_of_lt hw.1) ?_ k
    have := hw.2
    simp only [Metric.mem_ball, dist_zero_right] at this
    exact this.le
  have hsum : DifferentiableOn ℂ (fun w : ℂ ↦ ∑' k : ℕ, gaussTerm w k) V :=
    Complex.differentiableOn_tsum_of_summable_norm (summable_gaussTerm_bound (M := M) hδ0)
      (fun k ↦ differentiableOn_gaussTerm k hVsub) hVopen hbound
  have hat : DifferentiableAt ℂ (fun w : ℂ ↦ ∑' k : ℕ, gaussTerm w k) s₀ :=
    hsum.differentiableAt (hVopen.mem_nhds hs₀V)
  have hres : DifferentiableAt ℂ
      (fun w : ℂ ↦ -(Real.eulerMascheroniConstant : ℂ) + ∑' k : ℕ, gaussTerm w k) s₀ :=
    (differentiableAt_const _).add hat
  exact hres

theorem differentiableOn_gaussSum : DifferentiableOn ℂ gaussSum rightHalfPlane :=
  fun _ hs ↦ (differentiableAt_gaussSum hs).differentiableWithinAt

theorem analyticOnNhd_gaussSum : AnalyticOnNhd ℂ gaussSum rightHalfPlane :=
  differentiableOn_gaussSum.analyticOnNhd isOpen_rightHalfPlane

theorem differentiableOn_Gamma_rightHalfPlane :
    DifferentiableOn ℂ Complex.Gamma rightHalfPlane := fun s hs ↦
  (Complex.differentiableAt_Gamma s (ne_neg_natCast_of_mem hs)).differentiableWithinAt

theorem differentiableOn_digamma : DifferentiableOn ℂ Complex.digamma rightHalfPlane := by
  have hΓ := differentiableOn_Gamma_rightHalfPlane
  have hd : DifferentiableOn ℂ (deriv Complex.Gamma) rightHalfPlane :=
    hΓ.deriv isOpen_rightHalfPlane
  have hne : ∀ s ∈ rightHalfPlane, Complex.Gamma s ≠ 0 := fun s hs ↦
    Complex.Gamma_ne_zero (ne_neg_natCast_of_mem hs)
  have := hd.div hΓ hne
  simpa only [Complex.digamma_def, logDeriv] using this

theorem analyticOnNhd_digamma : AnalyticOnNhd ℂ Complex.digamma rightHalfPlane :=
  differentiableOn_digamma.analyticOnNhd isOpen_rightHalfPlane

theorem frequently_digamma_eq_gaussSum :
    ∃ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, Complex.digamma z = gaussSum z := by
  set u : ℕ → ℂ := fun n ↦ (((1 : ℝ) + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) with hu
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 + 1 / ((n : ℝ) + 1) := by
    intro n
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    positivity
  have htend : Filter.Tendsto u Filter.atTop (nhds (1 : ℂ)) := by
    have h0 : Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhds (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc : Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ)) Filter.atTop (nhds (1 : ℝ)) :=
      tendsto_const_nhds
    have hr : Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) + 1 / ((n : ℝ) + 1)) Filter.atTop
        (nhds (1 : ℝ)) := by simpa using hc.add h0
    simpa [hu, Function.comp_def] using (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hr
  have hne : ∀ n : ℕ, u n ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    simp only [hu, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have : (1 : ℝ) + 1 / ((n : ℝ) + 1) = 1 := by exact_mod_cast h
    linarith
  have hwithin : Filter.Tendsto u Filter.atTop (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u htend
      (Filter.Eventually.of_forall hne)
  refine hwithin.frequently (Filter.Frequently.of_forall fun n ↦ ?_)
  simpa [hu] using digamma_eq_gaussSum_of_pos (hpos n)

theorem digamma_eq_gaussSum {s : ℂ} (hs : 0 < s.re) : Complex.digamma s = gaussSum s := by
  have h1 : (1 : ℂ) ∈ rightHalfPlane := by simp [mem_rightHalfPlane_iff]
  exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_digamma
    analyticOnNhd_gaussSum isPreconnected_rightHalfPlane h1 frequently_digamma_eq_gaussSum
    (mem_rightHalfPlane_iff.mpr hs)

end GammaSolution
end

-- RSBounds.BacklundDigammaSeriesAdapter
section
open Complex

namespace TernaryGoldbach.RSBounds.BacklundZeta23.DigammaSeries

lemma harmonic_cast_eq (N : ℕ) :
    ((harmonic N : ℚ) : ℝ) = ∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1) := by
  rw [harmonic]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [one_div]

theorem hasSum_digamma_series {z : ℂ} (hz : 0 < z.re) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + n + 1))
      (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z) := by
  have hz' : 0 < (z + 1).re := by simp; linarith
  have hne := GammaSolution.ne_neg_natCast_of_mem hz
  have hne' := GammaSolution.ne_neg_natCast_of_mem (s := z + 1) hz'
  have hs := (GammaSolution.summable_gaussTerm hne').hasSum
  have he : (∑' k, GammaSolution.gaussTerm (z + 1) k) =
      Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z := by
    have h := GammaSolution.digamma_eq_gaussSum hz'
    rw [Complex.digamma_apply_add_one z hne, GammaSolution.gaussSum] at h
    simp only [one_div]
    linear_combination -h
  rw [he] at hs
  change HasSum (fun n : ℕ => ((n : ℂ) + 1)⁻¹ - ((n : ℂ) + (z + 1))⁻¹)
    (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z) at hs
  simpa only [GammaSolution.gaussTerm, one_div, add_assoc, add_comm, add_left_comm] using hs

end TernaryGoldbach.RSBounds.BacklundZeta23.DigammaSeries
end

-- RSBounds.BacklundDigammaStirling
section
noncomputable section

namespace TernaryGoldbach.RSBounds.BacklundZeta23
namespace StirlingVert

open Complex Filter Topology MeasureTheory intervalIntegral Set

theorem intervalIntegral_mul_const_C (c : ℂ) (f : ℝ → ℂ) (a b : ℝ) :
    ∫ x in a..b, f x * c = (∫ x in a..b, f x) * c :=
  intervalIntegral.integral_mul_const c f

theorem abs_im_le_norm_add {w : ℂ} (x : ℝ) : |w.im| ≤ ‖(x : ℂ) + w‖ := by
  have := Complex.abs_im_le_norm ((x : ℂ) + w)
  simpa using this

theorem re_add_pos {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) : 0 < ((x : ℂ) + w).re := by
  simp; linarith

theorem add_mem_slitPlane {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) :
    (x : ℂ) + w ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (re_add_pos hw hx))

theorem add_ne_zero {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) : (x : ℂ) + w ≠ 0 :=
  fun h => by have := re_add_pos hw hx; rw [h] at this; simp at this

theorem hasDerivAt_log_add {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => Complex.log ((y : ℂ) + w)) (((x : ℂ) + w)⁻¹) x := by
  have h1 : HasDerivAt (fun z : ℂ => Complex.log (z + w)) (((x : ℂ) + w)⁻¹) (x : ℂ) := by
    have := (Complex.hasDerivAt_log (add_mem_slitPlane hw hx)).comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).add_const w)
    simpa [Function.comp_def] using this
  exact h1.comp_ofReal

theorem integral_inv_add_eq_log_sub {w : ℂ} (hw : 0 < w.re) {m : ℝ} (hm : 0 ≤ m) :
    ∫ x in m..(m + 1), ((x : ℂ) + w)⁻¹
      = Complex.log (((m + 1 : ℝ) : ℂ) + w) - Complex.log ((m : ℂ) + w) := by
  have hcont : ContinuousOn (fun x : ℝ => ((x : ℂ) + w)⁻¹) (uIcc m (m + 1)) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact add_ne_zero hw (by linarith [hx.1])
  rw [integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => Complex.log ((y : ℂ) + w))
    (fun x hx => by
      rw [uIcc_of_le (by linarith)] at hx
      exact hasDerivAt_log_add hw (by linarith [hx.1]))
    (hcont.intervalIntegrable)]

theorem inv_add_expand {w : ℂ} {x m : ℝ} (hxw : (x : ℂ) + w ≠ 0) (hmw : (m : ℂ) + w ≠ 0) :
    ((x : ℂ) + w)⁻¹
      = ((m : ℂ) + w)⁻¹ - ((x - m : ℝ) : ℂ) / ((m : ℂ) + w) ^ 2
        + ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w)) := by
  field_simp
  push_cast
  ring

def eps (w : ℂ) (m : ℝ) : ℂ :=
  ∫ x in m..(m + 1), ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))

set_option maxHeartbeats 1200000 in
theorem integral_inv_add_eq {w : ℂ} (hw : 0 < w.re) {m : ℝ} (hm : 0 ≤ m) :
    ∫ x in m..(m + 1), ((x : ℂ) + w)⁻¹
      = ((m : ℂ) + w)⁻¹ - (1 / 2 : ℂ) / ((m : ℂ) + w) ^ 2 + eps w m := by
  have hmw := add_ne_zero hw hm
  have hcongr : ∫ x in m..(m + 1), ((x : ℂ) + w)⁻¹ = ∫ x in m..(m + 1),
      (((m : ℂ) + w)⁻¹ - ((x - m : ℝ) : ℂ) / ((m : ℂ) + w) ^ 2
        + ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))) := by
    apply integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact inv_add_expand (add_ne_zero hw (by linarith [hx.1])) hmw
  rw [hcongr]
  have hI : ∀ {f : ℝ → ℂ}, Continuous f → IntervalIntegrable f volume m (m + 1) :=
    fun hf => hf.intervalIntegrable _ _
  have hR : IntervalIntegrable (fun x : ℝ =>
      ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))) volume m (m + 1) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (f := fun x : ℝ => ((x - m : ℝ) : ℂ) ^ 2)
      (g := fun x : ℝ => ((m : ℂ) + w) ^ 2 * ((x : ℂ) + w)) (((Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)).pow _).continuousOn) ((continuous_const.mul (Complex.continuous_ofReal.add continuous_const)).continuousOn)
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact mul_ne_zero (pow_ne_zero _ hmw) (add_ne_zero hw (by linarith [hx.1]))
  have hmid : ∫ x in m..(m + 1), ((x - m : ℝ) : ℂ) / ((m : ℂ) + w) ^ 2
      = ((1 / 2 : ℝ) : ℂ) * ((((m : ℂ) + w) ^ 2)⁻¹) := by
    have e : (fun x : ℝ => ((x - m : ℝ) : ℂ) / ((m : ℂ) + w) ^ 2)
        = fun x : ℝ => ((x - m : ℝ) : ℂ) * ((((m : ℂ) + w) ^ 2)⁻¹) := by
      funext x; rw [div_eq_mul_inv]
    rw [e, intervalIntegral_mul_const_C, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_comp_sub_right (fun u : ℝ => u) m]
    simp only [sub_self, add_sub_cancel_left, integral_id]
    norm_num
  rw [integral_add ((hI (by fun_prop)).sub (hI (by fun_prop))) hR,
    integral_sub (hI (by fun_prop)) (hI (by fun_prop)), intervalIntegral.integral_const, hmid,
    show m + 1 - m = (1 : ℝ) by ring, one_smul]
  unfold eps
  push_cast
  ring

set_option maxHeartbeats 1200000 in
theorem norm_eps_le {w : ℂ} (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) {m : ℝ} (hm : 0 ≤ m) :
    ‖eps w m‖ ≤ 1 / (3 * ‖(m : ℂ) + w‖ ^ 2 * |w.im|) := by
  have hmw := add_ne_zero hw hm
  have hM : 0 < ‖(m : ℂ) + w‖ := norm_pos_iff.mpr hmw
  have ht0 : 0 < |w.im| := by linarith
  unfold eps
  calc ‖∫ x in m..(m + 1), ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))‖
      ≤ ∫ x in m..(m + 1), ‖((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ x in m..(m + 1), (x - m) ^ 2 / (‖(m : ℂ) + w‖ ^ 2 * |w.im|) := by
        apply intervalIntegral.integral_mono_on (by linarith)
        · refine (ContinuousOn.intervalIntegrable ?_).norm
          apply ContinuousOn.div (f := fun x : ℝ => ((x - m : ℝ) : ℂ) ^ 2)
            (g := fun x : ℝ => ((m : ℂ) + w) ^ 2 * ((x : ℂ) + w)) (((Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)).pow _).continuousOn) ((continuous_const.mul (Complex.continuous_ofReal.add continuous_const)).continuousOn)
          intro x hx
          rw [uIcc_of_le (by linarith)] at hx
          exact mul_ne_zero (pow_ne_zero _ hmw) (add_ne_zero hw (by linarith [hx.1]))
        · exact (by fun_prop : Continuous fun x : ℝ => (x - m) ^ 2 / (‖(m : ℂ) + w‖ ^ 2 * |w.im|))
            |>.intervalIntegrable _ _
        · intro x hx
          have hx0 : 0 ≤ x := by linarith [hx.1]
          have hxw : |w.im| ≤ ‖(x : ℂ) + w‖ := abs_im_le_norm_add x
          rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            sq_abs]
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hxw (by positivity)
    _ = 1 / (3 * ‖(m : ℂ) + w‖ ^ 2 * |w.im|) := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 2) m]
        simp only [sub_self, add_sub_cancel_left, integral_pow]
        norm_num
        field_simp

section Seq
variable {w : ℂ}

theorem natp1_re_pos (hw : 0 < w.re) (n : ℕ) : 0 < ((n : ℂ) + 1 + w).re := by
  simp; positivity

theorem natp1_ne_zero (hw : 0 < w.re) (n : ℕ) : (n : ℂ) + 1 + w ≠ 0 := fun h => by
  have := natp1_re_pos hw n; rw [h] at this; simp at this

theorem natp1_le_norm (hw : 0 < w.re) (n : ℕ) : (n : ℝ) + 1 ≤ ‖(n : ℂ) + 1 + w‖ := by
  have h := Complex.re_le_norm ((n : ℂ) + 1 + w)
  simp at h; linarith

theorem inv_natp1_eq (hw : 0 < w.re) (n : ℕ) :
    ((n : ℂ) + 1 + w)⁻¹
      = (Complex.log (((n + 1 : ℕ) : ℂ) + 1 + w) - Complex.log ((n : ℂ) + 1 + w))
        + (1 / 2 : ℂ) / ((n : ℂ) + 1 + w) ^ 2 - eps w ((n : ℝ) + 1) := by
  have hm : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have h1 := integral_inv_add_eq hw hm
  have h2 := integral_inv_add_eq_log_sub hw hm
  rw [h2] at h1
  have e1 : ((((n : ℝ) + 1 : ℝ)) : ℂ) + w = (n : ℂ) + 1 + w := by push_cast; ring
  have e2 : ((((n : ℝ) + 1 + 1 : ℝ)) : ℂ) + w = ((n + 1 : ℕ) : ℂ) + 1 + w := by push_cast; ring
  rw [e1, e2] at h1
  linear_combination (-1 : ℂ) * h1

def rho (w : ℂ) (n : ℕ) : ℂ := 1 / (((n : ℂ) + 1 + w) ^ 2 * ((n : ℂ) + 2 + w))

theorem inv_natp1_sq_eq (hw : 0 < w.re) (n : ℕ) :
    1 / ((n : ℂ) + 1 + w) ^ 2
      = (((n : ℂ) + 1 + w)⁻¹ - (((n + 1 : ℕ) : ℂ) + 1 + w)⁻¹) + rho w n := by
  have h1 := natp1_ne_zero hw n
  have h2 := natp1_ne_zero hw (n + 1)
  have e : ((n + 1 : ℕ) : ℂ) + 1 + w = (n : ℂ) + 2 + w := by push_cast; ring
  rw [e] at h2 ⊢
  unfold rho
  field_simp
  ring

theorem norm_rho_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (n : ℕ) :
    ‖rho w n‖ ≤ 1 / (‖(n : ℂ) + 1 + w‖ ^ 2 * |w.im|) := by
  have h1 := natp1_ne_zero hw n
  have hn2 : |w.im| ≤ ‖(n : ℂ) + 2 + w‖ := by
    have := Complex.abs_im_le_norm ((n : ℂ) + 2 + w); simpa using this
  have ht0 : 0 < |w.im| := by linarith
  unfold rho
  rw [norm_div, norm_one, norm_mul, norm_pow]
  apply div_le_div_of_nonneg_left zero_le_one (by positivity)
  exact mul_le_mul_of_nonneg_left hn2 (by positivity)

theorem norm_eps_natp1_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (n : ℕ) :
    ‖eps w ((n : ℝ) + 1)‖ ≤ 1 / (3 * ‖(n : ℂ) + 1 + w‖ ^ 2 * |w.im|) := by
  have := norm_eps_le hw ht (m := (n : ℝ) + 1) (by positivity)
  rw [show ((((n : ℝ) + 1 : ℝ)) : ℂ) + w = (n : ℂ) + 1 + w by push_cast; ring] at this
  exact this

theorem partial_sum_eq (hw : 0 < w.re) (N : ℕ) :
    ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (w + n + 1))
      = (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1))
        - (Complex.log ((N : ℂ) + 1 + w) - Complex.log ((0 : ℕ) + 1 + w : ℂ))
        - (1 / 2 : ℂ) * (((0 : ℕ) + 1 + w : ℂ)⁻¹ - ((N : ℂ) + 1 + w)⁻¹
            + ∑ n ∈ Finset.range N, rho w n)
        + ∑ n ∈ Finset.range N, eps w ((n : ℝ) + 1) := by
  rw [Finset.sum_sub_distrib]
  have hterm : ∀ n ∈ Finset.range N, (1 : ℂ) / (w + n + 1)
      = (Complex.log (((n + 1 : ℕ) : ℂ) + 1 + w) - Complex.log ((n : ℂ) + 1 + w))
        + (1 / 2 : ℂ) * ((((n : ℂ) + 1 + w)⁻¹ - (((n + 1 : ℕ) : ℂ) + 1 + w)⁻¹) + rho w n)
        - eps w ((n : ℝ) + 1) := by
    intro n _
    have A := inv_natp1_eq hw n
    have B := inv_natp1_sq_eq hw n
    rw [show (1 : ℂ) / (w + n + 1) = ((n : ℂ) + 1 + w)⁻¹ by rw [one_div]; ring_nf]
    linear_combination A + (1 / 2 : ℂ) * B
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_range_sub (fun n => Complex.log ((n : ℂ) + 1 + w)) N, ← Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_range_sub' (fun n => ((n : ℂ) + 1 + w)⁻¹) N]
  push_cast
  ring

theorem norm_sq_natp1_ge (hw : 0 < w.re) (n : ℕ) :
    ((n : ℝ) + 1) ^ 2 + w.im ^ 2 ≤ ‖(n : ℂ) + 1 + w‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : ((n : ℂ) + 1 + w).re = (n : ℝ) + 1 + w.re := by simp
  have him : ((n : ℂ) + 1 + w).im = w.im := by simp
  rw [hre, him]
  nlinarith

theorem inv_norm_sq_le_telescope (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (n : ℕ) :
    1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 2 * (1 / ((n : ℝ) + |w.im|) - 1 / ((n : ℝ) + 1 + |w.im|)) := by
  have h1 := norm_sq_natp1_ge hw n
  have ht0 : 0 < |w.im| := by linarith
  have hpos : 0 < ((n : ℝ) + 1) ^ 2 + w.im ^ 2 := by positivity
  have htele : 1 / ((n : ℝ) + |w.im|) - 1 / ((n : ℝ) + 1 + |w.im|)
      = 1 / (((n : ℝ) + |w.im|) * ((n : ℝ) + 1 + |w.im|)) := by
    field_simp; ring
  rw [htele]
  have hsq : w.im ^ 2 = |w.im| ^ 2 := (sq_abs _).symm
  calc 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 1 / (((n : ℝ) + 1) ^ 2 + w.im ^ 2) :=
        div_le_div_of_nonneg_left zero_le_one hpos h1
    _ ≤ 2 * (1 / (((n : ℝ) + |w.im|) * ((n : ℝ) + 1 + |w.im|))) := by
        rw [hsq, ← div_eq_mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg ((n : ℝ) + 1 - |w.im|)]

theorem sum_inv_norm_sq_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (N : ℕ) :
    ∑ n ∈ Finset.range N, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 2 / |w.im| := by
  have ht0 : 0 < |w.im| := by linarith
  calc ∑ n ∈ Finset.range N, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2
      ≤ ∑ n ∈ Finset.range N, 2 * (1 / ((n : ℝ) + |w.im|) - 1 / ((n : ℝ) + 1 + |w.im|)) :=
        Finset.sum_le_sum fun n _ => inv_norm_sq_le_telescope hw ht n
    _ = 2 * (1 / |w.im| - 1 / ((N : ℝ) + |w.im|)) := by
        rw [← Finset.mul_sum, Finset.sum_congr rfl (fun (i : ℕ) _ => by
          rw [show ((i : ℝ) + 1 + |w.im|) = (((i + 1 : ℕ) : ℝ) + |w.im|) by push_cast; ring]),
          Finset.sum_range_sub' (fun n : ℕ => 1 / ((n : ℝ) + |w.im|)) N]
        push_cast
        ring
    _ ≤ 2 / |w.im| := by
        have : 0 ≤ 1 / ((N : ℝ) + |w.im|) := by positivity
        rw [div_eq_mul_one_div 2]
        linarith

theorem summable_inv_norm_sq (hw : 0 < w.re) :
    Summable (fun n : ℕ => 1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have := (Real.summable_one_div_nat_pow.mpr one_lt_two)
    exact_mod_cast (summable_nat_add_iff 1).mpr this
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  exact div_le_div_of_nonneg_left zero_le_one (by positivity)
    (pow_le_pow_left₀ (by positivity) (natp1_le_norm hw n) 2)

theorem summable_rho (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) : Summable (rho w) := by
  refine Summable.of_norm_bounded ((summable_inv_norm_sq hw).mul_left (1 / |w.im|)) fun n => ?_
  refine le_trans (norm_rho_le hw ht n) (le_of_eq ?_)
  field_simp

theorem summable_eps (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    Summable (fun n : ℕ => eps w ((n : ℝ) + 1)) := by
  refine Summable.of_norm_bounded ((summable_inv_norm_sq hw).mul_left (1 / (3 * |w.im|)))
    fun n => ?_
  refine le_trans (norm_eps_natp1_le hw ht n) (le_of_eq ?_)
  field_simp

theorem summable_norm_rho (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) : Summable (fun n => ‖rho w n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_inv_norm_sq hw).mul_left (1 / |w.im|))
  refine le_trans (norm_rho_le hw ht n) (le_of_eq ?_)
  field_simp

theorem summable_norm_eps (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    Summable (fun n : ℕ => ‖eps w ((n : ℝ) + 1)‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_inv_norm_sq hw).mul_left (1 / (3 * |w.im|)))
  refine le_trans (norm_eps_natp1_le hw ht n) (le_of_eq ?_)
  field_simp

theorem tsum_inv_norm_sq_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ∑' n : ℕ, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 2 / |w.im| :=
  Real.tsum_le_of_sum_range_le (fun n => by positivity) (sum_inv_norm_sq_le hw ht)

theorem norm_tsum_rho_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ‖∑' n, rho w n‖ ≤ 2 / w.im ^ 2 := by
  have ht0 : 0 < |w.im| := by linarith
  have hS := tsum_inv_norm_sq_le hw ht
  calc ‖∑' n, rho w n‖ ≤ ∑' n, ‖rho w n‖ := norm_tsum_le_tsum_norm (summable_norm_rho hw ht)
    _ ≤ ∑' n : ℕ, (1 / |w.im|) * (1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
        refine Summable.tsum_le_tsum (fun n => ?_) (summable_norm_rho hw ht)
          ((summable_inv_norm_sq hw).mul_left _)
        refine le_trans (norm_rho_le hw ht n) (le_of_eq ?_)
        field_simp
    _ = (1 / |w.im|) * ∑' n : ℕ, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 := tsum_mul_left
    _ ≤ (1 / |w.im|) * (2 / |w.im|) := by gcongr
    _ = 2 / w.im ^ 2 := by rw [← sq_abs]; field_simp

theorem norm_tsum_eps_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ ≤ (2 / 3) / w.im ^ 2 := by
  have ht0 : 0 < |w.im| := by linarith
  have hS := tsum_inv_norm_sq_le hw ht
  calc ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ ≤ ∑' n : ℕ, ‖eps w ((n : ℝ) + 1)‖ :=
        norm_tsum_le_tsum_norm (summable_norm_eps hw ht)
    _ ≤ ∑' n : ℕ, (1 / (3 * |w.im|)) * (1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
        refine Summable.tsum_le_tsum (fun n => ?_) (summable_norm_eps hw ht)
          ((summable_inv_norm_sq hw).mul_left _)
        refine le_trans (norm_eps_natp1_le hw ht n) (le_of_eq ?_)
        field_simp
    _ = (1 / (3 * |w.im|)) * ∑' n : ℕ, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 := tsum_mul_left
    _ ≤ (1 / (3 * |w.im|)) * (2 / |w.im|) := by gcongr
    _ = (2 / 3) / w.im ^ 2 := by rw [← sq_abs]; field_simp

theorem tendsto_harmonic_sub_clog (hw : 0 < w.re) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1))
      - Complex.log ((N : ℂ) + 1 + w)) atTop (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by

  have hdecomp : ∀ N : ℕ, (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1))
      - Complex.log ((N : ℂ) + 1 + w)
      = (((harmonic N : ℚ) : ℝ) - Real.log ((N : ℝ) + 1) : ℝ)
        - Complex.log (1 + w / ((N : ℂ) + 1)) := by
    intro N
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hN1 : (N : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero N
    have hq' : 1 + w / ((N : ℂ) + 1) = ((N : ℂ) + 1 + w) / ((N : ℂ) + 1) := by
      field_simp
    have hq : 1 + w / ((N : ℂ) + 1) ≠ 0 := by
      rw [hq']; exact div_ne_zero (natp1_ne_zero hw N) hN1
    have hlog : Complex.log ((N : ℂ) + 1 + w)
        = Real.log ((N : ℝ) + 1) + Complex.log (1 + w / ((N : ℂ) + 1)) := by
      rw [← Complex.log_ofReal_mul hN hq, hq']
      congr 1
      push_cast
      field_simp
    rw [hlog, TernaryGoldbach.RSBounds.BacklundZeta23.DigammaSeries.harmonic_cast_eq]
    push_cast
    ring
  simp_rw [hdecomp]
  have h1 : Tendsto (fun N : ℕ => ((((harmonic N : ℚ) : ℝ) - Real.log ((N : ℝ) + 1) : ℝ) : ℂ))
      atTop (𝓝 (Real.eulerMascheroniConstant : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_harmonic_sub_log_add_one
  have h2 : Tendsto (fun N : ℕ => Complex.log (1 + w / ((N : ℂ) + 1))) atTop (𝓝 0) := by
    have hq : Tendsto (fun N : ℕ => w / ((N : ℂ) + 1)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have : (fun N : ℕ => ‖w / ((N : ℂ) + 1)‖) = fun N : ℕ => ‖w‖ * (1 / ((N : ℝ) + 1)) := by
        funext N
        rw [norm_div, show ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        ring
      rw [this]
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ‖w‖
    have hcont : ContinuousAt Complex.log 1 := continuousAt_clog (by simp)
    have := hcont.tendsto.comp (by simpa using hq.const_add 1)
    simpa [Function.comp_def] using this
  simpa using h1.sub h2

theorem tendsto_inv_natp1 (hw : 0 < w.re) :
    Tendsto (fun N : ℕ => ((N : ℂ) + 1 + w)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat (fun N => norm_nonneg _) (fun N => ?_)
  rw [norm_inv]
  have h := natp1_le_norm hw N
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le hpos h

theorem digamma_eq (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    Complex.digamma w = Complex.log (1 + w) - 1 / w - (1 / 2 : ℂ) * (1 + w)⁻¹
      - (1 / 2 : ℂ) * (∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1) := by
  have hL := (TernaryGoldbach.RSBounds.BacklundZeta23.DigammaSeries.hasSum_digamma_series hw).tendsto_sum_nat

  have hR : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (w + n + 1)))
      atTop (𝓝 ((Real.eulerMascheroniConstant : ℂ) + Complex.log (1 + w)
        - (1 / 2 : ℂ) * ((1 + w)⁻¹ - 0 + ∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1))) := by
    have e : ∀ N : ℕ, ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (w + n + 1))
        = ((∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1)) - Complex.log ((N : ℂ) + 1 + w))
          + Complex.log (1 + w)
          - (1 / 2 : ℂ) * ((1 + w)⁻¹ - ((N : ℂ) + 1 + w)⁻¹ + ∑ n ∈ Finset.range N, rho w n)
          + ∑ n ∈ Finset.range N, eps w ((n : ℝ) + 1) := by
      intro N
      rw [partial_sum_eq hw N]
      push_cast
      ring
    simp_rw [e]
    refine (((tendsto_harmonic_sub_clog hw).add tendsto_const_nhds).sub
      (((tendsto_const_nhds.sub (tendsto_inv_natp1 hw)).add
        (summable_rho hw ht).hasSum.tendsto_sum_nat).const_mul _)).add
      (summable_eps hw ht).hasSum.tendsto_sum_nat
  have := tendsto_nhds_unique hL hR
  rw [sub_zero] at this
  linear_combination this

theorem log_one_add_sub_log (hw : 0 < w.re) :
    Complex.log (1 + w) - Complex.log w = w⁻¹ - (1 / 2 : ℂ) / w ^ 2 + eps w 0 := by
  have h1 := integral_inv_add_eq hw (m := 0) le_rfl
  have h2 := integral_inv_add_eq_log_sub hw (m := 0) le_rfl
  rw [h2] at h1
  simpa [add_comm] using h1

theorem norm_eps_zero_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) : ‖eps w 0‖ ≤ (1 / 3) / |w.im| ^ 3 := by
  have h := norm_eps_le hw ht (m := 0) le_rfl
  have ht0 : 0 < |w.im| := by linarith
  have hw' : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  simp only [Complex.ofReal_zero, zero_add] at h
  calc ‖eps w 0‖ ≤ 1 / (3 * ‖w‖ ^ 2 * |w.im|) := h
    _ ≤ 1 / (3 * |w.im| ^ 2 * |w.im|) := by
        apply div_le_div_of_nonneg_left zero_le_one (by positivity)
        gcongr
    _ = (1 / 3) / |w.im| ^ 3 := by field_simp

theorem digamma_stirling (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ‖Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w‖ ≤ 3 / w.im ^ 2 := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have h1w : 1 + w ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have ht0 : 0 < |w.im| := by linarith
  have hwn : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  have h1wn : |w.im| ≤ ‖1 + w‖ := by have := Complex.abs_im_le_norm (1 + w); simpa using this
  have hid := digamma_eq hw ht
  have hlog := log_one_add_sub_log hw

  have key : Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w
      = -(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0
        - (1 / 2 : ℂ) * (∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1) := by
    rw [hid, show Complex.log (1 + w) = Complex.log w + (w⁻¹ - (1 / 2 : ℂ) / w ^ 2 + eps w 0) by
      rw [← hlog]; ring]
    field_simp
    ring
  rw [key]
  have hsq : |w.im| ^ 2 = w.im ^ 2 := sq_abs _
  have b1 : ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))‖ ≤ (1 / 2) / w.im ^ 2 := by
    rw [norm_div, norm_neg, norm_mul, norm_pow]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this, ← hsq]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have h1 : 1 ≤ ‖1 + w‖ := le_trans (by simp; linarith) (Complex.re_le_norm (1 + w))
    calc |w.im| ^ 2 = |w.im| ^ 2 * 1 := (mul_one _).symm
      _ ≤ ‖w‖ ^ 2 * ‖1 + w‖ := by gcongr
  have b2 : ‖eps w 0‖ ≤ (2 / 3) / w.im ^ 2 := by
    refine le_trans (norm_eps_zero_le hw ht) ?_
    rw [← hsq, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : |w.im| ^ 3 = |w.im| ^ 2 * |w.im| := by ring
    rw [h3]
    have : 0 < |w.im| ^ 2 := by positivity
    nlinarith
  have b3 : ‖(1 / 2 : ℂ) * ∑' n, rho w n‖ ≤ 1 / w.im ^ 2 := by
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    have h := mul_le_mul_of_nonneg_left (norm_tsum_rho_le hw ht) (by norm_num : (0:ℝ) ≤ 1 / 2)
    calc 1 / 2 * ‖∑' n, rho w n‖ ≤ 1 / 2 * (2 / w.im ^ 2) := h
      _ = 1 / w.im ^ 2 := by ring
  have b4 := norm_tsum_eps_le hw ht
  calc ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0 - (1 / 2 : ℂ) * ∑' n, rho w n
        + ∑' n : ℕ, eps w ((n : ℝ) + 1)‖
      ≤ ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))‖ + ‖eps w 0‖ + ‖(1 / 2 : ℂ) * ∑' n, rho w n‖
        + ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ := by
        have s1 := norm_add_le (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0 - (1 / 2 : ℂ) * ∑' n, rho w n)
          (∑' n : ℕ, eps w ((n : ℝ) + 1))
        have s2 := norm_sub_le (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0) ((1 / 2 : ℂ) * ∑' n, rho w n)
        have s3 := norm_add_le (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))) (eps w 0)
        linarith
    _ ≤ (1 / 2) / w.im ^ 2 + (2 / 3) / w.im ^ 2 + 1 / w.im ^ 2 + (2 / 3) / w.im ^ 2 := by
        gcongr
    _ ≤ 3 / w.im ^ 2 := by
        have hpos : 0 < w.im ^ 2 := by rw [← hsq]; positivity
        rw [show (1 / 2) / w.im ^ 2 + (2 / 3) / w.im ^ 2 + 1 / w.im ^ 2 + (2 / 3) / w.im ^ 2
          = (17 / 6) / w.im ^ 2 by ring]
        apply div_le_div_of_nonneg_right _ hpos.le
        norm_num

end Seq

end StirlingVert
end TernaryGoldbach.RSBounds.BacklundZeta23
end
end

-- RSBounds.BacklundGammaModulusDigamma
section
open Complex Real

namespace TernaryGoldbach.RSBounds.BacklundGammaModulus

theorem abs_digamma_re_sub_log_le {a t : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 3 / 2) (ht : 50 ≤ t) :
    |(Complex.digamma ((a : ℂ) + t * I)).re - Real.log t| ≤ 9 / (2 * t ^ 2) := by
  let w : ℂ := (a : ℂ) + t * I
  have ha0 : 0 < a := by linarith
  have ht0 : 0 < t := by linarith
  have hre : w.re = a := by simp [w]
  have him : w.im = t := by simp [w]
  have hw : 0 < w.re := by simpa [hre] using ha0
  have hD : 0 < a ^ 2 + t ^ 2 := by positivity
  have hmain := TernaryGoldbach.RSBounds.BacklundZeta23.StirlingVert.digamma_stirling hw
    (by rw [him, abs_of_pos ht0]; linarith)
  rw [him] at hmain
  have hlogre : (Complex.log w).re = Real.log (a ^ 2 + t ^ 2) / 2 := by
    rw [Complex.log_re, show ‖w‖ = Real.sqrt (a ^ 2 + t ^ 2) by
      rw [Complex.norm_eq_sqrt_sq_add_sq, hre, him], Real.log_sqrt hD.le]
  have hinvre : ((1 / 2 : ℂ) / w).re = a / (2 * (a ^ 2 + t ^ 2)) := by
    rw [show (1 / 2 : ℂ) / w = ((1 / 2 : ℝ) : ℂ) * w⁻¹ by push_cast; ring,
      Complex.re_ofReal_mul, Complex.inv_re, Complex.normSq_apply, hre, him]
    field_simp
  have hR : |(Complex.digamma w).re - Real.log (a ^ 2 + t ^ 2) / 2 +
      a / (2 * (a ^ 2 + t ^ 2))| ≤ 3 / t ^ 2 := by
    have h := (Complex.abs_re_le_norm _).trans hmain
    simpa only [Complex.add_re, Complex.sub_re, hlogre, hinvre] using h
  have hlog : 0 ≤ Real.log (a ^ 2 + t ^ 2) / 2 - Real.log t ∧
      Real.log (a ^ 2 + t ^ 2) / 2 - Real.log t ≤ 9 / (8 * t ^ 2) := by
    have he : a ^ 2 + t ^ 2 = t ^ 2 * (1 + a ^ 2 / t ^ 2) := by
      field_simp
      ring
    rw [he, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have hl0 : 0 ≤ Real.log (1 + a ^ 2 / t ^ 2) :=
      Real.log_nonneg (le_add_of_nonneg_right (by positivity))
    have hl1 := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + a ^ 2 / t ^ 2)
    have ha2 : a ^ 2 ≤ 9 / 4 := by nlinarith
    have hq : a ^ 2 / t ^ 2 ≤ (9 / 4) / t ^ 2 :=
      div_le_div_of_nonneg_right ha2 (sq_nonneg t)
    ring_nf at hq hl0 hl1 ⊢
    constructor <;> linarith
  have hi : 0 ≤ a / (2 * (a ^ 2 + t ^ 2)) ∧
      a / (2 * (a ^ 2 + t ^ 2)) ≤ 3 / (4 * t ^ 2) := by
    constructor
    · positivity
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (by linarith : 0 ≤ 3 / 2 - a) (sq_nonneg t)]
  rw [abs_le] at hR ⊢
  change -(9 / (2 * t ^ 2)) ≤ (Complex.digamma w).re - Real.log t ∧
    (Complex.digamma w).re - Real.log t ≤ 9 / (2 * t ^ 2)
  have ht2 : 0 < t ^ 2 := by positivity
  ring_nf at hR hlog hi ⊢
  constructor <;> nlinarith [hR.1, hR.2, hlog.1, hlog.2, hi.1, hi.2,
    sq_nonneg t⁻¹]

end TernaryGoldbach.RSBounds.BacklundGammaModulus
end

-- RSBounds.BacklundGammaModulusHorizontal
section
open Complex Real Set
open scoped RealInnerProductSpace

namespace TernaryGoldbach.RSBounds.BacklundGammaModulus

theorem hasDerivAt_log_norm {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hne : f x ≠ 0) :
    HasDerivAt (fun u => Real.log ‖f u‖) (f' / f x).re x := by
  have hn : ‖f x‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have h := (hf.norm_sq.log (pow_ne_zero 2 hn)).div_const 2
  convert h using 1
  · funext u
    rw [Real.log_pow]
    ring
  · rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply, Complex.div_re,
      Complex.sq_norm]
    change f'.re * (f x).re / Complex.normSq (f x) +
      f'.im * (f x).im / Complex.normSq (f x) =
      2 * (f' * (starRingEnd ℂ) (f x)).re / Complex.normSq (f x) / 2
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring

theorem hasDerivAt_log_norm_Gamma {a t : ℝ} (ha : 0 < a) :
    HasDerivAt (fun x : ℝ => Real.log ‖Complex.Gamma ((x : ℂ) + t * I)‖)
      (Complex.digamma ((a : ℂ) + t * I)).re a := by
  have hz : 0 < ((a : ℂ) + t * I).re := by simpa using ha
  have hne := GammaSolution.ne_neg_natCast_of_mem (s := (a : ℂ) + t * I) hz
  have hG := (Complex.differentiableAt_Gamma _ hne).hasDerivAt
  have hC := hG.comp (a : ℂ) ((hasDerivAt_id (a : ℂ)).add_const ((t : ℂ) * I))
  have hreal : HasDerivAt (fun x : ℝ => Complex.Gamma ((x : ℂ) + t * I))
      (deriv Complex.Gamma ((a : ℂ) + t * I)) a := by
    simpa using hC.comp_ofReal
  have h := hasDerivAt_log_norm hreal (Complex.Gamma_ne_zero hne)
  simpa [Complex.digamma_def, logDeriv_apply] using h

theorem abs_log_norm_Gamma_sub_le {a t : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 3 / 2) (ht : 50 ≤ t) :
    |Real.log ‖Complex.Gamma ((a : ℂ) + t * I)‖ -
      Real.log ‖Complex.Gamma (1 + t * I)‖ - (a - 1) * Real.log t| ≤
      9 / (4 * t ^ 2) := by
  let f : ℝ → ℝ := fun x => Real.log ‖Complex.Gamma ((x : ℂ) + t * I)‖ - x * Real.log t
  let f' : ℝ → ℝ := fun x => (Complex.digamma ((x : ℂ) + t * I)).re - Real.log t
  have hd : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2), HasDerivWithinAt f (f' x)
      (Icc (1 / 2 : ℝ) (3 / 2)) x := by
    intro x hx
    convert! ((hasDerivAt_log_norm_Gamma (t := t)
      (by linarith [hx.1] : 0 < x)).sub
        ((hasDerivAt_id x).mul_const (Real.log t))).hasDerivWithinAt using 1
    simp [f']
  have hb : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2), ‖f' x‖ ≤ 9 / (2 * t ^ 2) := by
    intro x hx
    simpa [f', Real.norm_eq_abs] using abs_digamma_re_sub_log_le hx.1 hx.2 ht
  have h := (convex_Icc (1 / 2 : ℝ) (3 / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd hb (x := 1) (y := a) (by norm_num) ⟨ha, ha'⟩
  have hdist : |a - 1| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  have hc : 0 ≤ 9 / (2 * t ^ 2) := by positivity
  have h' := h.trans (mul_le_mul_of_nonneg_left
    (show ‖a - 1‖ ≤ (1 / 2 : ℝ) by simpa [Real.norm_eq_abs] using hdist) hc)
  rw [Real.norm_eq_abs] at h'
  convert h' using 1
  · congr 1
    dsimp [f]
    norm_num
    ring
  · ring

theorem norm_Gamma_horizontal_le {a t : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 3 / 2) (ht : 50 ≤ t) :
    ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
      ‖Complex.Gamma (1 + t * I)‖ * t ^ (a - 1) * Real.exp (9 / (4 * t ^ 2)) := by
  have h := (abs_le.mp (abs_log_norm_Gamma_sub_le ha ha' ht)).2
  have hGa : 0 < ‖Complex.Gamma ((a : ℂ) + t * I)‖ := by
    apply norm_pos_iff.mpr
    apply Complex.Gamma_ne_zero_of_re_pos
    simp
    linarith
  have hG1 : 0 < ‖Complex.Gamma (1 + t * I)‖ := by
    apply norm_pos_iff.mpr
    apply Complex.Gamma_ne_zero_of_re_pos
    norm_num
  have ht0 : 0 < t := by linarith
  have he := Real.exp_le_exp.mpr (show
    Real.log ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
      Real.log ‖Complex.Gamma (1 + t * I)‖ + (a - 1) * Real.log t +
        9 / (4 * t ^ 2) by linarith)
  rw [Real.exp_log hGa, Real.exp_add, Real.exp_add, Real.exp_log hG1] at he
  rw [Real.rpow_def_of_pos ht0]
  simpa [mul_comm (a - 1) (Real.log t)] using he

end TernaryGoldbach.RSBounds.BacklundGammaModulus
end

-- RSBounds.BacklundFunctionalStrip
section
open Complex Real
open scoped ComplexConjugate

namespace TernaryGoldbach.RSBounds.BacklundFunctionalMultiplier

theorem norm_cos_le_cosh_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.cosh z.im := by
  rw [Complex.cos, norm_div, Complex.norm_ofNat]
  calc
    _ ≤ (‖Complex.exp (z * I)‖ + ‖Complex.exp (-z * I)‖) / 2 := by
      gcongr
      exact norm_add_le _ _
    _ = Real.cosh z.im := by
      rw [Complex.norm_exp_mul_I, Complex.norm_exp_mul_I, Complex.neg_im, neg_neg,
        Real.cosh_eq]
      ring

theorem cosh_div_sinh_half_eq {t : ℝ} (ht : 0 < t) :
    Real.cosh (Real.pi * t / 2) / Real.sinh (Real.pi * t / 2) =
      (1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t)) := by
  have h : 0 < Real.pi * t / 2 := by positivity
  have he : Real.exp (-Real.pi * t) = (Real.exp (Real.pi * t / 2))⁻¹ ^ 2 := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    ring
  have hp : 1 < Real.exp (Real.pi * t / 2) := Real.one_lt_exp_iff.mpr h
  have hn : Real.exp (Real.pi * t / 2) ≠ 0 := (Real.exp_pos _).ne'
  rw [he, Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
  field_simp <;> ring

theorem gamma_cosh_ratio_eq {t : ℝ} (ht : 0 < t) :
    ‖Complex.Gamma (1 + (t : ℂ) * I)‖ * Real.cosh (Real.pi * t / 2) / Real.pi =
      Real.sqrt (t / (2 * Real.pi)) *
        Real.sqrt ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t))) := by
  have hs : 0 < Real.sinh (Real.pi * t / 2) := Real.sinh_pos_iff.mpr (by positivity)
  have hc : 0 < Real.cosh (Real.pi * t / 2) := Real.cosh_pos _
  have hd : Real.sinh (Real.pi * t) =
      2 * Real.sinh (Real.pi * t / 2) * Real.cosh (Real.pi * t / 2) := by
    convert Real.sinh_two_mul (x := Real.pi * t / 2) using 1 <;> ring
  have hq : 0 ≤ (1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t)) := by
    rw [← cosh_div_sinh_half_eq ht]
    positivity
  have he : (‖Complex.Gamma (1 + (t : ℂ) * I)‖ * Real.cosh (Real.pi * t / 2) / Real.pi) ^ 2 =
      t / (2 * Real.pi) * ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t))) := by
    rw [div_pow, mul_pow, BacklundGammaBaseline.norm_Gamma_one_add_mul_I_sq ht,
      ← cosh_div_sinh_half_eq ht, hd]
    field_simp <;> ring
  have hs1 := Real.sq_sqrt (by positivity : 0 ≤ t / (2 * Real.pi))
  have hs2 := Real.sq_sqrt hq
  have hprod : (Real.sqrt (t / (2 * Real.pi)) *
      Real.sqrt ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t)))) ^ 2 =
      t / (2 * Real.pi) * ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t))) := by
    rw [mul_pow, hs1, hs2]
  have hL : 0 ≤ ‖Complex.Gamma (1 + (t : ℂ) * I)‖ * Real.cosh (Real.pi * t / 2) / Real.pi := by positivity
  have hR : 0 ≤ Real.sqrt (t / (2 * Real.pi)) *
      Real.sqrt ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t))) := by positivity
  nlinarith

theorem power_normalization {t : ℝ} (ht : 0 < t) (σ : ℝ) :
    (2 * Real.pi) ^ σ * t ^ (-σ) * Real.sqrt (t / (2 * Real.pi)) =
      (t / (2 * Real.pi)) ^ (1 / 2 - σ) := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hd : 0 < t / (2 * Real.pi) := div_pos ht hp
  rw [Real.sqrt_eq_rpow]
  simp only [Real.rpow_def_of_pos hp, Real.rpow_def_of_pos ht,
    Real.rpow_def_of_pos hd]
  rw [← Real.exp_add, ← Real.exp_add, Real.log_div ht.ne' hp.ne']
  congr 1
  ring

theorem norm_multiplier_strip_le {σ t : ℝ}
    (hσ : -(1 / 2 : ℝ) ≤ σ) (hσ' : σ ≤ 1 / 2) (ht : 50 ≤ t) :
    ‖multiplier ((σ : ℂ) + t * I)‖ ≤
      (t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.exp (5 / (2 * t ^ 2)) := by
  have ht0 : 0 < t := by linarith
  have hp : 0 < 2 * Real.pi := by positivity
  have hG : ‖Complex.Gamma (1 - ((σ : ℂ) + t * I))‖ ≤
      ‖Complex.Gamma (1 + (t : ℂ) * I)‖ * t ^ (-σ) * Real.exp (9 / (4 * t ^ 2)) := by
    have he : 1 - ((σ : ℂ) + t * I) = conj (((1 - σ : ℝ) : ℂ) + t * I) := by
      simp
      push_cast
      ring
    rw [he, Complex.Gamma_conj, norm_conj]
    convert BacklundGammaModulus.norm_Gamma_horizontal_le
      (a := 1 - σ) (t := t) (by linarith) (by linarith) ht using 1 <;> ring
  have hP : ‖(2 * (Real.pi : ℂ)) ^ (-(1 - ((σ : ℂ) + t * I)))‖ =
      (2 * Real.pi) ^ (σ - 1) := by
    have he : 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [he, Complex.norm_cpow_eq_rpow_re_of_pos hp]
    congr 1
    simp <;> ring
  have hC : ‖Complex.cos ((Real.pi : ℂ) * (1 - ((σ : ℂ) + t * I)) / 2)‖ ≤
      Real.cosh (Real.pi * t / 2) := by
    have he : (((Real.pi : ℂ) * (1 - ((σ : ℂ) + t * I)) / 2)).im = -(Real.pi * t / 2) := by
      simp [Complex.div_ofNat_im, Complex.mul_im] <;> ring
    simpa [he, Real.cosh_neg] using norm_cos_le_cosh_im
      ((Real.pi : ℂ) * (1 - ((σ : ℂ) + t * I)) / 2)
  have hpow : 2 * (2 * Real.pi) ^ (σ - 1) = (2 * Real.pi) ^ σ / Real.pi := by
    rw [Real.rpow_sub hp, Real.rpow_one]
    field_simp
  unfold multiplier
  rw [norm_mul, norm_mul, norm_mul, hP, Complex.norm_ofNat]
  calc
    _ ≤ 2 * (2 * Real.pi) ^ (σ - 1) *
        (‖Complex.Gamma (1 + (t : ℂ) * I)‖ * t ^ (-σ) * Real.exp (9 / (4 * t ^ 2))) *
        Real.cosh (Real.pi * t / 2) := by gcongr
    _ = ((2 * Real.pi) ^ σ * t ^ (-σ) * Real.sqrt (t / (2 * Real.pi))) *
        Real.sqrt ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t))) *
        Real.exp (9 / (4 * t ^ 2)) := by
      rw [hpow]
      have he := gamma_cosh_ratio_eq ht0
      calc
        _ = ((2 * Real.pi) ^ σ * t ^ (-σ)) *
            (‖Complex.Gamma (1 + (t : ℂ) * I)‖ * Real.cosh (Real.pi * t / 2) / Real.pi) *
            Real.exp (9 / (4 * t ^ 2)) := by ring
        _ = _ := by rw [he]; ring
    _ ≤ (t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.exp (1 / (4 * t ^ 2)) *
        Real.exp (9 / (4 * t ^ 2)) := by
      rw [power_normalization ht0]
      gcongr
      exact BacklundHyperbolicFactor.sqrt_exp_ratio_le ht
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem norm_zeta_reflected_strip_le {σ t : ℝ}
    (hσ : -(1 / 2 : ℝ) ≤ σ) (hσ' : σ ≤ 1 / 2) (ht : 50 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
      (t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.exp (5 / (2 * t ^ 2)) *
        ‖riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖ := by
  have ht0 : 0 < t := by linarith
  rw [functional_equation (by simpa using ht0.ne'), norm_mul]
  have he : 1 - ((σ : ℂ) + t * I) = conj (((1 - σ : ℝ) : ℂ) + t * I) := by
    simp
    push_cast
    ring
  rw [he, riemannZeta_conj, norm_conj]
  exact mul_le_mul_of_nonneg_right (norm_multiplier_strip_le hσ hσ' ht) (norm_nonneg _)

end TernaryGoldbach.RSBounds.BacklundFunctionalMultiplier
end

-- RSBounds.BacklundEulerMaclaurin
section
open Complex MeasureTheory Set Filter
open scoped Interval Topology

namespace TernaryGoldbach.RSBounds.BacklundEulerMaclaurin

noncomputable def firstWeight (a x : ℝ) : ℂ := ((x - a - 1 / 2 : ℝ) : ℂ)

noncomputable def secondWeight (a x : ℝ) : ℂ :=
  (((x - a) ^ 2 - (x - a) + 1 / 6 : ℝ) / 2 : ℝ)

theorem hasDerivAt_firstWeight (a x : ℝ) :
    HasDerivAt (firstWeight a) 1 x := by
  unfold firstWeight
  convert (((hasDerivAt_id x).sub_const a).sub_const (1 / 2)).ofReal_comp using 1 <;> simp

theorem hasDerivAt_secondWeight (a x : ℝ) :
    HasDerivAt (secondWeight a) (firstWeight a x) x := by
  unfold secondWeight firstWeight
  convert ((((hasDerivAt_id x).sub_const a).pow 2).sub
    ((hasDerivAt_id x).sub_const a) |>.add_const (1 / 6) |>.div_const 2).ofReal_comp using 1 <;>
    simp <;> ring

theorem norm_secondWeight_le (a : ℝ) {x : ℝ} (hx : x ∈ Icc a (a + 1)) :
    ‖secondWeight a x‖ ≤ 1 / 12 := by
  rw [secondWeight, Complex.norm_real, Real.norm_eq_abs, abs_le]
  have hu : 0 ≤ x - a := by linarith [hx.1]
  have hv : x - a ≤ 1 := by linarith [hx.2]
  have hp : (x - a) ^ 2 ≤ x - a := by nlinarith
  constructor <;> nlinarith [sq_nonneg (x - a - 1 / 2)]

theorem local_identity {f g h : ℝ → ℂ} {a : ℝ}
    (hf : ∀ x ∈ Icc a (a + 1), HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc a (a + 1), HasDerivAt g (h x) x)
    (hgi : IntervalIntegrable g volume a (a + 1))
    (hhi : IntervalIntegrable h volume a (a + 1)) :
    (f a + f (a + 1)) / 2 - (∫ x in a..a + 1, f x)
      - (g (a + 1) - g a) / 12 =
      -(∫ x in a..a + 1, secondWeight a x * h x) := by
  have hab : a ≤ a + 1 := by linarith
  have hfi : IntervalIntegrable f volume a (a + 1) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := firstWeight a) (u' := fun _ => (1 : ℂ)) (v := f) (v' := g)
    (fun x _ => hasDerivAt_firstWeight a x)
    (fun x hx => hf x (by simpa [uIcc_of_le hab] using hx))
    intervalIntegrable_const hgi
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := secondWeight a) (u' := firstWeight a) (v := g) (v' := h)
    (fun x _ => hasDerivAt_secondWeight a x)
    (fun x hx => hg x (by simpa [uIcc_of_le hab] using hx))
    ((show Continuous (firstWeight a) by unfold firstWeight; fun_prop).intervalIntegrable _ _) hhi
  simp only [one_mul] at h1
  rw [h1] at h2
  norm_num [firstWeight, secondWeight] at h2
  unfold secondWeight
  push_cast
  linear_combination h2

theorem local_error_le {f g h : ℝ → ℂ} {a : ℝ}
    (hf : ∀ x ∈ Icc a (a + 1), HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc a (a + 1), HasDerivAt g (h x) x)
    (hgi : IntervalIntegrable g volume a (a + 1))
    (hhi : IntervalIntegrable h volume a (a + 1)) :
    ‖(f a + f (a + 1)) / 2 - (∫ x in a..a + 1, f x)
      - (g (a + 1) - g a) / 12‖ ≤
      (1 / 12 : ℝ) * ∫ x in a..a + 1, ‖h x‖ := by
  rw [local_identity hf hg hgi hhi, norm_neg, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.norm_integral_le_of_norm_le (by linarith) _ (hhi.norm.const_mul _)
  · filter_upwards with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_secondWeight_le a ⟨hx.1.le, hx.2⟩) (norm_nonneg _)

theorem finite_error_le {f g h : ℝ → ℂ} (N M : ℕ) (hNM : N ≤ M)
    (hf : ∀ x : ℝ, (N : ℝ) ≤ x → HasDerivAt f (g x) x)
    (hg : ∀ x : ℝ, (N : ℝ) ≤ x → HasDerivAt g (h x) x)
    (hc : ContinuousOn h (Ici (N : ℝ))) :
    ‖(∑ k ∈ Finset.Ico N M, f k) + (f M - f N) / 2
        - (∫ x in (N : ℝ)..M, f x) - (g M - g N) / 12‖ ≤
      (1 / 12 : ℝ) * ∫ x in (N : ℝ)..M, ‖h x‖ := by
  have hfc : ContinuousOn f (Ici (N : ℝ)) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Ici (N : ℝ)) :=
    fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hint {u v : ℝ} (hu : (N : ℝ) ≤ u) (huv : u ≤ v) :
      IntervalIntegrable f volume u v ∧ IntervalIntegrable g volume u v ∧
        IntervalIntegrable h volume u v := by
    have hsub : uIcc u v ⊆ Ici (N : ℝ) := by
      rw [uIcc_of_le huv]
      exact fun x hx => hu.trans hx.1
    exact ⟨(hfc.mono hsub).intervalIntegrable,
      (hgc.mono hsub).intervalIntegrable, (hc.mono hsub).intervalIntegrable⟩
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    have hNM' : (N : ℝ) ≤ M := by exact_mod_cast hNM
    have hM1 : (M : ℝ) ≤ M + 1 := by linarith
    have hI1 := hint (u := N) (v := M) le_rfl hNM'
    have hI2 := hint (u := M) (v := M + 1) hNM' hM1
    have hloc := local_error_le (a := (M : ℝ))
      (fun x hx => hf x (hNM'.trans hx.1))
      (fun x hx => hg x (hNM'.trans hx.1)) hI2.2.1 hI2.2.2
    have hsumF := intervalIntegral.integral_add_adjacent_intervals hI1.1 hI2.1
    have hsumH := intervalIntegral.integral_add_adjacent_intervals hI1.2.2.norm hI2.2.2.norm
    rw [Finset.sum_Ico_succ_top hNM]
    push_cast
    calc
      _ = ‖((∑ k ∈ Finset.Ico N M, f k) + (f M - f N) / 2
          - (∫ x in (N : ℝ)..M, f x) - (g M - g N) / 12)
          + ((f M + f (M + 1)) / 2 - (∫ x in (M : ℝ)..M + 1, f x)
            - (g (M + 1) - g M) / 12)‖ := by
        congr 1
        rw [← hsumF]
        ring
      _ ≤ ‖(∑ k ∈ Finset.Ico N M, f k) + (f M - f N) / 2
          - (∫ x in (N : ℝ)..M, f x) - (g M - g N) / 12‖
          + ‖(f M + f (M + 1)) / 2 - (∫ x in (M : ℝ)..M + 1, f x)
            - (g (M + 1) - g M) / 12‖ := norm_add_le _ _
      _ ≤ (1 / 12 : ℝ) * (∫ x in (N : ℝ)..M, ‖h x‖)
          + (1 / 12 : ℝ) * (∫ x in (M : ℝ)..M + 1, ‖h x‖) := add_le_add ih hloc
      _ = (1 / 12 : ℝ) * ∫ x in (N : ℝ)..M + 1, ‖h x‖ := by
        rw [← mul_add, hsumH]

theorem regularized_infinite_error_le {f g h : ℝ → ℂ} (N : ℕ) {L : ℂ}
    (hf : ∀ x : ℝ, (N : ℝ) ≤ x → HasDerivAt f (g x) x)
    (hg : ∀ x : ℝ, (N : ℝ) ≤ x → HasDerivAt g (h x) x)
    (hc : ContinuousOn h (Ici (N : ℝ)))
    (hsumint : Tendsto (fun M : ℕ => (∑ k ∈ Finset.Ico N M, f k) -
      (∫ x in (N : ℝ)..M, f x)) atTop (𝓝 L))
    (hf0 : Tendsto (fun M : ℕ => f M) atTop (𝓝 0))
    (hg0 : Tendsto (fun M : ℕ => g M) atTop (𝓝 0))
    (hhi : IntegrableOn h (Ioi (N : ℝ))) :
    ‖L - f N / 2 + g N / 12‖ ≤
      (1 / 12 : ℝ) * ∫ x in Ioi (N : ℝ), ‖h x‖ := by
  have hIH := intervalIntegral_tendsto_integral_Ioi (N : ℝ) hhi.norm
    tendsto_natCast_atTop_atTop
  have hL := ((hsumint.add ((hf0.sub_const (f N)).div_const 2)).sub
    ((hg0.sub_const (g N)).div_const 12)).norm
  have hR := hIH.const_mul (1 / 12 : ℝ)
  have hlim := le_of_tendsto_of_tendsto hL hR
    (show ∀ᶠ M : ℕ in atTop,
      ‖((∑ k ∈ Finset.Ico N M, f k) - (∫ x in (N : ℝ)..M, f x)) +
        (f M - f N) / 2 - (g M - g N) / 12‖ ≤
        (1 / 12 : ℝ) * ∫ x in (N : ℝ)..M, ‖h x‖ from by
      filter_upwards [eventually_ge_atTop N] with M hM
      convert finite_error_le N M hM hf hg hc using 1 <;> congr 1 <;> ring)
  convert hlim using 1 <;> congr 1 <;> ring

end TernaryGoldbach.RSBounds.BacklundEulerMaclaurin
end

-- TernaryGoldbach.Explicit.Landau
section
open Complex Metric Set Filter Topology

namespace TernaryGoldbach.Explicit

variable {f : ℂ → ℂ} {c : ℂ} {R : ℝ}

noncomputable abbrev divB (f : ℂ → ℂ) (c : ℂ) (R : ℝ) := MeromorphicOn.divisor f (closedBall c R)

theorem divB_finite (f : ℂ → ℂ) (c : ℂ) (R : ℝ) : (divB f c R).support.Finite :=
  (divB f c R).finiteSupport (isCompact_closedBall c R)

noncomputable def zerosIn (f : ℂ → ℂ) (c : ℂ) (R r : ℝ) : Finset ℂ :=
  (divB_finite f c R).toFinset.filter fun u => ‖u - c‖ < r

theorem preperfect_closedBall (hR : 0 < R) : Preperfect (closedBall c R) := by
  rw [← closure_ball c hR.ne']
  exact (isOpen_ball.preperfect).perfect_closure.acc

theorem factor_ball (hf : Differentiable ℂ f) (hfc : f c ≠ 0) (hR : 0 < R) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall c R) ∧ (∀ z ∈ ball c (R / 2), g z ≠ 0) ∧
      ∀ z ∈ closedBall c R,
        f z = (∏ u ∈ zerosIn f c R (R / 2), (z - u) ^ (divB f c R u).toNat) * g z := by
  have hfa : AnalyticOnNhd ℂ f (closedBall c R) := fun z _ => hf.analyticAt z
  have hfa' : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  have hc0 : analyticOrderAt f c ≠ ⊤ := by
    rw [(hf.analyticAt c).analyticOrderAt_eq_zero.2 hfc]; simp
  have h₂f : ∀ u : closedBall c R, meromorphicOrderAt f u ≠ ⊤ := fun u => by
    rw [(hf.analyticAt u).meromorphicOrderAt_eq]
    have := hfa'.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ c)
      (mem_univ (u : ℂ)) hc0
    intro h
    apply this
    cases hk : analyticOrderAt f u <;> simp_all
  obtain ⟨g, hg, hg0, hfg⟩ := hfa.meromorphicOn.extract_zeros_poles h₂f (divB_finite f c R)
  set D := divB f c R with hD
  set S := (divB_finite f c R).toFinset with hS
  have hDnn : ∀ u, 0 ≤ D u := fun u => (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa) u

  have hP : ∀ z, (∏ᶠ u, (· - u) ^ D u) z = ∏ u ∈ S, (z - u) ^ (D u).toNat := by
    intro z
    rw [Function.FactorizedRational.finprod_eq_fun (divB_finite f c R)]
    simp only
    rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
    · refine Finset.prod_congr rfl fun u _ => ?_
      rw [← zpow_natCast, Int.toNat_of_nonneg (hDnn u)]
    · intro u hu
      rw [Function.mem_mulSupport] at hu
      simp only [hS, Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
      intro h0; apply hu; rw [h0, zpow_zero]

  have heq : ∀ z ∈ closedBall c R, f z = (∏ u ∈ S, (z - u) ^ (D u).toNat) * g z := by
    intro z hz
    have hPa : AnalyticAt ℂ (fun z => (∏ u ∈ S, (z - u) ^ (D u).toNat) * g z) z := by
      refine AnalyticAt.mul ?_ (hg z hz)
      exact Finset.analyticAt_fun_prod _ fun u _ => ((analyticAt_id.sub analyticAt_const).pow _)
    have hfg' : f =ᶠ[codiscreteWithin (closedBall c R)]
        (fun z => (∏ u ∈ S, (z - u) ^ (D u).toNat) * g z) := by
      refine hfg.trans (Filter.Eventually.of_forall fun w => ?_)
      simp only [Pi.smul_apply', smul_eq_mul]
      rw [hP w]
    have h := (hf.analyticAt z).meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
      hPa.meromorphicAt hz (preperfect_closedBall hR) hfg'
    exact tendsto_nhds_unique ((hf.continuous.continuousAt).tendsto.mono_left nhdsWithin_le_nhds)
      (hPa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.congr' h.symm)

  set Sout := S.filter fun u => ¬ ‖u - c‖ < R / 2
  refine ⟨fun z => (∏ u ∈ Sout, (z - u) ^ (D u).toNat) * g z, ?_, ?_, ?_⟩
  · intro z hz
    refine AnalyticAt.mul ?_ (hg z hz)
    exact Finset.analyticAt_fun_prod _ fun u _ => ((analyticAt_id.sub analyticAt_const).pow _)
  · intro z hz
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun u hu => pow_ne_zero _ ?_)
      (hg0 ⟨z, ball_subset_closedBall (ball_subset_ball (by linarith) hz)⟩)
    intro h
    rw [sub_eq_zero] at h
    rw [Finset.mem_filter] at hu
    rw [mem_ball, dist_eq_norm, h] at hz
    exact hu.2 hz
  · intro z hz
    rw [heq z hz, zerosIn, ← mul_assoc, Finset.prod_filter_mul_prod_filter_not]

noncomputable def Pin (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  ∏ u ∈ zerosIn f c R (R / 2), (z - u) ^ (divB f c R u).toNat

theorem mem_zerosIn {f : ℂ → ℂ} {c u : ℂ} {R r : ℝ} (hu : u ∈ zerosIn f c R r) :
    ‖u - c‖ < r ∧ divB f c R u ≠ 0 := by
  rw [zerosIn, Finset.mem_filter, Set.Finite.mem_toFinset, Function.mem_support] at hu
  exact ⟨hu.2, hu.1⟩

theorem logDeriv_Pin {z : ℂ} (hz : ∀ u ∈ zerosIn f c R (R / 2), z ≠ u) :
    logDeriv (Pin f c R) z = ∑ u ∈ zerosIn f c R (R / 2), ((divB f c R u).toNat : ℂ) / (z - u) := by
  have e : Pin f c R = ∏ u ∈ zerosIn f c R (R / 2), (fun z => (z - u) ^ (divB f c R u).toNat) := by
    ext w; simp [Pin, Finset.prod_apply]
  rw [e, logDeriv_prod (f := fun (u : ℂ) (w : ℂ) => (w - u) ^ (divB f c R u).toNat) (x := z)
    (fun u hu => pow_ne_zero _ (sub_ne_zero.2 (hz u hu)))
    (fun u _ => (differentiableAt_id.sub_const u).pow _)]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hd : DifferentiableAt ℂ (fun w : ℂ => w - u) z := differentiableAt_id.sub_const u
  rw [logDeriv_fun_pow hd, logDeriv_apply, deriv_sub_const, deriv_id'']
  ring

end TernaryGoldbach.Explicit
end

-- TernaryGoldbach.Explicit.RectResidue
section
open Complex Set MeasureTheory intervalIntegral Metric
open scoped Real Interval

namespace TernaryGoldbach.Explicit

noncomputable def rectInt (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

theorem integral_inv_add_real {a b : ℝ} {κ : ℂ} (h : ∀ x ∈ [[a, b]], (x : ℂ) + κ ∈ slitPlane) :
    ∫ x : ℝ in a..b, ((x : ℂ) + κ)⁻¹ = Complex.log (b + κ) - Complex.log (a + κ) := by
  have hd : ∀ x ∈ [[a, b]], HasDerivAt (fun x : ℝ => Complex.log ((x : ℂ) + κ)) ((x : ℂ) + κ)⁻¹ x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) + κ) 1 x := (hasDerivAt_id x).ofReal_comp.add_const κ
    have := h1.clog_real (h x hx)
    simpa using this
  have hc : ContinuousOn (fun x : ℝ => ((x : ℂ) + κ)⁻¹) [[a, b]] := by
    refine ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_
    exact slitPlane_ne_zero (h x hx)
  exact integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)

theorem integral_inv_add_imag {c d σ : ℝ} {κ : ℂ}
    (h : ∀ y ∈ [[c, d]], (σ : ℂ) + y * I + κ ∈ slitPlane) :
    ∫ y : ℝ in c..d, ((σ : ℂ) + y * I + κ)⁻¹ =
      -I * (Complex.log (σ + d * I + κ) - Complex.log (σ + c * I + κ)) := by
  have hd : ∀ y ∈ [[c, d]], HasDerivAt (fun y : ℝ => -I * Complex.log ((σ : ℂ) + y * I + κ))
      ((σ : ℂ) + y * I + κ)⁻¹ y := by
    intro y hy
    have h1 : HasDerivAt (fun y : ℝ => (σ : ℂ) + y * I + κ) I y := by
      have := ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (σ : ℂ) |>.add_const κ
      simpa using this
    have := (h1.clog_real (h y hy)).const_mul (-I)
    refine this.congr_deriv ?_
    have hne := slitPlane_ne_zero (h y hy)
    field_simp
    rw [I_sq]; ring
  have hc : ContinuousOn (fun y : ℝ => ((σ : ℂ) + y * I + κ)⁻¹) [[c, d]] := by
    refine ContinuousOn.inv₀ (by fun_prop) fun y hy => ?_
    exact slitPlane_ne_zero (h y hy)
  rw [integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  ring

theorem integral_inv_add_imag_neg {c d σ : ℝ} {κ : ℂ}
    (h : ∀ y ∈ [[c, d]], -((σ : ℂ) + y * I + κ) ∈ slitPlane) :
    ∫ y : ℝ in c..d, ((σ : ℂ) + y * I + κ)⁻¹ =
      -I * (Complex.log (-((σ : ℂ) + d * I + κ)) - Complex.log (-((σ : ℂ) + c * I + κ))) := by
  have hd : ∀ y ∈ [[c, d]], HasDerivAt (fun y : ℝ => -I * Complex.log (-((σ : ℂ) + y * I + κ)))
      ((σ : ℂ) + y * I + κ)⁻¹ y := by
    intro y hy
    have h1 : HasDerivAt (fun y : ℝ => -((σ : ℂ) + y * I + κ)) (-I) y :=
      ((((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (σ : ℂ)).add_const κ).neg.congr_deriv
        (by simp)
    have := (h1.clog_real (h y hy)).const_mul (-I)
    refine this.congr_deriv ?_
    have hne : (σ : ℂ) + y * I + κ ≠ 0 := by
      intro h0; have := slitPlane_ne_zero (h y hy); rw [h0, neg_zero] at this; exact this rfl
    field_simp
    rw [I_sq]; ring
  have hc : ContinuousOn (fun y : ℝ => ((σ : ℂ) + y * I + κ)⁻¹) [[c, d]] := by
    refine ContinuousOn.inv₀ (by fun_prop) fun y hy => ?_
    intro h0; have := slitPlane_ne_zero (h y hy); rw [h0, neg_zero] at this; exact this rfl
  rw [integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  ring

theorem log_sub_log_neg_of_im_pos {p : ℂ} (hp : 0 < p.im) :
    Complex.log p - Complex.log (-p) = π * I := by
  rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos hp]
  push_cast; ring

theorem log_sub_log_neg_of_im_neg {p : ℂ} (hp : p.im < 0) :
    Complex.log p - Complex.log (-p) = -(π * I) := by
  rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg hp]
  push_cast; ring

theorem rectInt_inv_sub {z w ρ : ℂ} (h1 : z.re < ρ.re) (h2 : ρ.re < w.re) (h3 : z.im < ρ.im)
    (h4 : ρ.im < w.im) : rectInt (fun s => (s - ρ)⁻¹) z w = 2 * π * I := by
  unfold rectInt

  have hB : ∫ x : ℝ in z.re..w.re, ((x : ℂ) + z.im * I - ρ)⁻¹ =
      Complex.log (w.re + (z.im * I - ρ)) - Complex.log (z.re + (z.im * I - ρ)) := by
    have := integral_inv_add_real (a := z.re) (b := w.re) (κ := z.im * I - ρ) (fun x _ => by
      refine Or.inr ?_
      simp; linarith)
    simpa [add_sub_assoc] using this
  have hT : ∫ x : ℝ in z.re..w.re, ((x : ℂ) + w.im * I - ρ)⁻¹ =
      Complex.log (w.re + (w.im * I - ρ)) - Complex.log (z.re + (w.im * I - ρ)) := by
    have := integral_inv_add_real (a := z.re) (b := w.re) (κ := w.im * I - ρ) (fun x _ => by
      refine Or.inr ?_
      simp; linarith)
    simpa [add_sub_assoc] using this
  have hR : ∫ y : ℝ in z.im..w.im, ((w.re : ℂ) + y * I - ρ)⁻¹ =
      -I * (Complex.log (w.re + w.im * I + -ρ) - Complex.log (w.re + z.im * I + -ρ)) := by
    have := integral_inv_add_imag (c := z.im) (d := w.im) (σ := w.re) (κ := -ρ) (fun y _ => by
      refine Or.inl ?_
      simp; linarith)
    simpa [sub_eq_add_neg] using this
  have hL : ∫ y : ℝ in z.im..w.im, ((z.re : ℂ) + y * I - ρ)⁻¹ =
      -I * (Complex.log (-((z.re : ℂ) + w.im * I + -ρ)) - Complex.log (-((z.re : ℂ) + z.im * I + -ρ))) := by
    have := integral_inv_add_imag_neg (c := z.im) (d := w.im) (σ := z.re) (κ := -ρ) (fun y _ => by
      refine Or.inl ?_
      simp; linarith)
    simpa [sub_eq_add_neg] using this
  simp only [smul_eq_mul]
  rw [hB, hT, hR, hL]
  have eTL : Complex.log ((z.re : ℂ) + (w.im * I - ρ)) - Complex.log (-((z.re : ℂ) + w.im * I + -ρ)) =
      π * I := by
    have hp : 0 < ((z.re : ℂ) + (w.im * I - ρ)).im := by simp; linarith
    rw [← log_sub_log_neg_of_im_pos hp]; congr 2; ring
  have eBL : Complex.log ((z.re : ℂ) + (z.im * I - ρ)) - Complex.log (-((z.re : ℂ) + z.im * I + -ρ)) =
      -(π * I) := by
    have hp : ((z.re : ℂ) + (z.im * I - ρ)).im < 0 := by simp; linarith
    rw [← log_sub_log_neg_of_im_neg hp]; congr 2; ring
  have e1 : Complex.log ((w.re : ℂ) + w.im * I + -ρ) = Complex.log ((w.re : ℂ) + (w.im * I - ρ)) := by
    congr 1; ring
  have e2 : Complex.log ((w.re : ℂ) + z.im * I + -ρ) = Complex.log ((w.re : ℂ) + (z.im * I - ρ)) := by
    congr 1; ring
  rw [e1, e2]
  have hII : I * -I = 1 := by rw [mul_neg, I_mul_I, neg_neg]
  linear_combination eTL - eBL + (Complex.log ((w.re : ℂ) + (w.im * I - ρ)) -
    Complex.log ((w.re : ℂ) + (z.im * I - ρ))) * hII -
    (Complex.log (-((z.re : ℂ) + w.im * I + -ρ)) - Complex.log (-((z.re : ℂ) + z.im * I + -ρ))) * hII

theorem mem_rect_boundary_ne {z w ρ : ℂ} (h1 : z.re < ρ.re) (h2 : ρ.re < w.re) (h3 : z.im < ρ.im)
    (h4 : ρ.im < w.im) :
    (∀ x : ℝ, (x : ℂ) + z.im * I ≠ ρ) ∧ (∀ x : ℝ, (x : ℂ) + w.im * I ≠ ρ) ∧
      (∀ y : ℝ, (w.re : ℂ) + y * I ≠ ρ) ∧ (∀ y : ℝ, (z.re : ℂ) + y * I ≠ ρ) := by
  refine ⟨fun x h => ?_, fun x h => ?_, fun y h => ?_, fun y h => ?_⟩
  · have := congrArg Complex.im h; simp at this; linarith
  · have := congrArg Complex.im h; simp at this; linarith
  · have := congrArg Complex.re h; simp at this; linarith
  · have := congrArg Complex.re h; simp at this; linarith

theorem rectInt_const_mul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectInt (fun s => c * f s) z w = c * rectInt f z w := by
  unfold rectInt
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

theorem rectInt_add_of_integrable {f g : ℂ → ℂ} {z w : ℂ}
    (hf1 : IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re w.re)
    (hf2 : IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re w.re)
    (hf3 : IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im)
    (hf4 : IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im)
    (hg1 : IntervalIntegrable (fun x : ℝ => g (x + z.im * I)) volume z.re w.re)
    (hg2 : IntervalIntegrable (fun x : ℝ => g (x + w.im * I)) volume z.re w.re)
    (hg3 : IntervalIntegrable (fun y : ℝ => g (w.re + y * I)) volume z.im w.im)
    (hg4 : IntervalIntegrable (fun y : ℝ => g (z.re + y * I)) volume z.im w.im) :
    rectInt (fun s => f s + g s) z w = rectInt f z w + rectInt g z w := by
  unfold rectInt
  rw [integral_add hf1 hg1, integral_add hf2 hg2, integral_add hf3 hg3, integral_add hf4 hg4]
  simp only [smul_eq_mul]
  ring

theorem rectInt_congr {f g : ℂ → ℂ} {z w : ℂ}
    (h1 : ∀ x : ℝ, f (x + z.im * I) = g (x + z.im * I)) (h2 : ∀ x : ℝ, f (x + w.im * I) = g (x + w.im * I))
    (h3 : ∀ y : ℝ, f (w.re + y * I) = g (w.re + y * I)) (h4 : ∀ y : ℝ, f (z.re + y * I) = g (z.re + y * I)) :
    rectInt f z w = rectInt g z w := by
  unfold rectInt
  simp only [h1, h2, h3, h4]

theorem rect_sides_integrable {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine ContinuousOn.intervalIntegrable ?_ <;>
    refine hf.comp (by fun_prop) fun t ht => ?_ <;>
    simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, add_im, mul_im, zero_add]
  · exact ⟨ht, left_mem_uIcc⟩
  · exact ⟨ht, right_mem_uIcc⟩
  · exact ⟨right_mem_uIcc, ht⟩
  · exact ⟨left_mem_uIcc, ht⟩

theorem rect_sides_integrable_inv {z w ρ : ℂ} (h1 : z.re < ρ.re) (h2 : ρ.re < w.re)
    (h3 : z.im < ρ.im) (h4 : ρ.im < w.im) :
    IntervalIntegrable (fun x : ℝ => ((x + z.im * I : ℂ) - ρ)⁻¹) volume z.re w.re ∧
    IntervalIntegrable (fun x : ℝ => ((x + w.im * I : ℂ) - ρ)⁻¹) volume z.re w.re ∧
    IntervalIntegrable (fun y : ℝ => ((w.re + y * I : ℂ) - ρ)⁻¹) volume z.im w.im ∧
    IntervalIntegrable (fun y : ℝ => ((z.re + y * I : ℂ) - ρ)⁻¹) volume z.im w.im := by
  obtain ⟨b1, b2, b3, b4⟩ := mem_rect_boundary_ne h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine ContinuousOn.intervalIntegrable ?_ <;>
    refine ContinuousOn.inv₀ (by fun_prop) fun t _ => sub_ne_zero.2 ?_
  exacts [b1 t, b2 t, b3 t, b4 t]

theorem rectInt_mul_inv_sub {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) {z w ρ : ℂ}
    (hsub : [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ U) (hg : DifferentiableOn ℂ g U)
    (h1 : z.re < ρ.re) (h2 : ρ.re < w.re) (h3 : z.im < ρ.im) (h4 : ρ.im < w.im) :
    rectInt (fun s => g s * (s - ρ)⁻¹) z w = 2 * π * I * g ρ := by
  set R := [[z.re, w.re]] ×ℂ [[z.im, w.im]] with hR
  have hρU : ρ ∈ U := hsub (mem_reProdIm.2 ⟨Set.mem_uIcc.2 (Or.inl ⟨h1.le, h2.le⟩),
    Set.mem_uIcc.2 (Or.inl ⟨h3.le, h4.le⟩)⟩)
  have hgρ : DifferentiableAt ℂ g ρ := hg.differentiableAt (hU.mem_nhds hρU)
  have hdc : ContinuousOn (dslope g ρ) R := by
    intro s hs
    by_cases hsρ : s = ρ
    · subst hsρ; exact (continuousAt_dslope_same.2 hgρ).continuousWithinAt
    · have hgs : DifferentiableAt ℂ g s := hg.differentiableAt (hU.mem_nhds (hsub hs))
      exact ((differentiableAt_dslope_of_ne hsρ).2 hgs).continuousAt.continuousWithinAt
  have hdd : ∀ s ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) \ {ρ},
      DifferentiableAt ℂ (dslope g ρ) s := by
    intro s hs
    have hsR : s ∈ R := ⟨Ioo_subset_Icc_self hs.1.1, Ioo_subset_Icc_self hs.1.2⟩
    have hgs : DifferentiableAt ℂ g s := hg.differentiableAt (hU.mem_nhds (hsub hsR))
    exact (differentiableAt_dslope_of_ne hs.2).2 hgs
  have h0 : rectInt (dslope g ρ) z w = 0 :=
    Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable (dslope g ρ)
      z w {ρ} (countable_singleton ρ) hdc hdd
  obtain ⟨b1, b2, b3, b4⟩ := mem_rect_boundary_ne h1 h2 h3 h4
  have hpt : ∀ s, s ≠ ρ → g s * (s - ρ)⁻¹ = dslope g ρ s + g ρ * (s - ρ)⁻¹ := by
    intro s hs
    rw [dslope_of_ne _ hs, slope_def_field]
    have : s - ρ ≠ 0 := sub_ne_zero.2 hs
    field_simp
    ring
  rw [rectInt_congr (g := fun s => dslope g ρ s + g ρ * (s - ρ)⁻¹)
    (fun x => hpt _ (b1 x)) (fun x => hpt _ (b2 x)) (fun y => hpt _ (b3 y)) (fun y => hpt _ (b4 y))]
  obtain ⟨d1, d2, d3, d4⟩ := rect_sides_integrable hdc
  obtain ⟨i1, i2, i3, i4⟩ := rect_sides_integrable_inv h1 h2 h3 h4
  rw [rectInt_add_of_integrable d1 d2 d3 d4 (i1.const_mul _) (i2.const_mul _) (i3.const_mul _)
    (i4.const_mul _), h0, zero_add, rectInt_const_mul, rectInt_inv_sub h1 h2 h3 h4]
  ring

theorem rectInt_congr' {f g : ℂ → ℂ} {z w : ℂ}
    (h1 : ∀ x ∈ [[z.re, w.re]], f (x + z.im * I) = g (x + z.im * I))
    (h2 : ∀ x ∈ [[z.re, w.re]], f (x + w.im * I) = g (x + w.im * I))
    (h3 : ∀ y ∈ [[z.im, w.im]], f (w.re + y * I) = g (w.re + y * I))
    (h4 : ∀ y ∈ [[z.im, w.im]], f (z.re + y * I) = g (z.re + y * I)) :
    rectInt f z w = rectInt g z w := by
  unfold rectInt
  rw [integral_congr (fun x hx => h1 x hx), integral_congr (fun x hx => h2 x hx),
    integral_congr (fun y hy => h3 y hy), integral_congr (fun y hy => h4 y hy)]

def RectIntegrable (F : ℂ → ℂ) (z w : ℂ) : Prop :=
  IntervalIntegrable (fun x : ℝ => F (x + z.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun x : ℝ => F (x + w.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun y : ℝ => F (w.re + y * I)) volume z.im w.im ∧
  IntervalIntegrable (fun y : ℝ => F (z.re + y * I)) volume z.im w.im

theorem RectIntegrable.add {F G : ℂ → ℂ} {z w : ℂ} (hF : RectIntegrable F z w)
    (hG : RectIntegrable G z w) : RectIntegrable (fun s => F s + G s) z w :=
  ⟨hF.1.add hG.1, hF.2.1.add hG.2.1, hF.2.2.1.add hG.2.2.1, hF.2.2.2.add hG.2.2.2⟩

theorem RectIntegrable.const_mul {F : ℂ → ℂ} {z w : ℂ} (hF : RectIntegrable F z w) (c : ℂ) :
    RectIntegrable (fun s => c * F s) z w :=
  ⟨hF.1.const_mul c, hF.2.1.const_mul c, hF.2.2.1.const_mul c, hF.2.2.2.const_mul c⟩

theorem rectIntegrable_of_continuousOn {F : ℂ → ℂ} {z w : ℂ}
    (hF : ContinuousOn F ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) : RectIntegrable F z w :=
  rect_sides_integrable hF

theorem rectInt_add' {F G : ℂ → ℂ} {z w : ℂ} (hF : RectIntegrable F z w) (hG : RectIntegrable G z w) :
    rectInt (fun s => F s + G s) z w = rectInt F z w + rectInt G z w :=
  rectInt_add_of_integrable hF.1 hF.2.1 hF.2.2.1 hF.2.2.2 hG.1 hG.2.1 hG.2.2.1 hG.2.2.2

theorem rectInt_finset_sum {ι : Type*} (S : Finset ι) (F : ι → ℂ → ℂ) {z w : ℂ}
    (hF : ∀ i ∈ S, RectIntegrable (F i) z w) :
    rectInt (fun s => ∑ i ∈ S, F i s) z w = ∑ i ∈ S, rectInt (F i) z w := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [rectInt]
  | insert a S ha ih =>
    have hS : RectIntegrable (fun s => ∑ i ∈ S, F i s) z w := by
      have key : ∀ (φ : ℝ → ℂ) (a b : ℝ),
          (∀ i ∈ S, IntervalIntegrable (fun t => F i (φ t)) volume a b) →
          IntervalIntegrable (fun t => ∑ i ∈ S, F i (φ t)) volume a b := by
        intro φ a b h
        have := IntervalIntegrable.sum S h
        convert this using 1
        ext t; simp [Finset.sum_apply]
      exact ⟨key _ _ _ fun i hi => (hF i (Finset.mem_insert_of_mem hi)).1,
        key _ _ _ fun i hi => (hF i (Finset.mem_insert_of_mem hi)).2.1,
        key _ _ _ fun i hi => (hF i (Finset.mem_insert_of_mem hi)).2.2.1,
        key _ _ _ fun i hi => (hF i (Finset.mem_insert_of_mem hi)).2.2.2⟩
    simp only [Finset.sum_insert ha]
    rw [rectInt_add' (hF a (Finset.mem_insert_self a S)) hS,
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

theorem mem_rect_cases {z w u : ℂ} (hu : u ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]]) (hzw1 : z.re < w.re)
    (hzw2 : z.im < w.im) :
    (z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im) ∨ u.im = z.im ∨ u.im = w.im ∨
      u.re = w.re ∨ u.re = z.re := by
  rw [mem_reProdIm, Set.uIcc_of_le hzw1.le, Set.uIcc_of_le hzw2.le] at hu
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := hu
  rcases a1.lt_or_eq with a1 | a1
  · rcases a2.lt_or_eq with a2 | a2
    · rcases b1.lt_or_eq with b1 | b1
      · rcases b2.lt_or_eq with b2 | b2
        · exact Or.inl ⟨a1, a2, b1, b2⟩
        · exact Or.inr (Or.inr (Or.inl b2))
      · exact Or.inr (Or.inl b1.symm)
    · exact Or.inr (Or.inr (Or.inr (Or.inl a2)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr a1.symm)))

def NoZerosOnSides (F : ℂ → ℂ) (z w : ℂ) : Prop :=
  (∀ x ∈ [[z.re, w.re]], F (x + z.im * I) ≠ 0) ∧ (∀ x ∈ [[z.re, w.re]], F (x + w.im * I) ≠ 0) ∧
  (∀ y ∈ [[z.im, w.im]], F (w.re + y * I) ≠ 0) ∧ (∀ y ∈ [[z.im, w.im]], F (z.re + y * I) ≠ 0)

theorem rectIntegrable_mul_inv_sub {h : ℂ → ℂ} {z w u : ℂ}
    (hh : ContinuousOn h ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (hu1 : ∀ x ∈ [[z.re, w.re]], (x : ℂ) + z.im * I ≠ u) (hu2 : ∀ x ∈ [[z.re, w.re]], (x : ℂ) + w.im * I ≠ u)
    (hu3 : ∀ y ∈ [[z.im, w.im]], (w.re : ℂ) + y * I ≠ u) (hu4 : ∀ y ∈ [[z.im, w.im]], (z.re : ℂ) + y * I ≠ u) :
    RectIntegrable (fun s => h s * (s - u)⁻¹) z w := by
  have hs := rect_sides_integrable hh
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine ContinuousOn.intervalIntegrable ?_
  · refine ContinuousOn.mul ?_ (ContinuousOn.inv₀ (by fun_prop) fun x hx => sub_ne_zero.2 (hu1 x hx))
    exact hh.comp (by fun_prop) fun x hx => by
      simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, add_im, mul_im, zero_add]; exact ⟨hx, left_mem_uIcc⟩
  · refine ContinuousOn.mul ?_ (ContinuousOn.inv₀ (by fun_prop) fun x hx => sub_ne_zero.2 (hu2 x hx))
    exact hh.comp (by fun_prop) fun x hx => by
      simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, add_im, mul_im, zero_add]; exact ⟨hx, right_mem_uIcc⟩
  · refine ContinuousOn.mul ?_ (ContinuousOn.inv₀ (by fun_prop) fun y hy => sub_ne_zero.2 (hu3 y hy))
    exact hh.comp (by fun_prop) fun y hy => by
      simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, add_im, mul_im, zero_add]; exact ⟨right_mem_uIcc, hy⟩
  · refine ContinuousOn.mul ?_ (ContinuousOn.inv₀ (by fun_prop) fun y hy => sub_ne_zero.2 (hu4 y hy))
    exact hh.comp (by fun_prop) fun y hy => by
      simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, add_im, mul_im, zero_add]; exact ⟨left_mem_uIcc, hy⟩

theorem rectInt_logDeriv_mul {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hfc : f c ≠ 0) {z w : ℂ} (hzw1 : z.re < w.re) (hzw2 : z.im < w.im)
    (hrect : [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ ball c (R / 2)) (hbd : NoZerosOnSides f z w)
    {h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hsubU : [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ U)
    (hh : DifferentiableOn ℂ h U) :
    rectInt (fun s => logDeriv f s * h s) z w = 2 * π * I *
      ∑ u ∈ (zerosIn f c R (R / 2)).filter
        (fun u => z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im),
        ((divB f c R u).toNat : ℂ) * h u := by
  classical
  obtain ⟨g, hg, hg0, hfg⟩ := factor_ball hf hfc hR
  set Z := zerosIn f c R (R / 2) with hZ
  set Rect := [[z.re, w.re]] ×ℂ [[z.im, w.im]] with hRect
  have hRb : Rect ⊆ ball c R := hrect.trans (ball_subset_ball (by linarith))

  have hfu : ∀ u ∈ Z, f u = 0 := by
    intro u hu
    have hu' := (mem_zerosIn hu).2
    have hucR : u ∈ closedBall c R := by
      rw [mem_closedBall, dist_eq_norm]; linarith [(mem_zerosIn hu).1]
    rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
      (fun z _ => hf.analyticAt z : AnalyticOnNhd ℂ f (closedBall c R)) hucR] at hu'
    by_contra hne
    exact hu' (by rw [(hf.analyticAt u).analyticOrderAt_eq_zero.2 hne]; simp)

  have hdec : ∀ s ∈ Rect, f s ≠ 0 →
      logDeriv f s = ∑ u ∈ Z, ((divB f c R u).toNat : ℂ) / (s - u) + logDeriv g s := by
    intro s hs hfs
    have hsZ : ∀ u ∈ Z, s ≠ u := fun u hu h => hfs (h ▸ hfu u hu)
    have hsb : s ∈ ball c R := hRb hs
    have hsb2 : s ∈ ball c (R / 2) := hrect hs
    have hPs : Pin f c R s ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun u hu => pow_ne_zero _ (sub_ne_zero.2 (hsZ u hu))
    have hgs : g s ≠ 0 := hg0 s hsb2
    have hloc : f =ᶠ[nhds s] fun w => Pin f c R w * g w := by
      filter_upwards [isOpen_ball.mem_nhds hsb] with v hv
      exact hfg v (ball_subset_closedBall hv)
    have hPd : DifferentiableAt ℂ (Pin f c R) s := by
      have : Pin f c R = fun w => ∏ u ∈ Z, (w - u) ^ (divB f c R u).toNat := rfl
      rw [this]
      exact DifferentiableAt.fun_finsetProd fun u _ => (differentiableAt_id.sub_const u).pow _
    have hgd : DifferentiableAt ℂ g s := (hg s (ball_subset_closedBall hsb)).differentiableAt
    rw [(logDeriv_congr_nhds hloc).eq_of_nhds,
      show (fun w => Pin f c R w * g w) = Pin f c R * g from rfl,
      logDeriv_mul (f := Pin f c R) (g := g) s hPs hgs hPd hgd, logDeriv_Pin hsZ]
  have hside1 : ∀ x ∈ [[z.re, w.re]], (x : ℂ) + z.im * I ∈ Rect := fun x hx =>
    mem_reProdIm.2 ⟨by simpa using hx, by simp [left_mem_uIcc]⟩
  have hside2 : ∀ x ∈ [[z.re, w.re]], (x : ℂ) + w.im * I ∈ Rect := fun x hx =>
    mem_reProdIm.2 ⟨by simpa using hx, by simp [right_mem_uIcc]⟩
  have hside3 : ∀ y ∈ [[z.im, w.im]], (w.re : ℂ) + y * I ∈ Rect := fun y hy =>
    mem_reProdIm.2 ⟨by simp [right_mem_uIcc], by simpa using hy⟩
  have hside4 : ∀ y ∈ [[z.im, w.im]], (z.re : ℂ) + y * I ∈ Rect := fun y hy =>
    mem_reProdIm.2 ⟨by simp [left_mem_uIcc], by simpa using hy⟩
  set F : ℂ → ℂ := fun s => (∑ u ∈ Z, ((divB f c R u).toNat : ℂ) * (h s * (s - u)⁻¹)) +
    logDeriv g s * h s with hF
  have hpt : ∀ s ∈ Rect, f s ≠ 0 → logDeriv f s * h s = F s := by
    intro s hs hfs
    rw [hdec s hs hfs, add_mul, Finset.sum_mul, hF]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [div_eq_mul_inv]; ring
  obtain ⟨b1, b2, b3, b4⟩ := hbd
  rw [rectInt_congr' (g := F) (fun x hx => hpt _ (hside1 x hx) (b1 x hx))
    (fun x hx => hpt _ (hside2 x hx) (b2 x hx)) (fun y hy => hpt _ (hside3 y hy) (b3 y hy))
    (fun y hy => hpt _ (hside4 y hy) (b4 y hy))]
  have hhc : ContinuousOn h Rect := hh.continuousOn.mono hsubU

  have hnot : ∀ u ∈ Z, (∀ x ∈ [[z.re, w.re]], (x : ℂ) + z.im * I ≠ u) ∧
      (∀ x ∈ [[z.re, w.re]], (x : ℂ) + w.im * I ≠ u) ∧
      (∀ y ∈ [[z.im, w.im]], (w.re : ℂ) + y * I ≠ u) ∧ (∀ y ∈ [[z.im, w.im]], (z.re : ℂ) + y * I ≠ u) := by
    intro u hu
    refine ⟨fun x hx h' => b1 x hx (h' ▸ hfu u hu), fun x hx h' => b2 x hx (h' ▸ hfu u hu),
      fun y hy h' => b3 y hy (h' ▸ hfu u hu), fun y hy h' => b4 y hy (h' ▸ hfu u hu)⟩
  have hint_u : ∀ u ∈ Z, RectIntegrable (fun s => h s * (s - u)⁻¹) z w := fun u hu =>
    rectIntegrable_mul_inv_sub hhc (hnot u hu).1 (hnot u hu).2.1 (hnot u hu).2.2.1 (hnot u hu).2.2.2

  have hgdiff : DifferentiableOn ℂ (fun s => logDeriv g s * h s) Rect := by
    intro s hs
    have hga : AnalyticAt ℂ g s := hg s (ball_subset_closedBall (hRb hs))
    have hgs : g s ≠ 0 := hg0 s (hrect hs)
    have hhs : DifferentiableAt ℂ h s := hh.differentiableAt (hU.mem_nhds (hsubU hs))
    have : DifferentiableAt ℂ (logDeriv g) s := by
      have e : logDeriv g = fun s => deriv g s / g s := funext fun s => logDeriv_apply g s
      rw [e]; exact hga.deriv.differentiableAt.div hga.differentiableAt hgs
    exact (this.mul hhs).differentiableWithinAt
  have hint_g : RectIntegrable (fun s => logDeriv g s * h s) z w :=
    rectIntegrable_of_continuousOn hgdiff.continuousOn
  have hint_sum : RectIntegrable (fun s => ∑ u ∈ Z, ((divB f c R u).toNat : ℂ) * (h s * (s - u)⁻¹)) z w := by
    have key : ∀ (φ : ℝ → ℂ) (a b : ℝ),
        (∀ u ∈ Z, IntervalIntegrable (fun t => h (φ t) * (φ t - u)⁻¹) volume a b) →
        IntervalIntegrable (fun t => ∑ u ∈ Z, ((divB f c R u).toNat : ℂ) * (h (φ t) * (φ t - u)⁻¹))
          volume a b := by
      intro φ a b hφ
      have := IntervalIntegrable.sum Z fun u hu => (hφ u hu).const_mul ((divB f c R u).toNat : ℂ)
      convert this using 1
      ext t; simp [Finset.sum_apply]
    exact ⟨key _ _ _ fun u hu => (hint_u u hu).1, key _ _ _ fun u hu => (hint_u u hu).2.1,
      key _ _ _ fun u hu => (hint_u u hu).2.2.1, key _ _ _ fun u hu => (hint_u u hu).2.2.2⟩
  have hg0' : rectInt (fun s => logDeriv g s * h s) z w = 0 := by
    exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn (fun s => logDeriv g s * h s) z w hgdiff
  rw [hF, rectInt_add' hint_sum hint_g, hg0', add_zero,
    rectInt_finset_sum Z _ fun u hu => (hint_u u hu).const_mul _]
  simp only [rectInt_const_mul]

  have hterm : ∀ u ∈ Z, ((divB f c R u).toNat : ℂ) * rectInt (fun s => h s * (s - u)⁻¹) z w =
      if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then
        2 * π * I * (((divB f c R u).toNat : ℂ) * h u) else 0 := by
    intro u hu
    split_ifs with hin
    · rw [rectInt_mul_inv_sub hU hsubU hh hin.1 hin.2.1 hin.2.2.1 hin.2.2.2]; ring
    · by_cases huR : u ∈ Rect
      · exfalso
        rcases mem_rect_cases huR hzw1 hzw2 with h' | h' | h' | h' | h'
        · exact hin h'
        · exact (hnot u hu).1 u.re (by
            rw [mem_reProdIm] at huR; exact huR.1) (by apply Complex.ext <;> simp [h'])
        · exact (hnot u hu).2.1 u.re (by
            rw [mem_reProdIm] at huR; exact huR.1) (by apply Complex.ext <;> simp [h'])
        · exact (hnot u hu).2.2.1 u.im (by
            rw [mem_reProdIm] at huR; exact huR.2) (by apply Complex.ext <;> simp [h'])
        · exact (hnot u hu).2.2.2 u.im (by
            rw [mem_reProdIm] at huR; exact huR.2) (by apply Complex.ext <;> simp [h'])
      · have hd : DifferentiableOn ℂ (fun s => h s * (s - u)⁻¹) Rect := by
          intro s hs
          have hsu : s - u ≠ 0 := sub_ne_zero.2 (fun h' => huR (h' ▸ hs))
          exact ((hh.differentiableAt (hU.mem_nhds (hsubU hs))).mul
            ((differentiableAt_id.sub_const u).inv hsu)).differentiableWithinAt
        have h0 : rectInt (fun s => h s * (s - u)⁻¹) z w = 0 := by
          exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn (fun s => h s * (s - u)⁻¹) z w hd
        rw [h0, mul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, ← Finset.mul_sum]

end TernaryGoldbach.Explicit
end

-- TernaryGoldbach.CircleMethod
section
open Complex MeasureTheory intervalIntegral Finset

namespace TernaryGoldbach

noncomputable def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * I * t)

end TernaryGoldbach
end

-- TernaryGoldbach.Explicit.LGrowth
section
open Complex MeasureTheory Set Filter
open Finset (range Icc)

namespace TernaryGoldbach.Explicit

variable {q : ℕ} [NeZero q]

theorem norm_cpow_neg {t : ℝ} (ht : 0 < t) (s : ℂ) :
    ‖(t : ℂ) ^ (-(s + 1))‖ = t ^ (-(s.re + 1)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]; simp

end TernaryGoldbach.Explicit
end

-- TernaryGoldbach.Explicit.ExplicitFormula
section
open Complex MeasureTheory Set Filter Asymptotics
open scoped Real Topology ArithmeticFunction.vonMangoldt Interval

namespace TernaryGoldbach.Explicit

structure GoodSmoothing (φ : ℝ → ℂ) (K c : ℝ) : Prop where
  continuousAt : ∀ y : ℝ, 0 < y → ContinuousAt φ y
  conv : MellinConvergent φ ((3 / 2 : ℝ) : ℂ)
  diff : ∀ s : ℂ, -1 < s.re → DifferentiableAt ℂ (mellin φ) s
  c_pos : 0 < c
  strip : ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖mellin φ s‖ ≤ K * Real.exp (-(c * |s.im|))

noncomputable def zT (T : ℝ) : ℂ := ((-1 / 2 : ℝ) : ℂ) + (-T : ℝ) * I
noncomputable def wT (T : ℝ) : ℂ := ((3 / 2 : ℝ) : ℂ) + (T : ℝ) * I

@[simp] theorem zT_re (T : ℝ) : (zT T).re = -1 / 2 := by simp [zT]
@[simp] theorem zT_im (T : ℝ) : (zT T).im = -T := by simp [zT]
@[simp] theorem wT_re (T : ℝ) : (wT T).re = 3 / 2 := by simp [wT]
@[simp] theorem wT_im (T : ℝ) : (wT T).im = T := by simp [wT]

noncomputable def RT (T : ℝ) : ℝ := 2 * (T + 3)

end TernaryGoldbach.Explicit
end

-- TernaryGoldbach.Explicit.Datum
section
open Complex MeasureTheory Set Filter Asymptotics Metric
open scoped Real Topology ArithmeticFunction.vonMangoldt Interval

namespace TernaryGoldbach.Explicit

structure LDatum (f : ℂ → ℂ) (B : ℝ → ℝ) (D CR : ℝ) : Prop where
  diff : Differentiable ℂ f
  center_ge : ∀ T : ℝ, 0.355 ≤ ‖f (2 + T * I)‖
  center_lt : ∀ T : ℝ, ‖f (2 + T * I)‖ < B T
  bound : ∀ T : ℝ, ∀ w ∈ closedBall (2 + T * I) 10, ‖f w‖ ≤ B T
  B_ge : ∀ T : ℝ, 1 ≤ B T
  B_mono : ∀ T T' : ℝ, |T| ≤ |T'| → B T ≤ B T'
  logB_lin : ∀ T : ℝ, Real.log (B T / 0.355) ≤ D + 37 + 2.6 * |T|
  D_nonneg : 0 ≤ D
  nz_strip : ∀ s : ℂ, -1 < s.re → s.re < 0 → f s ≠ 0
  nz_right : ∀ s : ℂ, 1 < s.re → f s ≠ 0
  right_bound : ∀ y : ℝ, ‖logDeriv f (((3 / 2 : ℝ) : ℂ) + y * I)‖ ≤ CR

noncomputable def multRectD (f : ℂ → ℂ) (T : ℝ) (u : ℂ) : ℕ :=
  (divB f 2 (RT T) u).toNat

end TernaryGoldbach.Explicit
end

-- TernaryGoldbach.Explicit.ZetaGrowth
section
open Complex MeasureTheory Set Filter Asymptotics
open scoped Real Topology

namespace TernaryGoldbach.Explicit

noncomputable def zetaF : ℂ → ℂ := Function.update (fun s ↦ (s - 1) * riemannZeta s) 1 1

theorem zetaF_of_ne {s : ℂ} (hs : s ≠ 1) : zetaF s = (s - 1) * riemannZeta s :=
  Function.update_of_ne hs _ _

theorem differentiableAt_zetaF_of_ne {s : ℂ} (hs : s ≠ 1) : DifferentiableAt ℂ zetaF s := by
  have : zetaF =ᶠ[𝓝 s] fun s => (s - 1) * riemannZeta s := by
    filter_upwards [isOpen_ne.mem_nhds hs] with t ht using zetaF_of_ne ht
  exact ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs)).congr_of_eventuallyEq
    this

theorem differentiable_zetaF : Differentiable ℂ zetaF := by
  intro s
  rcases ne_or_eq s 1 with hs | rfl
  · exact differentiableAt_zetaF_of_ne hs
  · refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact differentiableAt_zetaF_of_ne ht
    · simpa only [zetaF, continuousAt_update_same] using riemannZeta_residue_one

noncomputable def saw (t : ℝ) : ℂ := ((⌊t⌋₊ : ℝ) : ℂ) - t

theorem norm_saw_le {t : ℝ} (ht : 0 ≤ t) : ‖saw t‖ ≤ 1 := by
  rw [saw, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
    abs_of_nonneg (by linarith [Nat.floor_le ht])]
  linarith [Nat.lt_floor_add_one t]

theorem measurable_saw : Measurable saw := by
  unfold saw
  exact (Complex.measurable_ofReal.comp (measurable_from_nat.comp Nat.measurable_floor)).sub
    Complex.measurable_ofReal

noncomputable def Izeta (s : ℂ) : ℂ := ∫ t in Ioi (1:ℝ), saw t * (t : ℂ) ^ (-(s + 1))

theorem aesm_saw_integrand (s : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => saw t * (t : ℂ) ^ (-(s + 1))) (volume.restrict (Ioi 1)) := by
  refine measurable_saw.aestronglyMeasurable.mul ?_
  refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
  exact (Complex.continuousAt_ofReal_cpow_const t _
    (Or.inr (by have : (1:ℝ) < t := ht; positivity))).continuousWithinAt

theorem integrableOn_saw_integrand {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => saw t * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  refine ((integrableOn_Ioi_rpow_of_lt (a := -(s.re + 1)) (by linarith) one_pos).const_mul
    (1 : ℝ)).mono' (aesm_saw_integrand s) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
  have ht' : (0:ℝ) < t := lt_trans one_pos ht
  rw [norm_mul, norm_cpow_neg ht']
  exact mul_le_mul_of_nonneg_right (norm_saw_le ht'.le) (Real.rpow_nonneg ht'.le _)

theorem hasDerivAt_Izeta {s₀ : ℂ} (hs : 0 < s₀.re) :
    HasDerivAt Izeta (∫ t in Ioi (1:ℝ), saw t * (t : ℂ) ^ (-(s₀ + 1)) * (-(Real.log t : ℂ))) s₀ := by
  set σ₀ := s₀.re
  have hball : ∀ s ∈ Metric.ball s₀ (σ₀ / 2), σ₀ / 2 < s.re := fun s hs' => by
    rw [Metric.mem_ball, dist_eq_norm] at hs'
    have := Complex.abs_re_le_norm (s - s₀)
    rw [Complex.sub_re] at this
    linarith [neg_abs_le (s.re - s₀.re)]
  have hbd : IntegrableOn (fun t : ℝ => (1 : ℝ) * (4 / σ₀) * t ^ (-(σ₀ / 4) - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 1))
    (F := fun s t => saw t * (t : ℂ) ^ (-(s + 1)))
    (F' := fun s t => saw t * (t : ℂ) ^ (-(s + 1)) * (-(Real.log t : ℂ))) (x₀ := s₀)
    (bound := fun t => (1 : ℝ) * (4 / σ₀) * t ^ (-(σ₀ / 4) - 1))
    (Metric.ball_mem_nhds s₀ (half_pos hs))
    (Filter.Eventually.of_forall fun s => aesm_saw_integrand s)
    (integrableOn_saw_integrand hs)
    ((aesm_saw_integrand s₀).mul
      (Complex.measurable_ofReal.comp Real.measurable_log).neg.aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht s hs' => by
      have ht' : (1:ℝ) < t := ht
      have ht0 : (0:ℝ) < t := by linarith
      have hσ := hball s hs'
      rw [norm_mul, norm_mul, norm_cpow_neg ht0, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg ht'.le)]
      have hlog : Real.log t ≤ t ^ (σ₀ / 4) / (σ₀ / 4) := Real.log_le_rpow_div ht0.le (by positivity)
      have hpow : t ^ (-(s.re + 1)) ≤ t ^ (-(σ₀ / 2) - 1) :=
        Real.rpow_le_rpow_of_exponent_le ht'.le (by linarith)
      have e : t ^ (-(σ₀ / 2) - 1) * (t ^ (σ₀ / 4) / (σ₀ / 4)) = (4 / σ₀) * t ^ (-(σ₀ / 4) - 1) := by
        rw [mul_div_assoc', ← Real.rpow_add ht0, show -(σ₀ / 2) - 1 + σ₀ / 4 = -(σ₀ / 4) - 1 by ring]
        field_simp
      calc ‖saw t‖ * t ^ (-(s.re + 1)) * Real.log t
          ≤ (1 : ℝ) * t ^ (-(σ₀ / 2) - 1) * (t ^ (σ₀ / 4) / (σ₀ / 4)) :=
            mul_le_mul (mul_le_mul (norm_saw_le ht0.le) hpow (Real.rpow_nonneg ht0.le _)
              (by positivity)) hlog (Real.log_nonneg ht'.le) (by positivity)
          _ = (1 : ℝ) * (4 / σ₀) * t ^ (-(σ₀ / 4) - 1) := by rw [mul_assoc, e]; ring))
    hbd
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht s _ => by
      have ht0 : (0:ℝ) < t := lt_trans one_pos ht
      have ht0' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      have h1 : HasDerivAt (fun s : ℂ => -(s + 1)) (-1) s := ((hasDerivAt_id s).add_const 1).neg
      refine ((h1.const_cpow (Or.inl ht0')).const_mul (saw t)).congr_deriv ?_
      rw [← Complex.ofReal_log ht0.le]; ring))
  exact h.2

theorem riemannZeta_eq_Izeta {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) + s * Izeta s := by
  have hs0 : 0 < s.re := by linarith
  rw [← LSeries_one_eq_riemannZeta hs]
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (1 : ℕ → ℂ) k) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun n => ?_)
    simp
  have hsum : LSeriesSummable 1 s := by
    rw [show (1 : ℕ → ℂ) = fun _ => 1 from rfl]
    exact (LSeriesSummable_one_iff).2 hs
  rw [LSeries_eq_mul_integral _ zero_le_one hs hsum hO]
  have e1 : ∀ t : ℝ, (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k) = ((⌊t⌋₊ : ℝ) : ℂ) := by
    intro t; simp
  simp_rw [e1]
  have hI1 : IntegrableOn (fun t : ℝ => saw t * (t : ℂ) ^ (-(s + 1))) (Ioi 1) :=
    integrableOn_saw_integrand hs0
  have hI2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos
  have e2 : ∀ t ∈ Ioi (1:ℝ), ((⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      saw t * (t : ℂ) ^ (-(s + 1)) + (t : ℂ) ^ (-s) := by
    intro t ht
    have ht' : (0:ℝ) < t := lt_trans one_pos ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht'.ne'
    rw [saw, sub_mul, show (t : ℂ) ^ (-s) = (t : ℂ) * (t : ℂ) ^ (-(s + 1)) by
      rw [show -s = 1 + -(s + 1) by ring, Complex.cpow_add _ _ ht0, Complex.cpow_one]]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e2, integral_add hI1 hI2,
    integral_Ioi_cpow_of_lt (by simp; linarith) one_pos, Complex.ofReal_one, Complex.one_cpow]
  have hs1 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hs1' : -s + 1 ≠ 0 := by
    intro h; apply hs1; linear_combination -h
  rw [Izeta]
  field_simp
  ring

theorem zetaF_eq {s : ℂ} (hs : 0 < s.re) : zetaF s = s + s * (s - 1) * Izeta s := by
  set U := {s : ℂ | 0 < s.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hf : AnalyticOnNhd ℂ zetaF U := fun z _ => differentiable_zetaF.analyticAt z
  have hg : AnalyticOnNhd ℂ (fun s => s + s * (s - 1) * Izeta s) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    exact (differentiableAt_id.add ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
      (hasDerivAt_Izeta hz).differentiableAt)).differentiableWithinAt
  have h2 : (2 : ℂ) ∈ U := by show (0:ℝ) < (2:ℂ).re; norm_num
  have hev : zetaF =ᶠ[nhds (2 : ℂ)] fun s => s + s * (s - 1) * Izeta s := by
    have hopen : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by show (1:ℝ) < (2:ℂ).re; norm_num)
    filter_upwards [hopen] with s hs1
    have hne : s ≠ 1 := by intro h; rw [h] at hs1; simp at hs1
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hne
    rw [zetaF_of_ne hne, riemannZeta_eq_Izeta hs1]
    field_simp
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUc h2 hev hs

theorem norm_zetaF_le {s : ℂ} (hs : 0 < s.re) : ‖zetaF s‖ ≤ ‖s‖ + ‖s‖ * ‖s - 1‖ / s.re := by
  rw [zetaF_eq hs]
  have hb : ‖Izeta s‖ ≤ 1 / s.re := by
    have hi := (integrableOn_Ioi_rpow_of_lt (a := -(s.re + 1)) (by linarith) one_pos).const_mul (1 : ℝ)
    refine (norm_integral_le_of_norm_le hi ((ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun t ht => ?_))).trans (le_of_eq ?_)
    · have ht' : (0:ℝ) < t := lt_trans one_pos ht
      rw [norm_mul, norm_cpow_neg ht']
      exact mul_le_mul_of_nonneg_right (norm_saw_le ht'.le) (Real.rpow_nonneg ht'.le _)
    · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
        show -(s.re + 1) + 1 = -s.re by ring]
      have : s.re ≠ 0 := hs.ne'
      field_simp
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have := mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ) ≤ ‖s‖ * ‖s - 1‖)
  rw [mul_one_div] at this
  linarith

end TernaryGoldbach.Explicit
end

-- RSBounds.BacklundZetaRegularization
section
open Complex MeasureTheory Set Filter Finset
open scoped Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundZetaRegularization

open TernaryGoldbach.Explicit

theorem zeta_eq_Izeta_of_pos {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = 1 + 1 / (s - 1) + s * Izeta s := by
  have hh := zetaF_eq hs
  rw [zetaF_of_ne hs1] at hh
  have hn : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  apply (mul_left_cancel₀ hn)
  calc
    (s - 1) * riemannZeta s = s + s * (s - 1) * Izeta s := hh
    _ = (s - 1) * (1 + 1 / (s - 1) + s * Izeta s) := by field_simp [hn]; ring

noncomputable def firstRemainder (s : ℂ) (x : ℝ) : ℂ :=
  (-s * (x : ℂ) ^ (-s - 1)) * (B1 x : ℝ)

theorem firstRemainder_eq (s : ℂ) (x : ℝ) :
    firstRemainder s x = s * (saw x * (x : ℂ) ^ (-(s + 1))) +
      (s / 2) * (x : ℂ) ^ (-s - 1) := by
  unfold firstRemainder B1 saw
  push_cast
  rw [show -(s + 1) = -s - 1 by ring]
  ring

theorem integrableOn_firstRemainder {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (firstRemainder s) (Ioi (1 : ℝ)) := by
  change IntegrableOn (fun x => firstRemainder s x) (Ioi (1 : ℝ))
  simp_rw [firstRemainder_eq]
  exact ((integrableOn_saw_integrand hs).const_mul s).add
    ((integrableOn_Ioi_cpow_of_lt (a := -s - 1) (by simp; linarith)
      (by norm_num : (0 : ℝ) < 1)).const_mul (s / 2))

theorem integral_firstRemainder {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (1 : ℝ), firstRemainder s x) = s * Izeta s + 1 / 2 := by
  have hs0 : s ≠ 0 := by intro he; simp [he] at hs
  have hfi := integrableOn_saw_integrand hs
  have hgi := integrableOn_Ioi_cpow_of_lt (a := -s - 1) (by simp; linarith)
    (by norm_num : (0 : ℝ) < 1)
  simp_rw [firstRemainder_eq]
  rw [integral_add (hfi.const_mul s) (hgi.const_mul (s / 2)),
    integral_const_mul, integral_const_mul,
    integral_Ioi_cpow_of_lt (by simp; linarith) (by norm_num : (0 : ℝ) < 1)]
  simp only [Complex.ofReal_one, Complex.one_cpow, Izeta]
  field_simp [hs0]
  ring

theorem finite_regularized_sum {s : ℂ} (hs : 0 < s.re) {M : ℕ} (hM : 1 ≤ M) :
    (∑ k ∈ range M, (k : ℂ) ^ (-s)) - (∫ x in (1 : ℝ)..M, (x : ℂ) ^ (-s)) =
      (1 - (M : ℂ) ^ (-s)) / 2 + ∫ x in (1 : ℝ)..M, firstRemainder s x := by
  let f : ℝ → ℂ := fun x => (x : ℂ) ^ (-s)
  have hs0 : -s ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp at this
    linarith
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hderiv (x : ℝ) (hx : 1 ≤ x) :
      HasDerivAt f (-s * (x : ℂ) ^ (-s - 1)) x :=
    hasDerivAt_ofReal_cpow_const (by linarith) hs0
  have hc : ContinuousOn (deriv f) (uIcc (1 : ℝ) M) := by
    rw [uIcc_of_le hM']
    apply ContinuousOn.congr (f := fun x : ℝ => -s * (x : ℂ) ^ (-s - 1))
    · intro x hx
      exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const _ _
        (Or.inr (by linarith [hx.1])))).continuousWithinAt
    · intro x hx
      exact (hderiv x hx.1).deriv
  have hh := sum_eq_integral_add_integral_deriv (f := f)
    (a := 1) (b := (M : ℝ)) (by norm_num) hM'
    (fun x hx => (hderiv x hx.1).differentiableAt) hc
  simp only [RCLike.ofReal_eq_complex_ofReal] at hh
  have hsets : Finset.Ioc 1 M = Finset.Ico 2 (M + 1) := by ext k; simp; omega
  have hint : (∫ x in (1 : ℝ)..M, deriv f x * (B1 x : ℝ)) =
      ∫ x in (1 : ℝ)..M, firstRemainder s x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hM'] at hx
    dsimp only
    rw [(hderiv x hx.1).deriv]
    rfl
  rw [hint] at hh
  simp only [Nat.floor_one, Nat.floor_natCast] at hh
  rw [hsets, sum_Ico_eq_sub _ (by omega)] at hh
  simp only [sum_range_succ, sum_range_zero, add_zero] at hh
  norm_num [f, B1, hs0] at hh
  linear_combination hh

theorem regularized_sum_from_one_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun M : ℕ => (∑ k ∈ range M, (k : ℂ) ^ (-s)) -
      (∫ x in (1 : ℝ)..M, (x : ℂ) ^ (-s))) atTop (𝓝 (1 + s * Izeta s)) := by
  have hf0 : Tendsto (fun M : ℕ => (M : ℂ) ^ (-s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    change Tendsto (fun M : ℕ => ‖(M : ℂ) ^ (-s)‖) atTop (𝓝 0)
    simp only [Complex.norm_natCast_cpow_of_re_ne_zero _
      (show (-s).re ≠ 0 by simp only [Complex.neg_re]; linarith), Complex.neg_re]
    exact (tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop
  have hI := intervalIntegral_tendsto_integral_Ioi (1 : ℝ)
    (integrableOn_firstRemainder hs) tendsto_natCast_atTop_atTop
  have hlim := ((hf0.const_sub 1).div_const 2).add hI
  rw [integral_firstRemainder hs] at hlim
  have he : (1 - (0 : ℂ)) / 2 + (s * Izeta s + 1 / 2) = 1 + s * Izeta s := by ring
  rw [he] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with M hM
  exact (finite_regularized_sum hs hM).symm

theorem regularized_sum_tendsto {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    Tendsto (fun M : ℕ => (∑ k ∈ Ico N M, (k : ℂ) ^ (-s)) -
      (∫ x in (N : ℝ)..M, (x : ℂ) ^ (-s))) atTop
      (𝓝 (riemannZeta s - (∑ k ∈ range N, (k : ℂ) ^ (-s)) -
        (N : ℂ) ^ (1 - s) / (s - 1))) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hint {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro x hx
    exact (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr (by linarith [hx.1]))).continuousWithinAt
  have hIN : (∫ x in (1 : ℝ)..N, (x : ℂ) ^ (-s)) =
      ((N : ℂ) ^ (1 - s) - 1) / (1 - s) := by
    rw [integral_cpow (Or.inr ⟨by intro he; exact hs1 (neg_inj.mp he),
      by rw [uIcc_of_le hN']; simp⟩), Complex.ofReal_one, Complex.one_cpow]
    push_cast
    congr 2 <;> ring
  have hlim := ((regularized_sum_from_one_tendsto hs).sub_const
    (∑ k ∈ range N, (k : ℂ) ^ (-s))).add_const
      (∫ x in (1 : ℝ)..N, (x : ℂ) ^ (-s))
  have htarget : (1 + s * Izeta s - (∑ k ∈ range N, (k : ℂ) ^ (-s))) +
      (∫ x in (1 : ℝ)..N, (x : ℂ) ^ (-s)) =
      riemannZeta s - (∑ k ∈ range N, (k : ℂ) ^ (-s)) -
        (N : ℂ) ^ (1 - s) / (s - 1) := by
    rw [hIN, zeta_eq_Izeta_of_pos hs hs1]
    field_simp [sub_ne_zero.mpr hs1, sub_ne_zero.mpr hs1.symm]
    ring
  rw [htarget] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop N] with M hM
  have hM' : (N : ℝ) ≤ M := by exact_mod_cast hM
  have hcat := intervalIntegral.integral_add_adjacent_intervals
    (hint le_rfl hN') (hint hN' hM')
  rw [sum_Ico_eq_sub _ hM, ← hcat]
  ring

end TernaryGoldbach.RSBounds.BacklundZetaRegularization
end

-- TernaryGoldbach.Prelim.RamareHarm
section
open Real Finset Filter Topology

namespace TernaryGoldbach.Prelim.RamPf

theorem hasSum_log {a : ℝ} (ha : 0 < a) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1))
      (Real.log (1 + a⁻¹)) := Real.hasSum_log_one_add_inv ha

theorem log_term_nonneg {a : ℝ} (ha : 0 < a) (k : ℕ) :
    0 ≤ (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1) := by positivity

theorem log_one_add_inv_ge {a : ℝ} (ha : 0 < a) : 2 / (2 * a + 1) ≤ Real.log (1 + a⁻¹) := by
  have := le_hasSum (hasSum_log ha) 0 (fun k _ => log_term_nonneg ha k)
  simp only [Nat.cast_zero, mul_zero, zero_add, div_one, mul_one, pow_one] at this
  rw [div_eq_mul_one_div]; exact this

theorem log_one_add_inv_bounds {a : ℝ} (ha : 0 < a) (K : ℕ) :
    ∑ k ∈ range K, (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1) ≤
        Real.log (1 + a⁻¹) ∧
      Real.log (1 + a⁻¹) ≤ ∑ k ∈ range K, (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1) +
        2 / (2 * K + 1) * (1 / (2 * a + 1)) ^ (2 * K + 1) / (1 - (1 / (2 * a + 1)) ^ 2) := by
  have h := hasSum_log ha
  refine ⟨sum_le_hasSum _ (fun k _ => log_term_nonneg ha k) h, ?_⟩
  set y : ℝ := 1 / (2 * a + 1) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
  have hy2 : y ^ 2 < 1 := by nlinarith
  set f : ℕ → ℝ := fun k => (2 : ℝ) * (1 / (2 * k + 1)) * y ^ (2 * k + 1) with hf
  have htail := (hasSum_nat_add_iff' K).2 h

  have hg : HasSum (fun k : ℕ => 2 / (2 * K + 1) * y ^ (2 * K + 1) * (y ^ 2) ^ k)
      (2 / (2 * K + 1) * y ^ (2 * K + 1) / (1 - y ^ 2)) := by
    have := (hasSum_geometric_of_lt_one (by positivity) hy2).mul_left (2 / (2 * K + 1) * y ^ (2 * K + 1))
    rwa [← div_eq_mul_inv] at this
  have hle : ∀ k, f (k + K) ≤ 2 / (2 * K + 1) * y ^ (2 * K + 1) * (y ^ 2) ^ k := by
    intro k
    simp only [hf]
    have e : y ^ (2 * (↑(k + K) : ℕ) + 1) = y ^ (2 * K + 1) * (y ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    rw [show (2 : ℝ) * ((k + K : ℕ) : ℝ) + 1 = 2 * (k + K : ℕ) + 1 from rfl]
    have e2 : y ^ (2 * (k + K) + 1) = y ^ (2 * K + 1) * (y ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    rw [e2]
    have hk : (2 : ℝ) * (1 / (2 * ((k + K : ℕ) : ℝ) + 1)) ≤ 2 / (2 * K + 1) := by
      rw [mul_one_div]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hp : 0 ≤ y ^ (2 * K + 1) * (y ^ 2) ^ k := by positivity
    calc (2 : ℝ) * (1 / (2 * ((k + K : ℕ) : ℝ) + 1)) * (y ^ (2 * K + 1) * (y ^ 2) ^ k)
        ≤ 2 / (2 * K + 1) * (y ^ (2 * K + 1) * (y ^ 2) ^ k) := mul_le_mul_of_nonneg_right hk hp
      _ = _ := by ring
  have hT := hasSum_le hle htail hg
  linarith

theorem log_one_add_inv_le {a : ℝ} (ha : 0 < a) :
    Real.log (1 + a⁻¹) ≤ 2 / (2 * a + 1) + 1 / (6 * a * (a + 1) * (2 * a + 1)) := by
  have h := (log_one_add_inv_bounds ha 1).2
  simp only [range_one, sum_singleton, Nat.cast_zero, mul_zero, zero_add, div_one, mul_one,
    pow_one, Nat.cast_one] at h
  refine h.trans (le_of_eq ?_)
  have h1 : (2 * a + 1) ≠ 0 := by positivity
  have h3 : (1 : ℝ) - (1 / (2 * a + 1)) ^ 2 = 4 * a * (a + 1) / (2 * a + 1) ^ 2 := by
    field_simp; ring
  have h4 : (2 : ℝ) / (2 + 1) * (1 / (2 * a + 1)) ^ (2 + 1) / (4 * a * (a + 1) / (2 * a + 1) ^ 2) =
      1 / (6 * a * (a + 1) * (2 * a + 1)) := by
    have : a + 1 ≠ 0 := by positivity
    rw [show (2 : ℕ) + 1 = 3 from rfl, div_pow, one_pow]
    field_simp; ring
  rw [h3, h4, mul_one_div]

theorem dk_bounds {k : ℕ} (hk : 1 ≤ k) :
    1 / (2 * ((k : ℝ) + 1)) - 1 / (2 * ((k : ℝ) + 2)) ≤
        Real.log ((k : ℝ) + 1) - Real.log k - 1 / ((k : ℝ) + 1) ∧
      Real.log ((k : ℝ) + 1) - Real.log k - 1 / ((k : ℝ) + 1) ≤
        1 / (2 * (k : ℝ)) - 1 / (2 * ((k : ℝ) + 1)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog : Real.log ((k : ℝ) + 1) - Real.log k = Real.log (1 + (k : ℝ)⁻¹) := by
    rw [← Real.log_div (by positivity) hk0.ne']; congr 1; field_simp
  rw [hlog]
  have hl := log_one_add_inv_ge hk0
  have hu := log_one_add_inv_le hk0
  constructor
  · have : 1 / (2 * ((k : ℝ) + 1)) - 1 / (2 * ((k : ℝ) + 2)) ≤ 2 / (2 * k + 1) - 1 / ((k : ℝ) + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hk0]
    linarith
  · have : 2 / (2 * (k : ℝ) + 1) + 1 / (6 * k * (k + 1) * (2 * k + 1)) - 1 / ((k : ℝ) + 1) ≤
        1 / (2 * (k : ℝ)) - 1 / (2 * ((k : ℝ) + 1)) := by
      have e1 : 2 / (2 * (k : ℝ) + 1) + 1 / (6 * k * (k + 1) * (2 * k + 1)) - 1 / ((k : ℝ) + 1) =
          (6 * k + 1) / (6 * k * (k + 1) * (2 * k + 1)) := by field_simp; ring
      have e2 : 1 / (2 * (k : ℝ)) - 1 / (2 * ((k : ℝ) + 1)) = 3 * (2 * k + 1) / (6 * k * (k + 1) * (2 * k + 1)) := by
        field_simp; ring
      rw [e1, e2]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith

theorem harm_diff (n : ℕ) : ∀ M, n ≤ M →
    ((harmonic n : ℚ) : ℝ) - Real.log n - (((harmonic M : ℚ) : ℝ) - Real.log M) =
      ∑ k ∈ Ico n M, (Real.log ((k : ℝ) + 1) - Real.log k - 1 / ((k : ℝ) + 1)) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hnM ih =>
    rw [sum_Ico_succ_top hnM, ← ih, harmonic_succ]
    push_cast
    ring

theorem harm_bounds {n : ℕ} (hn : 1 ≤ n) :
    1 / (2 * ((n : ℝ) + 1)) ≤ ((harmonic n : ℚ) : ℝ) - Real.log n - eulerMascheroniConstant ∧
      ((harmonic n : ℚ) : ℝ) - Real.log n - eulerMascheroniConstant ≤ 1 / (2 * (n : ℝ)) := by
  set u : ℕ → ℝ := fun M => ((harmonic n : ℚ) : ℝ) - Real.log n - eulerMascheroniSeq' M with hu
  have hlim : Tendsto u atTop (𝓝 (((harmonic n : ℚ) : ℝ) - Real.log n - eulerMascheroniConstant)) :=
    tendsto_const_nhds.sub tendsto_eulerMascheroniSeq'
  have hseq : ∀ M, 1 ≤ M → eulerMascheroniSeq' M = ((harmonic M : ℚ) : ℝ) - Real.log M := by
    intro M hM; rw [eulerMascheroniSeq', if_neg (by omega)]

  have hlow : ∀ M, n ≤ M → 1 / (2 * ((n : ℝ) + 1)) - 1 / (2 * ((M : ℝ) + 1)) ≤ u M := by
    intro M hM
    simp only [hu]
    rw [hseq M (le_trans hn hM), harm_diff n M hM]
    have hsum : ∑ k ∈ Ico n M, (1 / (2 * ((k : ℝ) + 1)) - 1 / (2 * ((k : ℝ) + 2))) =
        1 / (2 * ((n : ℝ) + 1)) - 1 / (2 * ((M : ℝ) + 1)) := by
      induction M, hM using Nat.le_induction with
      | base => simp
      | succ M hnM ih => rw [sum_Ico_succ_top hnM, ih]; push_cast; ring
    rw [← hsum]
    exact sum_le_sum fun k hk => (dk_bounds (le_trans hn (mem_Ico.1 hk).1)).1
  have hup : ∀ M, n ≤ M → u M ≤ 1 / (2 * (n : ℝ)) - 1 / (2 * (M : ℝ)) := by
    intro M hM
    simp only [hu]
    rw [hseq M (le_trans hn hM), harm_diff n M hM]
    have hsum : ∑ k ∈ Ico n M, (1 / (2 * (k : ℝ)) - 1 / (2 * ((k : ℝ) + 1))) =
        1 / (2 * (n : ℝ)) - 1 / (2 * (M : ℝ)) := by
      induction M, hM using Nat.le_induction with
      | base => simp
      | succ M hnM ih => rw [sum_Ico_succ_top hnM, ih]; push_cast; ring
    rw [← hsum]
    exact sum_le_sum fun k hk => (dk_bounds (le_trans hn (mem_Ico.1 hk).1)).2
  have hz1 : Tendsto (fun M : ℕ => 1 / (2 * ((M : ℝ) + 1))) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (1 / 2 : ℝ)
    simp only [mul_zero] at this
    refine this.congr fun M => ?_
    field_simp
  have hz2 : Tendsto (fun M : ℕ => 1 / (2 * (M : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat).const_mul (1 / 2 : ℝ)
    simp only [mul_zero] at this
    refine this.congr fun M => ?_
    field_simp
  constructor
  · have h1 : Tendsto (fun M => u M + 1 / (2 * ((M : ℝ) + 1))) atTop
        (𝓝 (((harmonic n : ℚ) : ℝ) - Real.log n - eulerMascheroniConstant + 0)) := hlim.add hz1
    rw [add_zero] at h1
    exact ge_of_tendsto h1 (eventually_atTop.2 ⟨n, fun M hM => by linarith [hlow M hM]⟩)
  · have h1 : Tendsto (fun M => u M + 1 / (2 * (M : ℝ))) atTop
        (𝓝 (((harmonic n : ℚ) : ℝ) - Real.log n - eulerMascheroniConstant + 0)) := hlim.add hz2
    rw [add_zero] at h1
    exact le_of_tendsto h1 (eventually_atTop.2 ⟨n, fun M hM => by linarith [hup M hM]⟩)

end TernaryGoldbach.Prelim.RamPf
end

-- TernaryGoldbach.Prelim.LogWalk
section
open Finset Real

namespace TernaryGoldbach.Prelim.LogWalk

open TernaryGoldbach.Prelim.RamPf (log_one_add_inv_bounds)

def incrAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => incrAux k n + 2 * 10 ^ 30 / ((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1))

def incrLo (n : ℕ) : ℕ := incrAux 12 n
def incrHi (n : ℕ) : ℕ := incrAux 12 n + 12 + 3 * 10 ^ 30 / (25 * (2 * n + 1) ^ 25) + 1

theorem incrAux_le (n : ℕ) : ∀ k, (incrAux k n : ℝ) ≤
    10 ^ 30 * ∑ j ∈ range k, (2 : ℝ) * (1 / (2 * j + 1)) * (1 / (2 * (n : ℝ) + 1)) ^ (2 * j + 1)
  | 0 => by simp [incrAux]
  | k + 1 => by
    rw [incrAux, sum_range_succ, mul_add, Nat.cast_add]
    refine add_le_add (incrAux_le n k) ?_
    have := Nat.cast_div_le (α := ℝ) (m := 2 * 10 ^ 30) (n := (2 * k + 1) * (2 * n + 1) ^ (2 * k + 1))
    refine this.trans (le_of_eq ?_)
    rw [one_div_pow]
    push_cast
    field_simp
    norm_num

theorem le_incrAux (n : ℕ) : ∀ k, 10 ^ 30 * ∑ j ∈ range k,
    (2 : ℝ) * (1 / (2 * j + 1)) * (1 / (2 * (n : ℝ) + 1)) ^ (2 * j + 1) ≤ (incrAux k n : ℝ) + k
  | 0 => by simp [incrAux]
  | k + 1 => by
    rw [incrAux, sum_range_succ, mul_add, Nat.cast_add, Nat.cast_succ]
    have h1 := le_incrAux n k
    have hpos : 0 < (2 * k + 1) * (2 * n + 1) ^ (2 * k + 1) := by positivity
    have h2 := Nat.lt_div_mul_add (a := 2 * 10 ^ 30) hpos
    have h3 : ((2 * 10 ^ 30 : ℕ) : ℝ) < ((2 * 10 ^ 30 / ((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1)) : ℕ) : ℝ) *
        (((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1) : ℕ) : ℝ) + (((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1) : ℕ) : ℝ) := by
      exact_mod_cast h2
    have hq : (0 : ℝ) < (((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1) : ℕ) : ℝ) := by exact_mod_cast hpos
    have h4 : (10 : ℝ) ^ 30 * (2 * (1 / (2 * (k : ℝ) + 1)) * (1 / (2 * (n : ℝ) + 1)) ^ (2 * k + 1)) ≤
        ((2 * 10 ^ 30 / ((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1)) : ℕ) : ℝ) + 1 := by
      have e : (10 : ℝ) ^ 30 * (2 * (1 / (2 * (k : ℝ) + 1)) * (1 / (2 * (n : ℝ) + 1)) ^ (2 * k + 1)) =
          ((2 * 10 ^ 30 : ℕ) : ℝ) / (((2 * k + 1) * (2 * n + 1) ^ (2 * k + 1) : ℕ) : ℝ) := by
        rw [one_div_pow]; push_cast; field_simp; norm_num
      rw [e, div_le_iff₀ hq]; linarith
    linarith

theorem incr_bounds {n : ℕ} (hn : 1 ≤ n) :
    (incrLo n : ℝ) ≤ 10 ^ 30 * Real.log (1 + (n : ℝ)⁻¹) ∧
      10 ^ 30 * Real.log (1 + (n : ℝ)⁻¹) ≤ (incrHi n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨h1, h2⟩ := log_one_add_inv_bounds hn0 12
  refine ⟨(incrAux_le n 12).trans (by nlinarith), ?_⟩
  have h3 := le_incrAux n 12

  set y : ℝ := 1 / (2 * (n : ℝ) + 1) with hy
  have hy0 : 0 < y := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hy3 : y ≤ 1 / 3 := by
    rw [hy, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have htail : 2 / (2 * ((12 : ℕ) : ℝ) + 1) * y ^ (2 * 12 + 1) / (1 - y ^ 2) ≤ 3 / 25 * y ^ 25 := by
    have h1y : 8 / 9 ≤ 1 - y ^ 2 := by nlinarith
    rw [div_le_iff₀ (by linarith)]
    push_cast
    have : 0 ≤ y ^ 25 := by positivity
    nlinarith
  have hfl : (10 : ℝ) ^ 30 * (3 / 25 * y ^ 25) ≤ ((3 * 10 ^ 30 / (25 * (2 * n + 1) ^ 25) : ℕ) : ℝ) + 1 := by
    have hpos : 0 < 25 * (2 * n + 1) ^ 25 := by positivity
    have h2 := Nat.lt_div_mul_add (a := 3 * 10 ^ 30) hpos
    have hq : (0 : ℝ) < ((25 * (2 * n + 1) ^ 25 : ℕ) : ℝ) := by exact_mod_cast hpos
    have h3' : ((3 * 10 ^ 30 : ℕ) : ℝ) < ((3 * 10 ^ 30 / (25 * (2 * n + 1) ^ 25) : ℕ) : ℝ) *
        ((25 * (2 * n + 1) ^ 25 : ℕ) : ℝ) + ((25 * (2 * n + 1) ^ 25 : ℕ) : ℝ) := by exact_mod_cast h2
    have e : (10 : ℝ) ^ 30 * (3 / 25 * y ^ 25) = ((3 * 10 ^ 30 : ℕ) : ℝ) / ((25 * (2 * n + 1) ^ 25 : ℕ) : ℝ) := by
      rw [hy, one_div_pow]; push_cast; field_simp; norm_num
    rw [e, div_le_iff₀ hq]; linarith
  unfold incrHi
  push_cast
  push_cast at h3
  nlinarith

theorem floor_div_bounds (a b : ℕ) (hb : 0 < b) :
    ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b ∧ (a : ℝ) / b ≤ ((a / b : ℕ) : ℝ) + 1 := by
  refine ⟨Nat.cast_div_le, ?_⟩
  have h2 := Nat.lt_div_mul_add (a := a) hb
  have hq : (0 : ℝ) < b := by exact_mod_cast hb
  have : (a : ℝ) < ((a / b : ℕ) : ℝ) * b + b := by exact_mod_cast h2
  rw [div_le_iff₀ hq]; linarith

end TernaryGoldbach.Prelim.LogWalk
end

-- RSBounds.SmallTotientProduct
section
open Finset Real

namespace TernaryGoldbach.RSBounds.SmallTotientProduct

open TernaryGoldbach.Prelim.LogWalk
open TernaryGoldbach.Prelim.RamPf (log_one_add_inv_bounds)

def qAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, a, b => qAux k a b + 2 * 10 ^ 30 * b ^ (2 * k + 1) / ((2 * k + 1) * (2 * a + b) ^ (2 * k + 1))

def qLo (a b : ℕ) : ℕ := qAux 12 a b
def qHi (a b : ℕ) : ℕ := qAux 12 a b + 12 + 3 * 10 ^ 30 * b ^ 25 / (25 * (2 * a + b) ^ 25) + 1

theorem qAux_le (a b : ℕ) (hb : 0 < b) : ∀ k, (qAux k a b : ℝ) ≤
    10 ^ 30 * ∑ j ∈ range k, (2 : ℝ) * (1 / (2 * j + 1)) * ((b : ℝ) / (2 * a + b)) ^ (2 * j + 1)
  | 0 => by simp [qAux]
  | k + 1 => by
    rw [qAux, sum_range_succ, mul_add, Nat.cast_add]
    refine add_le_add (qAux_le a b hb k) ?_
    have := Nat.cast_div_le (α := ℝ) (m := 2 * 10 ^ 30 * b ^ (2 * k + 1))
      (n := (2 * k + 1) * (2 * a + b) ^ (2 * k + 1))
    refine this.trans (le_of_eq ?_)
    have : (0 : ℝ) < 2 * a + b := by positivity
    rw [div_pow]
    push_cast
    field_simp
    norm_num

theorem le_qAux (a b : ℕ) (hb : 0 < b) : ∀ k, 10 ^ 30 * ∑ j ∈ range k,
    (2 : ℝ) * (1 / (2 * j + 1)) * ((b : ℝ) / (2 * a + b)) ^ (2 * j + 1) ≤ (qAux k a b : ℝ) + k
  | 0 => by simp [qAux]
  | k + 1 => by
    rw [qAux, sum_range_succ, mul_add, Nat.cast_add, Nat.cast_succ]
    have h1 := le_qAux a b hb k
    have hpos : 0 < (2 * k + 1) * (2 * a + b) ^ (2 * k + 1) := by positivity
    obtain ⟨-, h2⟩ := floor_div_bounds (2 * 10 ^ 30 * b ^ (2 * k + 1)) _ hpos
    have e : (10 : ℝ) ^ 30 * (2 * (1 / (2 * (k : ℝ) + 1)) * ((b : ℝ) / (2 * a + b)) ^ (2 * k + 1)) =
        ((2 * 10 ^ 30 * b ^ (2 * k + 1) : ℕ) : ℝ) / (((2 * k + 1) * (2 * a + b) ^ (2 * k + 1) : ℕ) : ℝ) := by
      have : (0 : ℝ) < 2 * a + b := by positivity
      rw [div_pow]; push_cast; field_simp; norm_num
    linarith

theorem q_bounds {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    (qLo a b : ℝ) ≤ 10 ^ 30 * Real.log (1 + (b : ℝ) / a) ∧
      10 ^ 30 * Real.log (1 + (b : ℝ) / a) ≤ (qHi a b : ℝ) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  set r : ℝ := (a : ℝ) / b with hr
  have hr0 : 0 < r := by positivity
  obtain ⟨h1, h2⟩ := log_one_add_inv_bounds hr0 12
  have ey : 1 / (2 * r + 1) = (b : ℝ) / (2 * a + b) := by rw [hr]; field_simp
  have el : 1 + r⁻¹ = 1 + (b : ℝ) / a := by rw [hr, inv_div]
  rw [ey, el] at h1 h2
  refine ⟨(qAux_le a b hb 12).trans (by nlinarith), ?_⟩
  have h3 := le_qAux a b hb 12
  set y : ℝ := (b : ℝ) / (2 * a + b) with hy
  have hy0 : 0 < y := by positivity
  have hy3 : y ≤ 1 / 3 := by
    rw [hy, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (b : ℝ) ≤ a := by exact_mod_cast hba
    linarith
  have htail : 2 / (2 * ((12 : ℕ) : ℝ) + 1) * y ^ (2 * 12 + 1) / (1 - y ^ 2) ≤ 3 / 25 * y ^ 25 := by
    have h1y : 8 / 9 ≤ 1 - y ^ 2 := by nlinarith
    rw [div_le_iff₀ (by linarith)]
    push_cast
    have : 0 ≤ y ^ 25 := by positivity
    nlinarith
  have hfl : (10 : ℝ) ^ 30 * (3 / 25 * y ^ 25) ≤
      ((3 * 10 ^ 30 * b ^ 25 / (25 * (2 * a + b) ^ 25) : ℕ) : ℝ) + 1 := by
    have hpos : 0 < 25 * (2 * a + b) ^ 25 := by positivity
    obtain ⟨-, h4⟩ := floor_div_bounds (3 * 10 ^ 30 * b ^ 25) _ hpos
    have e : (10 : ℝ) ^ 30 * (3 / 25 * y ^ 25) =
        ((3 * 10 ^ 30 * b ^ 25 : ℕ) : ℝ) / ((25 * (2 * a + b) ^ 25 : ℕ) : ℝ) := by
      have : (0 : ℝ) < 2 * a + b := by positivity
      rw [hy, div_pow]; push_cast; field_simp; norm_num
    linarith
  unfold qHi
  push_cast
  push_cast at h3
  nlinarith

structure PS where
  Llo : ℕ
  Lhi : ℕ
  Tlo : ℕ
  Thi : ℕ
  Fhi : ℕ
  m : ℕ
  Mlo : ℕ
  Mhi : ℕ
deriving DecidableEq

end TernaryGoldbach.RSBounds.SmallTotientProduct

open Filter
open scoped Topology

namespace MertensGamma

private noncomputable def lower (n : ℕ) : ℝ :=
  (harmonic n : ℝ) - Real.log n - (1 / 2) / n

private noncomputable def upper (n : ℕ) : ℝ :=
  lower n + (1 / 8) * ((1 : ℝ) / n) ^ 2

private lemma log_trapezoid (x : ℝ) (hx : 0 < x) :
    (1 / 2) / x + (1 / 2) / (x+1) - (1 / 8) * ((1/x)^2 - (1/(x+1))^2) ≤
      Real.log ((x+1)/x) ∧
    Real.log ((x+1)/x) ≤ (1 / 2) / x + (1 / 2) / (x+1) := by
  let t : ℝ := 1/(2*x+1)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hs : t < 1 := (div_lt_one (by positivity : 0 < 2*x+1)).2 (by linarith)
  have hid : (1+t)/(1-t) = (x+1)/x := by dsimp [t]; field_simp; ring
  have hL := Real.sum_range_le_log_div ht hs 1
  have hU := Real.log_div_le_sum_range_add ht hs 0
  rw [hid] at hL hU
  simp at hL hU
  have htpos : 0 < 1-t^2 := by nlinarith [mul_pos (sub_pos.mpr hs) (show 0 < 1+t by linarith)]
  have hid' : t/(1-t^2) = ((1/2)/x + (1/2)/(x+1))/2 := by
    apply (div_eq_iff htpos.ne').2
    dsimp [t]
    field_simp
    ring
  constructor
  · apply le_trans (b := 2*t)
    · dsimp [t]
      field_simp
      nlinarith
    · linarith only [hL]
  · rw [hid'] at hU
    linarith only [hU]

private lemma steps (n : ℕ) (hn : 0 < n) :
    lower n ≤ lower (n+1) ∧ upper (n+1) ≤ upper n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨h₁,h₂⟩ := log_trapezoid (n : ℝ) hnR
  rw [Real.log_div (by positivity) hnR.ne'] at h₁ h₂
  simp only [upper, lower, harmonic_succ]
  push_cast
  simp only [div_eq_mul_inv] at h₁ h₂ ⊢
  constructor <;> linarith only [h₁,h₂]

theorem enclosure (N : ℕ) (hN : 0 < N) :
    lower N ≤ Real.eulerMascheroniConstant ∧ Real.eulerMascheroniConstant ≤ upper N := by
  have hL : Tendsto lower atTop (𝓝 Real.eulerMascheroniConstant) := by
    change Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n - (1/2)/n) _ _
    simpa only [sub_zero] using Real.tendsto_harmonic_sub_log.sub
      (tendsto_const_div_atTop_nhds_zero_nat (1/2 : ℝ))
  have hU : Tendsto upper atTop (𝓝 Real.eulerMascheroniConstant) := by
    change Tendsto (fun n : ℕ => lower n + 1/8*((1:ℝ)/n)^2) _ _
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using hL.add ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2 |>.const_mul (1/8 : ℝ))
  have hb : ∀ k, N ≤ k → lower N ≤ lower k ∧ upper k ≤ upper N := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact ⟨le_rfl,le_rfl⟩
    | succ k hk ih =>
      have h := steps k (hN.trans_le hk)
      exact ⟨ih.1.trans h.1, h.2.trans ih.2⟩
  constructor
  · apply ge_of_tendsto hL
    filter_upwards [eventually_ge_atTop N] with k hk using (hb k hk).1
  · apply le_of_tendsto hU
    filter_upwards [eventually_ge_atTop N] with k hk using (hb k hk).2

theorem gamma_under : Real.eulerMascheroniConstant ≤ (0.578 : ℝ) := by
  have hu := (enclosure 16 (by decide)).2
  have hh : harmonic 16 = (2436559 / 720720 : ℚ) := by decide +kernel
  have hl : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 4 using 1 <;> norm_num
  norm_num only [upper, lower, Nat.cast_ofNat] at hu
  rw [hh, hl] at hu
  norm_num at hu
  linarith only [hu, Real.log_two_gt_d9]

end MertensGamma
end

-- RSBounds.BacklundZetaBoundary
section
open Complex MeasureTheory Set Filter
open scoped Topology

namespace TernaryGoldbach.RSBounds.BacklundZetaBoundary

theorem zeta_norm_le_real_axis {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ ‖riemannZeta (s.re : ℂ)‖ := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs, CenterNumerics.norm_zeta_eq_tsum_rpow hs]
  have hsum := Complex.summable_one_div_nat_cpow.mpr hs
  calc
    _ ≤ ∑' n : ℕ, ‖1 / (n : ℂ) ^ s‖ := norm_tsum_le_tsum_norm hsum.norm
    _ = ∑' n : ℕ, (n : ℝ) ^ (-s.re) := by
      congr 1
      funext n
      rw [one_div, ← Complex.cpow_neg,
        Complex.norm_natCast_cpow_of_re_ne_zero _ (by simp; linarith), Complex.neg_re]

theorem zeta_norm_le_three {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖riemannZeta s‖ ≤ 3 := by
  have hs1 : 1 < s.re := by linarith
  have hh := CenterNumerics.zeta_tail_upper hs1 (N := 1) (by norm_num)
  norm_num [CenterNumerics.rpowSum] at hh
  have hden : (0 : ℝ) < s.re - 1 := by linarith
  have hdiv : 1 / (s.re - 1) ≤ 2 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  simp only [one_div] at hdiv
  exact (zeta_norm_le_real_axis hs1).trans (by linarith)

theorem nat_cpow_tendsto_zero {a : ℂ} (ha : a.re < 0) :
    Tendsto (fun n : ℕ => (n : ℂ) ^ a) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [Complex.norm_natCast_cpow_of_re_ne_zero _ ha.ne]
  simpa only [neg_neg, Function.comp_def] using
    (tendsto_rpow_neg_atTop (by linarith : 0 < -a.re)).comp
      tendsto_natCast_atTop_atTop

theorem zeta_second_order_remainder {s : ℂ} (hs : 0 < s.re) (hs_one : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - (∑ k ∈ Finset.range N, (k : ℂ) ^ (-s))
        - (N : ℂ) ^ (-s) / 2
        - (N : ℂ) ^ (1 - s) / (s - 1)
        - s * (N : ℂ) ^ (-s - 1) / 12‖ ≤
      (1 / 12 : ℝ) * ∫ x in Ioi (N : ℝ),
        ‖s * (s + 1) * (x : ℂ) ^ (-s - 2)‖ := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hs0 : -s ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp only [Complex.neg_re, Complex.zero_re] at this
    linarith
  have hs1 : -s - 1 ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.zero_re] at this
    linarith
  have hf (x : ℝ) (hx : (N : ℝ) ≤ x) :
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s))
        (-s * (x : ℂ) ^ (-s - 1)) x :=
    hasDerivAt_ofReal_cpow_const (hN0.trans_le hx).ne' hs0
  have hg (x : ℝ) (hx : (N : ℝ) ≤ x) :
      HasDerivAt (fun y : ℝ => -s * (y : ℂ) ^ (-s - 1))
        (s * (s + 1) * (x : ℂ) ^ (-s - 2)) x := by
    convert (hasDerivAt_ofReal_cpow_const (hN0.trans_le hx).ne' hs1).const_mul (-s)
      using 1
    rw [show -s - 1 - 1 = -s - 2 by ring]
    ring
  have hc : ContinuousOn (fun x : ℝ => s * (s + 1) * (x : ℂ) ^ (-s - 2))
      (Ici (N : ℝ)) := by
    intro x hx
    exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr (hN0.trans_le hx).ne'))).continuousWithinAt
  have hf0 := nat_cpow_tendsto_zero (a := -s) (by simp; linarith)
  have hg0 := (nat_cpow_tendsto_zero (a := -s - 1) (by simp; linarith)).const_mul (-s)
  simp only [mul_zero] at hg0
  have hhi := (integrableOn_Ioi_cpow_of_lt (a := -s - 2) (by simp; linarith)
    hN0).const_mul (s * (s + 1))
  have hh := BacklundEulerMaclaurin.regularized_infinite_error_le N hf hg hc
    (BacklundZetaRegularization.regularized_sum_tendsto hs hs_one hN) hf0 hg0 hhi
  push_cast at hh
  refine Eq.trans_le ?_ hh
  refine congrArg (fun z : ℂ => ‖z‖) ?_
  ring

theorem zeta_second_order_remainder_explicit_of_pos {s : ℂ} (hs : 0 < s.re)
    (hs_one : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - (∑ k ∈ Finset.range N, (k : ℂ) ^ (-s))
        - (N : ℂ) ^ (-s) / 2 - (N : ℂ) ^ (1 - s) / (s - 1)
        - s * (N : ℂ) ^ (-s - 1) / 12‖ ≤
      ‖s * (s + 1)‖ / (12 * (s.re + 1)) * (N : ℝ) ^ (-s.re - 1) := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hIH : (∫ x in Ioi (N : ℝ), ‖s * (s + 1) * (x : ℂ) ^ (-s - 2)‖) =
      ‖s * (s + 1)‖ * ((N : ℝ) ^ (-s.re - 1) / (s.re + 1)) := by
    calc
      _ = ∫ x in Ioi (N : ℝ), ‖s * (s + 1)‖ * x ^ (-s.re - 2) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        dsimp only
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hN0.trans hx)]
        simp
      _ = ‖s * (s + 1)‖ * ((N : ℝ) ^ (-s.re - 1) / (s.re + 1)) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hN0]
        congr 1
        rw [show -s.re - 2 + 1 = -s.re - 1 by ring,
          show -s.re - 1 = -(s.re + 1) by ring, div_neg, neg_div, neg_neg]
  have hh := zeta_second_order_remainder hs hs_one hN
  rw [hIH] at hh
  convert hh using 1
  field_simp

theorem zeta_second_order_remainder_explicit {s : ℂ} (hs : 1 < s.re)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - (∑ k ∈ Finset.range N, (k : ℂ) ^ (-s))
        - (N : ℂ) ^ (-s) / 2 - (N : ℂ) ^ (1 - s) / (s - 1)
        - s * (N : ℂ) ^ (-s - 1) / 12‖ ≤
      ‖s * (s + 1)‖ / (12 * (s.re + 1)) * (N : ℝ) ^ (-s.re - 1) :=
  zeta_second_order_remainder_explicit_of_pos (by linarith)
    (by intro he; simp [he] at hs) hN

theorem partial_sum_norm_le_harmonic {s : ℂ} (hs : 1 ≤ s.re) (n : ℕ) :
    ‖∑ k ∈ Finset.range (n + 1), (k : ℂ) ^ (-s)‖ ≤ (harmonic n : ℚ) := by
  have hs0 : -s ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp at this
    linarith
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, Complex.zero_cpow hs0, add_zero]
  calc
    _ ≤ ∑ k ∈ Finset.range n, ‖((k + 1 : ℕ) : ℂ) ^ (-s)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Complex.norm_natCast_cpow_of_pos (Nat.succ_pos k), Complex.neg_re]
      have hk1 : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast (Nat.succ_pos k)
      have hh := Real.rpow_le_rpow_of_exponent_le hk1 (show -s.re ≤ -1 by linarith)
      simpa only [Real.rpow_neg_one, Nat.cast_add, Nat.cast_one, Nat.cast_succ, one_div] using hh
    _ = (harmonic n : ℚ) := by simp [harmonic, Rat.cast_sum, one_div]

theorem zeta_norm_le_euler_maclaurin {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    ‖riemannZeta s‖ ≤ (harmonic n : ℚ) + ((n + 1 : ℕ) : ℝ) ^ (-s.re) / 2
      + ((n + 1 : ℕ) : ℝ) ^ (1 - s.re) / ‖s - 1‖
      + ‖s‖ * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1) / 12
      + ‖s * (s + 1)‖ / (12 * (s.re + 1)) * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1) := by
  let N : ℕ := n + 1
  let P : ℂ := ∑ k ∈ Finset.range N, (k : ℂ) ^ (-s)
  let a : ℂ := (N : ℂ) ^ (-s) / 2
  let b : ℂ := (N : ℂ) ^ (1 - s) / (s - 1)
  let c : ℂ := s * (N : ℂ) ^ (-s - 1) / 12
  let R : ℂ := riemannZeta s - P - a - b - c
  have hN0 : 0 < N := Nat.succ_pos n
  have hR := zeta_second_order_remainder_explicit hs (N := N) (by omega)
  have hP := partial_sum_norm_le_harmonic hs.le n
  have ha : ‖a‖ = (N : ℝ) ^ (-s.re) / 2 := by
    simp [a, norm_div, Complex.norm_natCast_cpow_of_pos hN0]
  have hb : ‖b‖ = (N : ℝ) ^ (1 - s.re) / ‖s - 1‖ := by
    simp [b, norm_div, Complex.norm_natCast_cpow_of_pos hN0]
  have hc : ‖c‖ = ‖s‖ * (N : ℝ) ^ (-s.re - 1) / 12 := by
    simp [c, norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos hN0]
  have htri : ‖riemannZeta s‖ ≤ ‖P‖ + ‖a‖ + ‖b‖ + ‖c‖ + ‖R‖ := by
    calc
      _ = ‖P + a + b + c + R‖ := by congr 1; dsimp [R]; ring
      _ ≤ ‖P + a + b + c‖ + ‖R‖ := norm_add_le _ _
      _ ≤ (‖P + a + b‖ + ‖c‖) + ‖R‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖P + a‖ + ‖b‖) + ‖c‖) + ‖R‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖P‖ + ‖a‖ + ‖b‖) + ‖c‖) + ‖R‖ := by gcongr; exact norm_add_le _ _
  rw [ha, hb, hc] at htri
  exact htri.trans (by dsimp [R, P, a, b, c, N] at *; linarith)

theorem harmonic_half_endpoint_le (n : ℕ) :
    (harmonic n : ℚ) + 1 / (2 * ((n + 1 : ℕ) : ℝ)) ≤
      Real.log ((n + 1 : ℕ) : ℝ) + Real.eulerMascheroniConstant := by
  have hh := (TernaryGoldbach.Prelim.RamPf.harm_bounds
    (n := n + 1) (by omega)).2
  rw [harmonic_succ] at hh
  push_cast at hh ⊢
  have hden : (n : ℝ) + 1 ≠ 0 := by positivity
  have he : ((n : ℝ) + 1)⁻¹ = 2 * (1 / (2 * ((n : ℝ) + 1))) := by
    field_simp
  rw [he] at hh
  linarith

theorem zeta_norm_le_log_cutoff {s : ℂ} (hs : 1 < s.re) (ht : 0 < s.im) (n : ℕ) :
    ‖riemannZeta s‖ ≤ Real.log ((n + 1 : ℕ) : ℝ) + Real.eulerMascheroniConstant
      + 1 / s.im + ‖s‖ / (12 * (((n + 1 : ℕ) : ℝ) ^ 2))
      + ‖s * (s + 1)‖ / (24 * (((n + 1 : ℕ) : ℝ) ^ 2)) := by
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  have hN1 : 1 ≤ N := by dsimp [N]; exact_mod_cast Nat.succ_pos n
  have hN0 : 0 < N := by linarith
  have hp1 : N ^ (-s.re) ≤ 1 / N := by
    have hh := Real.rpow_le_rpow_of_exponent_le hN1 (show -s.re ≤ -1 by linarith)
    simpa only [Real.rpow_neg_one, one_div] using hh
  have hp0 : N ^ (1 - s.re) ≤ 1 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hN1 (show 1 - s.re ≤ 0 by linarith)
    simpa only [Real.rpow_zero] using hh
  have hp2 : N ^ (-s.re - 1) ≤ 1 / N ^ 2 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hN1 (show -s.re - 1 ≤ -2 by linarith)
    simpa only [Real.rpow_neg hN0.le, Real.rpow_two, one_div] using hh
  have hden : s.im ≤ ‖s - 1‖ := by
    simpa using (le_abs_self (s - 1).im).trans (Complex.abs_im_le_norm (s - 1))
  have hden0 : 0 < ‖s - 1‖ := ht.trans_le hden
  have hb : N ^ (1 - s.re) / ‖s - 1‖ ≤ 1 / s.im := by
    exact (div_le_div_of_nonneg_right hp0 hden0.le).trans
      (one_div_le_one_div_of_le ht hden)
  have hc : ‖s‖ * N ^ (-s.re - 1) / 12 ≤ ‖s‖ / (12 * N ^ 2) := by
    calc
      _ ≤ ‖s‖ * (1 / N ^ 2) / 12 := by gcongr
      _ = _ := by ring
  have hd0 : ‖s * (s + 1)‖ / (12 * (s.re + 1)) ≤ ‖s * (s + 1)‖ / 24 := by
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) (by linarith)
  have hd : ‖s * (s + 1)‖ / (12 * (s.re + 1)) * N ^ (-s.re - 1) ≤
      ‖s * (s + 1)‖ / (24 * N ^ 2) := by
    calc
      _ ≤ (‖s * (s + 1)‖ / 24) * (1 / N ^ 2) :=
        mul_le_mul hd0 hp2 (Real.rpow_nonneg hN0.le _) (by positivity)
      _ = _ := by ring
  have ha : (harmonic n : ℚ) + N ^ (-s.re) / 2 ≤
      Real.log N + Real.eulerMascheroniConstant := by
    calc
      _ ≤ (harmonic n : ℚ) + (1 / N) / 2 := by gcongr
      _ = (harmonic n : ℚ) + 1 / (2 * N) := by ring
      _ ≤ _ := harmonic_half_endpoint_le n
  have hz := zeta_norm_le_euler_maclaurin hs n
  change ‖riemannZeta s‖ ≤ _ at hz
  change ‖riemannZeta s‖ ≤ Real.log N + Real.eulerMascheroniConstant +
    1 / s.im + ‖s‖ / (12 * N ^ 2) + ‖s * (s + 1)‖ / (24 * N ^ 2)
  dsimp only [N] at ha hb hc hd
  linarith

theorem norm_height_bounds {s : ℂ} (hs0 : 1 ≤ s.re) (hs1 : s.re ≤ 3 / 2)
    (ht : 50 ≤ s.im) :
    ‖s‖ ≤ 1.001 * s.im ∧ ‖s * (s + 1)‖ ≤ 1.004 * s.im ^ 2 := by
  have ht0 : 0 ≤ s.im := by linarith
  have ht2 : 2500 ≤ s.im ^ 2 := by nlinarith
  have hs2 : s.re ^ 2 ≤ 9 / 4 := by nlinarith
  have hs3 : (s.re + 1) ^ 2 ≤ 25 / 4 := by nlinarith
  have hn1 := Complex.sq_norm_sub_sq_im s
  have hn2 := Complex.sq_norm_sub_sq_im (s + 1)
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero] at hn2
  have h1 : ‖s‖ ≤ 1.001 * s.im := by nlinarith [norm_nonneg s]
  have h2 : ‖s + 1‖ ≤ 1.002 * s.im := by nlinarith [norm_nonneg (s + 1)]
  refine ⟨h1, ?_⟩
  rw [norm_mul]
  have hp := mul_le_mul h1 h2 (norm_nonneg (s + 1)) (by positivity)
  nlinarith

theorem zeta_norm_le_log_sub_of_le_three_halves {s : ℂ}
    (hs : 1 < s.re) (hs1 : s.re ≤ 3 / 2) (ht : 50 ≤ s.im) :
    ‖riemannZeta s‖ ≤ Real.log s.im - 0.048 := by
  let n : ℕ := ⌊s.im / 3⌋₊
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  have ht0 : 0 < s.im := by linarith
  have hNlo : s.im / 3 ≤ N := by
    dsimp [N, n]
    simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (s.im / 3)).le
  have hNhi : N ≤ s.im / 3 + 1 := by
    dsimp [N, n]
    push_cast
    have hh := Nat.floor_le (show (0 : ℝ) ≤ s.im / 3 by positivity)
    linarith
  have hN0 : 0 < N := by linarith
  have hN2 : s.im ^ 2 ≤ 9 * N ^ 2 := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ s.im / 3) hNlo 2
    nlinarith
  have hlog : Real.log N ≤ Real.log s.im - Real.log 3 + 3 / s.im := by
    have he : s.im / 3 + 1 = (s.im / 3) * (1 + 3 / s.im) := by field_simp
    calc
      _ ≤ Real.log (s.im / 3 + 1) := Real.log_le_log hN0 hNhi
      _ = Real.log s.im - Real.log 3 + Real.log (1 + 3 / s.im) := by
        rw [he, Real.log_mul (by positivity) (by positivity), Real.log_div ht0.ne' (by norm_num)]
      _ ≤ Real.log s.im - Real.log 3 + 3 / s.im := by
        have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 3 / s.im)
        linarith
  obtain ⟨h1, h2⟩ := norm_height_bounds hs.le hs1 ht
  have hc : ‖s‖ / (12 * N ^ 2) ≤ 0.75075 / s.im := by
    apply (div_le_div_iff₀ (by positivity) ht0).mpr
    have hh := mul_le_mul_of_nonneg_right h1 ht0.le
    nlinarith
  have hd : ‖s * (s + 1)‖ / (24 * N ^ 2) ≤ 0.3765 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hcorr : (4 + 0.75075) / s.im ≤ 0.095015 := by
    apply (div_le_iff₀ ht0).mpr
    nlinarith
  have hγ : Real.eulerMascheroniConstant ≤ 0.578 := by
    exact MertensGamma.gamma_under
  have hlog3 : 1.098 ≤ Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hz := zeta_norm_le_log_cutoff hs ht0 n
  change ‖riemannZeta s‖ ≤ Real.log N + Real.eulerMascheroniConstant +
    1 / s.im + ‖s‖ / (12 * N ^ 2) + ‖s * (s + 1)‖ / (24 * N ^ 2) at hz
  have he : 3 / s.im + 1 / s.im + 0.75075 / s.im = (4 + 0.75075) / s.im := by ring
  linarith

theorem zeta_norm_le_log_sub_on_one {s : ℂ} (hs : s.re = 1) (ht : 50 ≤ s.im) :
    ‖riemannZeta s‖ ≤ Real.log s.im - 0.048 := by
  let δ : ℕ → ℝ := fun n => (1 / ((n : ℝ) + 1)) / 2
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [zero_div, δ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
  have hδpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδle (n : ℕ) : δ n ≤ 1 / 2 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith : (1 : ℝ) ≤ (n : ℝ) + 1)
    dsimp [δ]
    norm_num at hh
    simp only [one_div]
    linarith
  have hzseq : Tendsto (fun n : ℕ => s + (δ n : ℂ)) atTop (𝓝 s) := by
    simpa using (Complex.continuous_ofReal.tendsto 0 |>.comp hδ).const_add s
  have hsne : s ≠ 1 := by
    intro he
    have := congrArg Complex.im he
    simp at this
    linarith
  have hζlim := ((differentiableAt_riemannZeta hsne).continuousAt.tendsto.comp hzseq).norm
  apply le_of_tendsto hζlim
  filter_upwards with n
  have hh := zeta_norm_le_log_sub_of_le_three_halves (s := s + (δ n : ℂ))
    (by simp [hs]; exact hδpos n) (by simp [hs]; linarith [hδle n]) (by simpa using ht)
  simpa using hh

theorem zeta_norm_le_log_sub {s : ℂ} (hs : 1 ≤ s.re) (ht : 50 ≤ s.im) :
    ‖riemannZeta s‖ ≤ Real.log s.im - 0.048 := by
  rcases eq_or_lt_of_le hs with he | hs'
  · exact zeta_norm_le_log_sub_on_one he.symm ht
  by_cases hs1 : s.re ≤ 3 / 2
  · exact zeta_norm_le_log_sub_of_le_three_halves hs' hs1 ht
  have hz := zeta_norm_le_three (le_of_not_ge hs1)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 27)
    (by linarith : (27 : ℝ) ≤ s.im)
  have he : Real.log (27 : ℝ) = 3 * Real.log 3 := by
    rw [show (27 : ℝ) = 3 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [he] at hlog
  linarith [Real.log_three_gt_d9]

end TernaryGoldbach.RSBounds.BacklundZetaBoundary
end

-- RSBounds.BacklundGammaModulusAbsorption
section
namespace TernaryGoldbach.RSBounds.BacklundGammaModulus

theorem log_le_half {t : ℝ} (ht : 0 < t) : Real.log t ≤ t / 2 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < t / 2 by positivity)
  rw [Real.log_div ht.ne' (by norm_num)] at h
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

theorem exp_mul_log_saving_lt {t : ℝ} (ht : 50 ≤ t) :
    Real.exp (5 / (2 * t ^ 2)) * (Real.log t - 6 / 125) < Real.log t := by
  have ht0 : 0 < t := by linarith
  have ht2 : 0 < t ^ 2 := by positivity
  have hl0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hq : 5 / (2 * t ^ 2) * Real.log t < 6 / 125 := by
    have h := mul_le_mul_of_nonneg_left (log_le_half ht0)
      (by positivity : 0 ≤ 5 / (2 * t ^ 2))
    have he : 5 / (2 * t ^ 2) * (t / 2) = 5 / (4 * t) := by
      field_simp
      ring
    rw [he] at h
    have hb : 5 / (4 * t) < 6 / 125 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    exact h.trans_lt hb
  have hexp := Real.add_one_le_exp (-(5 / (2 * t ^ 2)))
  have hprod := mul_le_mul_of_nonneg_right hexp hl0
  have hs : Real.log t - 6 / 125 <
      Real.exp (-(5 / (2 * t ^ 2))) * Real.log t := by
    nlinarith
  have hm := mul_lt_mul_of_pos_left hs (Real.exp_pos (5 / (2 * t ^ 2)))
  have he : Real.exp (5 / (2 * t ^ 2)) *
      (Real.exp (-(5 / (2 * t ^ 2))) * Real.log t) = Real.log t := by
    rw [← mul_assoc, ← Real.exp_add]
    simp
  rwa [he] at hm

end TernaryGoldbach.RSBounds.BacklundGammaModulus
end

-- RSBounds.BacklundLeftZetaBoundary
section
open Complex Real

namespace TernaryGoldbach.RSBounds.BacklundLeftZetaBoundary

theorem norm_zeta_left_strip_lt {σ t : ℝ}
    (hσ : -(1 / 2 : ℝ) ≤ σ) (hσ' : σ ≤ 0) (ht : 50 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ <
      (t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.log t := by
  have ht0 : 0 < t := by linarith
  have hζ : ‖riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖ ≤ Real.log t - 6 / 125 := by
    have h := BacklundZetaBoundary.zeta_norm_le_log_sub
      (s := (((1 - σ : ℝ) : ℂ) + t * I))
      (by simp; linarith) (by simpa using ht)
    convert h using 1
    norm_num
  have hP : 0 < (t / (2 * Real.pi)) ^ (1 / 2 - σ) :=
    Real.rpow_pos_of_pos (by positivity) _
  calc
    _ ≤ (t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.exp (5 / (2 * t ^ 2)) *
        ‖riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖ :=
      BacklundFunctionalMultiplier.norm_zeta_reflected_strip_le hσ (by linarith) ht
    _ ≤ (t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.exp (5 / (2 * t ^ 2)) *
        (Real.log t - 6 / 125) :=
      mul_le_mul_of_nonneg_left hζ (by positivity)
    _ = (t / (2 * Real.pi)) ^ (1 / 2 - σ) *
        (Real.exp (5 / (2 * t ^ 2)) * (Real.log t - 6 / 125)) := by ring
    _ < _ := mul_lt_mul_of_pos_left
      (BacklundGammaModulus.exp_mul_log_saving_lt ht) hP

end TernaryGoldbach.RSBounds.BacklundLeftZetaBoundary
end

-- RSBounds.BacklundCircleMajorantGeometry
section
open Complex Real Set

namespace TernaryGoldbach.RSBounds.BacklundCircleMajorant

theorem height_bounds {T t : ℝ} (hT : 100 ≤ T) (ht : T - radius ≤ t) :
    50 ≤ t := by
  dsimp [radius] at ht
  linarith

theorem log_height_pos {T : ℝ} (hT : 100 ≤ T) : 0 < Real.log (T + radius) :=
  Real.log_pos (by dsimp [radius]; linarith)

theorem heightLog_nonneg {T : ℝ} (hT : 100 ≤ T) : 0 ≤ heightLog T := by
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
    (show (3 : ℝ) ≤ T + radius by dsimp [radius]; linarith)
  exact Real.log_nonneg (by linarith [Real.log_three_gt_d9])

theorem powerLog_nonneg {T : ℝ} (hT : 100 ≤ T) : 0 ≤ powerLog T := by
  apply Real.log_nonneg
  rw [le_div_iff₀ (by positivity : 0 < 2 * Real.pi)]
  dsimp [radius]
  nlinarith [Real.pi_lt_four]

theorem strip_den_pos {T : ℝ} (hT : 100 ≤ T) : 0 < (T - radius) ^ 2 - 4 := by
  have hl : 50 ≤ T - radius := height_bounds hT le_rfl
  nlinarith

theorem stripLog_nonneg {T : ℝ} (hT : 100 ≤ T) : 0 ≤ stripLog T := by
  apply Real.log_nonneg
  rw [le_div_iff₀ (strip_den_pos hT)]
  linarith

theorem scalar_nonneg {H L V σ : ℝ} (hH : 0 ≤ H) (hL : 0 ≤ L) (hV : 0 ≤ V) :
    0 ≤ scalar H L V σ := by
  unfold scalar
  split_ifs with hσ hstrip
  · exact BacklundRightArc.logZeta_nonneg (by linarith)
  · positivity
  · positivity

theorem majorant_nonneg {T : ℝ} (hT : 100 ≤ T) (z : ℂ) : 0 ≤ majorant T z :=
  scalar_nonneg (heightLog_nonneg hT) (powerLog_nonneg hT) (stripLog_nonneg hT)

theorem exp_heightLog {T : ℝ} (hT : 100 ≤ T) :
    Real.exp (heightLog T) = Real.log (T + radius) := Real.exp_log (log_height_pos hT)

theorem exp_stripLog {T : ℝ} (hT : 100 ≤ T) :
    Real.exp (stripLog T) = (T - radius) ^ 2 / ((T - radius) ^ 2 - 4) := by
  have hl : 0 < T - radius := by have := height_bounds hT (t := T - radius) le_rfl; linarith
  apply Real.exp_log
  exact div_pos (sq_pos_of_pos hl) (strip_den_pos hT)

theorem exp_height_power {T e : ℝ} (hT : 100 ≤ T) :
    Real.exp (heightLog T + e * powerLog T) =
      Real.log (T + radius) * ((T + radius) / (2 * Real.pi)) ^ e := by
  have hupper : 0 < T + radius := by dsimp [radius]; linarith
  have hbase : 0 < (T + radius) / (2 * Real.pi) := by positivity
  rw [Real.exp_add, exp_heightLog hT, Real.rpow_def_of_pos hbase]
  congr 2
  unfold powerLog
  ring

theorem exp_height_power_strip {T e : ℝ} (hT : 100 ≤ T) :
    Real.exp (heightLog T + e * powerLog T + stripLog T) =
      Real.log (T + radius) * ((T + radius) / (2 * Real.pi)) ^ e *
        ((T - radius) ^ 2 / ((T - radius) ^ 2 - 4)) := by
  rw [Real.exp_add, exp_height_power hT, exp_stripLog hT]

theorem scalar_right {H L V σ : ℝ} (hσ : 5 / 4 ≤ σ) :
    scalar H L V σ = Real.log ‖riemannZeta (σ : ℂ)‖ := by simp [scalar, hσ]

theorem scalar_one {H L V σ : ℝ} (hσ : 1 ≤ σ) (hσ' : σ < 5 / 4) :
    scalar H L V σ = H := by
  simp [scalar, not_le.mpr hσ', max_eq_right (by linarith : 1 - σ ≤ 0),
    max_eq_right (by linarith : -σ ≤ 0), not_lt.mpr hσ]

theorem scalar_middle {H L V σ : ℝ} (hσ : 0 ≤ σ) (hσ' : σ < 1) :
    scalar H L V σ = H + ((1 - σ) / 2) * L + V := by
  simp [scalar, show ¬5 / 4 ≤ σ by linarith, hσ, hσ',
    max_eq_left (by linarith : 0 ≤ 1 - σ)]
  ring

theorem scalar_left {H L V σ : ℝ} (hσ : σ < 0) :
    scalar H L V σ = H + (1 / 2 - σ) * L := by
  simp [scalar, show ¬5 / 4 ≤ σ by linarith, not_le.mpr hσ,
    max_eq_left (by linarith : 0 ≤ 1 - σ), max_eq_left (by linarith : 0 ≤ -σ)]
  ring

theorem power_log_mono {T t e : ℝ} (hT : 100 ≤ T)
    (ht0 : T - radius ≤ t) (ht1 : t ≤ T + radius) (he : 0 ≤ e) :
    (t / (2 * Real.pi)) ^ e * Real.log t ≤
      ((T + radius) / (2 * Real.pi)) ^ e * Real.log (T + radius) := by
  have ht50 := height_bounds hT ht0
  have hT0 : 0 < T := by linarith
  have hupper : 0 < T + radius := by dsimp [radius]; linarith
  have hbase : 0 ≤ t / (2 * Real.pi) := by positivity
  apply mul_le_mul
  · exact Real.rpow_le_rpow hbase (div_le_div_of_nonneg_right ht1 (by positivity)) he
  · exact Real.log_le_log (by linarith) ht1
  · exact Real.log_nonneg (by linarith)
  · positivity

theorem strip_ratio_antitone {T t : ℝ} (hT : 100 ≤ T) (ht : T - radius ≤ t) :
    t ^ 2 / (t ^ 2 - 4) ≤ (T - radius) ^ 2 / ((T - radius) ^ 2 - 4) := by
  have hl := height_bounds hT (t := T - radius) le_rfl
  have ht50 := height_bounds hT ht
  have hd : 0 < t ^ 2 - 4 := by nlinarith
  have hs : (T - radius) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by linarith) ht 2
  rw [div_le_div_iff₀ hd (strip_den_pos hT)]
  nlinarith

theorem sphere_coordinates {z : ℂ}
    (hz : z ∈ Metric.sphere (5 / 4 : ℂ) radius) :
    -(1 / 2 : ℝ) ≤ z.re ∧ |z.im| ≤ radius := by
  have hn : ‖z - (5 / 4 : ℂ)‖ = radius := by
    simpa only [Metric.mem_sphere, dist_eq_norm] using hz
  have hr := Complex.abs_re_le_norm (z - (5 / 4 : ℂ))
  have hi := Complex.abs_im_le_norm (z - (5 / 4 : ℂ))
  rw [hn] at hr hi
  norm_num [Complex.sub_re, Complex.sub_im] at hr hi
  refine ⟨?_, hi⟩
  have hlo := (abs_le.mp hr).1
  dsimp [radius] at hlo
  linarith

theorem sphere_heights {T : ℝ} {z : ℂ}
    (hz : z ∈ Metric.sphere (5 / 4 : ℂ) radius) :
    (T - radius ≤ T + z.im ∧ T + z.im ≤ T + radius) ∧
      (T - radius ≤ T - z.im ∧ T - z.im ≤ T + radius) := by
  rcases abs_le.mp (sphere_coordinates hz).2 with ⟨hlo, hhi⟩
  constructor <;> constructor <;> linarith

end TernaryGoldbach.RSBounds.BacklundCircleMajorant
end

-- RSBounds.BacklundHalfStrip
section
open Complex Real Set Filter Metric
open scoped Topology

namespace TernaryGoldbach.RSBounds.BacklundHalfStrip

private theorem gaussian_top_tendsto {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    Tendsto (fun t : ℝ => Real.exp (ε * (1 - t ^ 2)) * (C * t ^ 2))
      atTop (𝓝 0) := by
  have hp : Tendsto (fun t : ℝ => ε * t ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).const_mul_atTop hε
  have hh := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hp).const_mul
    (C * Real.exp ε / ε)
  convert hh using 1
  · funext t
    simp only [Function.comp_apply, pow_one]
    rw [show ε * (1 - t ^ 2) = ε + -(ε * t ^ 2) by ring, Real.exp_add]
    field_simp
  · ring

theorem norm_le_one {f : ℂ → ℂ} {a : ℝ} (ha : 1 ≤ a)
    (hd : DiffContOnCl ℂ f (Ioo (0 : ℝ) 1 ×ℂ Ioi a))
    (hleft : ∀ z : ℂ, z.re = 0 → a ≤ z.im → ‖f z‖ ≤ 1)
    (hright : ∀ z : ℂ, z.re = 1 → a ≤ z.im → ‖f z‖ ≤ 1)
    (hbottom : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → z.im = a → ‖f z‖ ≤ 1)
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      0 ≤ z.re → z.re ≤ 1 → a ≤ z.im → ‖f z‖ ≤ C * z.im ^ 2)
    {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) (hza : a ≤ z.im) :
    ‖f z‖ ≤ 1 := by
  obtain ⟨C, hC, hgrowth⟩ := hgrowth
  suffices h : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ‖Complex.exp ((ε : ℂ) * z ^ 2) * f z‖ ≤ 1 by
    apply le_of_tendsto _ h
    convert (((Complex.continuous_ofReal.mul continuous_const).cexp.mul
      continuous_const).norm.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds using 1 <;> simp
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : 0 < ε := hε
  let g : ℂ → ℂ := fun w => Complex.exp ((ε : ℂ) * w ^ 2) * f w
  have he (w : ℂ) : ‖g w‖ =
      Real.exp (ε * (w.re ^ 2 - w.im ^ 2)) * ‖f w‖ := by
    simp only [g, norm_mul, Complex.norm_exp]
    congr 2
    simp [pow_two]
  obtain ⟨R, hRz, hRa, hR⟩ : ∃ R : ℝ, z.im < R ∧ a < R ∧
      Real.exp (ε * (1 - R ^ 2)) * (C * R ^ 2) ≤ 1 := by
    have hevent := (gaussian_top_tendsto hε0 C).eventually
      (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    exact ((eventually_gt_atTop z.im).and
      ((eventually_gt_atTop a).and hevent)).exists
  have hgd : DiffContOnCl ℂ g (Ioo (0 : ℝ) 1 ×ℂ Ioo a R) := by
    have hgexp : Differentiable ℂ (fun w : ℂ => Complex.exp ((ε : ℂ) * w ^ 2)) :=
      ((differentiable_id.pow 2).const_mul _).cexp
    simpa only [smul_eq_mul] using (hgexp.diffContOnCl.smul hd).mono
      (fun w (hw : w ∈ Ioo (0 : ℝ) 1 ×ℂ Ioo a R) => (⟨hw.1, hw.2.1⟩ : w ∈ Ioo (0 : ℝ) 1 ×ℂ Ioi a))
  have hweight (w : ℂ) (hw0 : 0 ≤ w.re) (hw1 : w.re ≤ 1) (hwa : a ≤ w.im) :
      Real.exp (ε * (w.re ^ 2 - w.im ^ 2)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    apply mul_nonpos_of_nonneg_of_nonpos hε0.le
    have hr2 : w.re ^ 2 ≤ 1 := pow_le_one₀ hw0 hw1
    nlinarith
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    ((isBounded_Ioo (0 : ℝ) 1).reProdIm (isBounded_Ioo a R)) hgd
  · intro w hw
    rw [frontier_reProdIm, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1),
      closure_Ioo hRa.ne, frontier_Ioo (by norm_num : (0 : ℝ) < 1),
      frontier_Ioo hRa] at hw
    simp only [mem_union, mem_reProdIm, mem_insert_iff, mem_singleton_iff] at hw
    rcases hw with ⟨⟨hw0, hw1⟩, hwa | hwR⟩ | ⟨hw0 | hw1, ⟨hwa, _⟩⟩
    · rw [he]
      exact mul_le_one₀ (hweight w hw0 hw1 hwa.ge) (norm_nonneg _)
        (hbottom w hw0 hw1 hwa)
    · rw [he, hwR]
      have hr2 : w.re ^ 2 ≤ 1 := pow_le_one₀ hw0 hw1
      calc
        _ ≤ Real.exp (ε * (1 - R ^ 2)) * (C * R ^ 2) := by
          apply mul_le_mul
          · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hε0.le)
          · simpa [hwR] using hgrowth w hw0 hw1 (by linarith)
          · exact norm_nonneg _
          · positivity
        _ ≤ 1 := hR
    · rw [he]
      exact mul_le_one₀ (hweight w hw0.ge (by linarith) hwa) (norm_nonneg _)
        (hleft w hw0 hwa)
    · rw [he]
      exact mul_le_one₀ (hweight w (by linarith) hw1.le hwa) (norm_nonneg _)
        (hright w hw1 hwa)
  · rw [closure_reProdIm, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), closure_Ioo hRa.ne]
    exact ⟨⟨hz0, hz1⟩, ⟨hza, hRz.le⟩⟩

end TernaryGoldbach.RSBounds.BacklundHalfStrip
end

-- RSBounds.BacklundStripNormalizer
section
open Complex Real MeasureTheory Set
open scoped Topology

namespace TernaryGoldbach.RSBounds.BacklundStripNormalizer

noncomputable def exponent (s : ℂ) : ℂ :=
  (s - 1) / 2 * Complex.log (-s * I / (2 * Real.pi)) - s / 2

noncomputable def normalizedZeta (s : ℂ) : ℂ :=
  riemannZeta s * Complex.exp (exponent s) / Complex.log (-s * I)

theorem arg_eq_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    z.arg = Real.arctan (z.im / z.re) := by
  rw [← Complex.tan_arg]
  exact (Real.arctan_tan
    (Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz))
    (Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz))).symm

theorem arctan_cubic_lower {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 3 ≤ Real.arctan x := by
  have hf : Continuous (fun u : ℝ => 1 - u ^ 2) := by fun_prop
  have hg : Continuous (fun u : ℝ => 1 / (1 + u ^ 2)) := by
    have h1 : ∀ u : ℝ, 1 + u ^ 2 ≠ 0 := fun u => by positivity
    have h2 : Continuous (fun u : ℝ => 1 + u ^ 2) := by fun_prop
    exact Continuous.div (f := fun _ : ℝ => (1 : ℝ)) (g := fun u : ℝ => 1 + u ^ 2)
      continuous_const h2 h1
  have hi := intervalIntegral.integral_mono_on (μ := volume) hx
    (hf.intervalIntegrable 0 x) (hg.intervalIntegrable 0 x)
    (fun u _ => by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + u ^ 2)).mpr
      nlinarith [sq_nonneg (u ^ 2)])
  rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
    ((show Continuous (fun u : ℝ => u ^ 2) by fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_const, integral_pow, integral_one_div_one_add_sq] at hi
  norm_num at hi ⊢
  exact hi

noncomputable def correctionExponent (σ t : ℝ) : ℝ :=
  (σ - 1) / 4 * Real.log (1 + (σ / t) ^ 2) +
    t / 2 * Real.arctan (σ / t) - σ / 2

theorem correctionExponent_nonpos {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 0 < t) : correctionExponent σ t ≤ 0 := by
  have hlog : 0 ≤ Real.log (1 + (σ / t) ^ 2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg (σ / t)])
  have ha := Real.arctan_le_self (div_nonneg hσ0 ht.le)
  have hm := mul_le_mul_of_nonneg_left ha (show 0 ≤ t / 2 by positivity)
  have he : t / 2 * (σ / t) = σ / 2 := by field_simp
  rw [he] at hm
  unfold correctionExponent
  have hn : (σ - 1) / 4 * Real.log (1 + (σ / t) ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog
  linarith

theorem correctionExponent_lower {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 0 < t) : -(1 / t ^ 2) ≤ correctionExponent σ t := by
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have hu : 0 ≤ σ / t := div_nonneg hσ0 ht.le
  have hl : Real.log (1 + (σ / t) ^ 2) ≤ (σ / t) ^ 2 := by
    simpa using Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + (σ / t) ^ 2)
  have ha := arctan_cubic_lower hu
  have hm := mul_le_mul_of_nonneg_left ha (show 0 ≤ t / 2 by positivity)
  have hml := mul_le_mul_of_nonpos_left hl (show (σ - 1) / 4 ≤ 0 by linarith)
  have hs2 : σ ^ 2 ≤ 1 := pow_le_one₀ hσ0 hσ1
  have hs3 : σ ^ 3 ≤ 1 := pow_le_one₀ hσ0 hσ1
  have he : (σ - 1) / 4 * (σ / t) ^ 2 +
      t / 2 * (σ / t - (σ / t) ^ 3 / 3) - σ / 2 =
      (σ ^ 3 / 12 - σ ^ 2 / 4) / t ^ 2 := by
    field_simp
    ring
  have hlo : (σ ^ 3 / 12 - σ ^ 2 / 4) / t ^ 2 ≤ correctionExponent σ t := by
    rw [← he]
    unfold correctionExponent
    linarith
  refine le_trans ?_ hlo
  rw [← neg_div, div_le_div_iff_of_pos_right ht2]
  nlinarith [pow_nonneg hσ0 3]

noncomputable def logModulus (σ t : ℝ) : ℝ :=
  Real.sqrt ((Real.log t + Real.log (1 + (σ / t) ^ 2) / 2) ^ 2 +
    (Real.arctan (σ / t)) ^ 2)

noncomputable def correction (σ t : ℝ) : ℝ :=
  Real.exp (correctionExponent σ t) * Real.log t / logModulus σ t

theorem log_le_logModulus {σ t : ℝ} (ht : 1 ≤ t) :
    Real.log t ≤ logModulus σ t := by
  have ht0 : 0 < t := by linarith
  have hL : 0 ≤ Real.log t := Real.log_nonneg ht
  have hl : 0 ≤ Real.log (1 + (σ / t) ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg (σ / t)])
  unfold logModulus
  apply (Real.le_sqrt (by positivity) (by positivity)).mpr
  nlinarith [sq_nonneg (Real.arctan (σ / t))]

theorem correction_le_one {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 1 < t) : correction σ t ≤ 1 := by
  have hL : 0 < Real.log t := Real.log_pos ht
  have hD := log_le_logModulus (σ := σ) ht.le
  have he : Real.exp (correctionExponent σ t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (correctionExponent_nonpos hσ0 hσ1 (by linarith))
  unfold correction
  apply (div_le_one (hL.trans_le hD)).mpr
  exact (mul_le_of_le_one_left hL.le he).trans hD

theorem one_le_log_of_three_le {t : ℝ} (ht : 3 ≤ t) : 1 ≤ Real.log t := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) ht
  linarith [Real.log_three_gt_d9]

theorem logModulus_upper {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 3 ≤ t) : logModulus σ t ≤ Real.log t + 1 / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hL := one_le_log_of_three_le ht
  have hd : 0 ≤ 1 / t ^ 2 := by positivity
  have hu2 : (σ / t) ^ 2 ≤ 1 / t ^ 2 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_right (pow_le_one₀ hσ0 hσ1) (sq_nonneg t)
  have hl0 : 0 ≤ Real.log (1 + (σ / t) ^ 2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg (σ / t)])
  have hl1 : Real.log (1 + (σ / t) ^ 2) ≤ 1 / t ^ 2 := by
    have h := Real.log_le_sub_one_of_pos
      (by positivity : (0 : ℝ) < 1 + (σ / t) ^ 2)
    linarith
  have ha0 : 0 ≤ Real.arctan (σ / t) := Real.arctan_nonneg.mpr (by positivity)
  have ha1 : Real.arctan (σ / t) ≤ 1 / t :=
    (Real.arctan_le_self (by positivity)).trans
      (div_le_div_of_nonneg_right hσ1 ht0.le)
  have ha2 : Real.arctan (σ / t) ^ 2 ≤ 1 / t ^ 2 := by
    have hsq : Real.arctan (σ / t) ^ 2 ≤ (1 / t) ^ 2 := by nlinarith
    simpa [div_pow] using hsq
  have hlsq : (Real.log t + Real.log (1 + (σ / t) ^ 2) / 2) ^ 2 ≤
      (Real.log t + (1 / t ^ 2) / 2) ^ 2 := by gcongr
  unfold logModulus
  apply Real.sqrt_le_iff.mpr
  constructor
  · linarith
  · have hm := mul_nonneg (sub_nonneg.mpr hL) hd
    nlinarith

theorem correction_lower {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 3 ≤ t) : 1 - 4 / t ^ 2 ≤ correction σ t := by
  have ht0 : 0 < t := by linarith
  have hL := one_le_log_of_three_le ht
  have hD := log_le_logModulus (σ := σ) (by linarith : 1 ≤ t)
  have hDpos : 0 < logModulus σ t := by linarith
  have hd : 0 ≤ 1 / t ^ 2 := by positivity
  have hdsmall : 1 / t ^ 2 ≤ 1 / 9 := by
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 9)
    nlinarith
  have hcoef : 0 ≤ 1 - 4 / t ^ 2 := by
    rw [show 4 / t ^ 2 = 4 * (1 / t ^ 2) by ring]
    linarith
  have hDupper : logModulus σ t ≤ Real.log t * (1 + 1 / t ^ 2) := by
    refine (logModulus_upper hσ0 hσ1 ht).trans ?_
    have hm := mul_nonneg (sub_nonneg.mpr hL) hd
    nlinarith
  have he : 1 - 1 / t ^ 2 ≤ Real.exp (correctionExponent σ t) := by
    have he0 := correctionExponent_lower hσ0 hσ1 ht0
    have he1 := Real.add_one_le_exp (correctionExponent σ t)
    linarith
  unfold correction
  apply (le_div_iff₀ hDpos).mpr
  calc
    _ ≤ (1 - 4 / t ^ 2) * (Real.log t * (1 + 1 / t ^ 2)) :=
      mul_le_mul_of_nonneg_left hDupper hcoef
    _ ≤ (1 - 1 / t ^ 2) * Real.log t := by
      have h1 := mul_nonneg (show 0 ≤ Real.log t by linarith) hd
      have h2 := mul_nonneg (show 0 ≤ Real.log t by linarith) (sq_nonneg (1 / t ^ 2))
      linear_combination 2 * h1 + 4 * h2
    _ ≤ Real.exp (correctionExponent σ t) * Real.log t :=
      mul_le_mul_of_nonneg_right he (by linarith)

theorem log_norm_horizontal {σ t : ℝ} (ht : 0 < t) :
    Real.log ‖(t : ℂ) - σ * I‖ =
      Real.log t + Real.log (1 + (σ / t) ^ 2) / 2 := by
  have hq : 0 < 1 + (σ / t) ^ 2 := by positivity
  have hn : ‖(t : ℂ) - σ * I‖ = t * Real.sqrt (1 + (σ / t) ^ 2) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hq.le, Complex.sq_norm, Complex.normSq_apply]
    simp
    field_simp
  rw [hn, Real.log_mul ht.ne' (Real.sqrt_pos.mpr hq).ne', Real.log_sqrt hq.le]

theorem log_horizontal {σ t : ℝ} (ht : 0 < t) :
    Complex.log ((t : ℂ) - σ * I) =
      ((Real.log t + Real.log (1 + (σ / t) ^ 2) / 2 : ℝ) : ℂ) -
        (Real.arctan (σ / t) : ℂ) * I := by
  apply Complex.ext
  · simpa [Complex.log_re] using log_norm_horizontal (σ := σ) ht
  · rw [Complex.log_im, arg_eq_arctan_of_re_pos (by simpa using ht)]
    simp [neg_div, Real.arctan_neg]

theorem norm_log_horizontal {σ t : ℝ} (ht : 0 < t) :
    ‖Complex.log ((t : ℂ) - σ * I)‖ = logModulus σ t := by
  rw [log_horizontal ht, Complex.norm_def]
  simp [logModulus, Complex.normSq_apply, pow_two]

theorem analyticAt_normalizedZeta {s : ℂ} (hs : 1 < s.im) :
    AnalyticAt ℂ normalizedZeta s := by
  have ht : 0 < s.im := by linarith
  have hp : s ≠ 1 := by
    intro he
    have hh := congrArg Complex.im he
    simp at hh
    linarith
  have hw : -s * I ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa using ht
  have hw' : -s * I / (2 * Real.pi) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    rw [show (2 : ℂ) * Real.pi = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      Complex.div_ofReal_re]
    simpa using div_pos ht (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)
  have hnorm : 1 < ‖-s * I‖ := by
    have h := Complex.re_le_norm (-s * I)
    have hr : (-s * I).re = s.im := by simp
    rw [hr] at h
    linarith
  have hn : Complex.log (-s * I) ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    rw [Complex.log_re, Complex.zero_re] at h
    have hp := Real.log_pos hnorm
    linarith
  have hd : AnalyticAt ℂ (fun z : ℂ => Complex.log (-z * I)) s :=
    (analyticAt_id.neg.mul analyticAt_const).clog hw
  have hc : AnalyticAt ℂ (fun z : ℂ => Complex.log (-z * I / (2 * Real.pi))) s :=
    ((analyticAt_id.neg.mul analyticAt_const).div_const).clog hw'
  have he : AnalyticAt ℂ exponent s := by
    unfold exponent
    exact (((analyticAt_id.sub analyticAt_const).div_const).mul hc).sub
      analyticAt_id.div_const
  have hz : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s (by simpa using hp)
  exact (hz.mul he.cexp).div hd hn

theorem exponent_re_horizontal {σ t : ℝ} (ht : 0 < t) :
    (exponent ((σ : ℂ) + t * I)).re =
      (σ - 1) / 2 * Real.log (t / (2 * Real.pi)) + correctionExponent σ t := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hw : (t : ℂ) - σ * I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    exact ht.ne' hh
  have hrot : -((σ : ℂ) + t * I) * I = (t : ℂ) - σ * I := by
    ring_nf
    simp
  have hdiv : ((t : ℂ) - σ * I) / (2 * Real.pi) =
      ((t : ℂ) - σ * I) * (((2 * Real.pi)⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  have hl : Complex.log (((t : ℂ) - σ * I) / (2 * Real.pi)) =
      -(Real.log (2 * Real.pi) : ℂ) +
      ((Real.log t + Real.log (1 + (σ / t) ^ 2) / 2 : ℝ) : ℂ) -
        (Real.arctan (σ / t) : ℂ) * I := by
    rw [hdiv, Complex.log_mul_ofReal _ (inv_pos.mpr hp) _ hw,
      Real.log_inv, log_horizontal ht]
    push_cast
    ring
  unfold exponent
  rw [hrot, hl, Real.log_div ht.ne' hp.ne']
  simp [correctionExponent, Complex.mul_re, Complex.mul_im, div_ofNat_re, div_ofNat_im]
  ring

theorem norm_normalizedZeta_horizontal {σ t : ℝ} (ht : 1 < t) :
    ‖normalizedZeta ((σ : ℂ) + t * I)‖ =
      (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
        ‖riemannZeta ((σ : ℂ) + t * I)‖ / Real.log t * correction σ t := by
  have ht0 : 0 < t := by linarith
  have hp : 0 < t / (2 * Real.pi) := by positivity
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hD : logModulus σ t ≠ 0 := ne_of_gt
    ((Real.log_pos ht).trans_le (log_le_logModulus ht.le))
  have hrot : -((σ : ℂ) + t * I) * I = (t : ℂ) - σ * I := by
    ring_nf
    simp
  rw [normalizedZeta, norm_div, norm_mul, Complex.norm_exp,
    exponent_re_horizontal ht0, Real.exp_add, hrot, norm_log_horizontal ht0]
  rw [Real.rpow_def_of_pos hp]
  unfold correction
  field_simp

theorem zeta_norm_le_of_normalized_le {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 3 ≤ t) (hφ : ‖normalizedZeta ((σ : ℂ) + t * I)‖ ≤ 1) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
      t ^ 2 / (t ^ 2 - 4) * (t / (2 * Real.pi)) ^ ((1 - σ) / 2) * Real.log t := by
  have ht0 : 0 < t := by linarith
  have ht2 : 0 < t ^ 2 - 4 := by nlinarith
  have hp : 0 < t / (2 * Real.pi) := by positivity
  have hL : 0 < Real.log t := Real.log_pos (by linarith)
  have hA : 0 < (t / (2 * Real.pi)) ^ ((σ - 1) / 2) := Real.rpow_pos_of_pos hp _
  have hq0 : 0 < 1 - 4 / t ^ 2 := by
    apply sub_pos.mpr
    apply (div_lt_one (sq_pos_of_pos ht0)).mpr
    nlinarith
  have hq := correction_lower hσ0 hσ1 ht
  rw [norm_normalizedZeta_horizontal (by linarith : 1 < t)] at hφ
  have hprod : (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
      ‖riemannZeta ((σ : ℂ) + t * I)‖ / Real.log t * (1 - 4 / t ^ 2) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hq (by positivity)).trans hφ
  have hab : (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
      (t / (2 * Real.pi)) ^ ((1 - σ) / 2) = 1 := by
    rw [← Real.rpow_add hp, show (σ - 1) / 2 + (1 - σ) / 2 = 0 by ring,
      Real.rpow_zero]
  have htarget : (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
      (t ^ 2 / (t ^ 2 - 4) * (t / (2 * Real.pi)) ^ ((1 - σ) / 2) * Real.log t) /
        Real.log t * (1 - 4 / t ^ 2) = 1 := by
    have he : 1 - 4 / t ^ 2 = (t ^ 2 - 4) / t ^ 2 := by field_simp
    rw [he]
    field_simp
    nlinarith [hab]
  have hm : 0 < (t / (2 * Real.pi)) ^ ((σ - 1) / 2) / Real.log t *
      (1 - 4 / t ^ 2) := by positivity
  apply (mul_le_mul_iff_right₀ hm).mp
  convert hprod.trans_eq htarget.symm using 1 <;> ring

end TernaryGoldbach.RSBounds.BacklundStripNormalizer
end

-- RSBounds.BacklundBottomCertificates
section
open Complex Real Finset

namespace TernaryGoldbach.RSBounds.BacklundBottomCertificates
open TernaryGoldbach.Prelim.LogWalk

def logLo : ℕ → ℕ
  | 0 => 0
  | n + 1 => if n = 0 then 0 else logLo n + incrLo n

def logHi : ℕ → ℕ
  | 0 => 0
  | n + 1 => if n = 0 then 0 else logHi n + incrHi n

theorem log_bounds (n : ℕ) (hn : 1 ≤ n) :
    (logLo n : ℝ) ≤ 10 ^ 30 * Real.log n ∧
      10 ^ 30 * Real.log n ≤ (logHi n : ℝ) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      simp [logLo, logHi]
    · have hn1 : 1 ≤ n := by omega
      obtain ⟨hl, hu⟩ := ih hn1
      obtain ⟨hil, hiu⟩ := incr_bounds hn1
      have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hlog : Real.log (n + 1 : ℕ) = Real.log n + Real.log (1 + (n : ℝ)⁻¹) := by
        rw [← Real.log_mul hnR.ne' (by positivity)]
        congr 1
        push_cast
        field_simp
      simp only [Nat.cast_add, Nat.cast_one] at hlog
      simp only [logLo, logHi, if_neg hn0, Nat.cast_add, Nat.cast_one]
      rw [hlog]
      constructor <;> linarith

def piLo : ℚ := 314159265358979323846 / 10 ^ 20
def piHi : ℚ := 314159265358979323847 / 10 ^ 20

def angleCheck (n m : ℕ) (q : ℚ) : Bool := decide
  (-(1 / 100000 : ℚ) ≤ 50 * (logLo n : ℚ) / 10 ^ 30 - q - m * piHi / 2 ∧
    50 * (logHi n : ℚ) / 10 ^ 30 - q - m * piLo / 2 ≤ 1 / 100000)

theorem angleCheck_sound {n m : ℕ} {q : ℚ} (hn : 1 ≤ n)
    (hc : angleCheck n m q = true) :
    |50 * Real.log n - ((q : ℝ) + m * Real.pi / 2)| ≤ 1 / 100000 := by
  have hc' : -(1 / 100000 : ℚ) ≤ 50 * (logLo n : ℚ) / 10 ^ 30 - q - m * piHi / 2 ∧
      50 * (logHi n : ℚ) / 10 ^ 30 - q - m * piLo / 2 ≤ 1 / 100000 :=
    of_decide_eq_true hc
  have hlo := Rat.cast_mono (K := ℝ) hc'.1
  have hhi := Rat.cast_mono (K := ℝ) hc'.2
  push_cast at hlo hhi
  obtain ⟨hl, hu⟩ := log_bounds n hn
  have hpiL : (piLo : ℝ) ≤ Real.pi := by
    norm_num [piLo]
    linarith [Real.pi_gt_d20]
  have hpiU : Real.pi ≤ (piHi : ℝ) := by
    norm_num [piHi]
    linarith [Real.pi_lt_d20]
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hml := mul_le_mul_of_nonneg_left hpiL hm0
  have hmu := mul_le_mul_of_nonneg_left hpiU hm0
  rw [abs_le]
  constructor <;> linarith

noncomputable def taylor (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range 8, ((x : ℂ) * I) ^ k / k.factorial

def cosPoly (x : ℚ) : ℚ := 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720
def sinPoly (x : ℚ) : ℚ := x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040

theorem taylor_eq (q : ℚ) :
    taylor (q : ℝ) = (cosPoly q : ℂ) + (sinPoly q : ℂ) * I := by
  unfold taylor cosPoly sinPoly
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  push_cast
  ring_nf
  simp
  ring

theorem exp_taylor_bound {x : ℝ} (hx : |x| ≤ 1) :
    ‖Complex.exp ((x : ℂ) * I) - taylor x‖ ≤ 1 / 30000 := by
  have hnorm : ‖(x : ℂ) * I‖ ≤ 1 := by simpa using hx
  have h := Complex.exp_bound hnorm (by norm_num : (0 : ℕ) < 8)
  have hp : |x| ^ 8 ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
  norm_num [Nat.factorial] at h
  unfold taylor
  nlinarith

def cosRot (q : ℚ) (m : ℕ) : ℚ :=
  if m % 4 = 0 then cosPoly q else if m % 4 = 1 then -sinPoly q
  else if m % 4 = 2 then -cosPoly q else sinPoly q

def sinRot (q : ℚ) (m : ℕ) : ℚ :=
  if m % 4 = 0 then sinPoly q else if m % 4 = 1 then cosPoly q
  else if m % 4 = 2 then -sinPoly q else -cosPoly q

theorem taylor_mul_I_pow (q : ℚ) (m : ℕ) :
    taylor (q : ℝ) * I ^ m = (cosRot q m : ℂ) + (sinRot q m : ℂ) * I := by
  rw [taylor_eq, Complex.I_pow_eq_pow_mod]
  have hm : m % 4 < 4 := Nat.mod_lt m (by decide)
  interval_cases h : m % 4 <;> simp [cosRot, sinRot, h] <;> ring_nf <;> simp <;> ring

theorem rotated_taylor_bound {q : ℚ} (hq : |(q : ℝ)| ≤ 1) (m : ℕ) :
    ‖Complex.exp (((q : ℝ) + m * Real.pi / 2 : ℝ) * I) -
      ((cosRot q m : ℂ) + (sinRot q m : ℂ) * I)‖ ≤ 1 / 30000 := by
  rw [← taylor_mul_I_pow]
  have he : Complex.exp (((q : ℝ) + m * Real.pi / 2 : ℝ) * I) =
      Complex.exp ((q : ℂ) * I) * I ^ m := by
    push_cast
    rw [show ((q : ℂ) + m * Real.pi / 2) * I =
      (q : ℂ) * I + (m : ℂ) * (Real.pi / 2 * I) by ring,
      Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_div_two_mul_I]
  rw [he, ← sub_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one]
  exact exp_taylor_bound hq

theorem trig_approx {n m : ℕ} {q : ℚ} (hn : 1 ≤ n)
    (hc : angleCheck n m q = true) (hq : |(q : ℝ)| ≤ 1) :
    |Real.cos (50 * Real.log n) - (cosRot q m : ℝ)| ≤ 1 / 10000 ∧
      |Real.sin (50 * Real.log n) - (sinRot q m : ℝ)| ≤ 1 / 10000 := by
  have ha := angleCheck_sound hn hc
  have ht := rotated_taylor_bound hq m
  have hr := (Complex.abs_re_le_norm _).trans ht
  have hi := (Complex.abs_im_le_norm _).trans ht
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_I_re, Complex.ratCast_re,
    Complex.ratCast_im, neg_zero, add_zero, Complex.exp_ofReal_mul_I_re] at hr
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_I_im, Complex.ratCast_re,
    Complex.ratCast_im, zero_add, Complex.exp_ofReal_mul_I_im] at hi
  have hcr := (Real.abs_cos_sub_cos_le (50 * Real.log n)
    ((q : ℝ) + m * Real.pi / 2)).trans ha
  have hsi := (Real.abs_sin_sub_sin_le (50 * Real.log n)
    ((q : ℝ) + m * Real.pi / 2)).trans ha
  constructor
  · have h := abs_add_le (Real.cos (50 * Real.log n) -
      Real.cos ((q : ℝ) + m * Real.pi / 2))
      (Real.cos ((q : ℝ) + m * Real.pi / 2) - (cosRot q m : ℝ))
    rw [sub_add_sub_cancel] at h
    linarith
  · have h := abs_add_le (Real.sin (50 * Real.log n) -
      Real.sin ((q : ℝ) + m * Real.pi / 2))
      (Real.sin ((q : ℝ) + m * Real.pi / 2) - (sinRot q m : ℝ))
    rw [sub_add_sub_cancel] at h
    linarith

end TernaryGoldbach.RSBounds.BacklundBottomCertificates
end

-- RSBounds.BacklundBottomData
section
namespace TernaryGoldbach.RSBounds.BacklundBottomCertificates

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def quarterTurns : ℕ → ℕ
  | 1 => 0
  | 2 => 22
  | 3 => 35
  | 4 => 44
  | 5 => 51
  | 6 => 57
  | 7 => 62
  | 8 => 66
  | 9 => 70
  | 10 => 73
  | 11 => 76
  | 12 => 79
  | 13 => 82
  | 14 => 84
  | 15 => 86
  | 16 => 88
  | 17 => 90
  | 18 => 92
  | 19 => 94
  | 20 => 95
  | _ => 0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def reducedAngle : ℕ → ℚ
  | 1 => 0
  | 2 => (312 / 3125)
  | 3 => (-47257 / 1000000)
  | 4 => (624 / 3125)
  | 5 => (361283 / 1000000)
  | 6 => (52583 / 1000000)
  | 7 => (-18773 / 200000)
  | 8 => (936 / 3125)
  | 9 => (-47257 / 500000)
  | 10 => (461123 / 1000000)
  | 11 => (514243 / 1000000)
  | 12 => (152423 / 1000000)
  | 13 => (-557831 / 1000000)
  | 14 => (239 / 40000)
  | 15 => (157013 / 500000)
  | 16 => (399359 / 1000000)
  | 17 => (144499 / 500000)
  | 18 => (2663 / 500000)
  | 19 => (-216453 / 500000)
  | 20 => (560963 / 1000000)
  | _ => 0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def amplitudeNumerator : ℕ → ℕ
  | 1 => 1000000
  | 2 => 707107
  | 3 => 577351
  | 4 => 500000
  | 5 => 447214
  | 6 => 408249
  | 7 => 377965
  | 8 => 353554
  | 9 => 333334
  | 10 => 316228
  | 11 => 301512
  | 12 => 288676
  | 13 => 277351
  | 14 => 267262
  | 15 => 258199
  | 16 => 250000
  | 17 => 242536
  | 18 => 235703
  | 19 => 229416
  | 20 => 223607
  | _ => 0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def rowCheck (n : ℕ) : Bool :=
  angleCheck n (quarterTurns n) (reducedAngle n) &&
    decide (|reducedAngle n| ≤ 1 ∧ 10 ^ 12 ≤ (amplitudeNumerator n) ^ 2 * n)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem all_rows_checked : (List.range' 1 20).all rowCheck = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def amplitudeLo (n : ℕ) : ℚ := 1 / n
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def amplitudeHi (n : ℕ) : ℚ := (amplitudeNumerator n : ℚ) / 10 ^ 6

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def realLo (n : ℕ) : ℚ := min
  (amplitudeLo n * (cosRot (reducedAngle n) (quarterTurns n) - 1 / 10000))
  (amplitudeHi n * (cosRot (reducedAngle n) (quarterTurns n) - 1 / 10000))
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def realHi (n : ℕ) : ℚ := max
  (amplitudeLo n * (cosRot (reducedAngle n) (quarterTurns n) + 1 / 10000))
  (amplitudeHi n * (cosRot (reducedAngle n) (quarterTurns n) + 1 / 10000))
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def sineLo (n : ℕ) : ℚ := min
  (amplitudeLo n * (sinRot (reducedAngle n) (quarterTurns n) - 1 / 10000))
  (amplitudeHi n * (sinRot (reducedAngle n) (quarterTurns n) - 1 / 10000))
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def sineHi (n : ℕ) : ℚ := max
  (amplitudeLo n * (sinRot (reducedAngle n) (quarterTurns n) + 1 / 10000))
  (amplitudeHi n * (sinRot (reducedAngle n) (quarterTurns n) + 1 / 10000))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def weight (n : ℕ) : ℚ := if n = 20 then 1 / 2 else 1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem aggregate_checked :
    -(127 / 100 : ℚ) ≤ ∑ n ∈ Finset.Icc 1 20, weight n * realLo n ∧
    (∑ n ∈ Finset.Icc 1 20, weight n * realHi n) ≤ 159 / 100 ∧
    -(125 / 100 : ℚ) ≤ ∑ n ∈ Finset.Icc 1 20, weight n * sineLo n ∧
    (∑ n ∈ Finset.Icc 1 20, weight n * sineHi n) ≤ 125 / 100 := by decide +kernel

end TernaryGoldbach.RSBounds.BacklundBottomCertificates
end

-- RSBounds.BacklundBottomFiniteSum
section
open Complex Real Finset

namespace TernaryGoldbach.RSBounds.BacklundBottomCertificates

theorem row_checked {n : ℕ} (hn : n ∈ Finset.Icc 1 20) : rowCheck n = true := by
  obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  have hm : n ∈ List.range' 1 20 := by
    rw [List.mem_range']
    exact ⟨n - 1, by omega, by omega⟩
  exact List.all_eq_true.mp all_rows_checked n hm

theorem amplitude_bounds {n : ℕ} (hn : n ∈ Finset.Icc 1 20)
    {σ : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    (amplitudeLo n : ℝ) ≤ (n : ℝ) ^ (-σ) ∧
      (n : ℝ) ^ (-σ) ≤ (amplitudeHi n : ℝ) := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hc := row_checked hn
  simp only [rowCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hc' := hc.2
  have hu := CenterNumerics.root_upper (n := n) (p := 1) (k := 2)
    (D := 10 ^ 6) (b := amplitudeNumerator n) hn0 (by norm_num) (by norm_num)
    (by norm_num; exact hc'.2)
  constructor
  · have hh := Real.rpow_le_rpow_of_exponent_le hnR (show (-1 : ℝ) ≤ -σ by linarith)
    simpa [amplitudeLo, Real.rpow_neg_one, one_div] using hh
  · have hh := Real.rpow_le_rpow_of_exponent_le hnR (show -σ ≤ -(1 / 2 : ℝ) by linarith)
    apply hh.trans
    norm_num [amplitudeHi] at hu ⊢
    exact hu

theorem interval_product_bounds {A B C D x y : ℝ}
    (hx0 : 0 ≤ x) (hxl : A ≤ x) (hxu : x ≤ B) (hyl : C ≤ y) (hyu : y ≤ D) :
    min (A * C) (B * C) ≤ x * y ∧ x * y ≤ max (A * D) (B * D) := by
  constructor
  · apply le_trans _ (mul_le_mul_of_nonneg_left hyl hx0)
    by_cases hC : 0 ≤ C
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hxl hC)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hxu (le_of_not_ge hC))
  · apply le_trans (mul_le_mul_of_nonneg_left hyu hx0)
    by_cases hD : 0 ≤ D
    · exact (mul_le_mul_of_nonneg_right hxu hD).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_right hxl (le_of_not_ge hD)).trans (le_max_left _ _)

theorem power_components {n : ℕ} (hn : 1 ≤ n) (σ : ℝ) :
    ((n : ℂ) ^ (-((σ : ℂ) + 50 * I))).re =
      (n : ℝ) ^ (-σ) * Real.cos (50 * Real.log n) ∧
    ((n : ℂ) ^ (-((σ : ℂ) + 50 * I))).im =
      -((n : ℝ) ^ (-σ) * Real.sin (50 * Real.log n)) := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hl : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    simpa using (Complex.ofReal_log hnR.le).symm
  have he : Complex.log (n : ℂ) * (-((σ : ℂ) + 50 * I)) =
      ((-σ * Real.log n : ℝ) : ℂ) + ((-(50 * Real.log n) : ℝ) : ℂ) * I := by
    rw [hl]
    push_cast
    ring
  have hp : (n : ℂ) ^ (-((σ : ℂ) + 50 * I)) =
      Complex.exp (((-σ * Real.log n : ℝ) : ℂ) + ((-(50 * Real.log n) : ℝ) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero hnC, he]
  have hlr : (Complex.log (n : ℂ)).re = Real.log n := by rw [hl]; rfl
  have hli : (Complex.log (n : ℂ)).im = 0 := by rw [hl]; rfl
  constructor <;> rw [hp] <;>
    simp [Complex.exp_re, Complex.exp_im, Real.rpow_def_of_pos hnR, hlr, hli, mul_comm]

theorem term_rectangle {n : ℕ} (hn : n ∈ Finset.Icc 1 20)
    {σ : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    (realLo n : ℝ) ≤ ((n : ℂ) ^ (-((σ : ℂ) + 50 * I))).re ∧
      ((n : ℂ) ^ (-((σ : ℂ) + 50 * I))).re ≤ (realHi n : ℝ) ∧
    (sineLo n : ℝ) ≤ -((n : ℂ) ^ (-((σ : ℂ) + 50 * I))).im ∧
      -((n : ℂ) ^ (-((σ : ℂ) + 50 * I))).im ≤ (sineHi n : ℝ) := by
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hc := row_checked hn
  simp only [rowCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hq : |(reducedAngle n : ℝ)| ≤ 1 := by
    exact_mod_cast hc.2.1
  obtain ⟨hcos, hsin⟩ := trig_approx hn1 hc.1 hq
  rw [abs_le] at hcos hsin
  obtain ⟨ha, hb⟩ := amplitude_bounds hn hσ0 hσ1
  have hnn := Real.rpow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (-σ)
  have hR := interval_product_bounds hnn ha hb
    (show (cosRot (reducedAngle n) (quarterTurns n) : ℝ) - 1 / 10000 ≤
      Real.cos (50 * Real.log n) by linarith)
    (show Real.cos (50 * Real.log n) ≤
      (cosRot (reducedAngle n) (quarterTurns n) : ℝ) + 1 / 10000 by linarith)
  have hI := interval_product_bounds hnn ha hb
    (show (sinRot (reducedAngle n) (quarterTurns n) : ℝ) - 1 / 10000 ≤
      Real.sin (50 * Real.log n) by linarith)
    (show Real.sin (50 * Real.log n) ≤
      (sinRot (reducedAngle n) (quarterTurns n) : ℝ) + 1 / 10000 by linarith)
  obtain ⟨hr, hi⟩ := power_components hn1 σ
  rw [hr, hi, neg_neg]
  exact ⟨by simpa [realLo] using hR.1, by simpa [realHi] using hR.2,
    by simpa [sineLo] using hI.1, by simpa [sineHi] using hI.2⟩

noncomputable def finitePart (σ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 20, (weight n : ℂ) * (n : ℂ) ^ (-((σ : ℂ) + 50 * I))

theorem finitePart_rectangle {σ : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    -(127 / 100 : ℝ) ≤ (finitePart σ).re ∧ (finitePart σ).re ≤ 159 / 100 ∧
      -(125 / 100 : ℝ) ≤ -(finitePart σ).im ∧ -(finitePart σ).im ≤ 125 / 100 := by
  have hw (n : ℕ) : 0 ≤ (weight n : ℝ) := by unfold weight; split_ifs <;> norm_num
  have h1 : (∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (realLo n : ℝ)) ≤ (finitePart σ).re := by
    simp only [finitePart, Complex.re_sum, Complex.mul_re, Complex.ratCast_re,
      Complex.ratCast_im, zero_mul, sub_zero]
    exact Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left
      (term_rectangle hn hσ0 hσ1).1 (hw n)
  have h2 : (finitePart σ).re ≤ ∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (realHi n : ℝ) := by
    simp only [finitePart, Complex.re_sum, Complex.mul_re, Complex.ratCast_re,
      Complex.ratCast_im, zero_mul, sub_zero]
    exact Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left
      (term_rectangle hn hσ0 hσ1).2.1 (hw n)
  have h3 : (∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (sineLo n : ℝ)) ≤ -(finitePart σ).im := by
    simp only [finitePart, Complex.im_sum, Complex.mul_im, Complex.ratCast_re,
      Complex.ratCast_im, zero_mul, add_zero, ← Finset.sum_neg_distrib, ← mul_neg]
    exact Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left
      (term_rectangle hn hσ0 hσ1).2.2.1 (hw n)
  have h4 : -(finitePart σ).im ≤ ∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (sineHi n : ℝ) := by
    simp only [finitePart, Complex.im_sum, Complex.mul_im, Complex.ratCast_re,
      Complex.ratCast_im, zero_mul, add_zero, ← Finset.sum_neg_distrib, ← mul_neg]
    exact Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left
      (term_rectangle hn hσ0 hσ1).2.2.2 (hw n)
  have ha : -(127 / 100 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (realLo n : ℝ) := by
    have hh := Rat.cast_mono (K := ℝ) aggregate_checked.1
    push_cast at hh
    exact hh
  have hb : (∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (realHi n : ℝ)) ≤ 159 / 100 := by
    have hh := Rat.cast_mono (K := ℝ) aggregate_checked.2.1
    push_cast at hh
    exact hh
  have hc : -(125 / 100 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (sineLo n : ℝ) := by
    have hh := Rat.cast_mono (K := ℝ) aggregate_checked.2.2.1
    push_cast at hh
    exact hh
  have hd : (∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (sineHi n : ℝ)) ≤ 125 / 100 := by
    have hh := Rat.cast_mono (K := ℝ) aggregate_checked.2.2.2
    push_cast at hh
    exact hh
  exact ⟨ha.trans h1, h2.trans hb, hc.trans h3, h4.trans hd⟩

theorem finitePart_norm_le {σ : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    ‖finitePart σ‖ ≤ 2.03 := by
  obtain ⟨hlr, hur, hli, hui⟩ := finitePart_rectangle hσ0 hσ1
  have hr : (finitePart σ).re ^ 2 ≤ (1.59 : ℝ) ^ 2 := by nlinarith
  have hi : (finitePart σ).im ^ 2 ≤ (1.25 : ℝ) ^ 2 := by nlinarith
  have hn := Complex.sq_norm_sub_sq_im (finitePart σ)
  nlinarith [norm_nonneg (finitePart σ)]

theorem finitePart_eq (σ : ℝ) :
    finitePart σ = (∑ n ∈ Finset.range 20, (n : ℂ) ^ (-((σ : ℂ) + 50 * I))) +
      (20 : ℂ) ^ (-((σ : ℂ) + 50 * I)) / 2 := by
  have hs0 : -((σ : ℂ) + 50 * I) ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    norm_num at hh
  have hsets : Finset.Icc (1 : ℕ) 20 = insert 20 (Finset.Icc 1 19) := by ext n; simp; omega
  have hsets' : Finset.Icc (1 : ℕ) 19 = Finset.Ico 1 20 := by ext n; simp; omega
  have hsum : (∑ n ∈ Finset.Icc 1 19, (weight n : ℂ) *
      (n : ℂ) ^ (-((σ : ℂ) + 50 * I))) =
      ∑ n ∈ Finset.Icc (1 : ℕ) 19, (n : ℂ) ^ (-((σ : ℂ) + 50 * I)) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn20 : n ≠ 20 := by have := (Finset.mem_Icc.mp hn).2; omega
    simp [weight, hn20]
  rw [finitePart, hsets, Finset.sum_insert (by decide), hsum, hsets',
    Finset.sum_Ico_eq_sub _ (by decide)]
  simp only [Finset.sum_range_one, Nat.cast_zero, Complex.zero_cpow hs0, sub_zero]
  norm_num [weight, Finset.sum_range_one, hs0]
  ring

theorem zeta_bottom_bound {σ : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    ‖riemannZeta ((σ : ℂ) + 50 * I)‖ ≤ 3.75 := by
  let s : ℂ := (σ : ℂ) + 50 * I
  have hsr : s.re = σ := by simp [s]
  have hsi : s.im = 50 := by simp [s]
  have hs0 : 0 < s.re := by rw [hsr]; linarith
  have hs1 : s ≠ 1 := by intro he; have := congrArg Complex.im he; simp [hsi] at this
  have hn1 : ‖s‖ ≤ 50.01 := by
    have hh := Complex.sq_norm_sub_sq_im s
    rw [hsr, hsi] at hh
    nlinarith [norm_nonneg s]
  have hn2 : ‖s + 1‖ ≤ 50.04 := by
    have hh := Complex.sq_norm_sub_sq_im (s + 1)
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      hsr, hsi, add_zero] at hh
    nlinarith [norm_nonneg (s + 1)]
  have hp : ‖s * (s + 1)‖ ≤ 50.01 * 50.04 := by
    rw [norm_mul]
    exact mul_le_mul hn1 hn2 (norm_nonneg _) (by norm_num)
  have ha : (20 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 0.223607 := by
    have hh := (amplitude_bounds (n := 20) (by decide)
      (σ := 1 / 2) (by norm_num) (by norm_num)).2
    norm_num [amplitudeHi, amplitudeNumerator] at hh ⊢
    exact hh
  have hpow : (20 : ℝ) ^ (-σ - 1) ≤ 0.01118035 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 20)
      (show -σ - 1 ≤ -(1 / 2 : ℝ) + -1 by linarith)
    rw [Real.rpow_add (by norm_num), Real.rpow_neg_one] at hh
    nlinarith
  have hmainpow : (20 : ℝ) ^ (1 - σ) ≤ 4.473 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 20)
      (show 1 - σ ≤ (1 / 2 : ℝ) by linarith)
    rw [← Real.sqrt_eq_rpow] at hh
    exact hh.trans ((Real.sqrt_le_left (by norm_num)).mpr (by norm_num))
  have hd : (50 : ℝ) ≤ ‖s - 1‖ := by
    simpa [hsi] using Complex.abs_im_le_norm (s - 1)
  let a : ℂ := (20 : ℂ) ^ (1 - s) / (s - 1)
  let b : ℂ := s * (20 : ℂ) ^ (-s - 1) / 12
  have hpowNorm (z : ℂ) : ‖(20 : ℂ) ^ z‖ = (20 : ℝ) ^ z.re := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 20) z
  have hna : ‖a‖ ≤ 0.08946 := by
    have he : ‖a‖ = (20 : ℝ) ^ (1 - σ) / ‖s - 1‖ := by
      simp [a, norm_div, hpowNorm, hsr]
    rw [he]
    apply (div_le_iff₀ (by linarith : 0 < ‖s - 1‖)).mpr
    nlinarith
  have hnb : ‖b‖ ≤ 0.047 := by
    have he : ‖b‖ = ‖s‖ * (20 : ℝ) ^ (-σ - 1) / 12 := by
      simp [b, norm_div, norm_mul, hpowNorm, hsr]
    rw [he]
    have hh := mul_le_mul hn1 hpow
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 20) _) (by norm_num)
    linarith
  have hcoef : ‖s * (s + 1)‖ / (12 * (σ + 1)) ≤ (50.01 * 50.04 : ℝ) / 18 := by
    apply (div_le_div_iff₀ (by linarith : 0 < 12 * (σ + 1)) (by norm_num)).mpr
    nlinarith
  have htail : ‖s * (s + 1)‖ / (12 * (σ + 1)) * (20 : ℝ) ^ (-σ - 1) ≤ 1.555 := by
    calc
      _ ≤ ((50.01 * 50.04 : ℝ) / 18) * 0.01118035 := mul_le_mul hcoef hpow
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 20) _) (by norm_num)
      _ ≤ _ := by norm_num
  let R : ℂ := riemannZeta s - finitePart σ - a - b
  have hR : ‖R‖ ≤ 1.555 := by
    have hh := BacklundZetaBoundary.zeta_second_order_remainder_explicit_of_pos
      hs0 hs1 (N := 20) (by decide)
    norm_num only [Nat.cast_ofNat] at hh
    rw [hsr] at hh
    have he : riemannZeta s - (∑ k ∈ Finset.range 20, (k : ℂ) ^ (-s)) -
        (20 : ℂ) ^ (-s) / 2 - (20 : ℂ) ^ (1 - s) / (s - 1) -
        s * (20 : ℂ) ^ (-s - 1) / 12 = R := by
      dsimp [R, a, b]
      rw [finitePart_eq]
      dsimp [s]
      ring
    rw [he] at hh
    exact hh.trans htail
  have hH := finitePart_norm_le hσ0 hσ1
  have htri : ‖riemannZeta s‖ ≤ ‖finitePart σ‖ + ‖a‖ + ‖b‖ + ‖R‖ := by
    calc
      _ = ‖finitePart σ + a + b + R‖ := by congr 1; dsimp [R]; ring
      _ ≤ ‖finitePart σ + a + b‖ + ‖R‖ := norm_add_le _ _
      _ ≤ ‖finitePart σ + a‖ + ‖b‖ + ‖R‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖finitePart σ‖ + ‖a‖ + ‖b‖ + ‖R‖ := by gcongr; exact norm_add_le _ _
  change ‖riemannZeta s‖ ≤ 3.75
  linarith

theorem norm_zeta_height_fifty_le {σ : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    ‖riemannZeta ((σ : ℂ) + (50 : ℂ) * I)‖ ≤ 3.75 :=
  zeta_bottom_bound hσ0 hσ1

end TernaryGoldbach.RSBounds.BacklundBottomCertificates
end

-- RSBounds.BacklundStrip
section
open Complex Real Set
open scoped Topology

namespace TernaryGoldbach.RSBounds.BacklundStrip
open BacklundStripNormalizer

private theorem base_ge_one {t : ℝ} (ht : 50 ≤ t) : 1 ≤ t / (2 * Real.pi) := by
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
  linarith [Real.pi_lt_four]

private theorem norm_le_raw {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 50 ≤ t) :
    ‖normalizedZeta ((σ : ℂ) + t * I)‖ ≤
      (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
        ‖riemannZeta ((σ : ℂ) + t * I)‖ / Real.log t := by
  rw [norm_normalizedZeta_horizontal (by linarith : 1 < t)]
  have hL : 0 < Real.log t := Real.log_pos (by linarith)
  exact mul_le_of_le_one_right (by positivity)
    (correction_le_one hσ0 hσ1 (by linarith))

private theorem norm_le_zeta_div_log {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 50 ≤ t) :
    ‖normalizedZeta ((σ : ℂ) + t * I)‖ ≤
      ‖riemannZeta ((σ : ℂ) + t * I)‖ / Real.log t := by
  have hL : 0 < Real.log t := Real.log_pos (by linarith)
  have hP : (t / (2 * Real.pi)) ^ ((σ - 1) / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (base_ge_one ht) (by linarith)
  exact (norm_le_raw hσ0 hσ1 ht).trans
    (div_le_div_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) hP) hL.le)

private theorem norm_le_reflected {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2)
    (ht : 50 ≤ t) :
    ‖normalizedZeta ((σ : ℂ) + t * I)‖ ≤ Real.exp (5 / (2 * t ^ 2)) *
      ‖riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖ / Real.log t := by
  have hL : 0 < Real.log t := Real.log_pos (by linarith)
  have hp : 0 < t / (2 * Real.pi) := by positivity
  have hP : (t / (2 * Real.pi)) ^ (-σ / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (base_ge_one ht) (by linarith)
  have hab : (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
      (t / (2 * Real.pi)) ^ (1 / 2 - σ) = (t / (2 * Real.pi)) ^ (-σ / 2) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  calc
    _ ≤ (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
      ‖riemannZeta ((σ : ℂ) + t * I)‖ / Real.log t :=
        norm_le_raw hσ0 (by linarith) ht
    _ ≤ (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
      ((t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.exp (5 / (2 * t ^ 2)) *
        ‖riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖) / Real.log t := by
      gcongr
      exact BacklundFunctionalMultiplier.norm_zeta_reflected_strip_le (by linarith) hσ1 ht
    _ = (t / (2 * Real.pi)) ^ (-σ / 2) *
      (Real.exp (5 / (2 * t ^ 2)) * ‖riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖) /
        Real.log t := by rw [← hab]; ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_of_le_one_left (by positivity) hP) hL.le

private theorem norm_right_edge {t : ℝ} (ht : 50 ≤ t) :
    ‖normalizedZeta (1 + (t : ℂ) * I)‖ ≤ 1 := by
  have hL : 0 < Real.log t := Real.log_pos (by linarith)
  have hz := BacklundZetaBoundary.zeta_norm_le_log_sub
    (s := 1 + (t : ℂ) * I) (by simp) (by simpa using ht)
  have hraw := norm_le_zeta_div_log (σ := 1) (by norm_num) le_rfl ht
  simp only [Complex.ofReal_one] at hraw
  refine hraw.trans ?_
  apply (div_le_one hL).mpr
  simp only [Complex.add_im, Complex.one_im, Complex.mul_I_im, Complex.ofReal_re,
    zero_add] at hz
  linarith

private theorem norm_left_edge {t : ℝ} (ht : 50 ≤ t) :
    ‖normalizedZeta ((t : ℂ) * I)‖ ≤ 1 := by
  have hL : 0 < Real.log t := Real.log_pos (by linarith)
  have hz := BacklundZetaBoundary.zeta_norm_le_log_sub
    (s := 1 + (t : ℂ) * I) (by simp) (by simpa using ht)
  simp only [Complex.add_im, Complex.one_im, Complex.mul_I_im, Complex.ofReal_re,
    zero_add] at hz
  have hraw := norm_le_reflected (σ := 0) le_rfl (by norm_num) ht
  norm_num at hraw
  refine hraw.trans ?_
  apply (div_le_one hL).mpr
  have hb : ‖riemannZeta (1 + (t : ℂ) * I)‖ ≤ Real.log t - 6 / 125 := by
    convert hz using 1 <;> norm_num
  exact (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans
    (BacklundGammaModulus.exp_mul_log_saving_lt ht).le

private theorem bottom_budget : (3.75 : ℝ) ≤ Real.log 50 - 6 / 125 := by
  have h48 : Real.log (48 : ℝ) = 4 * Real.log 2 + Real.log 3 := by
    rw [show (48 : ℝ) = 2 ^ 4 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 48) (by norm_num : (48 : ℝ) ≤ 50)
  rw [h48] at hle
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

private theorem norm_bottom_edge {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ‖normalizedZeta ((σ : ℂ) + (50 : ℂ) * I)‖ ≤ 1 := by
  have hL : 0 < Real.log (50 : ℝ) := Real.log_pos (by norm_num)
  by_cases hh : 1 / 2 ≤ σ
  · refine (norm_le_zeta_div_log hσ0 hσ1 (by norm_num : (50 : ℝ) ≤ 50)).trans ?_
    apply (div_le_one hL).mpr
    have h := BacklundBottomCertificates.norm_zeta_height_fifty_le hh hσ1
    norm_num at h ⊢
    linarith [bottom_budget]
  · have href := BacklundBottomCertificates.norm_zeta_height_fifty_le
      (σ := 1 - σ) (by linarith) (by linarith)
    refine (norm_le_reflected hσ0 (by linarith) (by norm_num : (50 : ℝ) ≤ 50)).trans ?_
    apply (div_le_one hL).mpr
    have hbound : ‖riemannZeta (((1 - σ : ℝ) : ℂ) + (50 : ℂ) * I)‖ ≤
        Real.log 50 - 6 / 125 := href.trans bottom_budget
    exact (mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le).trans
      (BacklundGammaModulus.exp_mul_log_saving_lt (by norm_num : (50 : ℝ) ≤ 50)).le

private theorem zeta_growth_right {σ t : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 50 ≤ t) : ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤ 5 * t := by
  let s : ℂ := (σ : ℂ) + t * I
  have hs : 0 < s.re := by simp [s]; linarith
  have ht0 : 0 < t := by linarith
  have hp : s ≠ 1 := by
    intro he
    have hh := congrArg Complex.im he
    simp [s] at hh
    linarith
  have hsn : ‖s‖ ≤ 2 * t := by
    have hh := norm_add_le (σ : ℂ) ((t : ℂ) * I)
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at hh
    rw [abs_of_nonneg (by linarith : 0 ≤ σ), abs_of_pos ht0] at hh
    change ‖(σ : ℂ) + t * I‖ ≤ 2 * t
    linarith
  have hdn : t ≤ ‖s - 1‖ := by
    have hh := Complex.abs_im_le_norm (s - 1)
    simpa [s, abs_of_pos ht0] using hh
  have hdpos : 0 < ‖s - 1‖ := ht0.trans_le hdn
  have hh := TernaryGoldbach.Explicit.norm_zetaF_le hs
  rw [TernaryGoldbach.Explicit.zetaF_of_ne hp, norm_mul] at hh
  have hdiv : ‖s‖ * ‖s - 1‖ / s.re ≤ 2 * ‖s‖ * ‖s - 1‖ := by
    apply (div_le_iff₀ hs).mpr
    have hsr : 1 / 2 ≤ s.re := by simpa [s] using hσ0
    have hm := mul_nonneg (mul_nonneg (norm_nonneg s) (norm_nonneg (s - 1)))
      (show 0 ≤ 2 * s.re - 1 by linarith)
    nlinarith
  have hprod : ‖s - 1‖ * ‖riemannZeta s‖ ≤ 2 * t + 4 * t * ‖s - 1‖ := by
    have hm := mul_le_mul_of_nonneg_right hsn (norm_nonneg (s - 1))
    nlinarith
  apply (mul_le_mul_iff_right₀ hdpos).mp
  change ‖s - 1‖ * ‖riemannZeta s‖ ≤ ‖s - 1‖ * (5 * t)
  refine hprod.trans ?_
  have hm := mul_nonneg ht0.le (show 0 ≤ ‖s - 1‖ - 2 by linarith)
  nlinarith

private theorem norm_growth {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 50 ≤ t) : ‖normalizedZeta ((σ : ℂ) + t * I)‖ ≤ t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hL : 1 ≤ Real.log t := one_le_log_of_three_le (by linarith)
  have hL0 : 0 < Real.log t := by linarith
  by_cases hh : 1 / 2 ≤ σ
  · refine (norm_le_zeta_div_log hσ0 hσ1 ht).trans ?_
    have hz := zeta_growth_right hh hσ1 ht
    apply (div_le_iff₀ hL0).mpr
    have hm := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hL)
    nlinarith
  · refine (norm_le_reflected hσ0 (by linarith) ht).trans ?_
    have hz := zeta_growth_right (σ := 1 - σ) (by linarith) (by linarith) ht
    have he : Real.exp (5 / (2 * t ^ 2)) ≤ 3 := by
      apply (Real.exp_le_exp.mpr ?_).trans Real.exp_one_lt_three.le
      apply (div_le_one (by positivity : (0 : ℝ) < 2 * t ^ 2)).mpr
      nlinarith
    have hm := mul_le_mul he hz (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
    apply (div_le_iff₀ hL0).mpr
    have hmul := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hL)
    nlinarith

theorem norm_normalizedZeta_le_one {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 50 ≤ t) : ‖normalizedZeta ((σ : ℂ) + t * I)‖ ≤ 1 := by
  have hd : DiffContOnCl ℂ normalizedZeta (Ioo (0 : ℝ) 1 ×ℂ Ioi (50 : ℝ)) := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    rw [closure_reProdIm, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), closure_Ioi] at hz
    have hzim : (50 : ℝ) ≤ z.im := hz.2
    exact (analyticAt_normalizedZeta (by linarith)).differentiableAt.differentiableWithinAt
  apply BacklundHalfStrip.norm_le_one (a := 50) (by norm_num) hd
  · intro z hre hzt
    have he : z = (z.im : ℂ) * I := by apply Complex.ext <;> simp [hre]
    rw [he]
    exact norm_left_edge hzt
  · intro z hre hzt
    have he : z = 1 + (z.im : ℂ) * I := by apply Complex.ext <;> simp [hre]
    rw [he]
    exact norm_right_edge hzt
  · intro z hz0 hz1 hzt
    have he : z = (z.re : ℂ) + (50 : ℂ) * I := by apply Complex.ext <;> simp [hzt]
    rw [he]
    exact norm_bottom_edge hz0 hz1
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz0 hz1 hzt
    simpa only [Complex.re_add_im, one_mul] using norm_growth hz0 hz1 hzt
  · simpa using hσ0
  · simpa using hσ1
  · simpa using ht

theorem norm_zeta_strip_le {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 50 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
      t ^ 2 / (t ^ 2 - 4) * (t / (2 * Real.pi)) ^ ((1 - σ) / 2) * Real.log t :=
  zeta_norm_le_of_normalized_le hσ0 hσ1 (by linarith)
    (norm_normalizedZeta_le_one hσ0 hσ1 ht)

end TernaryGoldbach.RSBounds.BacklundStrip
end

-- RSBounds.BacklundCircleMajorantBounds
section
open Complex Real Set

namespace TernaryGoldbach.RSBounds.BacklundCircleMajorant

theorem zeta_norm_le_exp_scalar {T σ t : ℝ} (hT : 100 ≤ T)
    (hσ : -(1 / 2 : ℝ) ≤ σ) (ht0 : T - radius ≤ t) (ht1 : t ≤ T + radius) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
      Real.exp (scalar (heightLog T) (powerLog T) (stripLog T) σ) := by
  have ht50 := height_bounds hT ht0
  have htpos : 0 < t := by linarith
  by_cases hright : 5 / 4 ≤ σ
  · rw [scalar_right hright, Real.exp_log]
    · simpa using BacklundZetaBoundary.zeta_norm_le_real_axis
        (s := (σ : ℂ) + t * I) (by simp; linarith)
    · apply norm_pos_iff.mpr
      exact riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  have hright' : σ < 5 / 4 := lt_of_not_ge hright
  by_cases hone : 1 ≤ σ
  · rw [scalar_one hone hright', exp_heightLog hT]
    have hz := BacklundZetaBoundary.zeta_norm_le_log_sub
      (s := (σ : ℂ) + t * I) (by simpa using hone) (by simpa using ht50)
    have hl := Real.log_le_log htpos ht1
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul,
      zero_add, add_zero] at hz
    linarith
  have hone' : σ < 1 := lt_of_not_ge hone
  by_cases hzero : 0 ≤ σ
  · rw [scalar_middle hzero hone', exp_height_power_strip hT]
    have hz := BacklundStrip.norm_zeta_strip_le hzero hone'.le ht50
    have hratio := strip_ratio_antitone hT ht0
    have hpower := power_log_mono hT ht0 ht1 (show 0 ≤ (1 - σ) / 2 by linarith)
    have hp0 : 0 ≤ (t / (2 * Real.pi)) ^ ((1 - σ) / 2) * Real.log t := by
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.log_nonneg (by linarith))
    have hc0 : 0 ≤ (T - radius) ^ 2 / ((T - radius) ^ 2 - 4) := by
      exact div_nonneg (sq_nonneg _) (strip_den_pos hT).le
    have hm := mul_le_mul hratio hpower hp0 hc0
    have he : t ^ 2 / (t ^ 2 - 4) * (t / (2 * Real.pi)) ^ ((1 - σ) / 2) * Real.log t =
        (t ^ 2 / (t ^ 2 - 4)) * ((t / (2 * Real.pi)) ^ ((1 - σ) / 2) * Real.log t) := by ring
    rw [he] at hz
    exact hz.trans (by convert hm using 1; ring)
  have hzero' : σ < 0 := lt_of_not_ge hzero
  rw [scalar_left hzero', exp_height_power hT]
  have hz := BacklundLeftZetaBoundary.norm_zeta_left_strip_lt hσ hzero'.le ht50
  have hm := power_log_mono hT ht0 ht1 (show 0 ≤ 1 / 2 - σ by linarith)
  exact hz.le.trans (by simpa only [mul_comm] using hm)

theorem zeta_plus_le_exp_majorant {T : ℝ} (hT : 100 ≤ T) {z : ℂ}
    (hz : z ∈ Metric.sphere (5 / 4 : ℂ) radius) :
    ‖riemannZeta (z + T * I)‖ ≤ Real.exp (majorant T z) := by
  have hheights := (sphere_heights (T := T) hz).1
  have hh := zeta_norm_le_exp_scalar hT (sphere_coordinates hz).1 hheights.1 hheights.2
  have he : z + T * I = (z.re : ℂ) + ((T + z.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [add_comm]
  simpa only [majorant, he] using hh

theorem zeta_minus_le_exp_majorant {T : ℝ} (hT : 100 ≤ T) {z : ℂ}
    (hz : z ∈ Metric.sphere (5 / 4 : ℂ) radius) :
    ‖riemannZeta (z - T * I)‖ ≤ Real.exp (majorant T z) := by
  have hheights := (sphere_heights (T := T) hz).2
  have hh := zeta_norm_le_exp_scalar hT (sphere_coordinates hz).1 hheights.1 hheights.2
  have he : z - T * I = (starRingEnd ℂ)
      ((z.re : ℂ) + ((T - z.im : ℝ) : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [he, riemannZeta_conj, norm_conj]
  exact hh

end TernaryGoldbach.RSBounds.BacklundCircleMajorant
end

-- RSBounds.BacklundCircleSymmetry
section
open Complex Real MeasureTheory Set
open scoped Interval

namespace TernaryGoldbach.RSBounds.BacklundCircleMajorant

theorem real_circleMap (c r θ : ℝ) :
    (circleMap (c : ℂ) r θ).re = c + r * Real.cos θ := by
  simp [circleMap]

theorem circleIntegrable_re_of_upper {f : ℝ → ℝ} {c r : ℝ}
    (hi : IntervalIntegrable (fun θ => f (c + r * Real.cos θ)) volume 0 Real.pi) :
    CircleIntegrable (fun z : ℂ => f z.re) (c : ℂ) r := by
  let u : ℝ → ℝ := fun θ => f (c + r * Real.cos θ)
  change IntervalIntegrable u volume 0 Real.pi at hi
  have he : ∀ θ, u (-θ) = u θ := by intro θ; simp [u]
  have hp : Function.Periodic u (2 * Real.pi) := by intro θ; simp [u]
  have hn : IntervalIntegrable u volume (-Real.pi) 0 := by
    have h := (IntervalIntegrable.iff_comp_neg).mp hi
    simpa only [neg_zero, he] using h.symm
  have hfull : IntervalIntegrable u volume (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    convert hn.trans hi using 1
    ring
  have hi' := hp.intervalIntegrable (by positivity : 2 * Real.pi ≠ 0) hfull 0 (2 * Real.pi)
  simpa only [CircleIntegrable, real_circleMap, u] using hi'

theorem circleAverage_re_eq_upper {f : ℝ → ℝ} {c r : ℝ}
    (hi : IntervalIntegrable (fun θ => f (c + r * Real.cos θ)) volume 0 Real.pi) :
    circleAverage (fun z : ℂ => f z.re) (c : ℂ) r =
      (∫ θ in (0 : ℝ)..Real.pi, f (c + r * Real.cos θ)) / Real.pi := by
  let u : ℝ → ℝ := fun θ => f (c + r * Real.cos θ)
  change IntervalIntegrable u volume 0 Real.pi at hi
  have he : ∀ θ, u (-θ) = u θ := by intro θ; simp [u]
  have hn : IntervalIntegrable u volume (-Real.pi) 0 := by
    have h := (IntervalIntegrable.iff_comp_neg).mp hi
    simpa only [neg_zero, he] using h.symm
  have hneg : (∫ θ in -Real.pi..(0 : ℝ), u θ) = ∫ θ in (0 : ℝ)..Real.pi, u θ := by
    have h := intervalIntegral.integral_comp_neg (f := u) (a := 0) (b := Real.pi)
    simpa only [neg_zero, he] using h.symm
  rw [circleAverage_eq_integral_add (η := -Real.pi)]
  simp only [real_circleMap]
  change (2 * Real.pi)⁻¹ • (∫ θ in (0 : ℝ)..2 * Real.pi, u (θ + -Real.pi)) = _
  rw [intervalIntegral.integral_comp_add_right]
  norm_num only [zero_add, show 2 * Real.pi + -Real.pi = Real.pi by ring]
  rw [← intervalIntegral.integral_add_adjacent_intervals hn hi, hneg]
  simp only [smul_eq_mul]
  dsimp [u]
  field_simp [Real.pi_ne_zero]
  ring

end TernaryGoldbach.RSBounds.BacklundCircleMajorant
end

-- RSBounds.BacklundRightArcNumericsBase
section
open Real Complex Finset MeasureTheory
open TernaryGoldbach.RSBounds.CenterNumerics

namespace TernaryGoldbach.RSBounds.BacklundRightArc

def cosDoubleCheck (D : ℕ) (a : ℤ) : List ℤ → Bool
  | [] => true
  | b :: bs => decide (0 ≤ a ∧ b * D ≤ 2 * a ^ 2 - (D : ℤ) ^ 2) && cosDoubleCheck D b bs

def cosEnd (a : ℤ) : List ℤ → ℤ
  | [] => a
  | b :: bs => cosEnd b bs

lemma cosDoubleCheck_sound {D : ℕ} (hD : 0 < D) {a : ℤ} {θ : ℝ} {bs : List ℤ}
    (ha : (a : ℝ) / D ≤ Real.cos θ) (hc : cosDoubleCheck D a bs = true) :
    ((cosEnd a bs : ℤ) : ℝ) / D ≤ Real.cos ((2 : ℝ) ^ bs.length * θ) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  induction bs generalizing a θ with
  | nil => simpa [cosEnd] using ha
  | cons b bs ih =>
    simp only [cosDoubleCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
    have ha0 : (0 : ℝ) ≤ a := by exact_mod_cast hc.1.1
    have hb : (b : ℝ) * D ≤ 2 * (a : ℝ) ^ 2 - (D : ℝ) ^ 2 := by exact_mod_cast hc.1.2
    have hb' : (b : ℝ) / D ≤ 2 * ((a : ℝ) / D) ^ 2 - 1 := by
      apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hD0)).mp
      convert hb using 1 <;> field_simp [hD0.ne'] <;> ring
    have hnext : (b : ℝ) / D ≤ Real.cos (2 * θ) := by
      rw [Real.cos_two_mul]
      have hsq : ((a : ℝ) / D) ^ 2 ≤ Real.cos θ ^ 2 :=
        pow_le_pow_left₀ (div_nonneg ha0 hD0.le) ha 2
      linarith
    have hh := ih hnext hc.2
    simpa only [cosEnd, List.length_cons, pow_succ, mul_assoc] using hh

lemma cos_initial_lower {θ X c : ℝ} (hθ : 0 ≤ θ) (hθX : θ ≤ X)
    (hc : c ≤ 1 - X ^ 2 / 2) : c ≤ Real.cos θ := by
  have hs : θ ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hθ hθX 2
  linarith [Real.one_sub_sq_div_two_le_cos (x := θ)]

lemma sigma_sample_lower_of_cos_cert {i p : ℕ} {a : ℤ} {bs : List ℤ}
    (hlen : bs.length = 8) (hc : cosDoubleCheck 1000000000000 a bs = true)
    (hinit : (a : ℝ) / 1000000000000 ≤
      1 - ((3.141593 : ℝ) * i / 8192) ^ 2 / 2)
    (hfinal : (p : ℝ) / 64 ≤ 5 / 4 + (33 / 25) *
      ((cosEnd a bs : ℤ) : ℝ) / 1000000000000) :
    (p : ℝ) / 64 ≤ 5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * i) := by
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hθ : Real.pi * i / 8192 ≤ (3.141593 : ℝ) * i / 8192 := by
    gcongr
    exact Real.pi_lt_d6.le
  have hs := cos_initial_lower (show 0 ≤ Real.pi * i / 8192 by positivity) hθ hinit
  have he := cosDoubleCheck_sound (by norm_num : 0 < 1000000000000) hs hc
  rw [hlen, show (2 : ℝ) ^ 8 * (Real.pi * i / 8192) = Real.pi / 32 * i by ring] at he
  nlinarith

lemma logZeta_le_of_root_cert {p : ℕ} (hp : 64 < p) {bs : List ℕ}
    (hlen : bs.length = 16) (hc : rootCheck p 64 100000000 1 bs = true)
    {bTail : ℕ} (hTail : 100000000 ^ 64 ≤ bTail ^ 64 * 16 ^ (p - 64))
    {B : ℝ} (hB : 0 ≤ B)
    (hnum : ((bs.sum + 16 : ℕ) : ℝ) / 100000000 +
      ((bTail : ℝ) / 100000000) / ((p : ℝ) / 64 - 1) ≤
      ∑ i ∈ Finset.range 16, B ^ i / (i.factorial : ℝ)) :
    logZeta ((p : ℝ) / 64) ≤ B := by
  have hpR : (64 : ℝ) < p := by exact_mod_cast hp
  have hs : 1 < (p : ℝ) / 64 := by linarith
  have hpart := (rootCheck_sound (by norm_num : 0 < 1) (by norm_num : 0 < 64)
    (by norm_num : 0 < 100000000) hc).2
  rw [hlen] at hpart
  have ht := zeta_tail_upper hs (N := 16) (by norm_num)
  have hroot := root_upper (n := 16) (p := p - 64) (k := 64)
    (D := 100000000) (b := bTail) (by norm_num) (by norm_num) (by norm_num) hTail
  have he : 1 - (p : ℝ) / 64 = -((p - 64 : ℕ) : ℝ) / 64 := by
    rw [Nat.cast_sub hp.le]
    push_cast
    ring
  rw [he] at ht
  have hz : ‖riemannZeta (((p : ℝ) / 64 : ℝ) : ℂ)‖ ≤ Real.exp B := by
    refine ht.trans ((add_le_add hpart (div_le_div_of_nonneg_right hroot (by linarith))).trans ?_)
    exact hnum.trans (Real.sum_le_exp_of_nonneg hB 16)
  unfold logZeta
  have hn : 0 < ‖riemannZeta (((p : ℝ) / 64 : ℝ) : ℂ)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simpa using hs))
  simpa only [Real.log_exp] using Real.log_le_log hn hz

end TernaryGoldbach.RSBounds.BacklundRightArc
end

-- RSBounds.BacklundRightArcNumerics
section
open Finset
namespace TernaryGoldbach.RSBounds.BacklundRightArc

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def roots_0 : List ℕ := [100000000, 16928194, 5989309, 2865637, 1617667, 1013882, 683024, 485100, 358718, 273841, 214501, 171631, 139804, 115623, 96887, 82118]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem log_sample_0 : logZeta (164 / 64) ≤ (276700 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 164) (bs := roots_0) (bTail := 1313901)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_0, Finset.sum_range_succ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem sigma_sample_0 : (164 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 0) := by
  have h := sigma_sample_lower_of_cos_cert (i := 0) (p := 164)
    (a := 1000000000000) (bs := [1000000000000, 1000000000000, 1000000000000, 1000000000000, 1000000000000, 1000000000000, 1000000000000, 1000000000000])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def roots_1 : List ℕ := [100000000, 16928194, 5989309, 2865637, 1617667, 1013882, 683024, 485100, 358718, 273841, 214501, 171631, 139804, 115623, 96887, 82118]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem log_sample_1 : logZeta (164 / 64) ≤ (276700 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 164) (bs := roots_1) (bTail := 1313901)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_1, Finset.sum_range_succ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem sigma_sample_1 : (164 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 1) := by
  have h := sigma_sample_lower_of_cos_cert (i := 1) (p := 164)
    (a := 999999926465) (bs := [999999705860, 999998823440, 999995293762, 999981175092, 999924701076, 999698815643, 998795443996, 995184677894])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def roots_2 : List ℕ := [100000000, 17298873, 6198503, 2992510, 1701109, 1072271, 725847, 517670, 384214, 294272, 231193, 185490, 151471, 125563, 105443, 89551]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem log_sample_2 : logZeta (162 / 64) ≤ (285253 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 162) (bs := roots_2) (bTail := 1432819)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_2, Finset.sum_range_succ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem sigma_sample_2 : (162 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 2) := by
  have h := sigma_sample_lower_of_cos_cert (i := 2) (p := 162)
    (a := 999999705862) (bs := [999998823448, 999995293794, 999981175220, 999924701588, 999698817691, 998795452185, 995184710610, 980785216463])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def roots_3 : List ℕ := [100000000, 17677669, 6415002, 3125000, 1788854, 1134023, 771356, 552427, 411522, 316227, 249182, 200468, 164112, 136357, 114755, 97656]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem log_sample_3 : logZeta (160 / 64) ≤ (294135 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 160) (bs := roots_3) (bTail := 1562500)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_3, Finset.sum_range_succ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem sigma_sample_3 : (160 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 3) := by
  have h := sigma_sample_lower_of_cos_cert (i := 3) (p := 160)
    (a := 999999338191) (bs := [999997352764, 999989411070, 999957644504, 999830581603, 999322383817, 997290453595, 989176497663, 956940287057])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def roots_4 : List ℕ := [100000000, 18064760, 6639064, 3263355, 1881125, 1199331, 819717, 589517, 440771, 339820, 268572, 216656, 177808, 148080, 124889, 106494]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem log_sample_4 : logZeta (158 / 64) ≤ (303361 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 158) (bs := roots_4) (bTail := 1703919)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_4, Finset.sum_range_succ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem sigma_sample_4 : (158 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 4) := by
  have h := sigma_sample_lower_of_cos_cert (i := 4) (p := 158)
    (a := 999998823451) (bs := [999995293806, 999981175268, 999924701780, 999698818459, 998795455256, 995184722880, 980785265307, 923879473286])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def roots_5 : List ℕ := [100000000, 18864555, 7110939, 3558714, 2080192, 1341447, 925726, 671335, 505654, 392418, 311995, 253058, 208724, 174634, 147921, 126644]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem log_sample_5 : logZeta (154 / 64) ≤ (322917 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 154) (bs := roots_5) (bTail := 2026312)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_5, Finset.sum_range_succ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem sigma_sample_5 : (154 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 5) := by
  have h := sigma_sample_lower_of_cos_cert (i := 5) (p := 154)
    (a := 999998161642) (bs := [999992646574, 999970586404, 999882347346, 999529417068, 998118111168, 992479527683, 970031225739, 881921157817])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def roots_6 : List ℕ := [100000000, 19699760, 7616352, 3880805, 2300324, 1500403, 1045445, 764509, 580088, 453158, 362439, 295575, 245016, 205950, 175200, 150606]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem log_sample_6 : logZeta (150 / 64) ≤ (344080 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 150) (bs := roots_6) (bTail := 2409705)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_6, Finset.sum_range_succ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem sigma_sample_6 : (150 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 6) := by
  have h := sigma_sample_lower_of_cos_cert (i := 6) (p := 150)
    (a := 999997352765) (bs := [999989411074, 999957644520, 999830581667, 999322384073, 997290454618, 989176501744, 956940303204, 831469487792])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def roots_7 : List ℕ := [100000000, 20795957, 8298931, 4324718, 2608531, 1725842, 1217095, 899366, 688722, 542469, 437113, 358905, 299379, 253106, 216480, 187031]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem log_sample_7 : logZeta (145 / 64) ≤ (373068 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 145) (bs := roots_7) (bTail := 2992511)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_7, Finset.sum_range_succ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem sigma_sample_7 : (145 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 7) := by
  have h := sigma_sample_lower_of_cos_cert (i := 7) (p := 145)
    (a := 999996396819) (bs := [999985587301, 999942349619, 999769405123, 999077726839, 996312608531, 985277627835, 941544007824, 773010237338])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def roots_8 : List ℕ := [100000000, 22192206, 9199246, 4924940, 3033363, 2041515, 1460671, 1092952, 846261, 673170, 547299, 453057, 380762, 324155, 279046, 242550]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem log_sample_8 : logZeta (139 / 64) ≤ (412130 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 139) (bs := roots_8) (bTail := 3880806)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_8, Finset.sum_range_succ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem sigma_sample_8 : (139 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 8) := by
  have h := sigma_sample_lower_of_cos_cert (i := 8) (p := 139)
    (a := 999995293804) (bs := [999981175260, 999924701748, 999698818331, 998795454744, 995184720834, 980785257162, 923879441332, 707106444231])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def roots_9 : List ℕ := [100000000, 23682199, 10197234, 5608465, 3527385, 2414929, 1752994, 1328208, 1039835, 835362, 685260, 571908, 484268, 415147, 359695, 314548]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem log_sample_9 : logZeta (133 / 64) ≤ (456702 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 133) (bs := roots_9) (bTail := 5032783)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_9, Finset.sum_range_succ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem sigma_sample_9 : (133 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 9) := by
  have h := sigma_sample_lower_of_cos_cert (i := 9) (p := 133)
    (a := 999994043721) (bs := [999976174954, 999904700951, 999618821967, 998475578461, 993906961566, 975702096498, 903989162221, 634392810826])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def roots_10 : List ℕ := [100000000, 25547428, 11499197, 6526711, 4206324, 2937749, 2168768, 1667406, 1322315, 1074607, 890754, 750519, 641097, 554064, 483693, 425979]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem log_sample_10 : logZeta (126 / 64) ≤ (517200 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 126) (bs := roots_10) (bTail := 6815674)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_10, Finset.sum_range_succ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem sigma_sample_10 : (126 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 10) := by
  have h := sigma_sample_lower_of_cos_cert (i := 10) (p := 126)
    (a := 999992646570) (bs := [999970586388, 999882347282, 999529416812, 998118110145, 992479523598, 970031209522, 881921094893, 555569635234])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def roots_11 : List ℕ := [100000000, 27559564, 12967392, 7595295, 5015943, 3573756, 2683155, 2093230, 1681532, 1382372, 1157871, 984911, 848714, 739465, 650437, 576885]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem log_sample_11 : logZeta (119 / 64) ≤ (589182 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 119) (bs := roots_11) (bTail := 9230164)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_11, Finset.sum_range_succ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem sigma_sample_11 : (119 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 11) := by
  have h := sigma_sample_lower_of_cos_cert (i := 11) (p := 119)
    (a := 999991102349) (bs := [999964409554, 999857640749, 999430603528, 997723062536, 990902619032, 963776000808, 857728359466, 471395877264])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def roots_12 : List ℕ := [100000000, 29730177, 14623044, 8838834, 5981395, 4347457, 3319544, 2627801, 2138334, 1778279, 1505091, 1292506, 1123567, 986906, 874662, 781250]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem log_sample_12 : logZeta (112 / 64) ≤ (676082 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 112) (bs := roots_12) (bTail := 12500000)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_12, Finset.sum_range_succ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem sigma_sample_12 : (112 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 12) := by
  have h := sigma_sample_lower_of_cos_cert (i := 12) (p := 112)
    (a := 999989411060) (bs := [999957644464, 999830581443, 999322383177, 997290451037, 989176487459, 956940246683, 831469271443, 382682298707])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def roots_13 : List ℕ := [100000000, 32420988, 16775596, 10511205, 7314316, 5438814, 4233657, 3407836, 2814206, 2371373, 2031126, 1763317, 1548253, 1372593, 1227020, 1104854]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem log_sample_13 : logZeta (104 / 64) ≤ (800295 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 104) (bs := roots_13) (bTail := 17677670)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_13, Finset.sum_range_succ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem sigma_sample_13 : (104 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 13) := by
  have h := sigma_sample_lower_of_cos_cert (i := 13) (p := 104)
    (a := 999987572703) (bs := [999950291120, 999801169421, 999204756751, 996820291827, 987301388396, 949528063057, 803207085065, 290283242997])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def roots_14 : List ℕ := [100000000, 35355339, 19245008, 12500000, 8944271, 6804138, 5399492, 4419417, 3703703, 3162277, 2741012, 2405626, 2133462, 1909008, 1721325, 1562500]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem log_sample_14 : logZeta (96 / 64) ≤ (963201 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 96) (bs := roots_14) (bTail := 25000000)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_14, Finset.sum_range_succ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem sigma_sample_14 : (96 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 14) := by
  have h := sigma_sample_lower_of_cos_cert (i := 14) (p := 96)
    (a := 999985587277) (bs := [999942349523, 999769404739, 999077725304, 996312602397, 985277603390, 941543911483, 773009874501, 195088532152])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def roots_15 : List ℕ := [100000000, 38555270, 22077926, 14865088, 10937454, 8512204, 6886367, 5731275, 4874348, 4216965, 3699006, 3281903, 2939868, 2655057, 2414763, 2209708]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem log_sample_15 : logZeta (88 / 64) ≤ (1188266 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 88) (bs := roots_15) (bTail := 35355340)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_15, Finset.sum_range_succ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem sigma_sample_15 : (88 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 15) := by
  have h := sigma_sample_lower_of_cos_cert (i := 15) (p := 88)
    (a := 999983454782) (bs := [999933819675, 999735287459, 998941289981, 995767401657, 983105436405, 932992598178, 740950376509, 98014920897])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private def roots_16 : List ℕ := [100000000, 42044820, 25327856, 17677669, 13374806, 10649051, 8782687, 7432544, 6415002, 5623413, 4991822, 4477374, 4051079, 3692665, 3387551, 3125000]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem log_sample_16 : logZeta (80 / 64) ≤ (1528345 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 80) (bs := roots_16) (bTail := 50000000)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_16, Finset.sum_range_succ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem sigma_sample_16 : (80 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 16) := by
  rw [show Real.pi / 32 * 16 = Real.pi / 2 by ring, Real.cos_pi_div_two]
  norm_num

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
noncomputable def sampleP : ℕ → ℕ
  | 0 => 164
  | 1 => 164
  | 2 => 162
  | 3 => 160
  | 4 => 158
  | 5 => 154
  | 6 => 150
  | 7 => 145
  | 8 => 139
  | 9 => 133
  | 10 => 126
  | 11 => 119
  | 12 => 112
  | 13 => 104
  | 14 => 96
  | 15 => 88
  | 16 => 80
  | _ => 80

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
noncomputable def sampleB : ℕ → ℝ
  | 0 => 276700 / 1000000
  | 1 => 276700 / 1000000
  | 2 => 285253 / 1000000
  | 3 => 294135 / 1000000
  | 4 => 303361 / 1000000
  | 5 => 322917 / 1000000
  | 6 => 344080 / 1000000
  | 7 => 373068 / 1000000
  | 8 => 412130 / 1000000
  | 9 => 456702 / 1000000
  | 10 => 517200 / 1000000
  | 11 => 589182 / 1000000
  | 12 => 676082 / 1000000
  | 13 => 800295 / 1000000
  | 14 => 963201 / 1000000
  | 15 => 1188266 / 1000000
  | 16 => 1528345 / 1000000
  | _ => 0

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma sampleP_gt_one (i : ℕ) (hi : i ≤ 16) : 1 < (sampleP i : ℝ) / 64 := by
  interval_cases i <;> norm_num [sampleP]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma sample_log_bound (i : ℕ) (hi : i ≤ 16) : logZeta ((sampleP i : ℝ) / 64) ≤ sampleB i := by
  interval_cases i
  · exact log_sample_0
  · exact log_sample_1
  · exact log_sample_2
  · exact log_sample_3
  · exact log_sample_4
  · exact log_sample_5
  · exact log_sample_6
  · exact log_sample_7
  · exact log_sample_8
  · exact log_sample_9
  · exact log_sample_10
  · exact log_sample_11
  · exact log_sample_12
  · exact log_sample_13
  · exact log_sample_14
  · exact log_sample_15
  · exact log_sample_16

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma sample_sigma_lower (i : ℕ) (hi : i ≤ 16) : (sampleP i : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * i) := by
  interval_cases i
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_0
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_1
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_2
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_3
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_4
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_5
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_6
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_7
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_8
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_9
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_10
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_11
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_12
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_13
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_14
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_15
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_16

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma sample_arc_bound (i : ℕ) (hi : i ≤ 16) :
    arcFunction (Real.pi / 32 * i) ≤ sampleB i := by
  have hiR : (i : ℝ) ≤ 16 := by exact_mod_cast hi
  have hmem : Real.pi / 32 * i ∈ Set.Icc 0 (Real.pi / 2) := by
    constructor
    · positivity
    · nlinarith [mul_le_mul_of_nonneg_left hiR Real.pi_pos.le]
  exact (antitoneOn_logZeta (sampleP_gt_one i hi) (arc_sigma_gt_one hmem)
    (sample_sigma_lower i hi)).trans (sample_log_bound i hi)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem right_arc_integral_lt :
    (∫ θ in (0 : ℝ)..Real.pi / 2, arcFunction θ) / (2 * Real.pi) < 0.1361 := by
  have hs : (∑ i ∈ Finset.range 16,
      (arcFunction (Real.pi / 32 * i) + arcFunction (Real.pi / 32 * ((i : ℝ) + 1))) / 2) ≤
      ∑ i ∈ Finset.range 16, (sampleB i + sampleB (i + 1)) / 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i < 16 := Finset.mem_range.mp hi
    have h0 := sample_arc_bound i (by omega)
    have h1 := sample_arc_bound (i + 1) (by omega)
    push_cast at h1
    linarith
  have hn : (∑ i ∈ Finset.range 16, (sampleB i + sampleB (i + 1)) / 2) / 64 < (0.1361 : ℝ) := by
    norm_num [sampleB, Finset.sum_range_succ]
  exact (right_arc_le_samples.trans (div_le_div_of_nonneg_right hs (by norm_num))).trans_lt hn

end TernaryGoldbach.RSBounds.BacklundRightArc
end

-- RSBounds.BacklundAngularCoefficients
section
open Real MeasureTheory

namespace TernaryGoldbach.RSBounds.BacklundAngularCoefficients

noncomputable def radius : ℝ := 33 / 25
noncomputable def q : ℝ := Real.log (44 / 25)
noncomputable def alpha : ℝ := Real.arccos (-(25 / 132))
noncomputable def beta : ℝ := Real.arccos (-(125 / 132))
noncomputable def slopeA : ℝ :=
  (radius * Real.sin alpha - (Real.pi - alpha) / 4 +
    radius * Real.sin beta - 5 * (Real.pi - beta) / 4) / (4 * Real.pi * q)
noncomputable def slopeB : ℝ := 1 / (4 * q)
noncomputable def intercept (C : ℝ) : ℝ :=
  C / q - slopeA * Real.log (2 * Real.pi) + Real.log (3.426 : ℝ) / (2 * q) + 1 / 2

lemma q_pos : 0 < q := Real.log_pos (by norm_num)

lemma first_cos_integral :
    (∫ θ in alpha..Real.pi, (radius * Real.cos θ + 1 / 4)) =
      -radius * Real.sin alpha + (Real.pi - alpha) / 4 := by
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, integral_cos, Real.sin_pi,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

lemma second_cos_integral :
    (∫ θ in beta..Real.pi, (radius * Real.cos θ + 5 / 4)) =
      -radius * Real.sin beta + 5 * (Real.pi - beta) / 4 := by
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, integral_cos, Real.sin_pi,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

lemma angular_integrals_eq (J L H V : ℝ) :
    (2 * Real.pi * J + Real.pi / 2 * H -
      L / 2 * (∫ θ in alpha..Real.pi, (radius * Real.cos θ + 1 / 4)) -
      L / 2 * (∫ θ in beta..Real.pi, (radius * Real.cos θ + 5 / 4)) +
      (beta - alpha) * V) / (2 * Real.pi * q) =
      J / q + slopeA * L + slopeB * H + (beta - alpha) * V / (2 * Real.pi * q) := by
  rw [first_cos_integral, second_cos_integral]
  unfold slopeA slopeB
  field_simp [q_pos.ne', Real.pi_ne_zero]
  ring

end TernaryGoldbach.RSBounds.BacklundAngularCoefficients
end

-- RSBounds.BacklundAngularAssembly
section
open Real Set MeasureTheory
open TernaryGoldbach.RSBounds.BacklundRightArc
open TernaryGoldbach.RSBounds.BacklundAngularCoefficients
open TernaryGoldbach.RSBounds.BacklundCircleMajorant (scalar)

namespace TernaryGoldbach.RSBounds.BacklundAngularAssembly

noncomputable def sigma (θ : ℝ) : ℝ := 5 / 4 + radius * Real.cos θ
noncomputable def arc (H L V θ : ℝ) : ℝ := scalar H L V (sigma θ)

lemma half_pi_le_alpha : Real.pi / 2 ≤ alpha := by
  have h := Real.arccos_le_arccos (show -(25 / 132 : ℝ) ≤ 0 by norm_num)
  simpa only [Real.arccos_zero, alpha] using h

lemma alpha_le_beta : alpha ≤ beta :=
  Real.arccos_le_arccos (by norm_num : -(125 / 132 : ℝ) ≤ -(25 / 132))

lemma beta_le_pi : beta ≤ Real.pi := Real.arccos_le_pi _
lemma alpha_le_pi : alpha ≤ Real.pi := alpha_le_beta.trans beta_le_pi
lemma alpha_nonneg : 0 ≤ alpha := Real.arccos_nonneg _
lemma beta_nonneg : 0 ≤ beta := Real.arccos_nonneg _
lemma cos_alpha : Real.cos alpha = -(25 / 132 : ℝ) :=
  Real.cos_arccos (by norm_num) (by norm_num)
lemma cos_beta : Real.cos beta = -(125 / 132 : ℝ) :=
  Real.cos_arccos (by norm_num) (by norm_num)

lemma sigma_gt_one {θ : ℝ} (h0 : 0 ≤ θ) (hα : θ < alpha) : 1 < sigma θ := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi h0 alpha_le_pi hα
  rw [cos_alpha] at h
  dsimp [sigma, radius]
  linarith

lemma sigma_lt_one {θ : ℝ} (hπ : θ ≤ Real.pi) (hα : alpha < θ) : sigma θ < 1 := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi alpha_nonneg hπ hα
  rw [cos_alpha] at h
  dsimp [sigma, radius]
  linarith

lemma sigma_pos {θ : ℝ} (h0 : 0 ≤ θ) (hβ : θ < beta) : 0 < sigma θ := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi h0 beta_le_pi hβ
  rw [cos_beta] at h
  dsimp [sigma, radius]
  linarith

lemma sigma_neg {θ : ℝ} (hπ : θ ≤ Real.pi) (hβ : beta < θ) : sigma θ < 0 := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi beta_nonneg hπ hβ
  rw [cos_beta] at h
  dsimp [sigma, radius]
  linarith

lemma sigma_lt_five_fourths {θ : ℝ} (hπ : θ ≤ Real.pi) (hθ : Real.pi / 2 < θ) :
    sigma θ < 5 / 4 := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ Real.pi / 2) hπ hθ
  rw [Real.cos_pi_div_two] at h
  dsimp [sigma, radius]
  linarith

lemma sector_one (H L V : ℝ) {θ : ℝ} (hθ : θ ∈ Ioo 0 (Real.pi / 2)) :
    arc H L V θ = arcFunction θ := by
  have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], hθ.2.le⟩
  have hs : 5 / 4 ≤ sigma θ := by dsimp [sigma, radius]; linarith
  simp only [arc, scalar, if_pos hs]
  rfl

lemma sector_two (H L V : ℝ) {θ : ℝ} (hθ : θ ∈ Ioo (Real.pi / 2) alpha) :
    arc H L V θ = H := by
  have h0 : 0 ≤ θ := by linarith [Real.pi_pos, hθ.1]
  have hπ : θ ≤ Real.pi := hθ.2.le.trans alpha_le_pi
  have hs1 := sigma_gt_one h0 hθ.2
  have hs54 := sigma_lt_five_fourths hπ hθ.1
  have hstrip : ¬(0 ≤ sigma θ ∧ sigma θ < 1) := by intro h; linarith [h.2]
  simp only [arc, scalar, if_neg (not_le.mpr hs54),
    max_eq_right (by linarith : 1 - sigma θ ≤ 0),
    max_eq_right (by linarith : -sigma θ ≤ 0), if_neg hstrip, add_zero, zero_add, mul_zero]

lemma sector_three (H L V : ℝ) {θ : ℝ} (hθ : θ ∈ Ioo alpha beta) :
    arc H L V θ = H - L / 2 * (radius * Real.cos θ + 1 / 4) + V := by
  have h0 : 0 ≤ θ := alpha_nonneg.trans hθ.1.le
  have hπ : θ ≤ Real.pi := hθ.2.le.trans beta_le_pi
  have hs0 := sigma_pos h0 hθ.2
  have hs1 := sigma_lt_one hπ hθ.1
  have hs54 : sigma θ < 5 / 4 := by linarith
  have hstrip : 0 ≤ sigma θ ∧ sigma θ < 1 := ⟨hs0.le, hs1⟩
  simp only [arc, scalar, if_neg (not_le.mpr hs54),
    max_eq_left (by linarith : 0 ≤ 1 - sigma θ),
    max_eq_right (by linarith : -sigma θ ≤ 0), if_pos hstrip, add_zero]
  dsimp [sigma]
  ring

lemma sector_four (H L V : ℝ) {θ : ℝ} (hθ : θ ∈ Ioo beta Real.pi) :
    arc H L V θ = H - L / 2 * (radius * Real.cos θ + 1 / 4) -
      L / 2 * (radius * Real.cos θ + 5 / 4) := by
  have hs0 := sigma_neg hθ.2.le hθ.1
  have hs54 : sigma θ < 5 / 4 := by linarith
  have hstrip : ¬(0 ≤ sigma θ ∧ sigma θ < 1) := by intro h; linarith [h.1]
  simp only [arc, scalar, if_neg (not_le.mpr hs54),
    max_eq_left (by linarith : 0 ≤ 1 - sigma θ),
    max_eq_left (by linarith : 0 ≤ -sigma θ), if_neg hstrip, add_zero]
  dsimp [sigma]
  ring

lemma sector_integrable (H L V : ℝ) :
    IntervalIntegrable (arc H L V) volume 0 (Real.pi / 2) ∧
    IntervalIntegrable (arc H L V) volume (Real.pi / 2) alpha ∧
    IntervalIntegrable (arc H L V) volume alpha beta ∧
    IntervalIntegrable (arc H L V) volume beta Real.pi := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (continuousOn_arcFunction.intervalIntegrable_of_Icc (by positivity)).congr_uIoo
    rw [uIoo_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    exact fun θ hθ => (sector_one H L V hθ).symm
  · apply (intervalIntegrable_const (c := H)).congr_uIoo
    rw [uIoo_of_le half_pi_le_alpha]
    exact fun θ hθ => (sector_two H L V hθ).symm
  · have h : Continuous (fun θ => H - L / 2 * (radius * Real.cos θ + 1 / 4) + V) := by fun_prop
    apply (h.intervalIntegrable alpha beta).congr_uIoo
    rw [uIoo_of_le alpha_le_beta]
    exact fun θ hθ => (sector_three H L V hθ).symm
  · have h : Continuous (fun θ => H - L / 2 * (radius * Real.cos θ + 1 / 4) -
        L / 2 * (radius * Real.cos θ + 5 / 4)) := by fun_prop
    apply (h.intervalIntegrable beta Real.pi).congr_uIoo
    rw [uIoo_of_le beta_le_pi]
    exact fun θ hθ => (sector_four H L V hθ).symm

lemma intervalIntegrable_scalar_arc (H L V : ℝ) :
    IntervalIntegrable (arc H L V) volume 0 Real.pi := by
  obtain ⟨h1, h2, h3, h4⟩ := sector_integrable H L V
  exact ((h1.trans h2).trans h3).trans h4

lemma scalar_arc_integral_raw (H L V : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi, arc H L V θ) =
      (∫ θ in (0 : ℝ)..Real.pi / 2, arcFunction θ) + Real.pi / 2 * H -
      L / 2 * (∫ θ in alpha..Real.pi, (radius * Real.cos θ + 1 / 4)) -
      L / 2 * (∫ θ in beta..Real.pi, (radius * Real.cos θ + 5 / 4)) + (beta - alpha) * V := by
  obtain ⟨h1, h2, h3, h4⟩ := sector_integrable H L V
  have he1 := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) (by positivity : (0 : ℝ) ≤ Real.pi / 2)
    (fun θ hθ => sector_one H L V hθ)
  have he2 := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) half_pi_le_alpha
    (fun θ hθ => sector_two H L V hθ)
  have he3 := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) alpha_le_beta
    (fun θ hθ => sector_three H L V hθ)
  have he4 := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) beta_le_pi
    (fun θ hθ => sector_four H L V hθ)
  have hc1 : Continuous (fun θ => radius * Real.cos θ + 1 / 4) := by fun_prop
  have hc2 : Continuous (fun θ => radius * Real.cos θ + 5 / 4) := by fun_prop
  have hj := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hc1.intervalIntegrable alpha beta)
    (hc1.intervalIntegrable beta Real.pi)
  rw [← intervalIntegral.integral_add_adjacent_intervals ((h1.trans h2).trans h3) h4,
    ← intervalIntegral.integral_add_adjacent_intervals (h1.trans h2) h3,
    ← intervalIntegral.integral_add_adjacent_intervals h1 h2,
    he1, he2, he3, he4]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) intervalIntegrable_const,
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
  rw [← hj]
  ring

lemma scalar_arc_integral_eq (H L V : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi, arc H L V θ) / (2 * Real.pi * q) =
      ((∫ θ in (0 : ℝ)..Real.pi / 2, arcFunction θ) / (2 * Real.pi)) / q +
      slopeA * L + slopeB * H + (beta - alpha) * V / (2 * Real.pi * q) := by
  rw [scalar_arc_integral_raw]
  convert angular_integrals_eq
    ((∫ θ in (0 : ℝ)..Real.pi / 2, arcFunction θ) / (2 * Real.pi)) L H V using 1 <;>
    field_simp [Real.pi_ne_zero, q_pos.ne'] <;> ring

lemma scalar_arc_integral_le (H L V : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi, arc H L V θ) / (2 * Real.pi * q) ≤
      (0.1361 : ℝ) / q + slopeA * L + slopeB * H +
        (beta - alpha) * V / (2 * Real.pi * q) := by
  rw [scalar_arc_integral_eq]
  have h := div_le_div_of_nonneg_right right_arc_integral_lt.le q_pos.le
  linarith

end TernaryGoldbach.RSBounds.BacklundAngularAssembly
end

-- RSBounds.BacklundAngularNumerics
section
open Real Finset
open TernaryGoldbach.RSBounds.BacklundRightArc
namespace TernaryGoldbach.RSBounds.BacklundAngularCoefficients

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private lemma cos_gamma_lo : (25 / 132 : ℝ) ≤ Real.cos (6901 / 5000 : ℝ) := by
  have hs : (9999990916480827 : ℝ) / 10000000000000000 ≤ Real.cos ((6901 / 5000 : ℝ) / 1024) :=
    cos_initial_lower (by norm_num) le_rfl (by norm_num)
  have he := cosDoubleCheck_sound (by norm_num : 0 < 10000000000000000) hs
    (by decide +kernel : cosDoubleCheck 10000000000000000 9999990916480827 [9999963665939810, 9999854664023272, 9999418660317597, 9997674708861553, 9990699916841987, 9962816965677297, 9851544378317476, 9410585327591732, 7711823241576957, 1894443541865304] = true)
  norm_num [cosEnd] at he
  linarith

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private lemma cos_gamma_hi : Real.cos (13803 / 10000 : ℝ) ≤ (25 / 132 : ℝ) := by
  have hs : (9999985207781639 : ℝ) / 10000000000000000 ≤ Real.cos ((Real.pi - (13803 / 10000 : ℝ)) / 1024) := by
    apply cos_initial_lower (show 0 ≤ (Real.pi - (13803 / 10000 : ℝ)) / 1024 by linarith [Real.pi_gt_three])
      (show (Real.pi - (13803 / 10000 : ℝ)) / 1024 ≤ (3.141593 - (13803 / 10000 : ℝ)) / 1024 by linarith [Real.pi_lt_d6])
    norm_num
  have he := cosDoubleCheck_sound (by norm_num : 0 < 10000000000000000) hs
    (by decide +kernel : cosDoubleCheck 10000000000000000 9999985207781639 [9999940831170317, 9999763325381458, 9999053312728807, 9996213430158585, 9984856588256572, 9939472217610134, 9758621592928742, 9046139078795019, 6366526446580478, -1893468200998271] = true)
  norm_num only [cosEnd, List.length_cons, List.length_nil, Nat.reduceAdd] at he
  rw [show (1024 : ℝ) * ((Real.pi - (13803 / 10000 : ℝ)) / 1024) = Real.pi - (13803 / 10000 : ℝ) by ring,
    Real.cos_pi_sub] at he
  norm_num at he
  linarith

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private lemma cos_delta_lo : (125 / 132 : ℝ) ≤ Real.cos (3271 / 10000 : ℝ) := by
  have hs : (9999999489810895 : ℝ) / 10000000000000000 ≤ Real.cos ((3271 / 10000 : ℝ) / 1024) :=
    cos_initial_lower (by norm_num) le_rfl (by norm_num)
  have he := cosDoubleCheck_sound (by norm_num : 0 < 10000000000000000) hs
    (by decide +kernel : cosDoubleCheck 10000000000000000 9999999489810895 [9999997959243632, 9999991836975360, 9999967347914766, 9999869391872295, 9999477570900876, 9997910338189936, 9991642226097040, 9966582874865082, 9866554840310784, 9469780883372032] = true)
  norm_num [cosEnd] at he
  linarith

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private lemma cos_delta_hi : Real.cos (409 / 1250 : ℝ) ≤ (125 / 132 : ℝ) := by
  have hs : (9999962230644424 : ℝ) / 10000000000000000 ≤ Real.cos ((Real.pi - (409 / 1250 : ℝ)) / 1024) := by
    apply cos_initial_lower (show 0 ≤ (Real.pi - (409 / 1250 : ℝ)) / 1024 by linarith [Real.pi_gt_three])
      (show (Real.pi - (409 / 1250 : ℝ)) / 1024 ≤ (3.141593 - (409 / 1250 : ℝ)) / 1024 by linarith [Real.pi_lt_d6])
    norm_num
  have he := cosDoubleCheck_sound (by norm_num : 0 < 10000000000000000) hs
    (by decide +kernel : cosDoubleCheck 10000000000000000 9999962230644424 [9999848922863000, 9999395696016860, 9997582857104100, 9990332596932355, 9961349079465834, 9845695096594963, 9387542387022819, 7625190413630017, 1628705768823021, -9469463503720523] = true)
  norm_num only [cosEnd, List.length_cons, List.length_nil, Nat.reduceAdd] at he
  rw [show (1024 : ℝ) * ((Real.pi - (409 / 1250 : ℝ)) / 1024) = Real.pi - (409 / 1250 : ℝ) by ring,
    Real.cos_pi_sub] at he
  norm_num at he
  linarith

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma gamma_bounds : (1.3802 : ℝ) ≤ Real.arccos (25 / 132) ∧
    Real.arccos (25 / 132) ≤ 1.3803 := by
  constructor
  · have h := Real.arccos_le_arccos cos_gamma_lo
    rw [Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])] at h
    convert h using 1 <;> norm_num
  · have h := Real.arccos_le_arccos cos_gamma_hi
    rw [Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])] at h
    convert h using 1 <;> norm_num

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma delta_bounds : (0.3271 : ℝ) ≤ Real.arccos (125 / 132) ∧
    Real.arccos (125 / 132) ≤ 0.3272 := by
  constructor
  · have h := Real.arccos_le_arccos cos_delta_lo
    rw [Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])] at h
    convert h using 1 <;> norm_num
  · have h := Real.arccos_le_arccos cos_delta_hi
    rw [Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])] at h
    convert h using 1 <;> norm_num

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma q_bounds : (0.5653 : ℝ) ≤ q ∧ q ≤ 0.5654 := by
  unfold q
  constructor
  · apply (Real.le_log_iff_exp_le (by norm_num)).mpr
    have h := Real.exp_bound' (x := (0.5653 : ℝ)) (by norm_num) (by norm_num) (n := 12) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith
  · apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg (x := (0.5654 : ℝ)) (by norm_num) 12
    norm_num [Finset.sum_range_succ] at h
    linarith

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma log_two_pi_lower : (1.8378 : ℝ) ≤ Real.log (2 * Real.pi) := by
  apply (Real.le_log_iff_exp_le (by positivity)).mpr
  have h := Real.exp_bound' (x := (0.9189 : ℝ)) (by norm_num) (by norm_num) (n := 14) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  have h1 : Real.exp (0.9189 : ℝ) ≤ 2.5066 := by linarith
  have h2 := pow_le_pow_left₀ (Real.exp_nonneg (0.9189 : ℝ)) h1 2
  rw [← Real.exp_nat_mul] at h2
  norm_num at h2
  nlinarith [Real.pi_gt_d6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma log_center_upper : Real.log (3.426 : ℝ) ≤ 1.2315 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).mpr
  have h := Real.sum_le_exp_of_nonneg (x := (1.2315 : ℝ)) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at h
  linarith

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma first_sine_bounds : (5.1844 : ℝ) / 4 ≤ radius * Real.sin alpha ∧
    radius * Real.sin alpha ≤ 5.1845 / 4 := by
  have hcos : Real.cos alpha = -(25 / 132 : ℝ) := Real.cos_arccos (by norm_num) (by norm_num)
  have hs0 : 0 ≤ radius * Real.sin alpha := mul_nonneg (by norm_num [radius])
    (Real.sin_nonneg_of_mem_Icc ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩)
  have hs := Real.sin_sq_add_cos_sq alpha
  rw [hcos] at hs
  constructor
  · apply (sq_le_sq₀ (by norm_num) hs0).mp
    unfold radius
    nlinarith
  · apply (sq_le_sq₀ hs0 (by norm_num)).mp
    unfold radius
    nlinarith

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma second_sine_bounds : (1.6965 : ℝ) / 4 ≤ radius * Real.sin beta ∧
    radius * Real.sin beta ≤ 1.6966 / 4 := by
  have hcos : Real.cos beta = -(125 / 132 : ℝ) := Real.cos_arccos (by norm_num) (by norm_num)
  have hs0 : 0 ≤ radius * Real.sin beta := mul_nonneg (by norm_num [radius])
    (Real.sin_nonneg_of_mem_Icc ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩)
  have hs := Real.sin_sq_add_cos_sq beta
  rw [hcos] at hs
  constructor
  · apply (sq_le_sq₀ (by norm_num) hs0).mp
    unfold radius
    nlinarith
  · apply (sq_le_sq₀ hs0 (by norm_num)).mp
    unfold radius
    nlinarith

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma slopeA_bounds : (0.1359 : ℝ) ≤ slopeA ∧ slopeA ≤ 0.1361 := by
  have hq0 : 0 < q := q_pos
  have hα : Real.pi - alpha = Real.arccos (25 / 132) := by unfold alpha; rw [Real.arccos_neg]; ring
  have hβ : Real.pi - beta = Real.arccos (125 / 132) := by unfold beta; rw [Real.arccos_neg]; ring
  have hdenpos : 0 < 4 * Real.pi * q := by positivity [q_pos]
  have hdenlo : 4 * (3.141592 : ℝ) * 0.5653 ≤ 4 * Real.pi * q := by
    gcongr
    · exact Real.pi_gt_d6.le
    · exact q_bounds.1
  have hdenhi : 4 * Real.pi * q ≤ 4 * (3.141593 : ℝ) * 0.5654 := by
    gcongr
    · exact Real.pi_lt_d6.le
    · exact q_bounds.2
  unfold slopeA
  rw [hα, hβ]
  constructor
  · apply (le_div_iff₀ hdenpos).mpr
    nlinarith [first_sine_bounds.1, second_sine_bounds.1, gamma_bounds.2, delta_bounds.2]
  · apply (div_le_iff₀ hdenpos).mpr
    nlinarith [first_sine_bounds.2, second_sine_bounds.2, gamma_bounds.1, delta_bounds.1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma slopeB_le : slopeB ≤ (0.4423 : ℝ) := by
  unfold slopeB
  apply (div_le_iff₀ (by positivity [q_pos])).mpr
  nlinarith [q_bounds.1]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma intercept_le_strong : intercept 0.1361 ≤ (1.5803 : ℝ) := by
  have hq0 : 0 < q := q_pos
  have hA0 : 0 ≤ slopeA := by linarith [slopeA_bounds.1]
  have hlog0 : 0 ≤ Real.log (3.426 : ℝ) := Real.log_nonneg (by norm_num)
  have h1 : (0.1361 : ℝ) / q ≤ 0.1361 / 0.5653 := by
    gcongr
    exact q_bounds.1
  have h2 : Real.log (3.426 : ℝ) / (2 * q) ≤ 1.2315 / (2 * 0.5653) := by
    gcongr
    · exact log_center_upper
    · exact q_bounds.1
  have h3 : (0.1359 : ℝ) * 1.8378 ≤ slopeA * Real.log (2 * Real.pi) := by
    gcongr
    · exact slopeA_bounds.1
    · exact log_two_pi_lower
  unfold intercept
  linarith

end TernaryGoldbach.RSBounds.BacklundAngularCoefficients
end

-- TernaryGoldbach.Explicit.ZetaDatum
section
open Complex MeasureTheory Set Filter Metric
open scoped Real Topology

namespace TernaryGoldbach.Explicit

theorem logDeriv_zetaF_eq {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    logDeriv zetaF s = 1 / (s - 1) + logDeriv riemannZeta s := by
  have hev : zetaF =ᶠ[𝓝 s] fun s => (s - 1) * riemannZeta s := by
    filter_upwards [isOpen_ne.mem_nhds hs] with t ht using zetaF_of_ne ht
  have hd : deriv zetaF s = 1 * riemannZeta s + (s - 1) * deriv riemannZeta s := by
    rw [hev.deriv_eq]
    exact ((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt |>.deriv
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 hs
  rw [logDeriv_apply, logDeriv_apply, hd, zetaF_of_ne hs]
  field_simp

end TernaryGoldbach.Explicit
end

-- TernaryGoldbach.Explicit.ZeroSums
section
open Complex MeasureTheory Set Filter
open scoped Real

namespace TernaryGoldbach.Explicit

theorem eq_zero_of_mem_zerosIn {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c u : ℂ} {R r : ℝ}
    (hu : u ∈ zerosIn f c R r) : f u = 0 := by
  by_contra hfu
  apply (mem_zerosIn hu).2
  by_cases hcR : u ∈ Metric.closedBall c R
  · rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
      (fun z _ => hf.analyticAt z : AnalyticOnNhd ℂ f (Metric.closedBall c R)) hcR,
      (hf.analyticAt u).analyticOrderAt_eq_zero.2 hfu]
    simp
  · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hcR

end TernaryGoldbach.Explicit
end

-- TernaryGoldbach.Explicit.ZeroSumGen
section
open Complex MeasureTheory Set Filter Metric
open scoped Real

namespace TernaryGoldbach.Explicit

structure PolyDatum (f : ℂ → ℂ) (B : ℝ → ℝ) (κ : ℝ) : Prop where
  diff : Differentiable ℂ f
  center_ge : ∀ T : ℝ, 0.355 ≤ ‖f (2 + T * I)‖
  bound : ∀ T : ℝ, ∀ w ∈ closedBall (2 + T * I) 10, ‖f w‖ ≤ B T
  B_ge : ∀ T : ℝ, 1 ≤ B T
  B_mono : ∀ T T' : ℝ, |T| ≤ |T'| → B T ≤ B T'
  growth : ∀ T0 m : ℝ, 0 < T0 → 0 ≤ m → Real.log (B (T0 + m) / 0.355) ≤ Real.log (B T0 / 0.355) + κ * m / T0
  κ_nonneg : 0 ≤ κ

variable {f : ℂ → ℂ} {B : ℝ → ℝ} {κ : ℝ}

theorem PolyDatum.log_pos (hp : PolyDatum f B κ) (T : ℝ) : 0 < Real.log (B T / 0.355) := by
  apply Real.log_pos; rw [lt_div_iff₀ (by norm_num)]; linarith [hp.B_ge T]

end TernaryGoldbach.Explicit
end

-- TernaryGoldbach.Explicit.Xi
section
open Complex MeasureTheory Set Filter
open scoped Real Topology

namespace TernaryGoldbach.Explicit

noncomputable def xiF (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta₀ s + 1

theorem differentiable_xiF : Differentiable ℂ xiF := by
  unfold xiF
  exact ((differentiable_id.mul (differentiable_id.sub_const 1)).mul differentiable_completedZeta₀).add_const 1

theorem xiF_one_sub (s : ℂ) : xiF (1 - s) = xiF s := by
  unfold xiF
  rw [completedRiemannZeta₀_one_sub]; ring

theorem xiF_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) : xiF s = s * Gammaℝ s * zetaF s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  rw [zetaF_of_ne hs1, riemannZeta_def_of_ne_zero hs0, completedRiemannZeta_eq, xiF]
  have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
  have h2 : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  field_simp
  ring

theorem xiF_one : xiF 1 = 1 := by simp [xiF]

theorem xiF_zero : xiF 0 = 1 := by simp [xiF]

theorem xiF_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : xiF s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs1
  · rw [xiF_one]; exact one_ne_zero
  rw [xiF_eq (by linarith) hs1, zetaF_of_ne hs1]
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  exact mul_ne_zero (mul_ne_zero hs0 (Gammaℝ_ne_zero_of_re_pos (by linarith)))
    (mul_ne_zero (sub_ne_zero.2 hs1) (riemannZeta_ne_zero_of_one_le_re hs))

theorem xiF_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) : xiF s ≠ 0 := by
  rw [← xiF_one_sub]
  exact xiF_ne_zero_of_one_le_re (by simp; linarith)

theorem xiF_eq_zero_iff {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) : xiF s = 0 ↔ riemannZeta s = 0 := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at h1; simp at h1
  have hs0 : s ≠ 0 := by intro h; rw [h] at h0; simp at h0
  rw [xiF_eq h0 hs1, zetaF_of_ne hs1]
  simp [hs0, Gammaℝ_ne_zero_of_re_pos h0, sub_ne_zero.2 hs1]

theorem logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Gammaℝ s = -(1 / 2) * Complex.log π + 1 / 2 * Complex.digamma (s / 2) := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hm : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hd1 : HasDerivAt (fun w : ℂ => (π : ℂ) ^ (-w / 2)) ((π : ℂ) ^ (-s / 2) * Complex.log π * (-1 / 2)) s := by
    have : HasDerivAt (fun w : ℂ => -w / 2) (-1 / 2) s := by
      simpa using ((hasDerivAt_id s).neg).div_const 2
    exact this.const_cpow (Or.inl hpi)
  have hd2 : HasDerivAt (fun w : ℂ => w / 2) (1 / 2) s := by
    simpa using (hasDerivAt_id s).div_const 2
  have hp0 : (π : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have hG0 : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hm
  have e : Gammaℝ = fun w : ℂ => (π : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) := by
    ext w; rw [Gammaℝ]
  rw [e, show (fun w : ℂ => (π : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)) =
      (fun w : ℂ => (π : ℂ) ^ (-w / 2)) * (fun w => Complex.Gamma (w / 2)) from rfl,
    logDeriv_mul (f := fun w : ℂ => (π : ℂ) ^ (-w / 2)) (g := fun w => Complex.Gamma (w / 2)) s
    hp0 hG0 hd1.differentiableAt (differentiableAt_Gamma _ hm |>.comp s hd2.differentiableAt),
    hd2.logDeriv_Gamma hm, logDeriv_apply, hd1.deriv]
  field_simp

theorem logDeriv_xiF {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hξ : xiF s ≠ 0) :
    logDeriv xiF s = 1 / s + (-(1 / 2) * Complex.log π + 1 / 2 * Complex.digamma (s / 2)) +
      logDeriv zetaF s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hz : zetaF s ≠ 0 := by
    intro h; apply hξ; rw [xiF_eq hs hs1, h, mul_zero]
  have hloc : xiF =ᶠ[𝓝 s] fun w => w * Gammaℝ w * zetaF w := by
    have hU : {w : ℂ | 0 < w.re ∧ w ≠ 1} ∈ 𝓝 s :=
      ((isOpen_lt (continuous_const (y := (0 : ℝ))) Complex.continuous_re).inter
        (isOpen_ne (x := (1 : ℂ)))).mem_nhds (show s ∈ {b : ℂ | 0 < b.re} ∩ {y : ℂ | y ≠ 1} from ⟨hs, hs1⟩)
    filter_upwards [hU] with w hw using xiF_eq hw.1 hw.2
  have hm : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hGd : DifferentiableAt ℂ Gammaℝ s := by
    have e : Gammaℝ = fun w : ℂ => (π : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) := by
      ext w; rw [Gammaℝ]
    rw [e]
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    refine (DifferentiableAt.const_cpow (by fun_prop) (Or.inl hpi)).mul ?_
    exact (differentiableAt_Gamma _ hm).comp s (by fun_prop)
  rw [(logDeriv_congr_nhds hloc).eq_of_nhds,
    show (fun w => w * Gammaℝ w * zetaF w) = (fun w => w * Gammaℝ w) * zetaF from rfl,
    logDeriv_mul (f := fun w => w * Gammaℝ w) (g := zetaF) s (mul_ne_zero hs0 hG) hz
      (differentiableAt_id.mul hGd) (differentiable_zetaF s),
    show (fun w => w * Gammaℝ w) = (fun w : ℂ => w) * Gammaℝ from rfl,
    logDeriv_mul (f := fun w : ℂ => w) (g := Gammaℝ) s hs0 hG differentiableAt_id hGd,
    logDeriv_id', logDeriv_Gammaℝ hs]

end TernaryGoldbach.Explicit
end

-- TernaryGoldbach.Explicit.XiPartial
section
open Complex Set Metric Filter
open scoped Real Interval Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Explicit

noncomputable def sqZ (A T : ℝ) : ℂ := ((1 / 2 - A : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I
noncomputable def sqW (A T : ℝ) : ℂ := ((1 / 2 + A : ℝ) : ℂ) + ((T : ℝ) : ℂ) * I

@[simp] theorem sqZ_re (A T : ℝ) : (sqZ A T).re = 1 / 2 - A := by simp [sqZ]
@[simp] theorem sqZ_im (A T : ℝ) : (sqZ A T).im = -T := by simp [sqZ]
@[simp] theorem sqW_re (A T : ℝ) : (sqW A T).re = 1 / 2 + A := by simp [sqW]
@[simp] theorem sqW_im (A T : ℝ) : (sqW A T).im = T := by simp [sqW]

theorem deriv_xiF_one_sub (w : ℂ) : deriv xiF (1 - w) = -deriv xiF w := by
  have h1 : HasDerivAt (fun s => xiF (1 - s)) (deriv xiF (1 - w) * (-1)) w := by
    have h3 : HasDerivAt (fun s : ℂ => 1 - s) (-1) w := by simpa using (hasDerivAt_id w).const_sub 1
    exact ((differentiable_xiF _).hasDerivAt).comp w h3
  have e : (fun s => xiF (1 - s)) = xiF := funext xiF_one_sub
  rw [e] at h1
  have := h1.unique (differentiable_xiF w).hasDerivAt
  linear_combination -this

theorem logDeriv_xiF_one_sub (w : ℂ) : logDeriv xiF (1 - w) = -logDeriv xiF w := by
  rw [logDeriv_apply, logDeriv_apply, deriv_xiF_one_sub, xiF_one_sub]; ring

theorem continuousAt_logDeriv_xiF {u : ℂ} (hu : xiF u ≠ 0) : ContinuousAt (logDeriv xiF) u := by
  have h1 : ContinuousAt (deriv xiF) u := (differentiable_xiF.analyticAt u).deriv.continuousAt
  have h2 : ContinuousAt xiF u := differentiable_xiF.continuous.continuousAt
  exact h1.div h2 hu

theorem xiF_conj (s : ℂ) : xiF (starRingEnd ℂ s) = starRingEnd ℂ (xiF s) := by
  rcases eq_or_ne s 0 with rfl | h0
  · simp [xiF_zero]
  rcases eq_or_ne s 1 with rfl | h1
  · simp [xiF_one]
  have h0' : starRingEnd ℂ s ≠ 0 := by simpa using h0
  have h1' : starRingEnd ℂ s ≠ 1 := by
    intro h; apply h1; simpa using congrArg (starRingEnd ℂ) h
  have e : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → xiF w = w * (w - 1) * (completedRiemannZeta w + 1 / w + 1 / (1 - w)) + 1 := by
    intro w _ _
    rw [completedRiemannZeta_eq]; unfold xiF; ring
  rw [e _ h0' h1', e _ h0 h1, completedRiemannZeta_conj]
  simp [map_add, map_mul, map_sub, map_div₀, map_one]

theorem logDeriv_xiF_conj (s : ℂ) : logDeriv xiF (starRingEnd ℂ s) = starRingEnd ℂ (logDeriv xiF s) := by
  have hf : (starRingEnd ℂ ∘ xiF ∘ starRingEnd ℂ) = xiF := by
    funext w; simp [Function.comp, xiF_conj]
  have hd := deriv_conj_conj (f := xiF)
  rw [hf] at hd
  have h2 : deriv xiF (starRingEnd ℂ s) = starRingEnd ℂ (deriv xiF s) := by
    rw [congrFun hd (starRingEnd ℂ s)]; simp [Function.comp]
  rw [logDeriv_apply, logDeriv_apply, h2, xiF_conj, map_div₀]

end TernaryGoldbach.Explicit
end

-- RSBounds.BacklundCountDefinitions
section
open Complex MeasureTheory Set
open scoped Real Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundCountIdentity
open TernaryGoldbach.Explicit

noncomputable def riemannSiegelTheta (T : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..(T / 2), (Complex.digamma (1 / 4 + t * I)).re) -
    T / 2 * Real.log Real.pi

noncomputable def arcVariation (f : ℂ → ℂ) (a T : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..T, (logDeriv f ((a : ℂ) + t * I)).re) -
    ∫ σ in (1 / 2 : ℝ)..a, (logDeriv f ((σ : ℂ) + T * I)).im

noncomputable def zetaArgVar (T : ℝ) : ℝ := arcVariation riemannZeta (5 / 4) T
noncomputable def xiArcVar (T : ℝ) : ℝ := arcVariation xiF (5 / 4) T

def zetaGoodHeight (T : ℝ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.im ≠ T

noncomputable def positiveZeros (T : ℝ) : Finset ℂ :=
  (zerosIn xiF 2 (RT T) (RT T / 2)).filter (fun ρ => 0 < ρ.im ∧ ρ.im < T)

noncomputable def N (T : ℝ) : ℕ :=
  ∑ ρ ∈ positiveZeros T, multRectD xiF T ρ

end TernaryGoldbach.RSBounds.BacklundCountIdentity
end

-- RSBounds.BacklundCountRealAxis
section
open Complex MeasureTheory Set Filter
open scoped Real Topology

namespace TernaryGoldbach.RSBounds.BacklundCountIdentity
open TernaryGoldbach.Explicit

theorem re_zetaF_real_ge {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    x ≤ (zetaF (x : ℂ)).re := by
  have hs : 0 < (x : ℂ).re := hx0
  rw [zetaF_eq hs]
  have hI : (Izeta (x : ℂ)).re ≤ 0 := by
    unfold Izeta
    have hint := integrableOn_saw_integrand hs
    rw [show (∫ t in Ioi (1 : ℝ), saw t * (t : ℂ) ^ (-((x : ℂ) + 1))).re =
        RCLike.re (∫ t in Ioi (1 : ℝ), saw t * (t : ℂ) ^ (-((x : ℂ) + 1))) from rfl,
      ← integral_re hint]
    refine setIntegral_nonpos measurableSet_Ioi fun t (ht : 1 < t) => ?_
    have he : (t : ℂ) ^ (-((x : ℂ) + 1)) = ((t ^ (-(x + 1)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by linarith)]
      push_cast
      rfl
    rw [show RCLike.re (saw t * (t : ℂ) ^ (-((x : ℂ) + 1))) =
        (saw t * (t : ℂ) ^ (-((x : ℂ) + 1))).re from rfl,
      he, saw, Complex.re_mul_ofReal]
    simp only [Complex.sub_re, Complex.ofReal_re]
    have hfloor : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
    have hp : 0 < t ^ (-(x + 1)) := Real.rpow_pos_of_pos (by linarith) _
    nlinarith
  simp only [add_re, mul_re, mul_im, ofReal_re, ofReal_im, sub_re, sub_im, one_re, one_im,
    sub_zero, sub_self, mul_zero, zero_mul, sub_zero, add_zero]
  have hc : x * (x - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx0.le (by linarith)
  nlinarith [mul_nonneg_of_nonpos_of_nonpos hc hI]

theorem xiF_ne_zero_real (x : ℝ) : xiF (x : ℂ) ≠ 0 := by
  by_cases hx0 : x ≤ 0
  · exact xiF_ne_zero_of_re_nonpos hx0
  by_cases hx1 : 1 ≤ x
  · exact xiF_ne_zero_of_one_le_re hx1
  have hx0' : 0 < x := lt_of_not_ge hx0
  have hx1' : x < 1 := lt_of_not_ge hx1
  have hxne1 : (x : ℂ) ≠ 1 := by exact_mod_cast (ne_of_lt hx1')
  rw [xiF_eq hx0' hxne1]
  apply mul_ne_zero (mul_ne_zero (by exact_mod_cast hx0'.ne')
    (Gammaℝ_ne_zero_of_re_pos hx0'))
  intro hz
  have hh := re_zetaF_real_ge hx0' hx1'
  rw [hz] at hh
  simp only [zero_re] at hh
  linarith

theorem xiF_zero_re_strip {ρ : ℂ} (hρ : xiF ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  constructor
  · by_contra h
    exact xiF_ne_zero_of_re_nonpos (not_lt.mp h) hρ
  · by_contra h
    exact xiF_ne_zero_of_one_le_re (not_lt.mp h) hρ

theorem xiF_ne_zero_of_goodHeight {T : ℝ} (hg : zetaGoodHeight T)
    {s : ℂ} (hs : s.im = T) : xiF s ≠ 0 := by
  intro hz
  have hstrip := xiF_zero_re_strip hz
  exact hg s ((xiF_eq_zero_iff hstrip.1 hstrip.2).mp hz) hs

end TernaryGoldbach.RSBounds.BacklundCountIdentity
end

-- RSBounds.BacklundCountRectangle
section
open Complex MeasureTheory Set Filter Metric
open scoped Real Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundCountIdentity
open TernaryGoldbach.Explicit

noncomputable def lowerCorner : ℂ := -1 / 4
noncomputable def upperCorner (T : ℝ) : ℂ := 5 / 4 + T * I

@[simp] theorem lowerCorner_re : lowerCorner.re = -1 / 4 := by norm_num [lowerCorner]
@[simp] theorem lowerCorner_im : lowerCorner.im = 0 := by norm_num [lowerCorner]
@[simp] theorem upperCorner_re (T : ℝ) : (upperCorner T).re = 5 / 4 := by simp [upperCorner]
@[simp] theorem upperCorner_im (T : ℝ) : (upperCorner T).im = T := by simp [upperCorner]

theorem xi_analyticOrderAt_ne_top (ρ : ℂ) : analyticOrderAt xiF ρ ≠ ⊤ := by
  have h2 : xiF 2 ≠ 0 := xiF_ne_zero_of_one_le_re (by norm_num)
  have hc : analyticOrderAt xiF 2 ≠ ⊤ := by
    rw [(differentiable_xiF.analyticAt 2).analyticOrderAt_eq_zero.mpr h2]
    simp
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
    (fun z _ => differentiable_xiF.analyticAt z : AnalyticOnNhd ℂ xiF univ)
    isPreconnected_univ (mem_univ 2) (mem_univ ρ) hc

theorem mem_positiveZeros_iff {T : ℝ} (hT : 0 < T) {ρ : ℂ} :
    ρ ∈ positiveZeros T ↔ xiF ρ = 0 ∧ 0 < ρ.im ∧ ρ.im < T := by
  classical
  constructor
  · intro h
    obtain ⟨hz, him0, himT⟩ := Finset.mem_filter.mp h
    exact ⟨eq_zero_of_mem_zerosIn differentiable_xiF hz, him0, himT⟩
  · rintro ⟨hz, him0, himT⟩
    have hre := xiF_zero_re_strip hz
    have hnorm : ‖ρ - 2‖ < RT T / 2 := by
      refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
      simp only [sub_re, sub_im]
      norm_num only [re_ofNat, im_ofNat, sub_zero]
      rw [abs_of_neg (by linarith : ρ.re - 2 < 0), abs_of_pos him0]
      unfold RT
      linarith
    have hρR : ρ ∈ closedBall (2 : ℂ) (RT T) := by
      rw [mem_closedBall, dist_eq_norm]
      unfold RT at *
      linarith
    have han : AnalyticOnNhd ℂ xiF (closedBall 2 (RT T)) :=
      fun z _ => differentiable_xiF.analyticAt z
    have hdiv : divB xiF 2 (RT T) ρ ≠ 0 := by
      rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply han hρR]
      have horder : analyticOrderAt xiF ρ ≠ 0 := by
        rw [Ne, (differentiable_xiF.analyticAt ρ).analyticOrderAt_eq_zero]
        exact not_not.mpr hz
      have hfinite := xi_analyticOrderAt_ne_top ρ
      cases ho : analyticOrderAt xiF ρ with
      | top => exact absurd ho hfinite
      | coe n => simpa [ho] using horder
    rw [positiveZeros, Finset.mem_filter, zerosIn, Finset.mem_filter,
      Set.Finite.mem_toFinset, Function.mem_support]
    exact ⟨⟨hdiv, hnorm⟩, him0, himT⟩

theorem mult_positiveZeros_eq_analyticOrder {T : ℝ} (hT : 0 < T) {ρ : ℂ}
    (hρ : ρ ∈ positiveZeros T) :
    multRectD xiF T ρ = (analyticOrderAt xiF ρ).toNat := by
  have hz := (Finset.mem_filter.mp hρ).1
  have hnorm := (mem_zerosIn hz).1
  have hρR : ρ ∈ closedBall (2 : ℂ) (RT T) := by
    rw [mem_closedBall, dist_eq_norm]
    unfold RT at *
    linarith
  rw [multRectD, divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
    (fun z _ => differentiable_xiF.analyticAt z : AnalyticOnNhd ℂ xiF (closedBall 2 (RT T))) hρR]
  cases ho : analyticOrderAt xiF ρ <;> simp

theorem N_eq_sum_analyticOrder {T : ℝ} (hT : 0 < T) :
    N T = ∑ ρ ∈ positiveZeros T, (analyticOrderAt xiF ρ).toNat := by
  unfold N
  exact Finset.sum_congr rfl (fun ρ hρ => mult_positiveZeros_eq_analyticOrder hT hρ)

theorem rectangle_filter_eq_positiveZeros {T : ℝ} (hT : 0 < T) :
    (zerosIn xiF 2 (RT T) (RT T / 2)).filter
      (fun ρ => lowerCorner.re < ρ.re ∧ ρ.re < (upperCorner T).re ∧
        lowerCorner.im < ρ.im ∧ ρ.im < (upperCorner T).im) = positiveZeros T := by
  classical
  apply Finset.ext
  intro ρ
  simp only [Finset.mem_filter, lowerCorner_re, lowerCorner_im, upperCorner_re,
    upperCorner_im, positiveZeros]
  constructor
  · rintro ⟨hz, _, _, h0, hT⟩
    exact ⟨hz, h0, hT⟩
  · rintro ⟨hz, h0, hT⟩
    have hre := xiF_zero_re_strip (eq_zero_of_mem_zerosIn differentiable_xiF hz)
    exact ⟨hz, by linarith [hre.1], by linarith [hre.2], h0, hT⟩

theorem noZerosOnSides_xi {T : ℝ} (hg : zetaGoodHeight T) :
    NoZerosOnSides xiF lowerCorner (upperCorner T) := by
  unfold NoZerosOnSides
  simp only [lowerCorner_re, lowerCorner_im, upperCorner_re, upperCorner_im,
    ofReal_zero, zero_mul, add_zero]
  refine ⟨fun x _ => xiF_ne_zero_real x, ?_, ?_, ?_⟩
  · intro x _
    exact xiF_ne_zero_of_goodHeight hg (by simp)
  · intro y _
    exact xiF_ne_zero_of_one_le_re (by norm_num)
  · intro y _
    exact xiF_ne_zero_of_re_nonpos (by norm_num)

theorem rectangle_count_identity {T : ℝ} (hT : 0 < T) (hg : zetaGoodHeight T) :
    rectInt (logDeriv xiF) lowerCorner (upperCorner T) =
      2 * Real.pi * I * (N T : ℂ) := by
  have hR : 0 < RT T := by unfold RT; linarith
  have hrect : [[lowerCorner.re, (upperCorner T).re]] ×ℂ
      [[lowerCorner.im, (upperCorner T).im]] ⊆ ball 2 (RT T / 2) := by
    intro s hs
    rw [mem_reProdIm, lowerCorner_re, lowerCorner_im, upperCorner_re, upperCorner_im,
      Set.uIcc_of_le (by norm_num : (-1 / 4 : ℝ) ≤ 5 / 4),
      Set.uIcc_of_le hT.le] at hs
    rw [mem_ball, dist_eq_norm]
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    simp only [sub_re, sub_im]
    norm_num only [re_ofNat, im_ofNat, sub_zero]
    rw [abs_of_neg (by linarith [hs.1.2] : s.re - 2 < 0), abs_of_nonneg hs.2.1]
    unfold RT
    linarith [hs.1.1, hs.2.2]
  have hh := rectInt_logDeriv_mul differentiable_xiF hR
    (xiF_ne_zero_of_one_le_re (by norm_num : 1 ≤ (2 : ℂ).re))
    (by norm_num : lowerCorner.re < (upperCorner T).re)
    (by simpa using hT : lowerCorner.im < (upperCorner T).im)
    hrect (noZerosOnSides_xi hg) isOpen_univ (subset_univ _)
    (differentiableOn_const (c := (1 : ℂ)))
  simp only [mul_one] at hh
  rw [rectangle_filter_eq_positiveZeros hT] at hh
  simpa only [N, Nat.cast_sum, multRectD] using hh

end TernaryGoldbach.RSBounds.BacklundCountIdentity
end

-- RSBounds.BacklundCountHalving
section
open Complex MeasureTheory Set Filter
open scoped Real Topology Interval ComplexConjugate

namespace TernaryGoldbach.RSBounds.BacklundCountIdentity
open TernaryGoldbach.Explicit

theorem continuous_logDeriv_xi_vertical :
    Continuous (fun t : ℝ => logDeriv xiF ((5 / 4 : ℂ) + t * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply ContinuousAt.comp (f := fun t : ℝ => (5 / 4 : ℂ) + t * I)
  · exact continuousAt_logDeriv_xiF (xiF_ne_zero_of_one_le_re (by norm_num))
  · fun_prop

theorem continuous_logDeriv_xi_horizontal {T : ℝ} (hg : zetaGoodHeight T) :
    Continuous (fun σ : ℝ => logDeriv xiF ((σ : ℂ) + T * I)) := by
  rw [continuous_iff_continuousAt]
  intro σ
  apply ContinuousAt.comp (f := fun σ : ℝ => (σ : ℂ) + T * I)
  · exact continuousAt_logDeriv_xiF (xiF_ne_zero_of_goodHeight hg (by simp))
  · fun_prop

private theorem logDeriv_xi_reflect (σ T : ℝ) :
    logDeriv xiF (((1 - σ : ℝ) : ℂ) + T * I) =
      -conj (logDeriv xiF ((σ : ℂ) + T * I)) := by
  have he : (((1 - σ : ℝ) : ℂ) + T * I) = 1 - conj ((σ : ℂ) + T * I) := by
    apply Complex.ext <;> simp
  rw [he, logDeriv_xiF_one_sub, logDeriv_xiF_conj]

theorem im_rectangle_eq_two_xiArcVar {T : ℝ} (hg : zetaGoodHeight T) :
    (rectInt (logDeriv xiF) lowerCorner (upperCorner T)).im = 2 * xiArcVar T := by
  set F := logDeriv xiF
  set A : ℂ := ∫ σ in (1 / 2 : ℝ)..(5 / 4), F ((σ : ℂ) + T * I)
  set B : ℂ := ∫ t in (0 : ℝ)..T, F ((5 / 4 : ℂ) + t * I)
  have ht : ∀ a b : ℝ, IntervalIntegrable
      (fun σ : ℝ => F ((σ : ℂ) + T * I)) volume a b :=
    (continuous_logDeriv_xi_horizontal hg).intervalIntegrable
  have hv := continuous_logDeriv_xi_vertical.intervalIntegrable (μ := volume) (0 : ℝ) T
  have hbottom : (∫ x in (-1 / 4 : ℝ)..(5 / 4), F (x : ℂ)).im = 0 := by
    have hc : conj (∫ x in (-1 / 4 : ℝ)..(5 / 4), F (x : ℂ)) =
        ∫ x in (-1 / 4 : ℝ)..(5 / 4), F (x : ℂ) := by
      rw [← intervalIntegral.intervalIntegral_conj]
      apply intervalIntegral.integral_congr
      intro x _
      exact (logDeriv_xiF_conj (x : ℂ)).symm.trans (by simp [F])
    have hh := congrArg Complex.im hc
    simp only [conj_im] at hh
    linarith
  have hleft : (∫ t in (0 : ℝ)..T, F ((-1 / 4 : ℂ) + t * I)) = -conj B := by
    rw [← intervalIntegral.intervalIntegral_conj, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    simpa only [show (1 : ℝ) - 5 / 4 = -1 / 4 by norm_num, ofReal_div,
      ofReal_neg, ofReal_one, ofReal_ofNat] using logDeriv_xi_reflect (5 / 4) t
  have htopLeft : (∫ σ in (-1 / 4 : ℝ)..(1 / 2), F ((σ : ℂ) + T * I)) =
      -conj A := by
    have hs := intervalIntegral.integral_comp_sub_left
      (a := (1 / 2 : ℝ)) (b := 5 / 4)
      (fun σ : ℝ => F ((σ : ℂ) + T * I)) 1
    rw [show (1 : ℝ) - 5 / 4 = -1 / 4 by norm_num,
      show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hs
    rw [← hs, ← intervalIntegral.intervalIntegral_conj, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro σ _
    exact logDeriv_xi_reflect σ T
  have htop : (∫ σ in (-1 / 4 : ℝ)..(5 / 4), F ((σ : ℂ) + T * I)) =
      A - conj A := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (ht (-1 / 4) (1 / 2))
      (ht (1 / 2) (5 / 4)), htopLeft]
    change -conj A + A = A - conj A
    ring
  have hAim : A.im = ∫ σ in (1 / 2 : ℝ)..(5 / 4),
      (F ((σ : ℂ) + T * I)).im := by
    exact (Complex.imCLM.intervalIntegral_comp_comm (ht (1 / 2) (5 / 4))).symm
  have hBre : B.re = ∫ t in (0 : ℝ)..T, (F ((5 / 4 : ℂ) + t * I)).re := by
    exact (Complex.reCLM.intervalIntegral_comp_comm hv).symm
  unfold rectInt
  simp only [lowerCorner_re, lowerCorner_im, upperCorner_re, upperCorner_im,
    ofReal_zero, zero_mul, add_zero, smul_eq_mul,
    ofReal_div, ofReal_neg, ofReal_one, ofReal_ofNat]
  change ((∫ x in (-1 / 4 : ℝ)..(5 / 4), F (x : ℂ)) -
      (∫ x in (-1 / 4 : ℝ)..(5 / 4), F ((x : ℂ) + T * I)) +
      I * B - I * (∫ t in (0 : ℝ)..T, F ((-1 / 4 : ℂ) + t * I))).im = _
  rw [htop, hleft]
  simp only [sub_im, add_im, I_mul_im, neg_re, conj_re, conj_im, hbottom]
  unfold xiArcVar arcVariation
  norm_num only [ofReal_div, ofReal_ofNat]
  rw [← hBre, ← hAim]
  ring

theorem pi_mul_N_eq_xiArcVar {T : ℝ} (hT : 0 < T) (hg : zetaGoodHeight T) :
    Real.pi * (N T : ℝ) = xiArcVar T := by
  have hr := congrArg Complex.im (rectangle_count_identity hT hg)
  rw [im_rectangle_eq_two_xiArcVar hg] at hr
  simp only [mul_im, mul_re, ofReal_re, ofReal_im, natCast_re, natCast_im,
    I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero, zero_add] at hr
  norm_num at hr
  linarith

end TernaryGoldbach.RSBounds.BacklundCountIdentity
end

-- RSBounds.BacklundCountMultiplicity
section
open Complex MeasureTheory Set Filter
open scoped Real Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundCountIdentity
open TernaryGoldbach.Explicit

theorem xiF_eq_zero_of_zeta_zero {ρ : ℂ} (him : ρ.im ≠ 0)
    (hz : riemannZeta ρ = 0) : xiF ρ = 0 := by
  have hρ0 : ρ ≠ 0 := by intro h; apply him; simp [h]
  have hρ1 : ρ ≠ 1 := by intro h; apply him; simp [h]
  have hG : Gammaℝ ρ ≠ 0 := by
    intro h
    obtain ⟨m, hm⟩ := Gammaℝ_eq_zero_iff.mp h
    apply him
    rw [hm]
    simp
  have hΛ : completedRiemannZeta ρ = 0 := by
    rw [riemannZeta_def_of_ne_zero hρ0] at hz
    exact (div_eq_zero_iff.mp hz).resolve_right hG
  have he : completedRiemannZeta₀ ρ = completedRiemannZeta ρ +
      1 / ρ + 1 / (1 - ρ) := by
    rw [completedRiemannZeta_eq]
    ring
  rw [xiF, he, hΛ]
  have h1 : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr hρ1.symm
  field_simp
  ring

theorem mem_positiveZeros_iff_zeta {T : ℝ} (hT : 0 < T) {ρ : ℂ} :
    ρ ∈ positiveZeros T ↔ riemannZeta ρ = 0 ∧ 0 < ρ.im ∧ ρ.im < T := by
  rw [mem_positiveZeros_iff hT]
  constructor
  · rintro ⟨hz, h0, hT⟩
    have hre := xiF_zero_re_strip hz
    exact ⟨(xiF_eq_zero_iff hre.1 hre.2).mp hz, h0, hT⟩
  · rintro ⟨hz, h0, hT⟩
    exact ⟨xiF_eq_zero_of_zeta_zero h0.ne' hz, h0, hT⟩

theorem analyticOrderAt_xi_eq_zeta {ρ : ℂ} (hρ : xiF ρ = 0) :
    analyticOrderAt xiF ρ = analyticOrderAt riemannZeta ρ := by
  have hre := xiF_zero_re_strip hρ
  have hρ0 : ρ ≠ 0 := by intro h; simp [h] at hre
  have hρ1 : ρ ≠ 1 := by intro h; simp [h] at hre
  have hloc : xiF =ᶠ[𝓝 ρ] fun s => (s * Gammaℝ s * (s - 1)) * riemannZeta s := by
    have hu : {s : ℂ | 0 < s.re ∧ s ≠ 1} ∈ 𝓝 ρ :=
      ((isOpen_lt (continuous_const (y := (0 : ℝ))) Complex.continuous_re).inter
        (isOpen_ne (x := (1 : ℂ)))).mem_nhds
        (show ρ ∈ {b : ℂ | 0 < b.re} ∩ {y : ℂ | y ≠ 1} from ⟨hre.1, hρ1⟩)
    filter_upwards [hu] with s hs
    rw [xiF_eq hs.1 hs.2, zetaF_of_ne hs.2]
    ring
  have hGamma : AnalyticAt ℂ Gammaℝ ρ := by
    apply DifferentiableOn.analyticOnNhd (s := {s : ℂ | 0 < s.re}) _
      (isOpen_lt continuous_const Complex.continuous_re) ρ hre.1
    intro s hs
    change 0 < s.re at hs
    have hm : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
      intro m h
      have hr := congrArg Complex.re h
      simp at hr
      have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hd : DifferentiableAt ℂ
        (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)) s :=
      (DifferentiableAt.const_cpow (by fun_prop) (Or.inl hpi)).mul
        ((Complex.differentiableAt_Gamma _ hm).comp s (differentiableAt_id.div_const 2))
    exact hd.differentiableWithinAt
  have he : AnalyticAt ℂ (fun s : ℂ => s * Gammaℝ s * (s - 1)) ρ :=
    (analyticAt_id.mul hGamma).mul (analyticAt_id.sub analyticAt_const)
  have hen : ρ * Gammaℝ ρ * (ρ - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hρ0 (Gammaℝ_ne_zero_of_re_pos hre.1)) (sub_ne_zero.mpr hρ1)
  rw [analyticOrderAt_congr hloc,
    show (fun s : ℂ => (s * Gammaℝ s * (s - 1)) * riemannZeta s) =
      (fun s : ℂ => s * Gammaℝ s * (s - 1)) * riemannZeta from rfl,
    analyticOrderAt_mul he (analyticOn_riemannZeta ρ hρ1),
    he.analyticOrderAt_eq_zero.mpr hen, zero_add]

theorem N_eq_sum_zetaMultiplicity {T : ℝ} (hT : 0 < T) :
    N T = ∑ ρ ∈ positiveZeros T, (analyticOrderAt riemannZeta ρ).toNat := by
  rw [N_eq_sum_analyticOrder hT]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [analyticOrderAt_xi_eq_zeta ((mem_positiveZeros_iff hT).mp hρ).1]

end TernaryGoldbach.RSBounds.BacklundCountIdentity
end

-- RSBounds.BacklundCountPole
section
open Complex MeasureTheory Set
open scoped Real Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundCountIdentity

noncomputable def poleKernel (s : ℂ) : ℂ := 1 / s + 1 / (s - 1)

theorem integral_re_inv_vertical {b : ℝ} (hb : 0 < b) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, (1 / ((b : ℂ) + t * I)).re) = Real.arctan (T / b) := by
  have hpt (t : ℝ) : (1 / ((b : ℂ) + t * I)).re = b / (b ^ 2 + t ^ 2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    simp
    ring_nf
  simp_rw [hpt]
  have hd : ∀ t ∈ [[(0 : ℝ), T]], HasDerivAt (fun t : ℝ => Real.arctan (t / b))
      (b / (b ^ 2 + t ^ 2)) t := by
    intro t _
    have hh := (Real.hasDerivAt_arctan (t / b)).comp t ((hasDerivAt_id t).div_const b)
    change HasDerivAt (fun u : ℝ => Real.arctan (u / b))
      ((1 / (1 + (t / b) ^ 2)) * (1 / b)) t at hh
    apply hh.congr_deriv
    field_simp <;> ring
  have hc : Continuous (fun t : ℝ => b / (b ^ 2 + t ^ 2)) :=
    continuous_const.div (g := fun t : ℝ => b ^ 2 + t ^ 2) (by fun_prop) (fun _ => by positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  simp

theorem integral_re_pole_vertical {a : ℝ} (ha : 1 < a) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, (poleKernel ((a : ℂ) + t * I)).re) =
      Real.arctan (T / a) + Real.arctan (T / (a - 1)) := by
  have he (t : ℝ) : ((a : ℂ) + t * I) - 1 = ((a - 1 : ℝ) : ℂ) + t * I := by
    push_cast
    ring
  have hc (b : ℝ) (hb : 0 < b) : Continuous (fun t : ℝ => (1 / ((b : ℂ) + t * I)).re) := by
    apply Complex.continuous_re.comp
    apply continuous_const.div (g := fun t : ℝ => (b : ℂ) + t * I) (by fun_prop)
    intro t h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  simp only [poleKernel, add_im, add_re, he]
  rw [intervalIntegral.integral_add ((hc a (by linarith)).intervalIntegrable _ _)
    ((hc (a - 1) (by linarith)).intervalIntegrable _ _),
    integral_re_inv_vertical (by linarith), integral_re_inv_vertical (by linarith)]

theorem integral_im_pole_horizontal {T : ℝ} (hT : 0 < T) (a : ℝ) :
    (∫ σ in (1 / 2 : ℝ)..a, (poleKernel ((σ : ℂ) + T * I)).im) =
      -(Real.arctan (a / T) + Real.arctan ((a - 1) / T)) := by
  have hpt (σ : ℝ) : (poleKernel ((σ : ℂ) + T * I)).im =
      -(T / (σ ^ 2 + T ^ 2)) - T / ((σ - 1) ^ 2 + T ^ 2) := by
    rw [poleKernel, add_im, one_div, one_div, inv_im, inv_im, normSq_apply, normSq_apply]
    simp
    ring_nf
  simp_rw [hpt]
  have hd : ∀ σ ∈ [[(1 / 2 : ℝ), a]],
      HasDerivAt (fun u : ℝ => -Real.arctan (u / T) - Real.arctan ((u - 1) / T))
        (-(T / (σ ^ 2 + T ^ 2)) - T / ((σ - 1) ^ 2 + T ^ 2)) σ := by
    intro σ _
    have h1 := (Real.hasDerivAt_arctan (σ / T)).comp σ ((hasDerivAt_id σ).div_const T)
    have h2 := (Real.hasDerivAt_arctan ((σ - 1) / T)).comp σ
      (((hasDerivAt_id σ).sub_const 1).div_const T)
    have hh : HasDerivAt (fun u : ℝ => -Real.arctan (u / T) - Real.arctan ((u - 1) / T))
        (-(1 / (1 + (σ / T) ^ 2) * (1 / T)) -
          (1 / (1 + ((σ - 1) / T) ^ 2) * (1 / T))) σ := h1.neg.sub h2
    apply hh.congr_deriv
    field_simp
    ring
  have hc : Continuous (fun σ : ℝ => -(T / (σ ^ 2 + T ^ 2)) -
      T / ((σ - 1) ^ 2 + T ^ 2)) := by
    have c1 : Continuous (fun σ : ℝ => T / (σ ^ 2 + T ^ 2)) :=
      continuous_const.div (g := fun σ : ℝ => σ ^ 2 + T ^ 2) (by fun_prop) (fun _ => by positivity)
    have c2 : Continuous (fun σ : ℝ => T / ((σ - 1) ^ 2 + T ^ 2)) :=
      continuous_const.div (g := fun σ : ℝ => (σ - 1) ^ 2 + T ^ 2) (by fun_prop)
        (fun _ => by positivity)
    exact c1.neg.sub c2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  rw [show ((1 : ℝ) / 2 - 1) / T = -((1 / 2) / T) by ring, Real.arctan_neg]
  ring

theorem pole_arc_eq_pi {a T : ℝ} (ha : 1 < a) (hT : 0 < T) :
    (∫ t in (0 : ℝ)..T, (poleKernel ((a : ℂ) + t * I)).re) -
      (∫ σ in (1 / 2 : ℝ)..a, (poleKernel ((σ : ℂ) + T * I)).im) = Real.pi := by
  rw [integral_re_pole_vertical ha, integral_im_pole_horizontal hT]
  have h1 := Real.arctan_inv_of_pos (show 0 < T / a by positivity)
  have h2 := Real.arctan_inv_of_pos (show 0 < T / (a - 1) by positivity)
  rw [inv_div] at h1 h2
  linarith

end TernaryGoldbach.RSBounds.BacklundCountIdentity
end

-- RSBounds.BacklundGammaPhaseBase
section
open Complex Real MeasureTheory intervalIntegral
open scoped Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundGammaPhase

noncomputable def phaseIntegral (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..(T / 2), (Complex.digamma (1 / 4 + t * Complex.I)).re

theorem differentiableAt_digamma {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.digamma z :=
  (GammaSolution.analyticOnNhd_digamma z hz).differentiableAt

theorem digamma_ofReal_im_zero {x : ℝ} (hx : 0 < x) :
    (Complex.digamma (x : ℂ)).im = 0 := by
  rw [GammaSolution.digamma_ofReal hx]
  rfl

theorem continuous_digamma_line {a : ℝ} (ha : 0 < a) :
    Continuous (fun t : ℝ ↦ Complex.digamma (((a : ℂ) + t * I) / 2)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hp : 0 < (((a : ℂ) + t * I) / 2).re := by
    simp [Complex.div_ofNat_re]
    positivity
  exact ContinuousAt.comp (g := Complex.digamma)
    (f := fun t : ℝ ↦ ((a : ℂ) + t * I) / 2) (x := t)
    (differentiableAt_digamma hp).continuousAt (by fun_prop)

theorem continuousOn_digamma_horizontal (T : ℝ) :
    ContinuousOn (fun a : ℝ ↦ Complex.digamma (((a : ℂ) + T * I) / 2))
      (Set.Ioi 0) := by
  intro a ha
  change 0 < a at ha
  have hp : 0 < (((a : ℂ) + T * I) / 2).re := by
    simpa [Complex.div_ofNat_re] using div_pos ha (by norm_num : (0 : ℝ) < 2)
  exact (ContinuousAt.comp (g := Complex.digamma)
    (f := fun a : ℝ ↦ ((a : ℂ) + T * I) / 2) (x := a)
    (differentiableAt_digamma hp).continuousAt (by fun_prop)).continuousWithinAt

private theorem integral_im {f : ℝ → ℂ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    (∫ t in a..b, f t).im = ∫ t in a..b, (f t).im := by
  exact (Complex.imCLM.intervalIntegral_comp_comm hf).symm

private theorem integral_re {f : ℝ → ℂ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    (∫ t in a..b, f t).re = ∫ t in a..b, (f t).re := by
  exact (Complex.reCLM.intervalIntegral_comp_comm hf).symm

theorem digamma_rectangle {a : ℝ} (ha : 1 / 2 ≤ a) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, (Complex.digamma (((a : ℂ) + t * I) / 2)).re) -
      (∫ σ in (1 / 2 : ℝ)..a, (Complex.digamma (((σ : ℂ) + T * I) / 2)).im) =
      2 * phaseIntegral T := by
  let f : ℂ → ℂ := fun s ↦ Complex.digamma (s / 2)
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have ha0 : 0 < a := hhalf.trans_le ha
  have hc : Set.uIcc (1 / 2 : ℝ) a = Set.Icc (1 / 2 : ℝ) a := Set.uIcc_of_le ha
  have hdiff : DifferentiableOn ℂ f
      (Set.uIcc ((1 / 2 : ℂ).re) (((a : ℂ) + T * I).re) ×ℂ
        Set.uIcc ((1 / 2 : ℂ).im) (((a : ℂ) + T * I).im)) := by
    intro s hs
    rw [Complex.mem_reProdIm] at hs
    have hre : 1 / 2 ≤ s.re := by
      have hsr : s.re ∈ Set.uIcc (1 / 2 : ℝ) a := by simpa using hs.1
      rw [hc] at hsr
      exact hsr.1
    have hp : 0 < (s / 2).re := by
      rw [Complex.div_ofNat_re]
      linarith
    exact ((differentiableAt_digamma hp).comp s
      (differentiableAt_id.div_const 2)).differentiableWithinAt
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    f (1 / 2 : ℂ) ((a : ℂ) + T * I) hdiff
  have hsub : Set.uIcc (1 / 2 : ℝ) a ⊆ Set.Ioi 0 := by
    intro t ht
    rw [hc] at ht
    exact hhalf.trans_le ht.1
  have htop : IntervalIntegrable (fun σ : ℝ ↦ f ((σ : ℂ) + T * I)) volume (1 / 2) a :=
    ((continuousOn_digamma_horizontal T).mono hsub).intervalIntegrable
  have hbot : IntervalIntegrable (fun σ : ℝ ↦ f ((σ : ℂ) + (0 : ℂ) * I))
      volume (1 / 2) a :=
    ((continuousOn_digamma_horizontal 0).mono hsub).intervalIntegrable
  have hright : IntervalIntegrable (fun t : ℝ ↦ f ((a : ℂ) + t * I)) volume 0 T :=
    (continuous_digamma_line ha0).intervalIntegrable 0 T
  have hleft : IntervalIntegrable (fun t : ℝ ↦ f ((1 / 2 : ℂ) + t * I)) volume 0 T :=
    by simpa [f] using (continuous_digamma_line hhalf).intervalIntegrable 0 T
  have him := congrArg Complex.im hrect
  simp only [Complex.div_ofNat_re, Complex.one_re, Complex.div_ofNat_im,
    Complex.one_im, zero_div, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
    Complex.ofReal_im, sub_zero, Complex.add_im, Complex.mul_I_im, zero_add,
    neg_zero, add_zero] at him
  norm_num only [Complex.ofReal_zero, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] at him
  rw [Complex.sub_im, Complex.add_im, Complex.sub_im, Complex.zero_im,
    smul_eq_mul, smul_eq_mul, Complex.I_mul_im, Complex.I_mul_im,
    integral_im hbot, integral_im htop, integral_re hright, integral_re hleft] at him
  have hbot0 : (∫ σ in (1 / 2 : ℝ)..a, (f ((σ : ℂ) + (0 : ℂ) * I)).im) = 0 := by
    calc
      _ = ∫ _σ in (1 / 2 : ℝ)..a, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro σ hσ
        have hσ0 : 0 < σ := hsub hσ
        have he : ((σ : ℂ) + (0 : ℂ) * I) / 2 = ((σ / 2 : ℝ) : ℂ) := by
          push_cast
          ring
        dsimp [f]
        rw [he]
        exact digamma_ofReal_im_zero (by positivity)
      _ = 0 := by simp
  rw [hbot0] at him
  have hl : (∫ t in (0 : ℝ)..T, (f ((1 / 2 : ℂ) + t * I)).re) =
      2 * phaseIntegral T := by
    have he : (fun t : ℝ ↦ (f ((1 / 2 : ℂ) + t * I)).re) =
        (fun t : ℝ ↦ (Complex.digamma (1 / 4 + (t / 2 : ℝ) * I)).re) := by
      funext t
      dsimp [f]
      congr 2
      push_cast
      ring
    rw [he, intervalIntegral.integral_comp_div
      (fun u : ℝ ↦ (Complex.digamma (1 / 4 + u * I)).re) (two_ne_zero)]
    simp [phaseIntegral, smul_eq_mul]
  rw [hl] at him
  dsimp [f] at him
  linarith

end TernaryGoldbach.RSBounds.BacklundGammaPhase
end

-- RSBounds.BacklundCountIdentity
section
open Complex MeasureTheory Set Filter
open scoped Real Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundCountIdentity
open TernaryGoldbach.Explicit

private theorem continuousAt_logDeriv_zeta {s : ℂ} (hs : s ≠ 1)
    (hz : riemannZeta s ≠ 0) : ContinuousAt (logDeriv riemannZeta) s := by
  have ha : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs
  exact ha.deriv.continuousAt.div ha.continuousAt hz

private theorem continuous_zeta_vertical :
    Continuous (fun t : ℝ => logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply ContinuousAt.comp (f := fun t : ℝ => (5 / 4 : ℂ) + t * I)
  · apply continuousAt_logDeriv_zeta
    · intro h
      have hh := congrArg Complex.re h
      norm_num at hh
    · exact riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  · fun_prop

private theorem continuous_zeta_horizontal {T : ℝ} (hT : 0 < T) (hg : zetaGoodHeight T) :
    Continuous (fun σ : ℝ => logDeriv riemannZeta ((σ : ℂ) + T * I)) := by
  rw [continuous_iff_continuousAt]
  intro σ
  apply ContinuousAt.comp (f := fun σ : ℝ => (σ : ℂ) + T * I)
  · apply continuousAt_logDeriv_zeta
    · intro h
      have hh := congrArg Complex.im h
      simp at hh
      linarith
    · intro hz
      exact hg _ hz (by simp)
  · fun_prop

theorem logDeriv_xi_factorization {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s ≠ 0) :
    logDeriv xiF s = poleKernel s - (Real.log Real.pi : ℂ) / 2 +
      (1 / 2 : ℂ) * Complex.digamma (s / 2) + logDeriv riemannZeta s := by
  have hx : xiF s ≠ 0 := by
    rw [xiF_eq hs hs1, zetaF_of_ne hs1]
    apply mul_ne_zero
    · apply mul_ne_zero
      · intro h
        simp [h] at hs
      · exact Gammaℝ_ne_zero_of_re_pos hs
    · exact mul_ne_zero (sub_ne_zero.mpr hs1) hz
  rw [logDeriv_xiF hs hs1 hx, logDeriv_zetaF_eq hs1 hz,
    ← Complex.ofReal_log Real.pi_pos.le]
  unfold poleKernel
  push_cast
  ring

private theorem continuous_pole_vertical :
    Continuous (fun t : ℝ => poleKernel ((5 / 4 : ℂ) + t * I)) := by
  unfold poleKernel
  apply Continuous.add
  · apply continuous_const.div (g := fun t : ℝ => (5 / 4 : ℂ) + t * I) (by fun_prop)
    intro t h
    have hh := congrArg Complex.re h
    norm_num at hh
  · apply continuous_const.div (g := fun t : ℝ => (5 / 4 : ℂ) + t * I - 1) (by fun_prop)
    intro t h
    have hh := congrArg Complex.re h
    norm_num at hh

private theorem continuous_pole_horizontal {T : ℝ} (hT : 0 < T) :
    Continuous (fun σ : ℝ => poleKernel ((σ : ℂ) + T * I)) := by
  unfold poleKernel
  apply Continuous.add
  · apply continuous_const.div (g := fun σ : ℝ => (σ : ℂ) + T * I) (by fun_prop)
    intro σ h
    have hh := congrArg Complex.im h
    simp at hh
    linarith
  · apply continuous_const.div (g := fun σ : ℝ => (σ : ℂ) + T * I - 1) (by fun_prop)
    intro σ h
    have hh := congrArg Complex.im h
    simp at hh
    linarith

theorem xiArcVar_eq_pi_add_theta_add_zetaArgVar {T : ℝ}
    (hT : 0 < T) (hg : zetaGoodHeight T) :
    xiArcVar T = Real.pi + riemannSiegelTheta T + zetaArgVar T := by
  have hpv := (Complex.continuous_re.comp continuous_pole_vertical).intervalIntegrable (μ := volume) (0 : ℝ) T
  have hgv := (Complex.continuous_re.comp
    (BacklundGammaPhase.continuous_digamma_line (by norm_num : (0 : ℝ) < 5 / 4))).intervalIntegrable (μ := volume) (0 : ℝ) T
  have hzv := (Complex.continuous_re.comp continuous_zeta_vertical).intervalIntegrable (μ := volume) (0 : ℝ) T
  have hph := (Complex.continuous_im.comp (continuous_pole_horizontal hT)).intervalIntegrable (μ := volume) (1 / 2 : ℝ) (5 / 4)
  have hgh : IntervalIntegrable (fun σ : ℝ =>
      (Complex.digamma (((σ : ℂ) + T * I) / 2)).im) volume (1 / 2) (5 / 4) := by
    apply ContinuousOn.intervalIntegrable
    apply Complex.continuous_im.comp_continuousOn
    apply (BacklundGammaPhase.continuousOn_digamma_horizontal T).mono
    intro σ hσ
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 5 / 4)] at hσ
    exact show (0 : ℝ) < σ from lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hσ.1
  have hzh := (Complex.continuous_im.comp (continuous_zeta_horizontal hT hg)).intervalIntegrable (μ := volume)
    (1 / 2 : ℝ) (5 / 4)
  dsimp only [Function.comp_def] at hpv hgv hzv hph hzh
  norm_num only [ofReal_div, ofReal_ofNat] at hgv
  have hv : (∫ t in (0 : ℝ)..T, (logDeriv xiF ((5 / 4 : ℂ) + t * I)).re) =
      (∫ t in (0 : ℝ)..T, (poleKernel ((5 / 4 : ℂ) + t * I)).re) - T / 2 * Real.log Real.pi +
      (1 / 2) * (∫ t in (0 : ℝ)..T, (Complex.digamma (((5 / 4 : ℂ) + t * I) / 2)).re) +
      (∫ t in (0 : ℝ)..T, (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)).re) := by
    have he (t : ℝ) : (logDeriv xiF ((5 / 4 : ℂ) + t * I)).re =
        (poleKernel ((5 / 4 : ℂ) + t * I)).re - Real.log Real.pi / 2 +
        (1 / 2) * (Complex.digamma (((5 / 4 : ℂ) + t * I) / 2)).re +
        (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)).re := by
      rw [logDeriv_xi_factorization (by norm_num) (by
        intro h; have hh := congrArg Complex.re h; norm_num at hh)
        (riemannZeta_ne_zero_of_one_lt_re (by norm_num))]
      simp [add_re, sub_re, mul_re, div_ofNat_re]
    simp_rw [he]
    rw [intervalIntegral.integral_add ((hpv.sub intervalIntegrable_const).add (hgv.const_mul _)) hzv,
      intervalIntegral.integral_add (hpv.sub intervalIntegrable_const) (hgv.const_mul _),
      intervalIntegral.integral_sub hpv intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  have hh : (∫ σ in (1 / 2 : ℝ)..(5 / 4), (logDeriv xiF ((σ : ℂ) + T * I)).im) =
      (∫ σ in (1 / 2 : ℝ)..(5 / 4), (poleKernel ((σ : ℂ) + T * I)).im) +
      (1 / 2) * (∫ σ in (1 / 2 : ℝ)..(5 / 4), (Complex.digamma (((σ : ℂ) + T * I) / 2)).im) +
      (∫ σ in (1 / 2 : ℝ)..(5 / 4), (logDeriv riemannZeta ((σ : ℂ) + T * I)).im) := by
    have he : EqOn (fun σ : ℝ => (logDeriv xiF ((σ : ℂ) + T * I)).im)
        (fun σ : ℝ => (poleKernel ((σ : ℂ) + T * I)).im +
          (1 / 2) * (Complex.digamma (((σ : ℂ) + T * I) / 2)).im +
          (logDeriv riemannZeta ((σ : ℂ) + T * I)).im) [[(1 / 2 : ℝ), 5 / 4]] := by
      intro σ hσ
      rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 5 / 4)] at hσ
      have hs : 0 < (((σ : ℂ) + T * I)).re := by simp; linarith [hσ.1]
      have hs1 : ((σ : ℂ) + T * I) ≠ 1 := by
        intro h; have hi := congrArg Complex.im h; simp at hi; linarith
      have hz : riemannZeta ((σ : ℂ) + T * I) ≠ 0 := by
        intro hz; exact hg _ hz (by simp)
      dsimp only
      rw [logDeriv_xi_factorization hs hs1 hz]
      simp [add_im, sub_im, mul_im, div_ofNat_im]
    rw [intervalIntegral.integral_congr he,
      intervalIntegral.integral_add (hph.add (hgh.const_mul _)) hzh,
      intervalIntegral.integral_add hph (hgh.const_mul _), intervalIntegral.integral_const_mul]
  have hp := pole_arc_eq_pi (by norm_num : (1 : ℝ) < 5 / 4) hT
  have hgamma := BacklundGammaPhase.digamma_rectangle (by norm_num : (1 / 2 : ℝ) ≤ 5 / 4) T
  unfold xiArcVar arcVariation
  norm_num only [ofReal_div, ofReal_ofNat]
  rw [hv, hh]
  unfold zetaArgVar arcVariation riemannSiegelTheta BacklundGammaPhase.phaseIntegral at *
  norm_num only [ofReal_div, ofReal_ofNat] at *
  linarith

theorem count_identity {T : ℝ} (hT : 0 < T) (hg : zetaGoodHeight T) :
    (N T : ℝ) = 1 + riemannSiegelTheta T / Real.pi + zetaArgVar T / Real.pi := by
  have h := pi_mul_N_eq_xiArcVar hT hg
  rw [xiArcVar_eq_pi_add_theta_add_zetaArgVar hT hg] at h
  field_simp
  nlinarith

noncomputable def mainTerm (T : ℝ) : ℝ :=
  T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8

noncomputable def gammaStirlingRemainder (T : ℝ) : ℝ :=
  BacklundGammaPhase.phaseIntegral T - T / 2 * Real.log (T / 2) + T / 2 + Real.pi / 8

theorem count_identity_mainTerm {T : ℝ} (hT : 0 < T) (hg : zetaGoodHeight T) :
    (N T : ℝ) = mainTerm T + zetaArgVar T / Real.pi +
      gammaStirlingRemainder T / Real.pi := by
  rw [count_identity hT hg]
  have hlog : Real.log (T / (2 * Real.pi)) = Real.log (T / 2) - Real.log Real.pi := by
    rw [show T / (2 * Real.pi) = (T / 2) / Real.pi by ring,
      Real.log_div (by positivity : T / 2 ≠ 0) Real.pi_ne_zero]
  rw [show riemannSiegelTheta T = BacklundGammaPhase.phaseIntegral T -
    T / 2 * Real.log Real.pi from rfl]
  unfold mainTerm gammaStirlingRemainder
  rw [hlog]
  field_simp
  ring

end TernaryGoldbach.RSBounds.BacklundCountIdentity
end

-- RSBounds.BacklundCenterNumericsData
section
namespace TernaryGoldbach.RSBounds.CenterNumerics

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def roots4 : List ℕ := [
  100000000, 42044820, 25327856, 17677669, 13374806, 10649051, 8782687, 7432544, 6415002, 5623413, 4991822, 4477374,
  4051079, 3692665, 3387551, 3125000, 2896935, 2697176, 2520913, 2364354, 2224466, 2098802, 1985364, 1882504,
  1788854, 1703269, 1624782, 1552574, 1485944, 1424290, 1367092, 1313900, 1264321, 1218011, 1174667, 1134023,
  1095841, 1059913, 1026051, 994088, 963873, 935272, 908164, 882437, 857994, 834742, 812601, 791495,
  771356, 752120, 733731, 716136, 699286, 683136, 667646, 652777, 638493, 624762, 611554, 598840,
  586594, 574791, 563409, 552427, 541824, 531581, 521682, 512110, 502850, 493886, 485207, 476797,
  468647, 460744, 453078, 445638, 438416, 431401, 424586, 417962, 411522, 405259, 399164, 393233,
  387459, 381836, 376357, 371019, 365815, 360742, 355793, 350966, 346255, 341656, 337167, 332782,
  328499, 324315, 320225, 316227, 312318, 308496, 304756, 301098, 297518, 294013, 290583, 287223,
  283933, 280710, 277553, 274458, 271426, 268453, 265538, 262680, 259876, 257126, 254428, 251781,
  249182, 246632, 244128, 241670, 239255, 236884, 234555, 232267, 230018, 227808, 225637, 223502,
  221403, 219340, 217311, 215316, 213353, 211422, 209522, 207653, 205814, 204004, 202222, 200468,
  198742, 197042, 195367, 193719, 192095, 190496, 188920, 187368, 185838, 184331, 182845, 181382,
  179939, 178516, 177114, 175731, 174368, 173023, 171698, 170390, 169100, 167828, 166572, 165334,
  164112, 162906, 161716, 160542, 159383, 158238, 157109, 155994, 154893, 153806, 152733, 151673,
  150626, 149592, 148571, 147563, 146566, 145582, 144609, 143649, 142699, 141761, 140834, 139917,
  139012, 138117, 137232, 136357, 135493, 134638, 133793, 132957, 132131, 131313, 130505, 129706,
  128916, 128134, 127361, 126596, 125839, 125090, 124350, 123617, 122892, 122175, 121465, 120762,
  120067, 119379, 118698, 118024, 117357, 116696, 116042, 115395, 114755, 114120, 113492, 112870,
  112254, 111645, 111041, 110443, 109851, 109264, 108683, 108108, 107538, 106974, 106414, 105860,
  105312, 104768, 104229, 103696, 103167, 102643, 102124, 101609, 101099, 100594, 100093, 99597,
  99105, 98618, 98135, 97656, 97181, 96710, 96244, 95781, 95323, 94868, 94418, 93971,
  93528, 93088, 92653, 92221, 91793, 91368, 90947, 90529, 90114, 89703, 89296, 88892,
  88491, 88093, 87699, 87307, 86919, 86534, 86152, 85773, 85397, 85024, 84654, 84286,
  83922, 83560, 83201, 82845, 82492, 82142, 81794, 81448, 81106, 80766, 80428, 80093,
  79761, 79431, 79103, 78778, 78455, 78135, 77817, 77501, 77188, 76877, 76568, 76261,
  75957, 75655, 75354, 75056, 74761, 74467, 74175, 73886, 73598, 73312, 73029, 72747,
  72467, 72190, 71914, 71640, 71368, 71098, 70829, 70563, 70298, 70035, 69774, 69514,
  69256, 69000, 68746, 68493, 68242, 67993, 67745, 67499, 67255, 67012, 66771, 66531,
  66293, 66056, 65821, 65587, 65355, 65124, 64895, 64667, 64441, 64216, 63992, 63770,
  63550, 63330, 63112, 62896, 62680, 62466, 62254, 62042, 61832, 61623, 61416, 61209,
  61004, 60800, 60598, 60396, 60196, 59997, 59799, 59603, 59407, 59213, 59020, 58828,
  58637, 58447, 58258, 58071, 57884, 57699, 57514, 57331, 57149, 56967, 56787, 56608,
  56430, 56253, 56076, 55901, 55727, 55554, 55382, 55210, 55040, 54870, 54702, 54534,
  54368, 54202, 54037, 53873, 53710, 53548, 53387, 53227, 53067, 52909, 52751, 52594,
  52438, 52282, 52128, 51974, 51821, 51669, 51518, 51368, 51218, 51069, 50921, 50774,
  50627, 50482, 50337, 50192, 50049, 49906, 49764, 49623, 49482, 49342, 49203, 49064,
  48927, 48790, 48653, 48517, 48382, 48248, 48114, 47981, 47849, 47717, 47586, 47456,
  47326, 47197, 47068, 46941, 46813, 46687, 46561, 46435, 46310, 46186, 46063, 45940,
  45817, 45695, 45574, 45454, 45333, 45214, 45095, 44977, 44859, 44741, 44625, 44509,
  44393, 44278, 44163, 44049, 43936, 43823, 43710, 43598, 43487, 43376, 43266, 43156,
  43046, 42937, 42829, 42721, 42614, 42507, 42400, 42294, 42189, 42084, 41979, 41875,
  41772, 41668, 41566, 41463, 41362, 41260, 41159, 41059, 40959, 40859, 40760, 40661,
  40563, 40465, 40368, 40271, 40174, 40078, 39982, 39887, 39792, 39697, 39603, 39510,
  39416, 39323, 39231, 39139, 39047, 38955, 38864, 38774, 38684, 38594, 38504, 38415,
  38326, 38238, 38150, 38062, 37975, 37888, 37802, 37715, 37630, 37544, 37459, 37374,
  37290, 37205, 37122, 37038, 36955, 36872, 36790, 36708, 36626, 36545, 36464, 36383,
  36302, 36222, 36142, 36063, 35984, 35905, 35826, 35748, 35670, 35592, 35515, 35438,
  35361, 35285, 35208, 35132, 35057, 34982, 34907, 34832, 34758, 34683, 34610, 34536,
  34463, 34390, 34317, 34245, 34172, 34100, 34029, 33958, 33886, 33816, 33745, 33675,
  33605, 33535, 33465, 33396, 33327, 33259, 33190, 33122, 33054, 32986, 32919, 32851,
  32784, 32718, 32651, 32585, 32519, 32453, 32388, 32322, 32257, 32193, 32128, 32064,
  32000]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem roots4_check : rootCheck 5 4 100000000 1 roots4 = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem roots4_length : roots4.length = 625 := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem roots4_sum : roots4.sum = 379526862 := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem partial54_bounds :
    (379526862 : ℝ) / 100000000 ≤ rpowSum (5 / 4) 1 625 ∧
    rpowSum (5 / 4) 1 625 ≤ (379527487 : ℝ) / 100000000 := by
  have h := rootCheck_sound (by norm_num : 0 < 1) (by norm_num : 0 < 4)
    (by norm_num : 0 < 100000000) roots4_check
  simpa only [roots4_length, roots4_sum, Nat.cast_ofNat, Nat.reduceAdd] using h

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def roots2 : List ℕ := [
  100000000, 17677669, 6415002, 3125000, 1788854, 1134023, 771356, 552427, 411522, 316227, 249182, 200468,
  164112, 136357, 114755, 97656, 83922, 72747, 63550, 55901, 49482, 44049, 39416, 35438,
  32000, 29011, 26399, 24104, 22080, 20286, 18689, 17263, 15985, 14835, 13798, 12860,
  12008, 11234, 10527, 9882, 9290, 8747, 8247, 7786, 7361, 6967, 6603, 6264,
  5949, 5656, 5383, 5128, 4890, 4666, 4457, 4261, 4076, 3903, 3739, 3586,
  3440, 3303, 3174, 3051, 2935, 2825, 2721, 2622, 2528, 2439, 2354, 2273,
  2196, 2122, 2052, 1985, 1922, 1861, 1802, 1746, 1693, 1642, 1593, 1546,
  1501, 1457, 1416, 1376, 1338, 1301, 1265, 1231, 1198, 1167, 1136, 1107,
  1079, 1051, 1025, 1000, 975, 951, 928, 906, 885, 864, 844, 824,
  806, 787, 770, 753, 736, 720, 705, 690, 675, 661, 647, 633,
  620, 608, 595, 584, 572, 561, 550, 539, 529, 518, 509, 499,
  490, 481, 472, 463, 455, 446, 438, 431, 423, 416, 408, 401,
  394, 388, 381, 375, 369, 362, 356, 351, 345, 339, 334, 328,
  323, 318, 313, 308, 304, 299, 294, 290, 285, 281, 277, 273,
  269, 265, 261, 257, 254, 250, 246, 243, 239, 236, 233, 230,
  226, 223, 220, 217, 214, 211, 209, 206, 203, 200, 198, 195,
  193, 190, 188, 185, 183, 181, 179, 176, 174, 172, 170, 168,
  166, 164, 162, 160, 158, 156, 154, 152, 151, 149, 147, 145,
  144, 142, 140, 139, 137, 136, 134, 133, 131, 130, 128, 127,
  126, 124, 123, 121, 120, 119, 118, 116, 115, 114, 113, 112,
  110, 109, 108, 107, 106, 105, 104, 103, 102, 101, 100, 99,
  98, 97, 96, 95, 94, 93, 92, 91, 90, 90, 89, 88,
  87, 86, 85, 85, 84, 83, 82, 81, 81, 80, 79, 79,
  78, 77, 76, 76, 75, 74, 74, 73, 72, 72, 71, 71,
  70, 69, 69, 68, 68, 67, 66, 66, 65, 65, 64, 64,
  63, 63, 62, 62, 61, 61, 60, 60, 59, 59, 58, 58,
  57, 57, 56, 56, 55, 55, 55, 54, 54, 53, 53, 52,
  52, 52, 51, 51, 50, 50, 50, 49, 49, 49, 48, 48,
  47, 47, 47, 46, 46, 46, 45, 45, 45, 44, 44, 44,
  43, 43, 43, 43, 42, 42, 42, 41, 41, 41, 40, 40,
  40, 40, 39, 39, 39, 39, 38, 38, 38, 37, 37, 37,
  37, 36, 36, 36, 36, 35, 35, 35, 35, 35, 34, 34,
  34, 34, 33, 33, 33, 33, 33, 32, 32, 32, 32, 32,
  31, 31, 31, 31, 31, 30, 30, 30, 30, 30, 29, 29,
  29, 29, 29, 29, 28, 28, 28, 28, 28, 27, 27, 27,
  27, 27, 27, 27, 26, 26, 26, 26, 26, 26, 25, 25,
  25, 25, 25, 25, 25, 24, 24, 24, 24, 24, 24, 24,
  23, 23, 23, 23, 23, 23, 23, 23, 22, 22, 22, 22,
  22, 22, 22, 22, 21, 21, 21, 21, 21, 21, 21, 21,
  20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 19, 19,
  19, 19, 19, 19, 19, 19, 19, 19, 18, 18, 18, 18,
  18, 18, 18, 18, 18, 18, 17, 17, 17, 17, 17, 17,
  17, 17, 17, 17, 17, 17, 16, 16, 16, 16, 16, 16,
  16, 16, 16, 16, 16, 16, 15, 15, 15, 15, 15, 15,
  15, 15, 15, 15, 15, 15, 15, 15, 14, 14, 14, 14,
  14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 13,
  13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
  13, 13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 12,
  12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 11, 11,
  11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
  11, 11, 11, 11, 11, 11, 11, 10, 10, 10, 10, 10,
  10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
  10]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem roots2_check : rootCheck 5 2 100000000 1 roots2 = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem roots2_length : roots2.length = 625 := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem roots2_sum : roots2.sum = 134144158 := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem partial52_bounds :
    (134144158 : ℝ) / 100000000 ≤ rpowSum (5 / 2) 1 625 ∧
    rpowSum (5 / 2) 1 625 ≤ (134144783 : ℝ) / 100000000 := by
  have h := rootCheck_sound (by norm_num : 0 < 1) (by norm_num : 0 < 2)
    (by norm_num : 0 < 100000000) roots2_check
  simpa only [roots2_length, roots2_sum, Nat.cast_ofNat, Nat.reduceAdd] using h

end TernaryGoldbach.RSBounds.CenterNumerics
end

-- RSBounds.BacklundCenterNumerics
section
namespace TernaryGoldbach.RSBounds

open CenterNumerics

private theorem zeta54_upper :
    ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ ≤ (459527487 : ℝ) / 100000000 := by
  have ht := zeta_tail_upper (σ := 5 / 4) (by norm_num) (N := 625) (by norm_num)
  have hr := root_upper (n := 625) (p := 1) (k := 4) (D := 5) (b := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num only [Nat.cast_ofNat] at hr
  rw [show (1 : ℝ) - 5 / 4 = -(1 : ℝ) / 4 by norm_num,
    show (5 / 4 : ℝ) - 1 = 1 / 4 by norm_num] at ht
  linarith [partial54_bounds.2]

private theorem zeta54_lower :
    (459486862 : ℝ) / 100000000 ≤ ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ := by
  have ht := zeta_tail_lower (σ := 5 / 4) (by norm_num) 625
  have hr := root_lower (n := 626) (p := 1) (k := 4) (D := 10000) (b := 1999)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num only [Nat.cast_ofNat] at hr
  rw [show (1 : ℝ) - 5 / 4 = -(1 : ℝ) / 4 by norm_num,
    show (5 / 4 : ℝ) - 1 = 1 / 4 by norm_num] at ht
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at ht
  linarith [partial54_bounds.1]

private theorem zeta52_lower :
    (134144158 : ℝ) / 100000000 ≤ ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ :=
  partial52_bounds.1.trans (zeta_partial_lower (by norm_num) 625)

private theorem zeta52_upper :
    ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ ≤
      (134144783 : ℝ) / 100000000 + 2 / 46875 := by
  have ht := zeta_tail_upper (σ := 5 / 2) (by norm_num) (N := 625) (by norm_num)
  have hr := root_upper (n := 625) (p := 3) (k := 2) (D := 15625) (b := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num only [Nat.cast_ofNat] at hr
  rw [show (1 : ℝ) - 5 / 2 = -(3 : ℝ) / 2 by norm_num,
    show (5 / 2 : ℝ) - 1 = 3 / 2 by norm_num] at ht
  linarith [partial52_bounds.2]

theorem zeta_five_fourths_upper :
    ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ < (23 / 5 : ℝ) := by
  linarith [zeta54_upper]

theorem zeta_five_fourths_ratio_bounds :
    (3.425 : ℝ) <
      ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ / ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ ∧
    ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ / ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ < 3.426 := by
  have hpos : 0 < ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ := by linarith [zeta52_lower]
  constructor
  · rw [lt_div_iff₀ hpos]
    linarith [zeta54_lower, zeta52_upper]
  · rw [div_lt_iff₀ hpos]
    linarith [zeta54_upper, zeta52_lower]

theorem zeta_norm_lower_five_fourths_3426 (T : ℝ) :
    (1 : ℝ) / 3.426 ≤ ‖riemannZeta (((5 / 4 : ℝ) : ℂ) + T * Complex.I)‖ := by
  have h1 : 0 < ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ := by linarith [zeta54_lower]
  have h2 : 0 < ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ := by linarith [zeta52_lower]
  have hratio := (div_lt_iff₀ h2).mp zeta_five_fourths_ratio_bounds.2
  have hc : (1 : ℝ) / 3.426 ≤
      ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ / ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ := by
    rw [le_div_iff₀ h1]
    linarith
  exact hc.trans (zeta_norm_lower_five_fourths_ratio T)

end TernaryGoldbach.RSBounds
end

-- RSBounds.BacklundAnchor
section
open Complex Filter MeasureTheory
open scoped Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundAnchor

noncomputable def eulerLog (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s))

lemma norm_neg_log_one_sub_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖-Complex.log (1 - z)‖ ≤ -Real.log (1 - ‖z‖) := by
  apply (Complex.hasSum_taylorSeries_neg_log' hz).norm_le_of_bounded
    (Real.hasSum_pow_div_log_of_abs_lt_one (by simpa using hz))
  intro n
  have hd : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)
  simp only [norm_div, norm_pow, hd, le_refl]

lemma real_eulerLog {σ : ℝ} (hσ : 1 < σ) :
    eulerLog (σ : ℂ) =
      ((∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-σ)) : ℝ) : ℂ) := by
  rw [eulerLog, Complex.ofReal_tsum]
  apply tsum_congr
  intro p
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hp0 : 0 < (p : ℝ) := by linarith
  have hpow : (p : ℂ) ^ (-(σ : ℂ)) = (((p : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_natCast] using
      (Complex.ofReal_cpow hp0.le (-σ)).symm
  have hlt : (p : ℝ) ^ (-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  rw [hpow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    ← Complex.ofReal_log (by linarith)]
  simp

lemma norm_eulerLog_le {s : ℂ} (hs : 1 < s.re) :
    ‖eulerLog s‖ ≤ Real.log ‖riemannZeta (s.re : ℂ)‖ := by
  let r : Nat.Primes → ℝ := fun p => (p : ℝ) ^ (-s.re)
  have hrs : Summable r := Nat.Primes.summable_rpow.mpr (by linarith)
  have hlogs : Summable (fun p => -Real.log (1 - r p)) := by
    simpa only [sub_eq_add_neg] using
      (Real.summable_log_one_add_of_summable hrs.neg).neg
  have he : Real.log ‖riemannZeta (s.re : ℂ)‖ =
      ∑' p : Nat.Primes, -Real.log (1 - r p) := by
    rw [← riemannZeta_eulerProduct_exp_log (by simpa using hs),
      show (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s.re : ℂ)))) =
        eulerLog (s.re : ℂ) from rfl,
      real_eulerLog hs, Complex.norm_exp, Complex.ofReal_re, Real.log_exp]
  rw [he]
  apply tsum_of_norm_bounded hlogs.hasSum
  intro p
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hp0 : 0 < (p : ℝ) := by linarith
  have hn : ‖(p : ℂ) ^ (-s)‖ = r p := by
    simpa only [r, Complex.neg_re, Complex.ofReal_natCast] using
      Complex.norm_cpow_eq_rpow_re_of_pos hp0 (-s)
  have hlt : r p < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  simpa only [hn] using norm_neg_log_one_sub_le (z := (p : ℂ) ^ (-s)) (hn ▸ hlt)

lemma log_zeta_five_fourths_lt_half_pi :
    Real.log ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ < Real.pi / 2 := by
  have he := Real.sum_le_exp_of_nonneg (x := (31 / 20 : ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at he
  have hπ : (31 / 20 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_d2]
  have hz : 0 < ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  apply (Real.log_lt_iff_lt_exp hz).mpr
  exact zeta_five_fourths_upper.trans
    ((show (23 / 5 : ℝ) < Real.exp (31 / 20) by linarith).trans
      (Real.exp_lt_exp.mpr hπ))

lemma re_zeta_anchor_pos (t : ℝ) :
    0 < (riemannZeta ((5 / 4 : ℂ) + t * I)).re := by
  let s : ℂ := (5 / 4 : ℂ) + t * I
  have hs : 1 < s.re := by simp [s]; norm_num
  have hb : ‖eulerLog s‖ < Real.pi / 2 :=
    (norm_eulerLog_le hs).trans_lt (by simpa [s] using log_zeta_five_fourths_lt_half_pi)
  have hi : |(eulerLog s).im| < Real.pi / 2 :=
    (Complex.abs_im_le_norm _).trans_lt hb
  have hc : 0 < Real.cos (eulerLog s).im := Real.cos_pos_of_mem_Ioo (abs_lt.mp hi)
  change 0 < (riemannZeta s).re
  rw [← riemannZeta_eulerProduct_exp_log hs, show
    (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s))) = eulerLog s from rfl,
    Complex.exp_re]
  exact mul_pos (Real.exp_pos _) hc

private lemma anchor_ne_one (t : ℝ) : (5 / 4 : ℂ) + t * I ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

private lemma anchor_ne_zero (t : ℝ) : riemannZeta ((5 / 4 : ℂ) + t * I) ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re (by simp; norm_num)

set_option maxHeartbeats 1000000 in
lemma hasDerivAt_log_anchor (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.log (riemannZeta ((5 / 4 : ℂ) + u * I)))
      (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I) * I) t := by
  have hl : HasDerivAt (fun u : ℝ => (5 / 4 : ℂ) + u * I) I t := by
    convert ((Complex.ofRealCLM.hasFDerivAt).hasDerivAt.mul_const I).const_add (5 / 4) using 1 <;> simp
  have hz := (differentiableAt_riemannZeta (anchor_ne_one t)).hasDerivAt.scomp t hl
  have h := hz.clog_real (Complex.mem_slitPlane_iff.mpr (Or.inl (re_zeta_anchor_pos t)))
  simp only [Function.comp_def, smul_eq_mul] at h
  convert h using 1 <;> simp only [logDeriv_apply] <;> ring

lemma continuous_vertical_integrand :
    Continuous (fun t : ℝ => (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)).re) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hl : ContinuousAt (fun u : ℝ => (5 / 4 : ℂ) + u * I) t := by fun_prop
  have ha : AnalyticAt ℂ riemannZeta ((5 / 4 : ℂ) + t * I) := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [eventually_ne_nhds (anchor_ne_one t)] with z hz
    exact differentiableAt_riemannZeta hz
  have hc : ContinuousAt (fun u : ℝ =>
      deriv riemannZeta ((5 / 4 : ℂ) + u * I) /
        riemannZeta ((5 / 4 : ℂ) + u * I)) t :=
    ContinuousAt.comp (g := fun s : ℂ => deriv riemannZeta s / riemannZeta s)
      (f := fun u : ℝ => (5 / 4 : ℂ) + u * I)
      (ha.deriv.continuousAt.div ha.continuousAt (anchor_ne_zero t)) hl
  simpa only [logDeriv_apply, Function.comp_def] using Complex.continuous_re.continuousAt.comp hc

lemma vertical_integral_eq_arg (T : ℝ) :
    (∫ t in (0 : ℝ)..T, (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)).re) =
      (riemannZeta ((5 / 4 : ℂ) + T * I)).arg := by
  have hd (t : ℝ) :
      HasDerivAt (fun u : ℝ => (Complex.log (riemannZeta ((5 / 4 : ℂ) + u * I))).im)
        (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)).re t := by
    convert! Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_log_anchor t) using 1 <;>
      simp [Function.comp_def]
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (continuous_vertical_integrand.intervalIntegrable 0 T)
  rw [he]
  simp only [Complex.log_im, Complex.ofReal_zero, zero_mul, add_zero]
  have hs := real_eulerLog (σ := (5 / 4 : ℝ)) (by norm_num)
  have he' := riemannZeta_eulerProduct_exp_log (s := ((5 / 4 : ℝ) : ℂ)) (by norm_num)
  change Complex.exp (eulerLog ((5 / 4 : ℝ) : ℂ)) = _ at he'
  rw [hs] at he'
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at he'
  have harg : (riemannZeta (5 / 4 : ℂ)).arg = 0 := by
    rw [← he', ← Complex.ofReal_exp]
    exact Complex.arg_ofReal_of_nonneg (Real.exp_nonneg _)
  rw [harg, sub_zero]

lemma abs_vertical_integral_le (T : ℝ) :
    |∫ t in (0 : ℝ)..T, (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)).re| ≤ Real.pi / 2 := by
  rw [vertical_integral_eq_arg]
  exact (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (re_zeta_anchor_pos T))).le

end TernaryGoldbach.RSBounds.BacklundAnchor
end

-- RSBounds.IEANTNDigammaDifference
section
open Complex Filter Topology Set MeasureTheory
namespace CH2Section81

theorem hasSum_telescope_inv {y : ℝ} (hy : 0 < y) :
    HasSum (fun k : ℕ ↦ 1 / ((k : ℝ) + y) - 1 / ((k : ℝ) + 1 + y)) (1 / y) := by
  have hpos : ∀ k : ℕ, 0 ≤ 1 / ((k : ℝ) + y) - 1 / ((k : ℝ) + 1 + y) := by
    intro k
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [sub_nonneg]; apply one_div_le_one_div_of_le (by positivity); linarith
  rw [hasSum_iff_tendsto_nat_of_nonneg hpos]
  have e : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 / ((k : ℝ) + y) - 1 / ((k : ℝ) + 1 + y))
      = 1 / y - 1 / ((n : ℝ) + y) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  simp_rw [e]
  have : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + y)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ y tendsto_natCast_atTop_atTop)
  simpa using tendsto_const_nhds.sub this

theorem norm_digamma_sub_le {z₁ z₂ : ℂ} (h1 : 0 < z₁.re) (h2 : 0 < z₂.re) (him : z₁.im = z₂.im)
    (hy : 2 ≤ z₁.im) :
    ‖Complex.digamma z₁ - Complex.digamma z₂‖ ≤ ‖z₁ - z₂‖ * (4 / z₁.im) := by
  set y := z₁.im with hy_def
  have hy0 : 0 < y := by linarith
  have hn1 : ∀ n : ℕ, z₁ ≠ -n := fun n h ↦ by
    have := congrArg Complex.re h; simp at this; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hn2 : ∀ n : ℕ, z₂ ≠ -n := fun n h ↦ by
    have := congrArg Complex.re h; simp at this; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hs1 := GammaSolution.summable_gaussTerm hn1
  have hs2 := GammaSolution.summable_gaussTerm hn2
  have hdiff : Complex.digamma z₁ - Complex.digamma z₂
      = ∑' k, (GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k) := by
    rw [GammaSolution.digamma_eq_gaussSum h1, GammaSolution.digamma_eq_gaussSum h2,
      GammaSolution.gaussSum, GammaSolution.gaussSum, hs1.tsum_sub hs2]
    ring

  have hk : ∀ k : ℕ, ‖GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k‖
      ≤ ‖z₁ - z₂‖ * 2 * (1 / ((k : ℝ) + (y - 1)) - 1 / ((k : ℝ) + 1 + (y - 1))) := by
    intro k
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hz1 : ((k : ℂ) + z₁) ≠ 0 := fun h ↦ hn1 k (by linear_combination h)
    have hz2 : ((k : ℂ) + z₂) ≠ 0 := fun h ↦ hn2 k (by linear_combination h)
    have e : GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k
        = (z₁ - z₂) / (((k : ℂ) + z₁) * ((k : ℂ) + z₂)) := by
      simp only [GammaSolution.gaussTerm]; field_simp; ring
    have hnorm : ∀ z : ℂ, 0 < z.re → z.im = y → (k : ℝ) ^ 2 + y ^ 2 ≤ ‖(k : ℂ) + z‖ ^ 2 := by
      intro z hz hzi
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.natCast_re, Complex.add_im, Complex.natCast_im, zero_add, hzi]
      nlinarith
    have hp1 := hnorm z₁ h1 rfl
    have hp2 := hnorm z₂ h2 him.symm
    have hprod : ((k : ℝ) + y) ^ 2 / 2 ≤ ‖((k : ℂ) + z₁) * ((k : ℂ) + z₂)‖ := by
      rw [norm_mul]
      have ha := norm_nonneg ((k : ℂ) + z₁)
      have hb := norm_nonneg ((k : ℂ) + z₂)
      have : ((k : ℝ) + y) ^ 2 / 2 ≤ (k : ℝ) ^ 2 + y ^ 2 := by nlinarith [sq_nonneg ((k:ℝ) - y)]
      have hc1 : Real.sqrt ((k : ℝ) ^ 2 + y ^ 2) ≤ ‖(k : ℂ) + z₁‖ := by
        have := Real.sqrt_le_sqrt hp1; rwa [Real.sqrt_sq ha] at this
      have hc2 : Real.sqrt ((k : ℝ) ^ 2 + y ^ 2) ≤ ‖(k : ℂ) + z₂‖ := by
        have := Real.sqrt_le_sqrt hp2; rwa [Real.sqrt_sq hb] at this
      have hmm := mul_le_mul hc1 hc2 (Real.sqrt_nonneg _) ha
      rw [Real.mul_self_sqrt (by positivity)] at hmm
      linarith
    have htel : 2 / ((k : ℝ) + y) ^ 2 ≤ 2 * (1 / ((k : ℝ) + (y - 1)) - 1 / ((k : ℝ) + 1 + (y - 1))) := by
      have hky : 0 < (k : ℝ) + (y - 1) := by linarith
      have hky' : 0 < (k : ℝ) + y := by linarith
      have h3 : 1 / ((k : ℝ) + y) ^ 2 ≤ 1 / ((k : ℝ) + (y - 1)) - 1 / ((k : ℝ) + 1 + (y - 1)) := by
        rw [show (k : ℝ) + 1 + (y - 1) = (k : ℝ) + y by ring, div_sub_div _ _ hky.ne' hky'.ne',
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have e2 : 2 / ((k : ℝ) + y) ^ 2 = 2 * (1 / ((k : ℝ) + y) ^ 2) := by ring
      rw [e2]; linarith
    rw [e, norm_div]
    calc ‖z₁ - z₂‖ / ‖((k : ℂ) + z₁) * ((k : ℂ) + z₂)‖
        ≤ ‖z₁ - z₂‖ / (((k : ℝ) + y) ^ 2 / 2) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hprod
      _ = ‖z₁ - z₂‖ * (2 / ((k : ℝ) + y) ^ 2) := by field_simp
      _ ≤ ‖z₁ - z₂‖ * (2 * (1 / ((k : ℝ) + (y - 1)) - 1 / ((k : ℝ) + 1 + (y - 1)))) :=
          mul_le_mul_of_nonneg_left htel (norm_nonneg _)
      _ = _ := by ring
  have htele := (hasSum_telescope_inv (y := y - 1) (by linarith)).mul_left (‖z₁ - z₂‖ * 2)
  have hsumn : Summable fun k : ℕ ↦ ‖GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hk htele.summable
  rw [hdiff]
  calc _ ≤ ∑' k, ‖GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k‖ := norm_tsum_le_tsum_norm hsumn
    _ ≤ ‖z₁ - z₂‖ * 2 * (1 / (y - 1)) := by
        rw [← htele.tsum_eq]; exact Summable.tsum_le_tsum hk hsumn htele.summable
    _ ≤ ‖z₁ - z₂‖ * (4 / y) := by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        have : 1 / (y - 1) ≤ 2 / y := by rw [div_le_div_iff₀ (by linarith) hy0]; nlinarith
        have e : 4 / y = 2 * (2 / y) := by ring
        rw [e]; linarith

end CH2Section81
end

-- RSBounds.BacklundReflection
section
noncomputable section
open Complex Real
open scoped Topology

namespace TernaryGoldbach.RSBounds.BacklundReflection

theorem logDeriv_pi_cpow_neg_half (s : ℂ) :
    logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s = -(Real.log Real.pi : ℂ) / 2 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hf : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2 : ℂ) s := by
    simpa using ((hasDerivAt_id s).neg.div_const 2)
  have hg : HasDerivAt (fun y : ℂ => (Real.pi : ℂ) ^ y)
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ)) (-s / 2) :=
    (hasStrictDerivAt_const_cpow (Or.inl hπ)).hasDerivAt
  have hd : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) s := by
    have := hg.comp s hf
    exact this
  have hval : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hπ]; exact Complex.exp_ne_zero _
  rw [logDeriv_apply, hd.deriv, Complex.ofReal_log Real.pi_pos.le]
  field_simp

theorem im_logDeriv_pi_cpow_neg_half (s : ℂ) :
    (logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s).im = 0 := by
  rw [logDeriv_pi_cpow_neg_half]
  simp

theorem logDeriv_completedZeta_one_sub {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv completedRiemannZeta (1 - s) = -logDeriv completedRiemannZeta s := by
  have hfe : completedRiemannZeta ∘ (fun z : ℂ => 1 - z) = completedRiemannZeta := by
    funext z; exact completedRiemannZeta_one_sub z
  have h1s0 : (1 : ℂ) - s ≠ 0 := fun h => hs1 (by linear_combination -h)
  have h1s1 : (1 : ℂ) - s ≠ 1 := fun h => hs0 (by linear_combination -h)
  have hf : DifferentiableAt ℂ completedRiemannZeta (1 - s) :=
    differentiableAt_completedZeta h1s0 h1s1
  have hg : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s := differentiableAt_id.const_sub 1
  have hderiv_g : deriv (fun z : ℂ => 1 - z) s = -1 :=
    ((hasDerivAt_id s).const_sub 1).deriv
  have hcomp := logDeriv_comp hf hg
  rw [hfe, hderiv_g] at hcomp

  rw [hcomp]; ring

theorem logDeriv_completedZeta_conj (s : ℂ) :
    logDeriv completedRiemannZeta (starRingEnd ℂ s)
      = starRingEnd ℂ (logDeriv completedRiemannZeta s) := by
  have hf : (starRingEnd ℂ ∘ completedRiemannZeta ∘ starRingEnd ℂ) =
      completedRiemannZeta := by
    funext w
    simp [Function.comp, completedRiemannZeta_conj]
  have hd := deriv_conj_conj (f := completedRiemannZeta)
  rw [hf] at hd
  have h2 : deriv completedRiemannZeta (starRingEnd ℂ s) =
      starRingEnd ℂ (deriv completedRiemannZeta s) := by
    rw [congrFun hd (starRingEnd ℂ s)]
    simp [Function.comp]
  rw [logDeriv_apply, logDeriv_apply, h2, completedRiemannZeta_conj, map_div₀]

theorem im_logDeriv_completedZeta_reflect (σ T : ℝ) (hT : T ≠ 0) :
    (logDeriv completedRiemannZeta ((1 - σ : ℝ) + T * Complex.I)).im
      = (logDeriv completedRiemannZeta ((σ : ℝ) + T * Complex.I)).im := by
  set s : ℂ := (σ : ℝ) + T * Complex.I with hs_def
  have hsim : s.im ≠ 0 := by rw [hs_def]; simp [hT]
  have hs0 : s ≠ 0 := fun h => hsim (by rw [h]; rfl)
  have hs1 : s ≠ 1 := by
    intro h; apply hsim; rw [h]; simp

  have hrewrite : ((1 - σ : ℝ) + T * Complex.I) = 1 - starRingEnd ℂ s := by
    rw [hs_def]; simp only [Complex.conj_ofReal, map_add, map_mul, Complex.conj_I]
    push_cast; ring
  rw [hrewrite]

  have hcs0 : starRingEnd ℂ s ≠ 0 := by rw [ne_eq, map_eq_zero]; exact hs0
  have hcs1 : starRingEnd ℂ s ≠ 1 := by
    intro h; apply hs1
    have := congrArg (starRingEnd ℂ) h
    rwa [Complex.conj_conj, map_one] at this
  rw [logDeriv_completedZeta_one_sub hcs0 hcs1, logDeriv_completedZeta_conj s]

  simp [Complex.neg_im, Complex.conj_im]

theorem im_logDeriv_zeta_decomp {σ T : ℝ} (hT : T ≠ 0)
    (hζ : riemannZeta ((σ : ℂ) + T * Complex.I) ≠ 0) :
    (logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im
      = (logDeriv completedRiemannZeta ((σ : ℂ) + T * Complex.I)).im
        - (logDeriv (fun z : ℂ => Complex.Gamma (z / 2))
            ((σ : ℂ) + T * Complex.I)).im := by
  set s : ℂ := (σ : ℂ) + T * Complex.I with hs_def
  have hsim : s.im ≠ 0 := by rw [hs_def]; simp [hT]
  have hs0 : s ≠ 0 := fun h => hsim (by rw [h]; exact Complex.zero_im)
  have hs1 : s ≠ 1 := fun h => hsim (by rw [h]; exact Complex.one_im)
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero

  have hhalf : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    apply hsim
    have him := congrArg Complex.im h
    simp only [Complex.div_ofNat_im, Complex.neg_im, Complex.natCast_im,
      neg_zero] at him
    linarith

  have hP_diff : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s := by
    have hf : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2 : ℂ) s := by
      simpa using ((hasDerivAt_id s).neg.div_const 2)
    have hg : HasDerivAt (fun y : ℂ => (Real.pi : ℂ) ^ y)
        ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ)) (-s / 2) :=
      (hasStrictDerivAt_const_cpow (Or.inl hπ)).hasDerivAt
    have hd : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
        ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) s := by
      exact hf.const_cpow (Or.inl hπ)
    exact hd.differentiableAt
  have hG_diff : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s := by
    have h1 : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
      Complex.differentiableAt_Gamma _ hhalf
    have h2 : DifferentiableAt ℂ (fun z : ℂ => z / 2) s :=
      differentiableAt_id.div_const 2
    exact DifferentiableAt.comp (g := Complex.Gamma) (f := fun z : ℂ => z / 2) s h1 h2
  have hP_ne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hπ]
    exact Complex.exp_ne_zero _
  have hG_ne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hhalf
  have hΛ_ne : completedRiemannZeta s ≠ 0 := by
    intro h
    apply hζ
    rw [riemannZeta_def_of_ne_zero hs0, h, zero_div]
  have hΛ_diff : DifferentiableAt ℂ completedRiemannZeta s :=
    differentiableAt_completedZeta hs0 hs1
  have hPG_ne : (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) ≠ 0 :=
    mul_ne_zero hP_ne hG_ne
  have hPG_diff : DifferentiableAt ℂ
      (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) s :=
    hP_diff.mul hG_diff

  have hopen : IsOpen {z : ℂ | z.im ≠ 0} := isOpen_ne.preimage Complex.continuous_im
  have hEq : riemannZeta =ᶠ[nhds s]
      fun z => completedRiemannZeta z
        / ((Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) := by
    filter_upwards [hopen.mem_nhds hsim] with z hz
    have hz0 : z ≠ 0 := fun h => hz (by rw [h]; exact Complex.zero_im)
    rw [riemannZeta_def_of_ne_zero hz0, Complex.Gammaℝ_def]
  have hlog_eq : logDeriv riemannZeta s
      = logDeriv (fun z => completedRiemannZeta z
          / ((Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2))) s := by
    rw [logDeriv_apply, logDeriv_apply, hEq.deriv_eq, hEq.self_of_nhds]
  have hdiv := logDeriv_div (f := completedRiemannZeta)
      (g := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2))
      s hΛ_ne hPG_ne hΛ_diff hPG_diff
  have hmul := logDeriv_mul (f := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      (g := fun z : ℂ => Complex.Gamma (z / 2))
      s hP_ne hG_ne hP_diff hG_diff
  simp only [Pi.div_def, Pi.mul_def] at hdiv hmul
  have hkey : logDeriv riemannZeta s
      = logDeriv completedRiemannZeta s
        - (logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s
            + logDeriv (fun z : ℂ => Complex.Gamma (z / 2)) s) := by
    rw [hlog_eq, hdiv, hmul]
  rw [hkey, Complex.sub_im, Complex.add_im, im_logDeriv_pi_cpow_neg_half s]
  ring

theorem im_logDeriv_zeta_reflect_diff {T : ℝ} (hT : T ≠ 0) (σ : ℝ)
    (hζ : riemannZeta ((σ : ℂ) + T * Complex.I) ≠ 0)
    (hζ' : riemannZeta (((1 - σ : ℝ) : ℂ) + T * Complex.I) ≠ 0) :
    (logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im
        - (logDeriv riemannZeta (((1 - σ : ℝ) : ℂ) + T * Complex.I)).im
      = (logDeriv (fun z : ℂ => Complex.Gamma (z / 2))
            (((1 - σ : ℝ) : ℂ) + T * Complex.I)).im
        - (logDeriv (fun z : ℂ => Complex.Gamma (z / 2))
            ((σ : ℂ) + T * Complex.I)).im := by
  have h1 := im_logDeriv_zeta_decomp hT hζ
  have h2 := im_logDeriv_zeta_decomp hT hζ'
  have hrefl := im_logDeriv_completedZeta_reflect σ T hT
  linarith

lemma logDeriv_Gamma_half {p : ℂ} (hp : p.im ≠ 0) :
    logDeriv (fun s : ℂ => Complex.Gamma (s / 2)) p
      = (1 / 2 : ℂ) * Complex.digamma (p / 2) := by
  have hp2ne : ∀ m : ℕ, (p / 2) ≠ -(m : ℂ) := by
    intro m heq
    apply hp
    have h2 : p = (2 : ℂ) * (p / 2) := by ring
    rw [heq] at h2
    rw [h2]; simp
  have hf : DifferentiableAt ℂ Complex.Gamma (p / 2) :=
    Complex.differentiableAt_Gamma _ hp2ne
  have hg : DifferentiableAt ℂ (fun s : ℂ => s / 2) p := by fun_prop
  have hcomp :
      logDeriv (Complex.Gamma ∘ (fun s : ℂ => s / 2)) p
        = logDeriv Complex.Gamma (p / 2) * deriv (fun s : ℂ => s / 2) p :=
    logDeriv_comp hf hg
  have hderiv2 : deriv (fun s : ℂ => s / 2) p = 1 / 2 := by
    rw [deriv_div_const]; simp
  have hcompeq : (Complex.Gamma ∘ (fun s : ℂ => s / 2)) = (fun s => Complex.Gamma (s / 2)) :=
    rfl
  rw [← hcompeq, hcomp, hderiv2, ← Complex.digamma_def]
  ring

theorem im_logDeriv_zeta_reflect_digamma {T : ℝ} (hT : T ≠ 0) (σ : ℝ)
    (hζ : riemannZeta ((σ : ℂ) + T * Complex.I) ≠ 0)
    (hζ' : riemannZeta (((1 - σ : ℝ) : ℂ) + T * Complex.I) ≠ 0) :
    (logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im
        - (logDeriv riemannZeta (((1 - σ : ℝ) : ℂ) + T * Complex.I)).im
      = (1 / 2 : ℝ) *
        (Complex.digamma ((((1 - σ : ℝ) : ℂ) + T * Complex.I) / 2)
          - Complex.digamma (((σ : ℂ) + T * Complex.I) / 2)).im := by
  rw [im_logDeriv_zeta_reflect_diff hT σ hζ hζ',
    logDeriv_Gamma_half (by simpa using hT),
    logDeriv_Gamma_half (by simpa using hT)]
  simp only [Complex.mul_im, Complex.div_ofNat_re, Complex.one_re,
    Complex.div_ofNat_im, Complex.one_im, Complex.sub_im]
  ring

end TernaryGoldbach.RSBounds.BacklundReflection
end
end

-- RSBounds.BacklundGammaReflection
section
open Complex Filter Set MeasureTheory
open scoped Real Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundGammaReflection

theorem norm_digamma_sub_le_of_one_le_re {z₁ z₂ : ℂ}
    (h1 : 1 ≤ z₁.re) (h2 : 1 ≤ z₂.re) :
    ‖Complex.digamma z₁ - Complex.digamma z₂‖ ≤ 2 * ‖z₁ - z₂‖ := by
  have hn1 := GammaSolution.ne_neg_natCast_of_mem
    (GammaSolution.mem_rightHalfPlane_iff.mpr (by linarith : 0 < z₁.re))
  have hn2 := GammaSolution.ne_neg_natCast_of_mem
    (GammaSolution.mem_rightHalfPlane_iff.mpr (by linarith : 0 < z₂.re))
  have hs1 := GammaSolution.summable_gaussTerm hn1
  have hs2 := GammaSolution.summable_gaussTerm hn2
  have hdiff : Complex.digamma z₁ - Complex.digamma z₂ =
      ∑' k, (GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k) := by
    rw [GammaSolution.digamma_eq_gaussSum (by linarith),
      GammaSolution.digamma_eq_gaussSum (by linarith),
      GammaSolution.gaussSum, GammaSolution.gaussSum, hs1.tsum_sub hs2]
    ring
  have hk : ∀ k : ℕ, ‖GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k‖ ≤
      ‖z₁ - z₂‖ * (2 * (((k : ℝ) + 1) * ((k : ℝ) + 1 + 1))⁻¹) := by
    intro k
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hk1 : (0 : ℝ) < k + 1 := by positivity
    have hz1 : ((k : ℂ) + z₁) ≠ 0 := fun h => hn1 k (by linear_combination h)
    have hz2 : ((k : ℂ) + z₂) ≠ 0 := fun h => hn2 k (by linear_combination h)
    have he : GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k =
        (z₁ - z₂) / (((k : ℂ) + z₁) * ((k : ℂ) + z₂)) := by
      simp only [GammaSolution.gaussTerm]
      field_simp
      ring
    have hnz1 : (k : ℝ) + 1 ≤ ‖(k : ℂ) + z₁‖ := by
      have hh := Complex.re_le_norm ((k : ℂ) + z₁)
      simp only [add_re, natCast_re] at hh
      linarith
    have hnz2 : (k : ℝ) + 1 ≤ ‖(k : ℂ) + z₂‖ := by
      have hh := Complex.re_le_norm ((k : ℂ) + z₂)
      simp only [add_re, natCast_re] at hh
      linarith
    have hp : ((k : ℝ) + 1) ^ 2 ≤ ‖((k : ℂ) + z₁) * ((k : ℂ) + z₂)‖ := by
      rw [norm_mul, pow_two]
      exact mul_le_mul hnz1 hnz2 hk1.le (norm_nonneg _)
    have hc : 1 / ((k : ℝ) + 1) ^ 2 ≤
        2 * (((k : ℝ) + 1) * ((k : ℝ) + 1 + 1))⁻¹ := by
      change 1 / ((k : ℝ) + 1) ^ 2 ≤
        2 / (((k : ℝ) + 1) * ((k : ℝ) + 1 + 1))
      rw [div_le_div_iff₀ (sq_pos_of_pos hk1) (by positivity)]
      nlinarith
    rw [he, norm_div]
    calc
      _ ≤ ‖z₁ - z₂‖ / ((k : ℝ) + 1) ^ 2 :=
        div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hk1) hp
      _ = ‖z₁ - z₂‖ * (1 / ((k : ℝ) + 1) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc (norm_nonneg _)
  have htele := GammaSolution.hasSum_comparison (t := 1) le_rfl ‖z₁ - z₂‖
  have hsumn : Summable (fun k : ℕ =>
      ‖GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hk htele.summable
  rw [hdiff]
  calc
    _ ≤ ∑' k, ‖GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k‖ :=
      norm_tsum_le_tsum_norm hsumn
    _ ≤ ‖z₁ - z₂‖ * (2 * (1 : ℝ)⁻¹) := by
      rw [← htele.tsum_eq]
      exact Summable.tsum_le_tsum hk hsumn htele.summable
    _ = _ := by ring

theorem digamma_eq_add_two_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    Complex.digamma z = Complex.digamma (z + 2) - z⁻¹ - (z + 1)⁻¹ := by
  have hn : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m he
    have hh := congrArg Complex.im he
    simp only [neg_im, natCast_im, neg_zero] at hh
    exact hz hh
  have hn1 : ∀ m : ℕ, z + 1 ≠ -(m : ℂ) := by
    intro m he
    have hh := congrArg Complex.im he
    simp only [add_im, one_im, add_zero, neg_im, natCast_im, neg_zero] at hh
    exact hz hh
  have h1 := Complex.digamma_apply_add_one z hn
  have h2 := Complex.digamma_apply_add_one (z + 1) hn1
  rw [show z + 2 = z + 1 + 1 by ring, h2, h1]
  ring

noncomputable def reflectedArg (σ T : ℝ) : ℂ := ((1 - σ : ℝ) + T * I) / 2
noncomputable def directArg (σ T : ℝ) : ℂ := ((σ : ℝ) + T * I) / 2

theorem reflectedArg_im (σ T : ℝ) : (reflectedArg σ T).im = T / 2 := by
  simp [reflectedArg, div_ofNat_im]

theorem directArg_im (σ T : ℝ) : (directArg σ T).im = T / 2 := by
  simp [directArg, div_ofNat_im]

theorem norm_arg_difference {σ T : ℝ} (hσ : 1 / 2 ≤ σ) :
    ‖reflectedArg σ T - directArg σ T‖ = σ - 1 / 2 := by
  have he : reflectedArg σ T - directArg σ T = ((1 / 2 - σ : ℝ) : ℂ) := by
    unfold reflectedArg directArg
    push_cast
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  ring

theorem norm_inverse_difference {z₁ z₂ : ℂ} {b : ℝ}
    (hb : 0 < b) (h1 : z₁.im = b) (h2 : z₂.im = b) :
    ‖z₁⁻¹ - z₂⁻¹‖ ≤ ‖z₁ - z₂‖ / b ^ 2 := by
  have hn1 : b ≤ ‖z₁‖ := by
    simpa only [h1, abs_of_pos hb] using Complex.abs_im_le_norm z₁
  have hn2 : b ≤ ‖z₂‖ := by
    simpa only [h2, abs_of_pos hb] using Complex.abs_im_le_norm z₂
  have hz1 : z₁ ≠ 0 := norm_pos_iff.mp (hb.trans_le hn1)
  have hz2 : z₂ ≠ 0 := norm_pos_iff.mp (hb.trans_le hn2)
  have he : z₁⁻¹ - z₂⁻¹ = (z₂ - z₁) / (z₁ * z₂) := by field_simp
  rw [he, norm_div, norm_sub_rev, norm_mul]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hb)
    (by rw [pow_two]; exact mul_le_mul hn1 hn2 hb.le (norm_nonneg _))

theorem norm_digamma_reflection_le {σ T : ℝ}
    (hT : 1 ≤ T) (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 5 / 4) :
    ‖Complex.digamma (reflectedArg σ T) - Complex.digamma (directArg σ T)‖ ≤
      16 * (σ - 1 / 2) / T := by
  have hT0 : 0 < T := by linarith
  have hb : 0 < T / 2 := by positivity
  have hσ : 0 ≤ σ - 1 / 2 := by linarith
  have h1re : 1 ≤ (reflectedArg σ T + 2).re := by
    simp [reflectedArg, div_ofNat_re]
    linarith
  have h2re : 1 ≤ (directArg σ T + 2).re := by
    simp [directArg, div_ofNat_re]
    linarith
  have hnorm : ‖(reflectedArg σ T + 2) - (directArg σ T + 2)‖ = σ - 1 / 2 := by
    rw [add_sub_add_right_eq_sub, norm_arg_difference hσ0]
  have hshift : ‖Complex.digamma (reflectedArg σ T + 2) -
      Complex.digamma (directArg σ T + 2)‖ ≤ 8 * (σ - 1 / 2) / T := by
    by_cases hT4 : T ≤ 4
    · have hh := norm_digamma_sub_le_of_one_le_re h1re h2re
      rw [hnorm] at hh
      refine hh.trans ?_
      rw [le_div_iff₀ hT0]
      nlinarith
    · have hh := CH2Section81.norm_digamma_sub_le
        (show 0 < (reflectedArg σ T + 2).re by linarith)
        (show 0 < (directArg σ T + 2).re by linarith)
        (by simp [reflectedArg_im, directArg_im])
        (by simp [reflectedArg_im]; linarith : 2 ≤ (reflectedArg σ T + 2).im)
      rw [hnorm] at hh
      norm_num [reflectedArg_im] at hh
      convert hh using 1; ring
  have hrec0 := norm_inverse_difference hb (reflectedArg_im σ T) (directArg_im σ T)
  rw [norm_arg_difference hσ0] at hrec0
  have hrec1 := norm_inverse_difference hb
    (show (reflectedArg σ T + 1).im = T / 2 by simp [reflectedArg_im])
    (show (directArg σ T + 1).im = T / 2 by simp [directArg_im])
  rw [add_sub_add_right_eq_sub, norm_arg_difference hσ0] at hrec1
  rw [digamma_eq_add_two_of_im_ne_zero (z := reflectedArg σ T) (by rw [reflectedArg_im]; exact hb.ne'),
    digamma_eq_add_two_of_im_ne_zero (z := directArg σ T) (by rw [directArg_im]; exact hb.ne')]
  have he : (Complex.digamma (reflectedArg σ T + 2) - (reflectedArg σ T)⁻¹ -
      (reflectedArg σ T + 1)⁻¹) - (Complex.digamma (directArg σ T + 2) -
      (directArg σ T)⁻¹ - (directArg σ T + 1)⁻¹) =
      (Complex.digamma (reflectedArg σ T + 2) - Complex.digamma (directArg σ T + 2)) -
      ((reflectedArg σ T)⁻¹ - (directArg σ T)⁻¹) -
      ((reflectedArg σ T + 1)⁻¹ - (directArg σ T + 1)⁻¹) := by ring
  rw [he]
  refine (norm_sub_le _ _).trans ?_
  have htri := norm_sub_le (Complex.digamma (reflectedArg σ T + 2) -
    Complex.digamma (directArg σ T + 2)) ((reflectedArg σ T)⁻¹ - (directArg σ T)⁻¹)
  have hsmall : 2 * ((σ - 1 / 2) / (T / 2) ^ 2) ≤ 8 * (σ - 1 / 2) / T := by
    field_simp
    nlinarith
  calc
    _ ≤ (‖Complex.digamma (reflectedArg σ T + 2) -
      Complex.digamma (directArg σ T + 2)‖ +
      ‖(reflectedArg σ T)⁻¹ - (directArg σ T)⁻¹‖) +
      ‖(reflectedArg σ T + 1)⁻¹ - (directArg σ T + 1)⁻¹‖ := add_le_add htri le_rfl
    _ ≤ (8 * (σ - 1 / 2) / T + (σ - 1 / 2) / (T / 2) ^ 2) +
      (σ - 1 / 2) / (T / 2) ^ 2 := add_le_add (add_le_add hshift hrec0) hrec1
    _ = 8 * (σ - 1 / 2) / T + 2 * ((σ - 1 / 2) / (T / 2) ^ 2) := by ring
    _ ≤ 8 * (σ - 1 / 2) / T + 8 * (σ - 1 / 2) / T := add_le_add le_rfl hsmall
    _ = _ := by ring

noncomputable def gammaReflectionDifference (σ T : ℝ) : ℝ :=
  (1 / 2) * (Complex.digamma (reflectedArg σ T) -
    Complex.digamma (directArg σ T)).im

noncomputable def zetaReflectionDifference (σ T : ℝ) : ℝ :=
  (logDeriv riemannZeta ((σ : ℂ) + T * I)).im -
    (logDeriv riemannZeta (((1 - σ : ℝ) : ℂ) + T * I)).im

theorem zetaReflectionDifference_eq_gamma {T : ℝ} (hT : T ≠ 0) (σ : ℝ)
    (hζ : riemannZeta ((σ : ℂ) + T * I) ≠ 0)
    (hζ' : riemannZeta (((1 - σ : ℝ) : ℂ) + T * I) ≠ 0) :
    zetaReflectionDifference σ T = gammaReflectionDifference σ T :=
  BacklundReflection.im_logDeriv_zeta_reflect_digamma hT σ hζ hζ'

theorem abs_gammaReflectionDifference_le {σ T : ℝ}
    (hT : 1 ≤ T) (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 5 / 4) :
    |gammaReflectionDifference σ T| ≤ 8 * (σ - 1 / 2) / T := by
  unfold gammaReflectionDifference
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    _ ≤ (1 / 2) * ‖Complex.digamma (reflectedArg σ T) -
        Complex.digamma (directArg σ T)‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (by norm_num)
    _ ≤ (1 / 2) * (16 * (σ - 1 / 2) / T) :=
      mul_le_mul_of_nonneg_left (norm_digamma_reflection_le hT hσ0 hσ1) (by norm_num)
    _ = _ := by ring

theorem integral_linear_majorant (T δ : ℝ) :
    (∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), 8 * (σ - 1 / 2) / T) =
      4 * δ ^ 2 / T := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      (f := fun σ : ℝ => σ) (g := fun _ => (1 / 2 : ℝ))
      (continuous_id.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    integral_id, intervalIntegral.integral_const]
  ring

theorem abs_integral_gammaReflectionDifference_le {T δ : ℝ}
    (hT : 1 ≤ T) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4) :
    |∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), gammaReflectionDifference σ T| ≤
      4 * δ ^ 2 / T := by
  rw [← Real.norm_eq_abs, ← integral_linear_majorant]
  apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
  · filter_upwards [] with σ hσ
    rw [Real.norm_eq_abs]
    exact abs_gammaReflectionDifference_le hT hσ.1.le (by linarith [hσ.2])
  · exact (show Continuous (fun σ : ℝ => 8 * (σ - 1 / 2) / T) by
      fun_prop).intervalIntegrable _ _

theorem abs_integral_zetaReflectionDifference_le {T δ : ℝ}
    (hT : 1 ≤ T) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4)
    (hζ : ∀ σ ∈ Icc (1 / 2) (1 / 2 + δ),
      riemannZeta ((σ : ℂ) + T * I) ≠ 0 ∧
      riemannZeta (((1 - σ : ℝ) : ℂ) + T * I) ≠ 0) :
    |∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), zetaReflectionDifference σ T| ≤
      4 * δ ^ 2 / T := by
  have he : (∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), zetaReflectionDifference σ T) =
      ∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), gammaReflectionDifference σ T := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le (by linarith : (1 / 2 : ℝ) ≤ 1 / 2 + δ)]
    intro σ hσ
    exact zetaReflectionDifference_eq_gamma (by linarith) σ (hζ σ hσ).1 (hζ σ hσ).2
  rw [he]
  exact abs_integral_gammaReflectionDifference_le hT hδ0 hδ1

end TernaryGoldbach.RSBounds.BacklundGammaReflection
end

-- RSBounds.BacklundPhase
section
open Filter Complex Metric
open scoped Topology

namespace TernaryGoldbach.RSBounds

theorem circle_powers_subsequence_one (u : Circle) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      Tendsto (fun j => (u : ℂ) ^ n j) atTop (𝓝 1) := by
  obtain ⟨n, hn, ht⟩ := (mapClusterPt_one_atTop_pow u).tendsto_subseq
  refine ⟨n, hn, ?_⟩
  have hc : Continuous ((↑) : Circle → ℂ) := continuous_subtype_val
  have h := (hc.tendsto (1 : Circle)).comp ht
  change Tendsto (fun j => ((u ^ n j : Circle) : ℂ)) atTop (𝓝 (1 : ℂ)) at h
  exact h

theorem complex_powers_phase_subsequence {z : ℂ} (hz : z ≠ 0) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      Tendsto (fun j => (z / (‖z‖ : ℂ)) ^ n j) atTop (𝓝 1) := by
  let u : Circle := ⟨z / (‖z‖ : ℂ), mem_sphere_zero_iff_norm.2 (by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr hz)])⟩
  exact circle_powers_subsequence_one u

theorem real_power_ratio_tendsto {z : ℂ} {n : ℕ → ℕ}
    (hp : Tendsto (fun j => (z / (‖z‖ : ℂ)) ^ n j) atTop (𝓝 1)) :
    Tendsto (fun j => (z ^ n j).re / ‖z‖ ^ n j) atTop (𝓝 (1 : ℝ)) := by
  have h := (Complex.continuous_re.tendsto (1 : ℂ)).comp hp
  simpa only [Function.comp_def, div_pow, ← Complex.ofReal_pow,
    Complex.div_ofReal_re, Complex.one_re] using h

theorem log_real_pow_div_tendsto {z : ℂ} (hz : z ≠ 0) {n : ℕ → ℕ}
    (hn : StrictMono n)
    (hp : Tendsto (fun j => (z / (‖z‖ : ℂ)) ^ n j) atTop (𝓝 1)) :
    Tendsto (fun j => Real.log |(z ^ n j).re| / (n j : ℝ))
      atTop (𝓝 (Real.log ‖z‖)) := by
  let w : ℂ := z / (‖z‖ : ℂ)
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hrc : (‖z‖ : ℂ) ≠ 0 := by simpa using hr.ne'
  have hdecomp : z = (‖z‖ : ℂ) * w := (mul_div_cancel₀ z hrc).symm
  have hpow (m : ℕ) : (z ^ m).re = ‖z‖ ^ m * (w ^ m).re := by
    calc (z ^ m).re = (((‖z‖ : ℂ) * w) ^ m).re := congrArg (fun t : ℂ => (t ^ m).re) hdecomp
      _ = ‖z‖ ^ m * (w ^ m).re := by
        rw [mul_pow]
        have hc : (‖z‖ : ℂ) ^ m = ((‖z‖ ^ m : ℝ) : ℂ) :=
          (Complex.ofReal_pow ‖z‖ m).symm
        rw [hc]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
  have hre : Tendsto (fun j => (w ^ n j).re) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, Complex.one_re] using
      (Complex.continuous_re.tendsto (1 : ℂ)).comp hp
  have hlog : Tendsto (fun j => Real.log ((w ^ n j).re)) atTop (𝓝 0) := by
    simpa using hre.log (one_ne_zero : (1 : ℝ) ≠ 0)
  have hnTop : Tendsto (fun j => (n j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn.tendsto_atTop
  have hlim : Tendsto (fun j => Real.log ‖z‖ + Real.log ((w ^ n j).re) / (n j : ℝ))
      atTop (𝓝 (Real.log ‖z‖)) := by
    have hconst : Tendsto (fun _ : ℕ => Real.log ‖z‖) atTop (𝓝 (Real.log ‖z‖)) :=
      tendsto_const_nhds
    simpa using hconst.add (hlog.div_atTop hnTop)
  have heq : (fun j => Real.log |(z ^ n j).re| / (n j : ℝ)) =ᶠ[atTop]
      (fun j => Real.log ‖z‖ + Real.log ((w ^ n j).re) / (n j : ℝ)) := by
    filter_upwards [hre.eventually (lt_mem_nhds (zero_lt_one : (0 : ℝ) < 1)),
      hnTop.eventually (eventually_gt_atTop (0 : ℝ))] with j hj hnj
    rw [Real.log_abs, hpow, Real.log_mul (pow_ne_zero _ hr.ne') hj.ne', Real.log_pow]
    rw [add_div, mul_div_cancel_left₀ _ hnj.ne']
  exact (Filter.tendsto_congr' heq).2 hlim

theorem exists_backlund_phase_sequence {z : ℂ} (hz : z ≠ 0) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      Tendsto (fun j => (z / (‖z‖ : ℂ)) ^ n j) atTop (𝓝 1) ∧
      Tendsto (fun j => Real.log |(z ^ n j).re| / (n j : ℝ))
        atTop (𝓝 (Real.log ‖z‖)) := by
  obtain ⟨n, hn, hp⟩ := complex_powers_phase_subsequence hz
  exact ⟨n, hn, hp, log_real_pow_div_tendsto hz hn hp⟩

end TernaryGoldbach.RSBounds
end

-- RSBounds.BacklundJensen
section
open Filter MeromorphicAt MeasureTheory MeromorphicOn Metric Real Set Topology Complex
open scoped ComplexConjugate

namespace TernaryGoldbach.RSBounds.BacklundJensen

noncomputable def zeroCount (f : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℝ :=
  ∑ᶠ u, (divisor f (closedBall c r) u : ℝ)

theorem zeroCount_mul_log_le_circleAverage {c : ℂ} {r R : ℝ} {f : ℂ → ℂ}
    (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c ≠ 0) :
    zeroCount f c r * Real.log (R / r) ≤
      circleAverage (fun z => Real.log ‖f z‖) c R - Real.log ‖f c‖ := by
  have hR : 0 < R := hr.trans hrR
  have hfa : AnalyticOnNhd ℂ f (closedBall c |R|) := by simpa [abs_of_pos hR] using hf
  have hJ := hfa.circleAverage_log_norm hfc
  rw [abs_of_pos hR] at hJ
  rw [hJ, add_sub_cancel_right, zeroCount, finsum_mul]
  refine finsum_le_finsum ?_ ?_ fun u => ?_
  · exact (divisor f (closedBall c r)).finiteSupport (isCompact_closedBall ..) |>.subset
      fun _ _ => (by simp_all)
  · exact (divisor f (closedBall c R)).finiteSupport (isCompact_closedBall ..) |>.subset
      fun _ _ => (by simp_all)
  · by_cases hbig : u ∈ closedBall c R
    · by_cases hsmall : u ∈ closedBall c r
      · simp only [hf.mono (closedBall_subset_closedBall hrR.le), hsmall,
          AnalyticOnNhd.divisor_apply, hf, hbig]
        by_cases huc : u = c
        · rw [huc, (hf c (by simp; positivity)).analyticOrderAt_eq_zero.mpr hfc]
          simp
        have hdist : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huc))
        have hdistR : ‖c - u‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm'] using hsmall
        apply mul_le_mul_of_nonneg_left ?_ (by simp)
        apply Real.log_le_log (div_pos hR hr)
        rw [← div_eq_mul_inv]
        exact div_le_div_of_nonneg_left hR.le hdist hdistR
      · simp only [hsmall, not_false_eq_true,
          Function.locallyFinsuppWithin.apply_eq_zero_of_notMem, Int.cast_zero, zero_mul]
        refine mul_nonneg (mod_cast hf.divisor_nonneg ..) ?_
        have hdist : 0 < ‖c - u‖ := by
          have : r < ‖c - u‖ := by simpa [mem_closedBall, dist_eq_norm', not_le] using hsmall
          linarith
        apply Real.log_nonneg
        rw [← div_eq_mul_inv, one_le_div hdist]
        simpa [mem_closedBall, dist_eq_norm'] using hbig
    · have hsmall : u ∉ closedBall c r := fun hu =>
        hbig (closedBall_subset_closedBall hrR.le hu)
      simp [hbig, hsmall]

noncomputable def powerAverage (f g : ℂ → ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  (f s ^ n + g s ^ n) / 2

theorem powerAverage_center {f g : ℂ → ℂ} {c : ℂ}
    (hc : g c = conj (f c)) (n : ℕ) :
    powerAverage f g n c = ((f c ^ n).re : ℂ) := by
  unfold powerAverage
  rw [hc, ← map_pow]
  rw [Complex.add_conj]
  push_cast
  ring

theorem analyticOnNhd_powerAverage {f g : ℂ → ℂ} {s : Set ℂ}
    (hf : AnalyticOnNhd ℂ f s) (hg : AnalyticOnNhd ℂ g s) (n : ℕ) :
    AnalyticOnNhd ℂ (powerAverage f g n) s := by
  intro z hz
  unfold powerAverage
  exact ((hf z hz).pow n |>.add ((hg z hz).pow n)).div_const (c := 2)

theorem norm_powerAverage_le {f g : ℂ → ℂ} {s : ℂ} {B : ℝ}
    (hf : ‖f s‖ ≤ Real.exp B) (hg : ‖g s‖ ≤ Real.exp B) (n : ℕ) :
    ‖powerAverage f g n s‖ ≤ Real.exp ((n : ℝ) * B) := by
  rw [powerAverage, norm_div, Complex.norm_ofNat]
  have h1 := norm_add_le (f s ^ n) (g s ^ n)
  rw [norm_pow, norm_pow] at h1
  have hp1 := pow_le_pow_left₀ (norm_nonneg (f s)) hf n
  have hp2 := pow_le_pow_left₀ (norm_nonneg (g s)) hg n
  rw [Real.exp_nat_mul]
  linarith

theorem log_norm_powerAverage_le {f g : ℂ → ℂ} {s : ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hf : ‖f s‖ ≤ Real.exp B) (hg : ‖g s‖ ≤ Real.exp B) (n : ℕ) :
    Real.log ‖powerAverage f g n s‖ ≤ (n : ℝ) * B := by
  by_cases hz : powerAverage f g n s = 0
  · simp [hz]
    positivity
  · have h := Real.log_le_log (norm_pos_iff.mpr hz) (norm_powerAverage_le hf hg n)
    simpa using h

end TernaryGoldbach.RSBounds.BacklundJensen
end

-- RSBounds.BacklundPairedJensen
section
open Real Complex Metric MeasureTheory MeromorphicOn Set

namespace TernaryGoldbach.RSBounds.BacklundPairedJensen

theorem divisor_at_zero_ge_one {f : ℂ → ℂ} {c u : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c ≠ 0)
    (hu : u ∈ closedBall c R) (hzero : f u = 0) :
    1 ≤ divisor f (closedBall c R) u := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hu, (hf u hu).meromorphicOrderAt_eq]
  have hz := (hf u hu).analyticOrderAt_ne_zero.mpr hzero
  have hc : c ∈ closedBall c R := by simpa using hR
  have hct : analyticOrderAt f c ≠ ⊤ := by
    rw [(hf c hc).analyticOrderAt_eq_zero.mpr hfc]
    exact ENat.natCast_ne_top 0
  have hut := hf.analyticOrderAt_ne_top_of_isPreconnected
    (convex_closedBall _ _).isPreconnected hc hu hct
  cases h : analyticOrderAt f u with
  | top => exact absurd h hut
  | coe n =>
    simp only [ENat.map_natCast, WithTop.untop₀_coe]
    have hn : 0 < n := by
      rw [h] at hz
      have : n ≠ 0 := by rintro rfl; exact hz rfl
      omega
    exact_mod_cast hn

theorem reflected_distance_product_le {a b : ℝ}
    (ha : a < 5 / 4) (hb : 1 - a ≤ b) :
    (5 / 4 - a) * (5 / 4 - b) ≤ (3 / 4 : ℝ) ^ 2 := by
  have h := mul_le_mul_of_nonneg_left (show 5 / 4 - b ≤ 1 / 4 + a by linarith)
    (show 0 ≤ 5 / 4 - a by linarith)
  nlinarith [sq_nonneg (a - 1 / 2)]

theorem paired_log_weight {R a b : ℝ} (hR : 0 < R)
    (ha : a < 5 / 4) (hb : b ≤ 1 / 2) (hpair : 1 - a ≤ b) :
    2 * Real.log (R / (3 / 4)) ≤
      Real.log (R / (5 / 4 - a)) + Real.log (R / (5 / 4 - b)) := by
  have hu : 0 < 5 / 4 - a := by linarith
  have hv : 0 < 5 / 4 - b := by linarith
  have hp := reflected_distance_product_le ha hpair
  have hh : (R / (3 / 4)) ^ 2 ≤ (R / (5 / 4 - a)) * (R / (5 / 4 - b)) := by
    rw [div_mul_div_comm, le_div_iff₀ (mul_pos hu hv)]
    nlinarith [mul_le_mul_of_nonneg_left hp (sq_nonneg R)]
  have hl := Real.log_le_log (show 0 < (R / (3 / 4)) ^ 2 by positivity) hh
  rw [Real.log_pow, Real.log_mul (ne_of_gt (div_pos hR hu))
    (ne_of_gt (div_pos hR hv))] at hl
  simpa using hl

theorem far_log_weight {R a b : ℝ} (hR : 0 < R)
    (ha : a < 5 / 4) (hpair : 1 - a ≤ b) (hout : R < 5 / 4 - b) :
    2 * Real.log (R / (3 / 4)) ≤ Real.log (R / (5 / 4 - a)) := by
  have hu : 0 < 5 / 4 - a := by linarith
  have hp := reflected_distance_product_le ha hpair
  have hRu : R * (5 / 4 - a) ≤ (3 / 4 : ℝ) ^ 2 := by
    nlinarith [mul_lt_mul_of_pos_left hout hu]
  have hh : (R / (3 / 4)) ^ 2 ≤ R / (5 / 4 - a) := by
    rw [le_div_iff₀ hu]
    nlinarith [mul_le_mul_of_nonneg_left hRu hR.le]
  have hl := Real.log_le_log (show 0 < (R / (3 / 4)) ^ 2 by positivity) hh
  simpa only [Real.log_pow, Nat.cast_ofNat] using hl

theorem paired_jensen_with_unpaired_lower {f : ℂ → ℂ} {R : ℝ} (hR : 3 / 4 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall (5 / 4 : ℂ) R))
    (hfc : f (5 / 4 : ℂ) ≠ 0) {k n : ℕ} {a b : ℕ → ℝ}
    (ha_zero : ∀ i, i < k + n → f (a i : ℂ) = 0)
    (ha_lo : ∀ i, i < k + n → 1 / 2 ≤ a i)
    (ha_hi : ∀ i, i < k + n → a i < 5 / 4)
    (ha_inj : ∀ i j, i < k + n → j < k + n → a i = a j → i = j)
    (hb_zero : ∀ i, i < n → f (b i : ℂ) = 0)
    (hb_pair : ∀ i, i < n → 1 - a (i + k) ≤ b i)
    (hb_hi : ∀ i, i < n → b i ≤ 1 / 2)
    (hb_inj : ∀ i j, i < n → j < n → b i = b j → i = j)
    (hdisj : ∀ i j, i < k + n → j < n → a i ≠ b j) :
    (2 * (n : ℝ) + k) * Real.log (R / (3 / 4)) ≤
      circleAverage (fun z => Real.log ‖f z‖) (5 / 4 : ℂ) R -
        Real.log ‖f (5 / 4 : ℂ)‖ := by
  classical
  have hR0 : 0 < R := by linarith
  let c : ℂ := 5 / 4
  let D := divisor f (closedBall c R)
  let w : ℂ → ℝ := fun u => (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹)
  have hDfin : (D.support : Set ℂ).Finite := D.finiteSupport (isCompact_closedBall c R)
  have hwfin : w.support.Finite := hDfin.subset (by
    intro u hu
    simp only [Function.mem_support, w, ne_eq, mul_eq_zero, not_or, Int.cast_eq_zero] at hu
    exact hu.1)
  have hw_nonneg : ∀ u, 0 ≤ w u := by
    intro u
    by_cases hDu : D u = 0
    · simp [w, hDu]
    have hu : u ∈ closedBall c R := D.supportWithinDomain (by
      simpa only [Function.mem_support] using hDu)
    have huc : c ≠ u := by
      intro he
      apply hDu
      subst u
      change divisor f (closedBall c R) c = 0
      rw [MeromorphicOn.divisor_apply hf.meromorphicOn hu,
        (hf c hu).meromorphicOrderAt_eq, (hf c hu).analyticOrderAt_eq_zero.mpr hfc]
      rfl
    have hd : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huc)
    apply mul_nonneg (by exact_mod_cast (hf.divisor_nonneg u))
    apply Real.log_nonneg
    rw [← div_eq_mul_inv, one_le_div hd]
    simpa only [mem_closedBall, dist_eq_norm'] using hu
  have hj : (∑ᶠ u, w u) = circleAverage (fun z => Real.log ‖f z‖) c R - Real.log ‖f c‖ := by
    have hfa : AnalyticOnNhd ℂ f (closedBall c |R|) := by simpa [abs_of_pos hR0] using hf
    have h := hfa.circleAverage_log_norm hfc
    rw [abs_of_pos hR0] at h
    simpa only [w, D] using (eq_sub_iff_add_eq.mpr h.symm)
  have hnrm (x : ℝ) (hx : x < 5 / 4) : ‖c - (x : ℂ)‖ = 5 / 4 - x := by
    have he : c - (x : ℂ) = ((5 / 4 - x : ℝ) : ℂ) := by dsimp [c]; push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hw_real (x : ℝ) (hx : x < 5 / 4) (hd : 5 / 4 - x ≤ R) (hz : f (x : ℂ) = 0) :
      Real.log (R / (5 / 4 - x)) ≤ w (x : ℂ) := by
    have hu : (x : ℂ) ∈ closedBall c R := by
      simpa only [mem_closedBall, dist_eq_norm', hnrm x hx] using hd
    have hD1 : (1 : ℝ) ≤ (D (x : ℂ) : ℝ) := by
      exact_mod_cast divisor_at_zero_ge_one hR0.le hf hfc hu hz
    have hl : 0 ≤ Real.log (R / (5 / 4 - x)) :=
      Real.log_nonneg ((one_le_div (by linarith)).mpr hd)
    dsimp [w]
    rw [hnrm x hx, ← div_eq_mul_inv]
    exact le_mul_of_one_le_left hl hD1
  have hp (i : ℕ) (hi : i < n) :
      2 * Real.log (R / (3 / 4)) ≤ w (a (i + k) : ℂ) + w (b i : ℂ) := by
    have hik : i + k < k + n := by omega
    have ha := hw_real (a (i + k)) (ha_hi (i + k) hik)
      (by linarith [ha_lo (i + k) hik]) (ha_zero (i + k) hik)
    by_cases hb : 5 / 4 - b i ≤ R
    · have hbw := hw_real (b i) (by linarith [hb_hi i hi]) hb (hb_zero i hi)
      linarith [paired_log_weight hR0 (ha_hi (i + k) (by omega)) (hb_hi i hi) (hb_pair i hi)]
    · have hw := hw_nonneg (b i : ℂ)
      linarith [far_log_weight hR0 (ha_hi (i + k) (by omega)) (hb_pair i hi) (lt_of_not_ge hb)]
  let Za : Finset ℂ := (Finset.range (k + n)).image (fun i => (a i : ℂ))
  let Zb : Finset ℂ := (Finset.range n).image (fun i => (b i : ℂ))
  have hai : ∀ i ∈ Finset.range (k + n), ∀ j ∈ Finset.range (k + n), (a i : ℂ) = (a j : ℂ) → i = j := by
    intro i hi j hj he
    exact ha_inj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (by exact_mod_cast he)
  have hbi : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n, (b i : ℂ) = (b j : ℂ) → i = j := by
    intro i hi j hj he
    exact hb_inj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (by exact_mod_cast he)
  have hdj : Disjoint Za Zb := by
    rw [Finset.disjoint_left]
    intro z hza hzb
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hza
    obtain ⟨j, hj, he'⟩ := Finset.mem_image.mp hzb
    exact hdisj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
      (by exact_mod_cast (he.trans he'.symm))
  have hsingle (i : ℕ) (hi : i < k) : Real.log (R / (3 / 4)) ≤ w (a i : ℂ) := by
    have hii : i < k + n := by omega
    have ha := hw_real (a i) (ha_hi i hii) (by linarith [ha_lo i hii]) (ha_zero i hii)
    have hd : 0 < 5 / 4 - a i := by linarith [ha_hi i hii]
    have hh : R / (3 / 4) ≤ R / (5 / 4 - a i) :=
      div_le_div_of_nonneg_left hR0.le hd (by linarith [ha_lo i hii])
    exact (Real.log_le_log (by positivity) hh).trans ha
  have hsingle_sum : (k : ℝ) * Real.log (R / (3 / 4)) ≤ ∑ i ∈ Finset.range k, w (a i : ℂ) := by
    have hh := Finset.sum_le_sum (fun i hi => hsingle i (Finset.mem_range.mp hi))
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hh
  have hpair_sum : 2 * (n : ℝ) * Real.log (R / (3 / 4)) ≤
      ∑ i ∈ Finset.range n, (w (a (i + k) : ℂ) + w (b i : ℂ)) := by
    have hh := Finset.sum_le_sum (fun i hi => hp i (Finset.mem_range.mp hi))
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc,
      mul_left_comm] using hh
  have hsum : (2 * (n : ℝ) + k) * Real.log (R / (3 / 4)) ≤ ∑ z ∈ Za ∪ Zb, w z := by
    rw [Finset.sum_union hdj, Finset.sum_image hai, Finset.sum_image hbi,
      Finset.sum_range_add, add_assoc, ← Finset.sum_add_distrib]
    simp only [Nat.add_comm k] at *
    nlinarith [hsingle_sum, hpair_sum]
  let F := hwfin.toFinset
  have hsum_le : ∑ z ∈ Za ∪ Zb, w z ≤ ∑ z ∈ F, w z := by
    calc
      _ ≤ ∑ z ∈ (Za ∪ Zb) ∪ F, w z :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun z _ _ => hw_nonneg z)
      _ = ∑ z ∈ F, w z := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro z _ hz
        have hz' : z ∉ w.support := by simpa only [F, Set.Finite.mem_toFinset] using hz
        simpa only [Function.mem_support, not_not] using hz'
  have hfinsum : (∑ᶠ u, w u) = ∑ z ∈ F, w z :=
    finsum_eq_sum_of_support_subset_of_finite w (le_refl _) hwfin
  exact hsum.trans (hsum_le.trans_eq (hfinsum.symm.trans hj))

end TernaryGoldbach.RSBounds.BacklundPairedJensen
end

-- RSBounds.BacklundFirstCrossing
section
namespace TernaryGoldbach.RSBounds.BacklundFirstCrossing

open Set

theorem exists_firstCrossing {φ : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn φ (Set.Icc a b)) (hlo : φ a < ℓ) (hhi : ℓ < φ b) :
    ∃ c ∈ Set.Ioo a b, φ c = ℓ ∧ ∀ x ∈ Set.Ico a c, φ x < ℓ := by
  set S : Set ℝ := Set.Icc a b ∩ φ ⁻¹' {ℓ} with hSdef

  have hSne : S.Nonempty := by
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hab hcont ⟨hlo.le, hhi.le⟩
    exact ⟨x, hx, hfx⟩

  have hSclosed : IsClosed S :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hSbdd : BddBelow S := ⟨a, fun x hx => hx.1.1⟩
  set c : ℝ := sInf S with hcdef
  have hcS : c ∈ S := hSclosed.csInf_mem hSne hSbdd
  have hcIcc : c ∈ Set.Icc a b := hcS.1
  have hφc : φ c = ℓ := hcS.2
  have hac : a < c := by
    refine hcIcc.1.lt_of_ne ?_
    intro h
    exact hlo.ne (by rw [h]; exact hφc)
  have hcb : c < b := by
    refine hcIcc.2.lt_of_ne ?_
    intro h
    exact hhi.ne' (by rw [← h]; exact hφc)
  refine ⟨c, ⟨hac, hcb⟩, hφc, ?_⟩

  intro x hx
  have hxb : x ∈ Set.Icc a b := ⟨hx.1, hx.2.le.trans hcIcc.2⟩
  by_contra hge
  push Not at hge
  have hne : φ x ≠ ℓ := by
    intro heq
    have hxS : x ∈ S := ⟨hxb, heq⟩
    exact absurd hx.2 (not_lt.mpr (csInf_le hSbdd hxS))
  have hlt : ℓ < φ x := lt_of_le_of_ne hge (Ne.symm hne)

  have hsub : Set.Icc a x ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hxb.2
  obtain ⟨y, hy, hfy⟩ :=
    intermediate_value_Icc hx.1 (hcont.mono hsub) ⟨hlo.le, hlt.le⟩
  have hyS : y ∈ S := ⟨⟨hy.1, hy.2.trans hxb.2⟩, hfy⟩
  have hcy : c ≤ y := csInf_le hSbdd hyS
  exact absurd (hcy.trans hy.2) (not_le.mpr hx.2)

theorem exists_lastCrossing {φ : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn φ (Set.Icc a b)) (hlo : φ a < ℓ) (hhi : ℓ < φ b) :
    ∃ c ∈ Set.Ioo a b, φ c = ℓ ∧ ∀ x ∈ Set.Ioc c b, ℓ < φ x := by
  set S : Set ℝ := Set.Icc a b ∩ φ ⁻¹' {ℓ} with hSdef
  have hSne : S.Nonempty := by
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hab hcont ⟨hlo.le, hhi.le⟩
    exact ⟨x, hx, hfx⟩
  have hSclosed : IsClosed S :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hSbdd : BddAbove S := ⟨b, fun x hx => hx.1.2⟩
  set c : ℝ := sSup S with hcdef
  have hcS : c ∈ S := hSclosed.csSup_mem hSne hSbdd
  have hcIcc : c ∈ Set.Icc a b := hcS.1
  have hφc : φ c = ℓ := hcS.2
  have hac : a < c := by
    refine hcIcc.1.lt_of_ne ?_
    intro h
    exact hlo.ne (by rw [h]; exact hφc)
  have hcb : c < b := by
    refine hcIcc.2.lt_of_ne ?_
    intro h
    exact hhi.ne' (by rw [← h]; exact hφc)
  refine ⟨c, ⟨hac, hcb⟩, hφc, ?_⟩

  intro x hx
  have hxb : x ∈ Set.Icc a b := ⟨hcIcc.1.trans hx.1.le, hx.2⟩
  by_contra hge
  push Not at hge
  have hne : φ x ≠ ℓ := by
    intro heq
    have hxS : x ∈ S := ⟨hxb, heq⟩
    exact absurd hx.1 (not_lt.mpr (le_csSup hSbdd hxS))
  have hlt : φ x < ℓ := lt_of_le_of_ne hge hne

  have hsub : Set.Icc x b ⊆ Set.Icc a b := Set.Icc_subset_Icc hxb.1 le_rfl
  obtain ⟨y, hy, hfy⟩ :=
    intermediate_value_Icc hx.2 (hcont.mono hsub) ⟨hlt.le, hhi.le⟩
  have hyS : y ∈ S := ⟨⟨hxb.1.trans hy.1, hy.2⟩, hfy⟩
  have hyc : y ≤ c := le_csSup hSbdd hyS
  exact absurd (hy.1.trans hyc) (not_le.mpr hx.1)

theorem exists_firstCrossing_family {φ : ℝ → ℝ} {a b ℓ₀ : ℝ} {m : ℕ}
    (hab : a ≤ b) (hcont : ContinuousOn φ (Set.Icc a b))
    (hℓ₀ : φ a < ℓ₀) (htop : ℓ₀ + ((m : ℝ) - 1) * Real.pi < φ b) :
    ∃ c : ℕ → ℝ,
      (∀ i, i < m → c i ∈ Set.Ioo a b) ∧
      (∀ i j, i < j → j < m → c i < c j) ∧
      (∀ i, i < m → φ (c i) = ℓ₀ + (i : ℝ) * Real.pi) ∧
      (∀ i, i < m → ∀ x ∈ Set.Ico a (c i), φ x < ℓ₀ + (i : ℝ) * Real.pi) := by
  have hpi := Real.pi_pos
  have key : ∀ i : ℕ, i < m →
      ∃ c ∈ Set.Ioo a b, φ c = ℓ₀ + (i : ℝ) * Real.pi ∧
        ∀ x ∈ Set.Ico a c, φ x < ℓ₀ + (i : ℝ) * Real.pi := by
    intro i hi
    have hi0 : (0 : ℝ) ≤ (i : ℝ) * Real.pi :=
      mul_nonneg (Nat.cast_nonneg i) hpi.le
    have hlo : φ a < ℓ₀ + (i : ℝ) * Real.pi := by linarith
    have hcast : (i : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hi
    have hmul : (i : ℝ) * Real.pi ≤ ((m : ℝ) - 1) * Real.pi :=
      mul_le_mul_of_nonneg_right (by linarith) hpi.le
    have hhi : ℓ₀ + (i : ℝ) * Real.pi < φ b := by linarith
    exact exists_firstCrossing hab hcont hlo hhi
  choose! c hmem hval hmin using key
  refine ⟨c, hmem, ?_, hval, hmin⟩
  intro i j hij hjm
  have him : i < m := hij.trans hjm
  have hstep : (i : ℝ) * Real.pi < (j : ℝ) * Real.pi := by
    have : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    exact mul_lt_mul_of_pos_right this hpi
  by_contra hle
  push Not at hle
  rcases lt_or_eq_of_le hle with hlt | heq
  ·
    have h1 : φ (c j) < ℓ₀ + (i : ℝ) * Real.pi :=
      hmin i him (c j) ⟨(hmem j hjm).1.le, hlt⟩
    have h2 : φ (c j) = ℓ₀ + (j : ℝ) * Real.pi := hval j hjm
    linarith
  ·
    have h1 : φ (c i) = ℓ₀ + (i : ℝ) * Real.pi := hval i him
    have h2 : φ (c j) = ℓ₀ + (j : ℝ) * Real.pi := hval j hjm
    rw [heq] at h2
    linarith

theorem exists_lastCrossing_family {φ : ℝ → ℝ} {a b ℓ₀ : ℝ} {m : ℕ}
    (hab : a ≤ b) (hcont : ContinuousOn φ (Set.Icc a b))
    (hℓ₀ : ℓ₀ < φ b) (hbot : φ a < ℓ₀ - ((m : ℝ) - 1) * Real.pi) :
    ∃ c : ℕ → ℝ,
      (∀ i, i < m → c i ∈ Set.Ioo a b) ∧
      (∀ i j, i < j → j < m → c j < c i) ∧
      (∀ i, i < m → φ (c i) = ℓ₀ - (i : ℝ) * Real.pi) ∧
      (∀ i, i < m → ∀ x ∈ Set.Ioc (c i) b, ℓ₀ - (i : ℝ) * Real.pi < φ x) := by
  have hpi := Real.pi_pos
  have key : ∀ i : ℕ, i < m →
      ∃ c ∈ Set.Ioo a b, φ c = ℓ₀ - (i : ℝ) * Real.pi ∧
        ∀ x ∈ Set.Ioc c b, ℓ₀ - (i : ℝ) * Real.pi < φ x := by
    intro i hi
    have hi0 : (0 : ℝ) ≤ (i : ℝ) * Real.pi :=
      mul_nonneg (Nat.cast_nonneg i) hpi.le
    have hcast : (i : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hi
    have hmul : (i : ℝ) * Real.pi ≤ ((m : ℝ) - 1) * Real.pi :=
      mul_le_mul_of_nonneg_right (by linarith) hpi.le
    have hlo : φ a < ℓ₀ - (i : ℝ) * Real.pi := by linarith
    have hhi : ℓ₀ - (i : ℝ) * Real.pi < φ b := by linarith
    exact exists_lastCrossing hab hcont hlo hhi
  choose! c hmem hval hmax using key
  refine ⟨c, hmem, ?_, hval, hmax⟩
  intro i j hij hjm
  have him : i < m := hij.trans hjm
  have hstep : (i : ℝ) * Real.pi < (j : ℝ) * Real.pi := by
    have : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    exact mul_lt_mul_of_pos_right this hpi
  by_contra hle
  push Not at hle
  rcases lt_or_eq_of_le hle with hlt | heq
  ·
    have h1 : ℓ₀ - (i : ℝ) * Real.pi < φ (c j) :=
      hmax i him (c j) ⟨hlt, (hmem j hjm).2.le⟩
    have h2 : φ (c j) = ℓ₀ - (j : ℝ) * Real.pi := hval j hjm
    linarith
  ·
    have h1 : φ (c i) = ℓ₀ - (i : ℝ) * Real.pi := hval i him
    have h2 : φ (c j) = ℓ₀ - (j : ℝ) * Real.pi := hval j hjm
    rw [← heq] at h2
    linarith

theorem exists_first_halfturn_level (x : ℝ) :
    ∃ ℓ : ℝ, (∃ k : ℤ, ℓ = Real.pi / 2 + (k : ℝ) * Real.pi) ∧
      x < ℓ ∧ ℓ ≤ x + Real.pi := by
  have hpi := Real.pi_pos
  set y : ℝ := (x - Real.pi / 2) / Real.pi with hy
  have hyπ : y * Real.pi = x - Real.pi / 2 := div_mul_cancel₀ _ hpi.ne'
  refine ⟨Real.pi / 2 + ((⌊y⌋ + 1 : ℤ) : ℝ) * Real.pi, ⟨⌊y⌋ + 1, rfl⟩, ?_, ?_⟩
  · have h1 : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
    have h3 : y * Real.pi < ((⌊y⌋ : ℝ) + 1) * Real.pi :=
      mul_lt_mul_of_pos_right h1 hpi
    push_cast
    linarith
  · have h1 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
    have h3 : (⌊y⌋ : ℝ) * Real.pi ≤ y * Real.pi :=
      mul_le_mul_of_nonneg_right h1 hpi.le
    push_cast
    linarith

theorem exists_last_halfturn_level (x : ℝ) :
    ∃ ℓ : ℝ, (∃ k : ℤ, ℓ = Real.pi / 2 + (k : ℝ) * Real.pi) ∧
      ℓ < x ∧ x - Real.pi ≤ ℓ := by
  have hpi := Real.pi_pos
  set y : ℝ := (x - Real.pi / 2) / Real.pi with hy
  have hyπ : y * Real.pi = x - Real.pi / 2 := div_mul_cancel₀ _ hpi.ne'
  refine ⟨Real.pi / 2 + ((⌈y⌉ - 1 : ℤ) : ℝ) * Real.pi, ⟨⌈y⌉ - 1, rfl⟩, ?_, ?_⟩
  · have h1 : (⌈y⌉ : ℝ) < y + 1 := Int.ceil_lt_add_one y
    have h3 : ((⌈y⌉ : ℝ) - 1) * Real.pi < y * Real.pi :=
      mul_lt_mul_of_pos_right (by linarith) hpi
    push_cast
    linarith
  · have h1 : y ≤ (⌈y⌉ : ℝ) := Int.le_ceil y
    have h3 : (y - 1) * Real.pi ≤ ((⌈y⌉ : ℝ) - 1) * Real.pi :=
      mul_le_mul_of_nonneg_right (by linarith) hpi.le
    push_cast
    linarith

theorem cos_eq_zero_of_halfturn {ℓ : ℝ}
    (h : ∃ k : ℤ, ℓ = Real.pi / 2 + (k : ℝ) * Real.pi) : Real.cos ℓ = 0 := by
  obtain ⟨k, rfl⟩ := h
  rw [Real.cos_eq_zero_iff]
  exact ⟨k, by ring⟩

theorem halfturn_add_nat_mul {ℓ : ℝ}
    (h : ∃ k : ℤ, ℓ = Real.pi / 2 + (k : ℝ) * Real.pi) (n : ℕ) :
    ∃ k : ℤ, ℓ + (n : ℝ) * Real.pi = Real.pi / 2 + (k : ℝ) * Real.pi := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k + n, by push_cast; ring⟩

theorem halfturn_sub_nat_mul {ℓ : ℝ}
    (h : ∃ k : ℤ, ℓ = Real.pi / 2 + (k : ℝ) * Real.pi) (n : ℕ) :
    ∃ k : ℤ, ℓ - (n : ℝ) * Real.pi = Real.pi / 2 + (k : ℝ) * Real.pi := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k - n, by push_cast; ring⟩

end TernaryGoldbach.RSBounds.BacklundFirstCrossing
end

-- RSBounds.BacklundPairedCrossing
section
open Real Complex Metric MeasureTheory MeromorphicOn Set
open TernaryGoldbach.RSBounds.BacklundFirstCrossing
open TernaryGoldbach.RSBounds.BacklundPairedJensen

namespace TernaryGoldbach.RSBounds.BacklundPairedCrossing

theorem crossing_count_le {f : ℂ → ℂ} {R E : ℝ}
    (hR : 3 / 4 < R) (hE : 0 < E)
    (hf : AnalyticOnNhd ℂ f (closedBall (5 / 4 : ℂ) R))
    (hfc : f (5 / 4 : ℂ) ≠ 0) {ψ : ℝ → ℝ}
    (hψcont : ContinuousOn ψ (Icc (-1 / 4 : ℝ) (5 / 4 : ℝ)))
    (hψzero : ∀ x ∈ Icc (-1 / 4 : ℝ) (5 / 4 : ℝ),
      Real.cos (ψ x) = 0 → f (x : ℂ) = 0)
    (hψdelta : ∀ δ : ℝ, 0 < δ → δ ≤ 3 / 4 →
      |(ψ (1 / 2 + δ) - ψ (1 / 2)) - (ψ (1 / 2) - ψ (1 / 2 - δ))| ≤ E)
    {m₁ : ℕ} (hsweep : (m₁ : ℝ) * Real.pi < ψ (5 / 4) - ψ (1 / 2)) :
    (m₁ : ℝ) ≤ (circleAverage (fun z => Real.log ‖f z‖) (5 / 4 : ℂ) R -
      Real.log ‖f (5 / 4 : ℂ)‖) / (2 * Real.log (R / (3 / 4))) + 1 + E / (2 * Real.pi) := by
  let J := circleAverage (fun z => Real.log ‖f z‖) (5 / 4 : ℂ) R -
    Real.log ‖f (5 / 4 : ℂ)‖
  have hlog : 0 < Real.log (R / (3 / 4)) :=
    Real.log_pos ((one_lt_div (by norm_num)).mpr hR)
  have hJ : 0 ≤ J := by
    have hh := BacklundJensen.zeroCount_mul_log_le_circleAverage
      (by norm_num : (0 : ℝ) < 3 / 4) hR hf hfc
    have hn : 0 ≤ BacklundJensen.zeroCount f (5 / 4 : ℂ) (3 / 4) := by
      unfold BacklundJensen.zeroCount
      apply finsum_nonneg
      intro u
      exact_mod_cast (hf.mono (closedBall_subset_closedBall hR.le)).divisor_nonneg u
    exact le_trans (mul_nonneg hn hlog.le) hh
  have hJnonneg : 0 ≤ J / (2 * Real.log (R / (3 / 4))) := div_nonneg hJ (by positivity)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos

  set D : ℕ := 1 + ⌈E / Real.pi⌉₊ with hD_def
  have hD_cast : (D : ℝ) = 1 + (⌈E / Real.pi⌉₊ : ℝ) := by
    rw [hD_def]; push_cast; ring
  have hceil_ge : E
      ≤ (⌈E / Real.pi⌉₊ : ℝ) * Real.pi := by
    have h1 : E / Real.pi
        ≤ (⌈E / Real.pi⌉₊ : ℝ) := Nat.le_ceil _
    have h2 := mul_le_mul_of_nonneg_right h1 hπ.le
    rwa [div_mul_cancel₀ _ hπ.ne'] at h2
  have hDπ_ge : E + Real.pi ≤ (D : ℝ) * Real.pi := by
    have hexp : (D : ℝ) * Real.pi
        = Real.pi + (⌈E / Real.pi⌉₊ : ℝ) * Real.pi := by
      rw [hD_cast]; ring
    linarith [hceil_ge]
  have hD_le : (D : ℝ) ≤ 2 + E / Real.pi := by
    have h0 : (0 : ℝ) ≤ E / Real.pi := by positivity
    have h1 : (⌈E / Real.pi⌉₊ : ℝ)
        < E / Real.pi + 1 := Nat.ceil_lt_add_one h0
    linarith [hD_cast, h1]

  obtain ⟨ℓ₀, hℓ₀_ht, hℓ₀_gt, hℓ₀_le⟩ := exists_first_halfturn_level (ψ (1 / 2))
  have hsub_right : Set.Icc (1 / 2 : ℝ) (5 / 4 : ℝ)
      ⊆ Set.Icc (-1 / 4 : ℝ) (5 / 4 : ℝ) := Set.Icc_subset_Icc (by norm_num) le_rfl
  have htop : ℓ₀ + ((m₁ : ℝ) - 1) * Real.pi < ψ (5 / 4) := by
    have hexp : ℓ₀ + ((m₁ : ℝ) - 1) * Real.pi
        = ℓ₀ + (m₁ : ℝ) * Real.pi - Real.pi := by ring
    linarith [hℓ₀_le, hsweep, hexp]
  obtain ⟨c, hc_mem, hc_mono, hc_val, _hc_min⟩ :=
    exists_firstCrossing_family (by norm_num : (1 / 2 : ℝ) ≤ 5 / 4)
      (hψcont.mono hsub_right) hℓ₀_gt htop
  have hc_zero : ∀ i, i < m₁ → f (c i : ℂ) = 0 := by
    intro i hi
    have hmem := hc_mem i hi
    refine hψzero (c i) ⟨by linarith [hmem.1], hmem.2.le⟩ ?_
    rw [hc_val i hi]
    exact cos_eq_zero_of_halfturn (halfturn_add_nat_mul hℓ₀_ht i)
  have hc_inj : ∀ i j, i < m₁ → j < m₁ → c i = c j → i = j := by
    intro i j hi hj heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact (ne_of_lt (hc_mono i j hij hj)) heq
    · exact (ne_of_lt (hc_mono j i hji hi)) heq.symm
  have hJmul : J / (2 * Real.log (R / (3 / 4))) * (2 * Real.log (R / (3 / 4))) = J :=
    div_mul_cancel₀ _ (by positivity)
  have hEdiv : E / (2 * Real.pi) = (E / Real.pi) / 2 := by ring
  by_cases hm₁D : m₁ ≤ D
  · have hm₁R : (m₁ : ℝ) ≤ (D : ℝ) := by exact_mod_cast hm₁D
    have hj := paired_jensen_with_unpaired_lower (k := m₁) (n := 0)
      (a := c) (b := fun _ => 0) hR hf hfc
      (fun i hi => hc_zero i (by simpa using hi))
      (fun i hi => (hc_mem i (by simpa using hi)).1.le)
      (fun i hi => (hc_mem i (by simpa using hi)).2)
      (fun i j hi hj he => hc_inj i j (by simpa using hi) (by simpa using hj) he)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    have hcnt : (m₁ : ℝ) ≤ J / (2 * Real.log (R / (3 / 4))) + (D : ℝ) / 2 := by
      have hm := mul_le_mul_of_nonneg_right hm₁R hlog.le
      dsimp [J] at hJmul ⊢
      norm_num only [Nat.cast_zero, zero_mul, zero_add] at hj
      nlinarith
    linarith [hD_le, hEdiv]
  ·
    have hDlt : D < m₁ := not_le.mp hm₁D
    set n' : ℕ := m₁ - D with hn'_def
    have hn'_cast : (n' : ℝ) = (m₁ : ℝ) - (D : ℝ) := by
      have h : n' + D = m₁ := by omega
      have h2 : (n' : ℝ) + (D : ℝ) = (m₁ : ℝ) := by exact_mod_cast h
      linarith
    have hn'π : (n' : ℝ) * Real.pi = (m₁ : ℝ) * Real.pi - (D : ℝ) * Real.pi := by
      rw [hn'_cast]; ring
    have hdelta34 := hψdelta (3 / 4) (by norm_num) le_rfl
    rw [show (1 / 2 : ℝ) + 3 / 4 = 5 / 4 by norm_num,
      show (1 / 2 : ℝ) - 3 / 4 = -1 / 4 by norm_num] at hdelta34
    have hVL34 : (m₁ : ℝ) * Real.pi - E
        < ψ (1 / 2) - ψ (-1 / 4) := by
      have h2 := (abs_le.mp hdelta34).2
      linarith [hsweep]
    obtain ⟨ℓ'₀, hℓ'₀_ht, hℓ'₀_lt, hℓ'₀_ge⟩ := exists_last_halfturn_level (ψ (1 / 2))
    have hsub_left : Set.Icc (-1 / 4 : ℝ) (1 / 2 : ℝ)
        ⊆ Set.Icc (-1 / 4 : ℝ) (5 / 4 : ℝ) := Set.Icc_subset_Icc le_rfl (by norm_num)
    have hbot : ψ (-1 / 4) < ℓ'₀ - ((n' : ℝ) - 1) * Real.pi := by
      have hexp : ℓ'₀ - ((n' : ℝ) - 1) * Real.pi
          = ℓ'₀ - (n' : ℝ) * Real.pi + Real.pi := by ring
      linarith [hℓ'₀_ge, hDπ_ge, hVL34, hn'π, hexp]
    obtain ⟨l, hl_mem, hl_anti, hl_val, hl_max⟩ :=
      exists_lastCrossing_family (by norm_num : (-1 / 4 : ℝ) ≤ 1 / 2)
        (hψcont.mono hsub_left) hℓ'₀_lt hbot
    have hl_zero : ∀ j, j < n' → f (l j : ℂ) = 0 := by
      intro j hj
      have hmem := hl_mem j hj
      refine hψzero (l j) ⟨hmem.1.le, by linarith [hmem.2]⟩ ?_
      rw [hl_val j hj]
      exact cos_eq_zero_of_halfturn (halfturn_sub_nat_mul hℓ'₀_ht j)
    have hinterlace : ∀ k, k < n' → 1 - c (k + D) ≤ l k := by
      intro k hk
      have hkD : k + D < m₁ := by omega
      have hmemc := hc_mem (k + D) hkD
      set δ : ℝ := c (k + D) - 1 / 2 with hδ_def
      have hδ_pos : 0 < δ := by rw [hδ_def]; linarith [hmemc.1]
      have hδ_le : δ ≤ 3 / 4 := by rw [hδ_def]; linarith [hmemc.2]
      have h12δ : (1 / 2 : ℝ) + δ = c (k + D) := by rw [hδ_def]; ring
      have hd := hψdelta δ hδ_pos hδ_le
      rw [h12δ] at hd
      have hval := hc_val (k + D) hkD
      have hcastπ : ((k + D : ℕ) : ℝ) * Real.pi
          = (k : ℝ) * Real.pi + (D : ℝ) * Real.pi := by push_cast; ring
      have hVL_gt : ((k : ℝ) + 1) * Real.pi < ψ (1 / 2) - ψ (1 / 2 - δ) := by
        have h2 := (abs_le.mp hd).2
        linarith [hℓ₀_gt, hDπ_ge, hval, hcastπ]
      have hlt : ψ (1 / 2 - δ) < ℓ'₀ - (k : ℝ) * Real.pi := by
        linarith [hVL_gt, hℓ'₀_ge]
      by_contra hcon
      push Not at hcon
      have h1c : (1 : ℝ) - c (k + D) = 1 / 2 - δ := by rw [hδ_def]; ring
      have hxmem : (1 / 2 - δ : ℝ) ∈ Set.Ioc (l k) (1 / 2 : ℝ) :=
        Set.mem_Ioc.mpr ⟨by rw [← h1c]; exact hcon, by linarith⟩
      have hgt := hl_max k hk (1 / 2 - δ) hxmem
      linarith [hlt, hgt]
    have ha_inj : ∀ i j, i < n' → j < n' → c (i + D) = c (j + D) → i = j := by
      intro i j hi hj heq
      by_contra hne'
      rcases Nat.lt_or_ge i j with hlt | hge
      · exact absurd heq (ne_of_lt (hc_mono (i + D) (j + D) (by omega) (by omega)))
      · have hgt : j < i := lt_of_le_of_ne hge (Ne.symm hne')
        exact absurd heq.symm
          (ne_of_lt (hc_mono (j + D) (i + D) (by omega) (by omega)))
    have ha'_inj : ∀ i j, i < n' → j < n' → l i = l j → i = j := by
      intro i j hi hj heq
      by_contra hne'
      rcases Nat.lt_or_ge i j with hlt | hge
      · exact absurd heq (ne_of_gt (hl_anti i j hlt hj))
      · have hgt : j < i := lt_of_le_of_ne hge (Ne.symm hne')
        exact absurd heq.symm (ne_of_gt (hl_anti j i hgt hi))
    have hdisj : ∀ i j, i < n' → j < n' → c (i + D) ≠ l j := by
      intro i j hi hj
      have h1 : (1 / 2 : ℝ) < c (i + D) := (hc_mem (i + D) (by omega)).1
      have h2 : l j < 1 / 2 := (hl_mem j hj).2
      exact ne_of_gt (lt_trans h2 h1)
    have hdisj_all : ∀ i j, i < D + n' → j < n' → c i ≠ l j := by
      intro i j hi hj
      have h1 := (hc_mem i (by omega)).1
      have h2 := (hl_mem j hj).2
      exact ne_of_gt (lt_trans h2 h1)
    have hj := paired_jensen_with_unpaired_lower (k := D) (n := n')
      (a := c) (b := l) hR hf hfc
      (fun i hi => hc_zero i (by omega))
      (fun i hi => ((hc_mem i (by omega)).1).le)
      (fun i hi => (hc_mem i (by omega)).2)
      (fun i j hi hj he => hc_inj i j (by omega) (by omega) he)
      hl_zero hinterlace (fun i hi => ((hl_mem i hi).2).le) ha'_inj hdisj_all
    have hcnt : (m₁ : ℝ) ≤ J / (2 * Real.log (R / (3 / 4))) + (D : ℝ) / 2 := by
      dsimp [J] at hJmul ⊢
      nlinarith [hj, hn'_cast]
    linarith [hcnt, hD_le, hEdiv]

theorem abs_argument_le {f : ℂ → ℂ} {R E : ℝ}
    (hR : 3 / 4 < R) (hE : 0 < E)
    (hf : AnalyticOnNhd ℂ f (closedBall (5 / 4 : ℂ) R))
    (hfc : f (5 / 4 : ℂ) ≠ 0) {ψ : ℝ → ℝ}
    (hψcont : ContinuousOn ψ (Icc (-1 / 4 : ℝ) (5 / 4 : ℝ)))
    (hψzero : ∀ x ∈ Icc (-1 / 4 : ℝ) (5 / 4 : ℝ),
      Real.cos (ψ x) = 0 → f (x : ℂ) = 0)
    (hψdelta : ∀ δ : ℝ, 0 < δ → δ ≤ 3 / 4 →
      |(ψ (1 / 2 + δ) - ψ (1 / 2)) - (ψ (1 / 2) - ψ (1 / 2 - δ))| ≤ E) :
    |ψ (5 / 4) - ψ (1 / 2)| / Real.pi ≤
      (circleAverage (fun z => Real.log ‖f z‖) (5 / 4 : ℂ) R -
        Real.log ‖f (5 / 4 : ℂ)‖) / (2 * Real.log (R / (3 / 4))) + 2 + E / (2 * Real.pi) := by
  let B := (circleAverage (fun z => Real.log ‖f z‖) (5 / 4 : ℂ) R -
    Real.log ‖f (5 / 4 : ℂ)‖) / (2 * Real.log (R / (3 / 4))) + 1 + E / (2 * Real.pi)
  have hc (m : ℕ) (hm : (m : ℝ) * Real.pi < |ψ (5 / 4) - ψ (1 / 2)|) : (m : ℝ) ≤ B := by
    rcases lt_abs.mp hm with hp | hn
    · exact crossing_count_le hR hE hf hfc hψcont hψzero hψdelta hp
    · apply crossing_count_le hR hE hf hfc hψcont.neg
        (ψ := fun x => -ψ x)
      · intro x hx hz
        exact hψzero x hx (by simpa only [Real.cos_neg] using hz)
      · intro δ hδ0 hδ1
        convert hψdelta δ hδ0 hδ1 using 1
        rw [show (-ψ (1 / 2 + δ) - -ψ (1 / 2)) -
            (-ψ (1 / 2) - -ψ (1 / 2 - δ)) =
            -((ψ (1 / 2 + δ) - ψ (1 / 2)) -
              (ψ (1 / 2) - ψ (1 / 2 - δ))) by ring, abs_neg]
      · linarith
  by_cases hz : |ψ (5 / 4) - ψ (1 / 2)| = 0
  · have hlog : 0 < Real.log (R / (3 / 4)) := Real.log_pos ((one_lt_div (by norm_num)).mpr hR)
    have hh := BacklundJensen.zeroCount_mul_log_le_circleAverage
      (by norm_num : (0 : ℝ) < 3 / 4) hR hf hfc
    have hn : 0 ≤ BacklundJensen.zeroCount f (5 / 4 : ℂ) (3 / 4) := by
      unfold BacklundJensen.zeroCount
      apply finsum_nonneg
      intro u
      exact_mod_cast (hf.mono (closedBall_subset_closedBall hR.le)).divisor_nonneg u
    have hj : 0 ≤ (circleAverage (fun z => Real.log ‖f z‖) (5 / 4 : ℂ) R -
        Real.log ‖f (5 / 4 : ℂ)‖) / (2 * Real.log (R / (3 / 4))) :=
      div_nonneg ((mul_nonneg hn hlog.le).trans hh) (by positivity)
    rw [hz, zero_div]
    positivity
  have hpos : 0 < |ψ (5 / 4) - ψ (1 / 2)| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hz)
  have hB : 0 ≤ B := by simpa only [Nat.cast_zero] using hc 0 (by simpa using hpos)
  have hfinal : |ψ (5 / 4) - ψ (1 / 2)| / Real.pi ≤ B + 1 := by
    by_contra hn
    have hlt : B + 1 < |ψ (5 / 4) - ψ (1 / 2)| / Real.pi := lt_of_not_ge hn
    have hfl := Nat.floor_le (show 0 ≤ B + 1 by linarith)
    have hfr := Nat.lt_floor_add_one (B + 1)
    have hsw : (⌊B + 1⌋₊ : ℝ) * Real.pi < |ψ (5 / 4) - ψ (1 / 2)| := by
      apply (lt_div_iff₀ Real.pi_pos).mp
      exact hfl.trans_lt hlt
    linarith [hc ⌊B + 1⌋₊ hsw]
  dsimp [B] at hfinal
  linarith

end TernaryGoldbach.RSBounds.BacklundPairedCrossing
end

-- RSBounds.BacklundPairedPower
section
open Filter Real Complex Metric MeasureTheory MeromorphicOn Set Topology
open scoped ComplexConjugate
open TernaryGoldbach.RSBounds.BacklundJensen
open TernaryGoldbach.RSBounds.BacklundPairedCrossing

namespace TernaryGoldbach.RSBounds.BacklundPairedPower

theorem normalized_power_argument_le {f g : ℂ → ℂ} {B : ℂ → ℝ} {θ : ℝ → ℝ}
    {R E : ℝ} {n : ℕ} (hR : 3 / 4 < R) (hE : 0 < E) (hn : 0 < n)
    (hf : AnalyticOnNhd ℂ f (closedBall (5 / 4 : ℂ) R))
    (hg : AnalyticOnNhd ℂ g (closedBall (5 / 4 : ℂ) R))
    (hfc : powerAverage f g n (5 / 4 : ℂ) ≠ 0)
    (hB : CircleIntegrable B (5 / 4 : ℂ) R)
    (hB0 : ∀ z ∈ sphere (5 / 4 : ℂ) R, 0 ≤ B z)
    (hfb : ∀ z ∈ sphere (5 / 4 : ℂ) R, ‖f z‖ ≤ Real.exp (B z))
    (hgb : ∀ z ∈ sphere (5 / 4 : ℂ) R, ‖g z‖ ≤ Real.exp (B z))
    (hθ : ContinuousOn θ (Icc (-1 / 4 : ℝ) (5 / 4 : ℝ)))
    (hzero : ∀ x ∈ Icc (-1 / 4 : ℝ) (5 / 4 : ℝ),
      Real.cos ((n : ℝ) * θ x) = 0 → powerAverage f g n (x : ℂ) = 0)
    (hdelta : ∀ δ : ℝ, 0 < δ → δ ≤ 3 / 4 →
      |(θ (1 / 2 + δ) - θ (1 / 2)) - (θ (1 / 2) - θ (1 / 2 - δ))| ≤ E) :
    |θ (5 / 4) - θ (1 / 2)| / Real.pi ≤
      (circleAverage B (5 / 4 : ℂ) R -
        Real.log ‖powerAverage f g n (5 / 4 : ℂ)‖ / n) / (2 * Real.log (R / (3 / 4))) +
        2 / n + E / (2 * Real.pi) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hR0 : 0 < R := by linarith
  have hlog : 0 < Real.log (R / (3 / 4)) := Real.log_pos ((one_lt_div (by norm_num)).mpr hR)
  have hpow := analyticOnNhd_powerAverage hf hg n
  have hpowa : AnalyticOnNhd ℂ (powerAverage f g n) (closedBall (5 / 4 : ℂ) |R|) := by
    simpa only [abs_of_pos hR0] using hpow
  have hi := (hpowa.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  have hiB : CircleIntegrable (fun z => (n : ℝ) * B z) (5 / 4 : ℂ) R := by
    unfold CircleIntegrable at hB ⊢
    exact hB.const_mul (n : ℝ)
  have havg := circleAverage_mono hi hiB (by
    rw [abs_of_pos hR0]
    exact fun z hz => log_norm_powerAverage_le (hB0 z hz) (hfb z hz) (hgb z hz) n)
  rw [show circleAverage (fun z => (n : ℝ) * B z) (5 / 4 : ℂ) R =
    (n : ℝ) * circleAverage B (5 / 4 : ℂ) R by
      simpa only [smul_eq_mul] using (circleAverage_fun_smul (a := (n : ℝ))
        (f := B) (c := (5 / 4 : ℂ)) (R := R))] at havg
  have hh := abs_argument_le hR (mul_pos hn0 hE) hpow hfc (hθ.const_mul (n : ℝ)) hzero
    (fun δ hδ0 hδ1 => by
      rw [show ((n : ℝ) * θ (1 / 2 + δ) - n * θ (1 / 2)) -
        (n * θ (1 / 2) - n * θ (1 / 2 - δ)) =
        n * ((θ (1 / 2 + δ) - θ (1 / 2)) -
          (θ (1 / 2) - θ (1 / 2 - δ))) by ring, abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (hdelta δ hδ0 hδ1) hn0.le)
  rw [show (n : ℝ) * θ (5 / 4) - n * θ (1 / 2) =
    n * (θ (5 / 4) - θ (1 / 2)) by ring, abs_mul, Nat.abs_cast] at hh
  have hh' : (n : ℝ) * |θ (5 / 4) - θ (1 / 2)| / Real.pi ≤
      ((n : ℝ) * circleAverage B (5 / 4 : ℂ) R -
        Real.log ‖powerAverage f g n (5 / 4 : ℂ)‖) / (2 * Real.log (R / (3 / 4))) +
        2 + (n : ℝ) * E / (2 * Real.pi) := by
    exact hh.trans (by gcongr)
  have hh'' := div_le_div_of_nonneg_right hh' hn0.le
  convert hh'' using 1 <;> field_simp [hn0.ne', hlog.ne', Real.pi_ne_zero]

theorem argument_bound {f g : ℂ → ℂ} {B : ℂ → ℝ} {θ : ℝ → ℝ} {R E : ℝ}
    (hR : 3 / 4 < R) (hE : 0 < E)
    (hf : AnalyticOnNhd ℂ f (closedBall (5 / 4 : ℂ) R))
    (hg : AnalyticOnNhd ℂ g (closedBall (5 / 4 : ℂ) R))
    (hfc : f (5 / 4 : ℂ) ≠ 0) (hconj : g (5 / 4 : ℂ) = conj (f (5 / 4 : ℂ)))
    (hB : CircleIntegrable B (5 / 4 : ℂ) R)
    (hB0 : ∀ z ∈ sphere (5 / 4 : ℂ) R, 0 ≤ B z)
    (hfb : ∀ z ∈ sphere (5 / 4 : ℂ) R, ‖f z‖ ≤ Real.exp (B z))
    (hgb : ∀ z ∈ sphere (5 / 4 : ℂ) R, ‖g z‖ ≤ Real.exp (B z))
    (hθ : ContinuousOn θ (Icc (-1 / 4 : ℝ) (5 / 4 : ℝ)))
    (hzero : ∀ n : ℕ, ∀ x ∈ Icc (-1 / 4 : ℝ) (5 / 4 : ℝ),
      Real.cos ((n : ℝ) * θ x) = 0 → powerAverage f g n (x : ℂ) = 0)
    (hdelta : ∀ δ : ℝ, 0 < δ → δ ≤ 3 / 4 →
      |(θ (1 / 2 + δ) - θ (1 / 2)) - (θ (1 / 2) - θ (1 / 2 - δ))| ≤ E) :
    |θ (5 / 4) - θ (1 / 2)| / Real.pi ≤
      (circleAverage B (5 / 4 : ℂ) R - Real.log ‖f (5 / 4 : ℂ)‖) /
        (2 * Real.log (R / (3 / 4))) + E / (2 * Real.pi) := by
  obtain ⟨n, hn, hp, hl⟩ := TernaryGoldbach.RSBounds.exists_backlund_phase_sequence hfc
  have hnTop : Tendsto (fun j => (n j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn.tendsto_atTop
  have hnpos : ∀ᶠ j in atTop, 0 < n j := by
    filter_upwards [hnTop.eventually (eventually_gt_atTop (0 : ℝ))] with j hj
    exact_mod_cast hj
  have hratio := TernaryGoldbach.RSBounds.real_power_ratio_tendsto hp
  have hnonzero : ∀ᶠ j in atTop, powerAverage f g (n j) (5 / 4 : ℂ) ≠ 0 := by
    filter_upwards [hratio.eventually (lt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
      with j hj
    rw [powerAverage_center hconj]
    apply Complex.ofReal_ne_zero.mpr
    intro hz
    rw [hz, zero_div] at hj
    exact lt_irrefl _ hj
  have hnorm (j : ℕ) : ‖powerAverage f g (n j) (5 / 4 : ℂ)‖ =
      |(f (5 / 4 : ℂ) ^ n j).re| := by
    rw [powerAverage_center hconj, Complex.norm_real, Real.norm_eq_abs]
  have hlim : Tendsto
      (fun j => (circleAverage B (5 / 4 : ℂ) R -
        Real.log ‖powerAverage f g (n j) (5 / 4 : ℂ)‖ / (n j : ℝ)) /
        (2 * Real.log (R / (3 / 4))) + 2 / (n j : ℝ) + E / (2 * Real.pi))
      atTop (𝓝 ((circleAverage B (5 / 4 : ℂ) R - Real.log ‖f (5 / 4 : ℂ)‖) /
        (2 * Real.log (R / (3 / 4))) + E / (2 * Real.pi))) := by
    simp_rw [hnorm]
    have hz : Tendsto (fun j => (2 : ℝ) / (n j : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hnTop
    simpa using (((tendsto_const_nhds.sub hl).div_const _).add hz).add_const (E / (2 * Real.pi))
  apply ge_of_tendsto hlim
  filter_upwards [hnpos, hnonzero] with j hj hnz
  exact normalized_power_argument_le hR hE hj hf hg hnz hB hB0 hfb hgb hθ (hzero (n j)) hdelta

end TernaryGoldbach.RSBounds.BacklundPairedPower
end

-- RSBounds.BacklundZetaPhase
section
noncomputable section
open Complex Real MeasureTheory
open scoped Topology ComplexConjugate

namespace TernaryGoldbach.RSBounds.BacklundZetaPhase
open BacklundCountIdentity

lemma riemannZeta_horizontal_ne_zero {T : ℝ} (hgood : zetaGoodHeight T)
    (σ : ℝ) : riemannZeta ((σ : ℂ) + T * Complex.I) ≠ 0 := by
  intro h
  have := hgood _ h
  simp at this

lemma hasDerivAt_horizontal_line (T σ : ℝ) :
    HasDerivAt (fun u : ℝ => (u : ℂ) + T * Complex.I) 1 σ := by
  have h : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 σ :=
    Complex.ofRealCLM.hasDerivAt (x := σ)
  simpa using h.add_const ((T : ℂ) * Complex.I)

lemma analyticAt_riemannZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ riemannZeta s := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [eventually_ne_nhds hs] with z hz
  exact differentiableAt_riemannZeta hz

lemma horizontal_ne_one_of_ne_zero {T : ℝ} (hT : T ≠ 0) (σ : ℝ) :
    (σ : ℂ) + T * Complex.I ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re,
    Complex.one_im, zero_add] at him
  exact hT him

lemma hasDerivAt_zeta_horiz {T : ℝ} (hT : T ≠ 0) (σ : ℝ) :
    HasDerivAt (fun u : ℝ => riemannZeta ((u : ℂ) + T * Complex.I))
      (deriv riemannZeta ((σ : ℂ) + T * Complex.I)) σ := by
  have hz : HasDerivAt riemannZeta
      (deriv riemannZeta ((σ : ℂ) + T * Complex.I)) ((σ : ℂ) + T * Complex.I) :=
    (differentiableAt_riemannZeta (horizontal_ne_one_of_ne_zero hT σ)).hasDerivAt
  have h := HasDerivAt.scomp (g₁ := riemannZeta) (h := fun u : ℝ => (u : ℂ) + T * Complex.I) σ
    hz (hasDerivAt_horizontal_line T σ)
  rw [one_smul] at h
  exact h

lemma continuous_logDeriv_horiz {T : ℝ} (hT : T ≠ 0) (hgood : zetaGoodHeight T) :
    Continuous (fun σ : ℝ => logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)) := by
  rw [continuous_iff_continuousAt]; intro σ
  have hline : ContinuousAt (fun u : ℝ => (u : ℂ) + T * Complex.I) σ :=
    (Complex.continuous_ofReal.add continuous_const).continuousAt
  have hana : AnalyticAt ℂ riemannZeta ((σ : ℂ) + T * Complex.I) :=
    analyticAt_riemannZeta_of_ne_one (horizontal_ne_one_of_ne_zero hT σ)
  have hζ : ContinuousAt (fun u : ℝ => riemannZeta ((u : ℂ) + T * Complex.I)) σ :=
    ContinuousAt.comp (g := riemannZeta) (f := fun u : ℝ => (u : ℂ) + T * Complex.I)
      hana.continuousAt hline
  have hζ' : ContinuousAt (fun u : ℝ => deriv riemannZeta ((u : ℂ) + T * Complex.I)) σ :=
    ContinuousAt.comp (g := deriv riemannZeta) (f := fun u : ℝ => (u : ℂ) + T * Complex.I)
      hana.deriv.continuousAt hline
  have hne := riemannZeta_horizontal_ne_zero hgood σ
  have : ContinuousAt (fun u : ℝ =>
      deriv riemannZeta ((u : ℂ) + T * Complex.I) /
        riemannZeta ((u : ℂ) + T * Complex.I)) σ := hζ'.div hζ hne
  simpa only [logDeriv_apply] using this

def zetaHArg (T a σ : ℝ) : ℝ :=
  (riemannZeta ((a : ℂ) + T * Complex.I)).arg
    + ∫ u in a..σ, (logDeriv riemannZeta ((u : ℂ) + T * Complex.I)).im

def zetaHReInt (T a σ : ℝ) : ℝ :=
  ∫ u in a..σ, (logDeriv riemannZeta ((u : ℂ) + T * Complex.I)).re

def zetaHPsi (T a σ : ℝ) : ℂ :=
  riemannZeta ((σ : ℂ) + T * Complex.I) * Complex.exp (-(zetaHArg T a σ : ℂ) * Complex.I)

def zetaHG (T a σ : ℝ) : ℂ :=
  zetaHPsi T a σ * Complex.exp (-(zetaHReInt T a σ : ℂ))

lemma hasDerivAt_zetaHArg {T : ℝ} (hT : T ≠ 0) (hgood : zetaGoodHeight T) (a σ : ℝ) :
    HasDerivAt (zetaHArg T a)
      ((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im) σ := by
  have hcont : Continuous (fun u : ℝ => (logDeriv riemannZeta ((u : ℂ) + T * Complex.I)).im) :=
    Complex.continuous_im.comp (continuous_logDeriv_horiz hT hgood)
  have hFTC := (hcont.integral_hasStrictDerivAt a σ).hasDerivAt
  unfold zetaHArg
  exact hFTC.const_add _

lemma hasDerivAt_zetaHReInt {T : ℝ} (hT : T ≠ 0) (hgood : zetaGoodHeight T) (a σ : ℝ) :
    HasDerivAt (zetaHReInt T a)
      ((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re) σ := by
  have hcont : Continuous (fun u : ℝ => (logDeriv riemannZeta ((u : ℂ) + T * Complex.I)).re) :=
    Complex.continuous_re.comp (continuous_logDeriv_horiz hT hgood)
  have hFTC := (hcont.integral_hasStrictDerivAt a σ).hasDerivAt
  unfold zetaHReInt
  exact hFTC

lemma hasDerivAt_zetaHPsi {T : ℝ} (hT : T ≠ 0) (hgood : zetaGoodHeight T) (a σ : ℝ) :
    HasDerivAt (zetaHPsi T a)
      (((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re : ℂ) * zetaHPsi T a σ) σ := by
  have hne := riemannZeta_horizontal_ne_zero hgood σ
  have hA : HasDerivAt (fun u : ℝ => riemannZeta ((u : ℂ) + T * Complex.I))
      (deriv riemannZeta ((σ : ℂ) + T * Complex.I)) σ := hasDerivAt_zeta_horiz hT σ
  have hθ : HasDerivAt (zetaHArg T a)
      ((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im) σ :=
    hasDerivAt_zetaHArg hT hgood a σ
  have hθc : HasDerivAt (fun s => ((zetaHArg T a s : ℝ) : ℂ))
      (((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im : ℂ)) σ := hθ.ofReal_comp
  have hexpArg : HasDerivAt (fun s => (-(zetaHArg T a s : ℂ)) * Complex.I)
      ((-(((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im : ℂ))) * Complex.I) σ :=
    (hθc.neg).mul_const Complex.I
  have hB : HasDerivAt (fun s => Complex.exp ((-(zetaHArg T a s : ℂ)) * Complex.I))
      (Complex.exp ((-(zetaHArg T a σ : ℂ)) * Complex.I)
        * ((-(((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im : ℂ))) * Complex.I)) σ :=
    hexpArg.cexp
  have hmul := hA.mul hB
  have hDL : logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)
        * riemannZeta ((σ : ℂ) + T * Complex.I)
      = deriv riemannZeta ((σ : ℂ) + T * Complex.I) := by
    rw [logDeriv_apply]; field_simp
  have hkey : logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)
        - ((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im : ℂ) * Complex.I
      = ((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re : ℂ) := by
    have := Complex.re_add_im (logDeriv riemannZeta ((σ : ℂ) + T * Complex.I))
    linear_combination -this
  have hval :
      deriv riemannZeta ((σ : ℂ) + T * Complex.I)
          * Complex.exp ((-(zetaHArg T a σ : ℂ)) * Complex.I)
        + riemannZeta ((σ : ℂ) + T * Complex.I)
          * (Complex.exp ((-(zetaHArg T a σ : ℂ)) * Complex.I)
            * ((-(((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im : ℂ))) * Complex.I))
      = ((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re : ℂ) * zetaHPsi T a σ := by
    unfold zetaHPsi
    rw [← hDL]
    linear_combination
      (riemannZeta ((σ : ℂ) + T * Complex.I)
        * Complex.exp ((-(zetaHArg T a σ : ℂ)) * Complex.I)) * hkey
  rw [hval] at hmul
  exact hmul

lemma hasDerivAt_zetaHG {T : ℝ} (hT : T ≠ 0) (hgood : zetaGoodHeight T) (a σ : ℝ) :
    HasDerivAt (zetaHG T a) 0 σ := by
  have hP := hasDerivAt_zetaHPsi hT hgood a σ
  have hgg := hasDerivAt_zetaHReInt hT hgood a σ
  have hggc : HasDerivAt (fun s => ((zetaHReInt T a s : ℝ) : ℂ))
      (((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re : ℂ)) σ := hgg.ofReal_comp
  have hExpG : HasDerivAt (fun s => Complex.exp (-(zetaHReInt T a s : ℂ)))
      (Complex.exp (-(zetaHReInt T a σ : ℂ))
        * (-(((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re : ℂ)))) σ :=
    (hggc.neg).cexp
  have hmul := hP.mul hExpG
  have hval :
      (((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re : ℂ) * zetaHPsi T a σ)
          * Complex.exp (-(zetaHReInt T a σ : ℂ))
        + zetaHPsi T a σ
          * (Complex.exp (-(zetaHReInt T a σ : ℂ))
            * (-(((logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).re : ℂ)))) = 0 := by ring
  rw [hval] at hmul
  exact hmul

theorem zeta_eq_norm_mul_cis {T : ℝ} (hT : T ≠ 0) (hgood : zetaGoodHeight T) (a σ : ℝ) :
    riemannZeta ((σ : ℂ) + T * Complex.I)
      = (‖riemannZeta ((σ : ℂ) + T * Complex.I)‖ : ℂ)
        * Complex.exp ((zetaHArg T a σ : ℂ) * Complex.I) := by

  have hGall : ∀ x, HasDerivAt (zetaHG T a) 0 x := fun x => hasDerivAt_zetaHG hT hgood a x
  have hconst := is_const_of_deriv_eq_zero (𝕜 := ℝ)
    (fun x => (hGall x).differentiableAt) (fun x => (hGall x).deriv) σ a

  have hGa : zetaHG T a a = (‖riemannZeta ((a : ℂ) + T * Complex.I)‖ : ℂ) := by
    unfold zetaHG zetaHPsi zetaHReInt zetaHArg
    rw [intervalIntegral.integral_same, intervalIntegral.integral_same]
    simp only [Complex.ofReal_zero, neg_zero, Complex.exp_zero, mul_one, add_zero]

    set w := riemannZeta ((a : ℂ) + T * Complex.I) with hw
    nth_rewrite 1 [← Complex.norm_mul_exp_arg_mul_I w]
    rw [mul_assoc, ← Complex.exp_add]
    rw [show (Complex.arg w : ℂ) * Complex.I + (-(Complex.arg w : ℂ)) * Complex.I = 0 by ring]
    rw [Complex.exp_zero, mul_one]
  rw [hGa] at hconst

  have hEne : Complex.exp (-(zetaHReInt T a σ : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hGσ : zetaHPsi T a σ * Complex.exp (-(zetaHReInt T a σ : ℂ))
      = (‖riemannZeta ((a : ℂ) + T * Complex.I)‖ : ℂ) := hconst
  have hEinv : (Complex.exp (-(zetaHReInt T a σ : ℂ)))⁻¹
      = ((Real.exp (zetaHReInt T a σ)) : ℂ) := by
    rw [Complex.exp_neg, inv_inv, ← Complex.ofReal_exp]
  have hpsiσ : zetaHPsi T a σ
      = (‖riemannZeta ((a : ℂ) + T * Complex.I)‖ : ℂ) * ((Real.exp (zetaHReInt T a σ)) : ℂ) := by
    have h := eq_div_of_mul_eq hEne hGσ
    rwa [div_eq_mul_inv, hEinv] at h

  have hr_nonneg : 0 ≤ ‖riemannZeta ((a : ℂ) + T * Complex.I)‖ * Real.exp (zetaHReInt T a σ) := by
    positivity
  have hpsiσ' : zetaHPsi T a σ
      = ((‖riemannZeta ((a : ℂ) + T * Complex.I)‖ * Real.exp (zetaHReInt T a σ) : ℝ) : ℂ) := by
    rw [hpsiσ]; push_cast; ring
  have hnormψ : ‖zetaHPsi T a σ‖ = ‖riemannZeta ((σ : ℂ) + T * Complex.I)‖ := by
    unfold zetaHPsi
    rw [norm_mul, Complex.norm_exp]
    simp
  have hr_eq : ‖riemannZeta ((a : ℂ) + T * Complex.I)‖ * Real.exp (zetaHReInt T a σ)
      = ‖riemannZeta ((σ : ℂ) + T * Complex.I)‖ := by
    have h := hnormψ
    rw [hpsiσ', Complex.norm_real, Real.norm_of_nonneg hr_nonneg] at h
    exact h
  have hpsiσ_norm : zetaHPsi T a σ = (‖riemannZeta ((σ : ℂ) + T * Complex.I)‖ : ℂ) := by
    rw [hpsiσ', hr_eq]

  have h1 : riemannZeta ((σ : ℂ) + T * Complex.I)
      * Complex.exp (-(zetaHArg T a σ : ℂ) * Complex.I)
      = (‖riemannZeta ((σ : ℂ) + T * Complex.I)‖ : ℂ) := by
    have := hpsiσ_norm; unfold zetaHPsi at this; exact this
  calc riemannZeta ((σ : ℂ) + T * Complex.I)
      = riemannZeta ((σ : ℂ) + T * Complex.I)
          * Complex.exp (-(zetaHArg T a σ : ℂ) * Complex.I)
          * Complex.exp ((zetaHArg T a σ : ℂ) * Complex.I) := by
        rw [mul_assoc, ← Complex.exp_add]
        rw [show (-(zetaHArg T a σ : ℂ) * Complex.I) + (zetaHArg T a σ : ℂ) * Complex.I = 0 by ring]
        rw [Complex.exp_zero, mul_one]
    _ = (‖riemannZeta ((σ : ℂ) + T * Complex.I)‖ : ℂ)
          * Complex.exp ((zetaHArg T a σ : ℂ) * Complex.I) := by rw [h1]

theorem re_zeta_pow_eq {T : ℝ} (hT : T ≠ 0) (hgood : zetaGoodHeight T) (a σ : ℝ) (N : ℕ) :
    ((riemannZeta ((σ : ℂ) + T * Complex.I)) ^ N).re
      = ‖riemannZeta ((σ : ℂ) + T * Complex.I)‖ ^ N
        * Real.cos ((N : ℝ) * zetaHArg T a σ) := by
  conv_lhs => rw [zeta_eq_norm_mul_cis hT hgood a σ]
  rw [mul_pow, ← Complex.exp_nat_mul,
    show (N : ℂ) * ((zetaHArg T a σ : ℂ) * Complex.I)
        = ((N : ℝ) * zetaHArg T a σ : ℝ) * Complex.I by push_cast; ring,
    ← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem zetaHArg_sub_eq_integral {T : ℝ} (hT : T ≠ 0) (hgood : zetaGoodHeight T)
    (a x y : ℝ) :
    zetaHArg T a x - zetaHArg T a y
      = ∫ σ in y..x, (logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im := by
  have hcontIm : Continuous
      (fun u : ℝ => (logDeriv riemannZeta ((u : ℂ) + T * Complex.I)).im) :=
    Complex.continuous_im.comp (continuous_logDeriv_horiz hT hgood)
  have hIx : IntervalIntegrable
      (fun u : ℝ => (logDeriv riemannZeta ((u : ℂ) + T * Complex.I)).im)
      volume a x := hcontIm.intervalIntegrable a x
  have hIy : IntervalIntegrable
      (fun u : ℝ => (logDeriv riemannZeta ((u : ℂ) + T * Complex.I)).im)
      volume a y := hcontIm.intervalIntegrable a y
  have hkey := intervalIntegral.integral_interval_sub_left hIx hIy
  unfold zetaHArg
  rw [← hkey]
  ring

theorem zetaHArg_continuous {T : ℝ} (hT : T ≠ 0) (hgood : zetaGoodHeight T)
    (a : ℝ) : Continuous (zetaHArg T a) :=
  continuous_iff_continuousAt.mpr fun σ =>
    (hasDerivAt_zetaHArg hT hgood a σ).continuousAt

theorem zeta_translate_conj (T x : ℝ) :
    riemannZeta ((x : ℂ) - T * Complex.I) =
      conj (riemannZeta ((x : ℂ) + T * Complex.I)) := by
  rw [← riemannZeta_conj]
  congr 1
  simp [sub_eq_add_neg]

theorem powerAverage_zeta_real (T x : ℝ) (n : ℕ) :
    BacklundJensen.powerAverage
      (fun z => riemannZeta (z + T * Complex.I))
      (fun z => riemannZeta (z - T * Complex.I)) n (x : ℂ) =
        ((riemannZeta ((x : ℂ) + T * Complex.I) ^ n).re : ℂ) :=
  BacklundJensen.powerAverage_center (zeta_translate_conj T x) n

theorem powerAverage_zeta_eq_zero_of_cos {T : ℝ} (hT : T ≠ 0)
    (hgood : zetaGoodHeight T) (a x : ℝ) (n : ℕ)
    (hcos : Real.cos ((n : ℝ) * zetaHArg T a x) = 0) :
    BacklundJensen.powerAverage
      (fun z => riemannZeta (z + T * Complex.I))
      (fun z => riemannZeta (z - T * Complex.I)) n (x : ℂ) = 0 := by
  rw [powerAverage_zeta_real, re_zeta_pow_eq hT hgood a x n, hcos, mul_zero,
    Complex.ofReal_zero]

theorem phase_reflection_eq_integral {T : ℝ} (hT : T ≠ 0)
    (hgood : zetaGoodHeight T) (a δ : ℝ) :
    (zetaHArg T a (1 / 2 + δ) - zetaHArg T a (1 / 2)) -
      (zetaHArg T a (1 / 2) - zetaHArg T a (1 / 2 - δ)) =
      ∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ),
        BacklundGammaReflection.zetaReflectionDifference σ T := by
  let f : ℝ → ℝ := fun σ =>
    (logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im
  have hc : Continuous f :=
    Complex.continuous_im.comp (continuous_logDeriv_horiz hT hgood)
  have hrc : Continuous (fun σ => f (1 - σ)) :=
    hc.comp (continuous_const.sub continuous_id)
  rw [zetaHArg_sub_eq_integral hT hgood a (1 / 2 + δ) (1 / 2),
    zetaHArg_sub_eq_integral hT hgood a (1 / 2) (1 / 2 - δ)]
  change (∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), f σ) -
      (∫ σ in (1 / 2 - δ : ℝ)..(1 / 2), f σ) =
      ∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), f σ - f (1 - σ)
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _)
    (hrc.intervalIntegrable _ _)]
  congr 1
  convert (intervalIntegral.integral_comp_sub_left f (a := (1 / 2 : ℝ))
    (b := 1 / 2 + δ) 1).symm using 1 <;> congr 1 <;> ring

theorem abs_phase_reflection_le {T δ : ℝ} (hT : 1 ≤ T)
    (hgood : zetaGoodHeight T) (a : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4) :
    |(zetaHArg T a (1 / 2 + δ) - zetaHArg T a (1 / 2)) -
      (zetaHArg T a (1 / 2) - zetaHArg T a (1 / 2 - δ))| ≤ 4 * δ ^ 2 / T := by
  rw [phase_reflection_eq_integral (by linarith : T ≠ 0) hgood a δ]
  exact BacklundGammaReflection.abs_integral_zetaReflectionDifference_le hT hδ0 hδ1
    (fun σ _ => ⟨riemannZeta_horizontal_ne_zero hgood σ,
      riemannZeta_horizontal_ne_zero hgood (1 - σ)⟩)

theorem abs_phase_reflection_le_four_div {T δ : ℝ} (hT : 1 ≤ T)
    (hgood : zetaGoodHeight T) (a : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4) :
    |(zetaHArg T a (1 / 2 + δ) - zetaHArg T a (1 / 2)) -
      (zetaHArg T a (1 / 2) - zetaHArg T a (1 / 2 - δ))| ≤ 4 / T := by
  refine (abs_phase_reflection_le hT hgood a hδ0 hδ1).trans ?_
  apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ T)
  nlinarith

theorem analyticOnNhd_zeta_translate {T R : ℝ} (hRT : R < T) :
    AnalyticOnNhd ℂ (fun z => riemannZeta (z + T * Complex.I))
        (Metric.closedBall (5 / 4 : ℂ) R) ∧
      AnalyticOnNhd ℂ (fun z => riemannZeta (z - T * Complex.I))
        (Metric.closedBall (5 / 4 : ℂ) R) := by
  have him (z : ℂ) (hz : z ∈ Metric.closedBall (5 / 4 : ℂ) R) : |z.im| ≤ R := by
    have hd : ‖z - (5 / 4 : ℂ)‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hi := Complex.abs_im_le_norm (z - (5 / 4 : ℂ))
    simpa using hi.trans hd
  constructor
  · intro z hz
    have hp : z + T * Complex.I ≠ 1 := by
      intro he
      have hh := congrArg Complex.im he
      simp only [Complex.add_im, Complex.mul_I_im, Complex.ofReal_re, Complex.one_im] at hh
      have hb := (abs_le.mp (him z hz)).1
      linarith
    exact (analyticAt_riemannZeta_of_ne_one hp).comp
      (f := fun w : ℂ => w + T * Complex.I) (x := z)
      (analyticAt_id.add analyticAt_const)
  · intro z hz
    have hp : z - T * Complex.I ≠ 1 := by
      intro he
      have hh := congrArg Complex.im he
      simp only [Complex.sub_im, Complex.mul_I_im, Complex.ofReal_re, Complex.one_im] at hh
      have hb := (abs_le.mp (him z hz)).2
      linarith
    exact (analyticAt_riemannZeta_of_ne_one hp).comp
      (f := fun w : ℂ => w - T * Complex.I) (x := z)
      (analyticAt_id.sub analyticAt_const)

theorem horizontal_argument_bound {T R : ℝ} {B : ℂ → ℝ}
    (hT : 1 ≤ T) (hgood : zetaGoodHeight T)
    (hR : 3 / 4 < R) (hRT : R < T)
    (hB : CircleIntegrable B (5 / 4 : ℂ) R)
    (hB0 : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) R, 0 ≤ B z)
    (hfb : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) R,
      ‖riemannZeta (z + T * Complex.I)‖ ≤ Real.exp (B z))
    (hgb : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) R,
      ‖riemannZeta (z - T * Complex.I)‖ ≤ Real.exp (B z)) :
    |∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
      (logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im| / Real.pi ≤
      (circleAverage B (5 / 4 : ℂ) R -
        Real.log ‖riemannZeta ((5 / 4 : ℂ) + T * Complex.I)‖) /
          (2 * Real.log (R / (3 / 4))) + 2 / (Real.pi * T) := by
  have hT0 : 0 < T := by linarith
  obtain ⟨hf, hg⟩ := analyticOnNhd_zeta_translate hRT
  have h := BacklundPairedPower.argument_bound
    (f := fun z => riemannZeta (z + T * Complex.I))
    (g := fun z => riemannZeta (z - T * Complex.I))
    (θ := zetaHArg T (5 / 4)) (E := 4 / T) hR (by positivity) hf hg
    (by simpa using riemannZeta_horizontal_ne_zero hgood (5 / 4))
    (by simpa using zeta_translate_conj T (5 / 4)) hB hB0 hfb hgb
    (zetaHArg_continuous hT0.ne' hgood (5 / 4)).continuousOn
    (fun n x _ hx => powerAverage_zeta_eq_zero_of_cos hT0.ne' hgood (5 / 4) x n hx)
    (fun δ hδ0 hδ1 => abs_phase_reflection_le_four_div hT hgood (5 / 4) hδ0.le hδ1)
  rw [zetaHArg_sub_eq_integral hT0.ne' hgood (5 / 4) (5 / 4) (1 / 2)] at h
  convert h using 1 <;> ring

end TernaryGoldbach.RSBounds.BacklundZetaPhase
end
end

-- RSBounds.BacklundGammaPhaseShift
section
open Complex Filter Set MeasureTheory
open scoped Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundGammaPhase

theorem norm_digamma_sub_le_of_re_ge {N : ℝ} (hN : 1 ≤ N) {z₁ z₂ : ℂ}
    (h1 : N ≤ z₁.re) (h2 : N ≤ z₂.re) :
    ‖Complex.digamma z₁ - Complex.digamma z₂‖ ≤ 2 * ‖z₁ - z₂‖ / N := by
  have hn1 := GammaSolution.ne_neg_natCast_of_mem
    (GammaSolution.mem_rightHalfPlane_iff.mpr (by linarith : 0 < z₁.re))
  have hn2 := GammaSolution.ne_neg_natCast_of_mem
    (GammaSolution.mem_rightHalfPlane_iff.mpr (by linarith : 0 < z₂.re))
  have hs1 := GammaSolution.summable_gaussTerm hn1
  have hs2 := GammaSolution.summable_gaussTerm hn2
  have hdiff : Complex.digamma z₁ - Complex.digamma z₂ =
      ∑' k, (GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k) := by
    rw [GammaSolution.digamma_eq_gaussSum (by linarith),
      GammaSolution.digamma_eq_gaussSum (by linarith),
      GammaSolution.gaussSum, GammaSolution.gaussSum, hs1.tsum_sub hs2]
    ring
  have hk : ∀ k : ℕ, ‖GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k‖ ≤
      ‖z₁ - z₂‖ * (2 * (((k : ℝ) + N) * ((k : ℝ) + N + 1))⁻¹) := by
    intro k
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hk1 : (0 : ℝ) < k + N := by linarith
    have hz1 : ((k : ℂ) + z₁) ≠ 0 := fun h => hn1 k (by linear_combination h)
    have hz2 : ((k : ℂ) + z₂) ≠ 0 := fun h => hn2 k (by linear_combination h)
    have he : GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k =
        (z₁ - z₂) / (((k : ℂ) + z₁) * ((k : ℂ) + z₂)) := by
      simp only [GammaSolution.gaussTerm]
      field_simp
      ring
    have hnz1 : (k : ℝ) + N ≤ ‖(k : ℂ) + z₁‖ := by
      have hh := Complex.re_le_norm ((k : ℂ) + z₁)
      simp only [add_re, natCast_re] at hh
      linarith
    have hnz2 : (k : ℝ) + N ≤ ‖(k : ℂ) + z₂‖ := by
      have hh := Complex.re_le_norm ((k : ℂ) + z₂)
      simp only [add_re, natCast_re] at hh
      linarith
    have hp : ((k : ℝ) + N) ^ 2 ≤ ‖((k : ℂ) + z₁) * ((k : ℂ) + z₂)‖ := by
      rw [norm_mul, pow_two]
      exact mul_le_mul hnz1 hnz2 hk1.le (norm_nonneg _)
    have hc : 1 / ((k : ℝ) + N) ^ 2 ≤
        2 * (((k : ℝ) + N) * ((k : ℝ) + N + 1))⁻¹ := by
      change 1 / ((k : ℝ) + N) ^ 2 ≤
        2 / (((k : ℝ) + N) * ((k : ℝ) + N + 1))
      rw [div_le_div_iff₀ (sq_pos_of_pos hk1) (by positivity)]
      nlinarith
    rw [he, norm_div]
    calc
      _ ≤ ‖z₁ - z₂‖ / ((k : ℝ) + N) ^ 2 :=
        div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hk1) hp
      _ = ‖z₁ - z₂‖ * (1 / ((k : ℝ) + N) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc (norm_nonneg _)
  have htele := GammaSolution.hasSum_comparison (t := N) hN ‖z₁ - z₂‖
  have hsumn : Summable (fun k : ℕ =>
      ‖GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hk htele.summable
  rw [hdiff]
  calc
    _ ≤ ∑' k, ‖GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k‖ :=
      norm_tsum_le_tsum_norm hsumn
    _ ≤ ‖z₁ - z₂‖ * (2 * N⁻¹) := by
      rw [← htele.tsum_eq]
      exact Summable.tsum_le_tsum hk hsumn htele.summable
    _ = _ := by simp only [div_eq_mul_inv]; ring

noncomputable def phaseAt (a τ : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..τ, (Complex.digamma ((a : ℂ) + t * I)).re

theorem continuous_digamma_unscaled {a : ℝ} (ha : 0 < a) :
    Continuous (fun t : ℝ ↦ Complex.digamma ((a : ℂ) + t * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (differentiableAt_digamma (by simpa using ha)).continuousAt.comp
    (by fun_prop : ContinuousAt (fun t : ℝ ↦ (a : ℂ) + t * I) t)

theorem digamma_quarter_shift_re_error {N t : ℝ} (hN : 1 ≤ N) (ht : 0 ≤ t) :
    |(Complex.digamma (((N + 1 / 4 : ℝ) : ℂ) + t * I)).re - Real.log N| ≤
      (2 * t + 5 / 4) / N := by
  have hN0 : 0 < N := by linarith
  have hx : 0 < N + 1 / 4 := by linarith
  have hd := norm_digamma_sub_le_of_re_ge hN
    (z₁ := (((N + 1 / 4 : ℝ) : ℂ) + t * I))
    (z₂ := ((N + 1 / 4 : ℝ) : ℂ))
    (by simp) (by simp)
  have hnorm : ‖(((N + 1 / 4 : ℝ) : ℂ) + t * I) - ((N + 1 / 4 : ℝ) : ℂ)‖ = t := by
    simp [norm_mul, Real.norm_eq_abs, abs_of_nonneg ht]
  rw [hnorm] at hd
  have hreal : |(Complex.digamma ((N + 1 / 4 : ℝ) : ℂ)).re - Real.log (N + 1 / 4)| ≤
      1 / (N + 1 / 4) := by
    rw [GammaSolution.digamma_ofReal hx, Complex.ofReal_re]
    exact GammaSolution.abs_deriv_log_Gamma_sub_log_le hx
  have hi : 1 / (N + 1 / 4) ≤ 1 / N :=
    one_div_le_one_div_of_le hN0 (by linarith)
  have hlog : |Real.log (N + 1 / 4) - Real.log N| ≤ (1 / 4) / N := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hN0 (by linarith)))]
    have hh := Real.log_le_sub_one_of_pos (div_pos hx hN0)
    rw [Real.log_div hx.ne' hN0.ne'] at hh
    have he : (N + 1 / 4) / N - 1 = (1 / 4) / N := by field_simp; ring
    rwa [he] at hh
  have hre := (Complex.abs_re_le_norm
    (Complex.digamma (((N + 1 / 4 : ℝ) : ℂ) + t * I) -
      Complex.digamma ((N + 1 / 4 : ℝ) : ℂ))).trans hd
  rw [Complex.sub_re] at hre
  have he : (2 * t + 5 / 4) / N = 2 * t / N + 1 / N + (1 / 4) / N := by ring
  rw [he, abs_le]
  rcases abs_le.mp hre with ⟨hrelo, hrehi⟩
  rcases abs_le.mp hreal with ⟨hrlo, hrhi⟩
  rcases abs_le.mp hlog with ⟨hllo, hlhi⟩
  constructor <;> linarith

theorem phaseAt_quarter_shift_error {N τ : ℝ} (hN : 1 ≤ N) (hτ : 0 ≤ τ) :
    |phaseAt (N + 1 / 4) τ - τ * Real.log N| ≤
      τ * (2 * τ + 5 / 4) / N := by
  have hx : 0 < N + 1 / 4 := by linarith
  have hi : IntervalIntegrable
      (fun t : ℝ ↦ (Complex.digamma (((N + 1 / 4 : ℝ) : ℂ) + t * I)).re) volume 0 τ :=
    (Complex.continuous_re.comp (continuous_digamma_unscaled hx)).intervalIntegrable 0 τ
  have he : phaseAt (N + 1 / 4) τ - τ * Real.log N =
      ∫ t in (0 : ℝ)..τ,
        ((Complex.digamma (((N + 1 / 4 : ℝ) : ℂ) + t * I)).re - Real.log N) := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const]
    simp [phaseAt, smul_eq_mul]
  rw [he, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ _t in (0 : ℝ)..τ, (2 * τ + 5 / 4) / N := by
      apply intervalIntegral.norm_integral_le_of_norm_le hτ
      · filter_upwards with t ht
        rw [Real.norm_eq_abs]
        exact (digamma_quarter_shift_re_error hN ht.1.le).trans
          (div_le_div_of_nonneg_right (by linarith [ht.2]) (by linarith))
      · exact intervalIntegrable_const
    _ = _ := by simp [smul_eq_mul]; ring

theorem tendsto_phaseAt_quarter_shift {τ : ℝ} (hτ : 0 ≤ τ) :
    Tendsto (fun N : ℕ ↦ phaseAt ((N : ℝ) + 1 / 4) τ - τ * Real.log N)
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun N : ℕ ↦ τ * (2 * τ + 5 / 4) / (N : ℝ))
    (Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _))
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    rw [Real.norm_eq_abs]
    exact phaseAt_quarter_shift_error (by exact_mod_cast hN) hτ
  · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

end TernaryGoldbach.RSBounds.BacklundGammaPhase
end

-- RSBounds.BacklundGammaPhaseArctan
section
open Complex Real Filter MeasureTheory intervalIntegral
open scoped Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundGammaPhase

theorem integral_const_div_sq_add_sq {c : ℝ} (hc : 0 < c) (τ : ℝ) :
    ∫ t in (0:ℝ)..τ, c / (c ^ 2 + t ^ 2) = Real.arctan (τ / c) := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) τ,
      HasDerivAt (fun u : ℝ => Real.arctan (u / c)) (c / (c ^ 2 + t ^ 2)) t := by
    intro t _
    have h1 : HasDerivAt (fun u : ℝ => u / c) (1 / c) t := by
      simpa using (hasDerivAt_id t).div_const c
    have h2 := h1.arctan
    convert h2 using 1
    have hden : (0:ℝ) < 1 + (t / c) ^ 2 := by positivity
    field_simp
  have hcont : ContinuousOn (fun t : ℝ => c / (c ^ 2 + t ^ 2)) (Set.uIcc 0 τ) := by
    apply ContinuousOn.div (g := fun t : ℝ => c ^ 2 + t ^ 2) continuousOn_const (by fun_prop)
    intro t _
    positivity
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcont.intervalIntegrable
  simpa using this

theorem phaseAt_add_one {a : ℝ} (ha : 0 < a) (τ : ℝ) :
    phaseAt (a + 1) τ = phaseAt a τ + Real.arctan (τ / a) := by
  have he : ∀ t : ℝ, (Complex.digamma (((a + 1 : ℝ) : ℂ) + t * I)).re =
      (Complex.digamma ((a : ℂ) + t * I)).re + a / (a ^ 2 + t ^ 2) := by
    intro t
    have hn := GammaSolution.ne_neg_natCast_of_mem
      (s := (a : ℂ) + t * I)
      (GammaSolution.mem_rightHalfPlane_iff.mpr (by simpa using ha))
    have hrec := Complex.digamma_apply_add_one ((a : ℂ) + t * I) hn
    have harg : (a : ℂ) + t * I + 1 = ((a + 1 : ℝ) : ℂ) + t * I := by
      push_cast
      ring
    rw [harg] at hrec
    rw [hrec, Complex.add_re, Complex.inv_re, Complex.normSq_apply]
    simp [pow_two]
  have hi : IntervalIntegrable (fun t : ℝ ↦ (Complex.digamma ((a : ℂ) + t * I)).re) volume 0 τ :=
    (Complex.continuous_re.comp (continuous_digamma_unscaled ha)).intervalIntegrable 0 τ
  have hj : IntervalIntegrable (fun t : ℝ ↦ a / (a ^ 2 + t ^ 2)) volume 0 τ := by
    apply Continuous.intervalIntegrable
    apply Continuous.div (g := fun t : ℝ => a ^ 2 + t ^ 2) continuous_const (by fun_prop)
    intro t
    positivity
  unfold phaseAt
  simp_rw [he]
  rw [intervalIntegral.integral_add hi hj, integral_const_div_sq_add_sq ha τ]

theorem phaseAt_add_nat {a : ℝ} (ha : 0 < a) (τ : ℝ) (N : ℕ) :
    phaseAt (a + N) τ = phaseAt a τ +
      ∑ k ∈ Finset.range N, Real.arctan (τ / (a + k)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hpos : 0 < a + (N : ℝ) := by positivity
    rw [Nat.cast_add_one, ← add_assoc, phaseAt_add_one hpos, ih, Finset.sum_range_succ]
    ring

theorem tendsto_arctan_gauss_phase {τ : ℝ} (hτ : 0 ≤ τ) :
    Tendsto (fun N : ℕ ↦ τ * Real.log N -
        ∑ k ∈ Finset.range N, Real.arctan (τ / (1 / 4 + (k : ℝ))))
      atTop (𝓝 (phaseAt (1 / 4) τ)) := by
  have hlim : Tendsto (fun N : ℕ ↦ phaseAt (1 / 4) τ -
      (phaseAt ((N : ℝ) + 1 / 4) τ - τ * Real.log N))
      atTop (𝓝 (phaseAt (1 / 4) τ - 0)) :=
    tendsto_const_nhds.sub (tendsto_phaseAt_quarter_shift hτ)
  have he : ∀ N : ℕ, phaseAt (1 / 4) τ -
      (phaseAt ((N : ℝ) + 1 / 4) τ - τ * Real.log N) =
      τ * Real.log N - ∑ k ∈ Finset.range N, Real.arctan (τ / (1 / 4 + (k : ℝ))) := by
    intro N
    rw [add_comm (N : ℝ) (1 / 4), phaseAt_add_nat (by norm_num : (0 : ℝ) < 1 / 4)]
    ring
  simp only [sub_zero, he] at hlim
  exact hlim

theorem arctan_le_self' {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have hmono : MonotoneOn (fun u : ℝ => u - Real.arctan u) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (continuous_id.sub Real.continuous_arctan).continuousOn
    · exact (differentiable_id.sub Real.differentiable_arctan).differentiableOn
    · intro u _
      have hd : HasDerivAt (fun u : ℝ => u - Real.arctan u)
          (1 - 1 / (1 + u ^ 2)) u := (hasDerivAt_id u).sub (Real.hasDerivAt_arctan u)
      rw [hd.deriv]
      have : (0:ℝ) < 1 + u ^ 2 := by positivity
      rw [sub_nonneg, div_le_one this]
      nlinarith
  have := hmono (Set.mem_Ici.mpr (le_refl (0 : ℝ))) (Set.mem_Ici.mpr hx) hx
  simpa [Real.arctan_zero] using this

end TernaryGoldbach.RSBounds.BacklundGammaPhase
end

-- RSBounds.BacklundGammaPhasePrimitive
section
open Real Filter MeasureTheory intervalIntegral
open scoped Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundGammaPhase

theorem hasDerivAt_arctan_quotient {τ x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun u : ℝ ↦ Real.arctan (τ / u)) (-τ / (x ^ 2 + τ ^ 2)) x := by
  have h := ((hasDerivAt_const x τ).div (hasDerivAt_id x) hx.ne').arctan
  simp only [Pi.div_apply, id_eq, zero_mul, zero_sub, mul_one] at h
  convert h using 1
  have hden : 0 < 1 + (τ / x) ^ 2 := by positivity
  field_simp <;> ring

theorem hasDerivAt_arctan_quotient_deriv {τ x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun u : ℝ ↦ -τ / (u ^ 2 + τ ^ 2))
      (2 * τ * x / (x ^ 2 + τ ^ 2) ^ 2) x := by
  have hden : 0 < x ^ 2 + τ ^ 2 := by positivity
  have h := (hasDerivAt_const x (-τ)).div
    ((hasDerivAt_pow 2 x).add_const (τ ^ 2)) hden.ne'
  convert h using 1 <;> ring

noncomputable def arctanPrimitive (τ x : ℝ) : ℝ :=
  x * Real.arctan (τ / x) + τ / 2 * Real.log (x ^ 2 + τ ^ 2)

theorem hasDerivAt_arctanPrimitive {τ x : ℝ} (hx : 0 < x) :
    HasDerivAt (arctanPrimitive τ) (Real.arctan (τ / x)) x := by
  have hden : 0 < x ^ 2 + τ ^ 2 := by positivity
  have hlog := (((hasDerivAt_pow 2 x).add_const (τ ^ 2)).log hden.ne').const_mul (τ / 2)
  have hp := (hasDerivAt_id x).mul (hasDerivAt_arctan_quotient (τ := τ) hx)
  convert hp.add hlog using 1
  · rfl
  · simp only [id_eq]
    field_simp <;> ring

theorem integral_arctan_quotient {a : ℝ} (ha : 0 < a) (τ : ℝ) (N : ℕ) :
    (∫ x in a..(a + N), Real.arctan (τ / x)) =
      arctanPrimitive τ (a + N) - arctanPrimitive τ a := by
  have hle : a ≤ a + (N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg N)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [Set.uIcc_of_le hle] at hx
    exact hasDerivAt_arctanPrimitive (ha.trans_le hx.1)
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    exact (hasDerivAt_arctan_quotient (τ := τ) (ha.trans_le hx.1)).continuousAt.continuousWithinAt

theorem tendsto_mul_arctan_quotient {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ) :
    Tendsto (fun N : ℕ ↦ ((N : ℝ) + a) * Real.arctan (τ / ((N : ℝ) + a)))
      atTop (𝓝 τ) := by
  have hr : Tendsto (fun N : ℕ ↦ τ / ((N : ℝ) + a)) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ a tendsto_natCast_atTop_atTop)
    · exact Filter.Eventually.of_forall (fun N ↦ div_pos hτ (add_pos_of_nonneg_of_pos (Nat.cast_nonneg N) ha))
  have hs : Tendsto (fun u : ℝ ↦ Real.arctan u / u) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hh := (Real.hasDerivAt_arctan 0).tendsto_slope.mono_left
      (nhdsGT_le_nhdsNE (0 : ℝ))
    simpa [slope_fun_def_field] using hh
  have hm := (hs.comp hr).mul_const τ
  convert hm using 1
  · funext N
    have hn : (N : ℝ) + a ≠ 0 := by positivity
    dsimp only [Function.comp_apply]
    field_simp [hn, hτ.ne'] <;> ring
  · ring

theorem tendsto_arctanPrimitive_sub_log {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ) :
    Tendsto (fun N : ℕ ↦ arctanPrimitive τ (a + N) - τ * Real.log N)
      atTop (𝓝 τ) := by
  have harg := tendsto_mul_arctan_quotient ha hτ
  have hd : Tendsto (fun N : ℕ ↦ Real.log ((N : ℝ) + a) - Real.log N)
      atTop (𝓝 0) :=
    (Real.tendsto_log_comp_add_sub_log a).comp tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun N : ℕ ↦ τ / ((N : ℝ) + a)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ a tendsto_natCast_atTop_atTop)
  have hl : Tendsto (fun N : ℕ ↦ Real.log (1 + (τ / ((N : ℝ) + a)) ^ 2))
      atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds.add (hr.pow 2)).log (by norm_num : (1 : ℝ) + 0 ^ 2 ≠ 0)
    simpa using hh
  have hm := (harg.add (hd.const_mul τ)).add (hl.const_mul (τ / 2))
  convert hm using 1
  · funext N
    have hx : 0 < (N : ℝ) + a := by positivity
    have he : ((N : ℝ) + a) ^ 2 + τ ^ 2 =
        ((N : ℝ) + a) ^ 2 * (1 + (τ / ((N : ℝ) + a)) ^ 2) := by
      field_simp <;> ring
    dsimp [arctanPrimitive]
    rw [add_comm a (N : ℝ), he, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    ring
  · ring

theorem phase_correction_eq {τ : ℝ} (hτ : 0 < τ) :
    arctanPrimitive τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2 - τ -
        (τ * Real.log τ - τ - Real.pi / 8) =
      τ / 2 * Real.log (1 + ((1 / 4) / τ) ^ 2) +
        (1 / 4) * Real.arctan ((1 / 4) / τ) := by
  have he : (1 / 4 : ℝ) ^ 2 + τ ^ 2 = τ ^ 2 * (1 + ((1 / 4) / τ) ^ 2) := by
    field_simp
    ring
  have hat : Real.arctan (τ / (1 / 4)) = Real.pi / 2 - Real.arctan ((1 / 4) / τ) := by
    simpa only [inv_div] using Real.arctan_inv_of_pos (by positivity : 0 < (1 / 4 : ℝ) / τ)
  unfold arctanPrimitive
  rw [hat, he, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  ring

theorem phase_correction_bounds {τ : ℝ} (hτ : 0 < τ) :
    0 ≤ arctanPrimitive τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2 - τ -
        (τ * Real.log τ - τ - Real.pi / 8) ∧
    arctanPrimitive τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2 - τ -
        (τ * Real.log τ - τ - Real.pi / 8) ≤ 3 / (32 * τ) := by
  rw [phase_correction_eq hτ]
  have hl0 : 0 ≤ Real.log (1 + ((1 / 4) / τ) ^ 2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg ((1 / 4 : ℝ) / τ)])
  have ha0 : 0 ≤ Real.arctan ((1 / 4) / τ) := Real.arctan_nonneg.mpr (by positivity)
  have hlu : Real.log (1 + ((1 / 4) / τ) ^ 2) ≤ ((1 / 4) / τ) ^ 2 := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + ((1 / 4 : ℝ) / τ) ^ 2)
    linarith
  have hau := arctan_le_self' (by positivity : 0 ≤ (1 / 4 : ℝ) / τ)
  constructor
  · positivity
  · calc
      _ ≤ τ / 2 * (((1 / 4) / τ) ^ 2) + (1 / 4) * ((1 / 4) / τ) := by gcongr
      _ = 3 / (32 * τ) := by field_simp; ring

end TernaryGoldbach.RSBounds.BacklundGammaPhase
end

-- RSBounds.BacklundTrapezoid
section
open Set MeasureTheory intervalIntegral
open scoped Interval

namespace TernaryGoldbach.RSBounds.BacklundTrapezoid

noncomputable section

def kernel (a x : ℝ) : ℝ := (x - a) * (a + 1 - x) / 2

theorem kernel_nonneg {a x : ℝ} (hx : x ∈ Icc a (a + 1)) :
    0 ≤ kernel a x := by
  unfold kernel
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2))
    (by norm_num)

theorem kernel_le {a x : ℝ} : kernel a x ≤ 1 / 8 := by
  unfold kernel
  nlinarith [sq_nonneg (x - a - 1 / 2)]

theorem hasDerivAt_kernel (a x : ℝ) :
    HasDerivAt (kernel a) (a + 1 / 2 - x) x := by
  change HasDerivAt (fun y : ℝ => (y - a) * (a + 1 - y) / 2) _ x
  convert (((hasDerivAt_id x).sub_const a).mul
    ((hasDerivAt_id x).const_sub (a + 1))).div_const 2 using 1 <;>
    norm_num <;> ring

theorem error_eq_integral_kernel {f f' f'' : ℝ → ℝ} {a : ℝ}
    (hf : ∀ x ∈ Icc a (a + 1), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc a (a + 1), HasDerivAt f' (f'' x) x)
    (hfi : IntervalIntegrable f'' volume a (a + 1)) :
    trapezoidal_error f 1 a (a + 1) =
      ∫ x in a..(a + 1), kernel a x * f'' x := by
  have hab : a ≤ a + 1 := by linarith
  have hu : [[a, a + 1]] = Icc a (a + 1) := uIcc_of_le hab
  have hf0 : ContinuousOn f [[a, a + 1]] := by
    rw [hu]; exact fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hf1 : ContinuousOn f' [[a, a + 1]] := by
    rw [hu]; exact fun x hx => (hf' x hx).continuousAt.continuousWithinAt
  have hK : Continuous (kernel a) := by unfold kernel; fun_prop
  have hL : Continuous (fun x : ℝ => a + 1 / 2 - x) := by fun_prop
  have h1 := integral_mul_deriv_eq_deriv_mul
    (a := a) (b := a + 1)
    (fun x _ => hasDerivAt_kernel a x)
    (fun x hx => hf' x (hu ▸ hx)) (hL.intervalIntegrable _ _) hfi
  have h2 := integral_mul_deriv_eq_deriv_mul
    (a := a) (b := a + 1)
    (fun x _ => (hasDerivAt_id x).const_sub (a + 1 / 2))
    (fun x hx => hf x (hu ▸ hx))
    (continuous_const.intervalIntegrable _ _) hf1.intervalIntegrable
  have hneg : (∫ x in a..(a + 1), (-1 : ℝ) * f x) =
      -(∫ x in a..(a + 1), f x) := by simp
  rw [hneg] at h2
  have hKa : kernel a a = 0 := by simp [kernel]
  have hKb : kernel a (a + 1) = 0 := by simp [kernel]
  rw [hKa, hKb, zero_mul, zero_mul, sub_self, zero_sub] at h1
  rw [trapezoidal_error, trapezoidal_integral_one]
  simp only [id_eq] at h2
  ring_nf at h1 h2 ⊢
  linarith

theorem error_bounds {f f' f'' : ℝ → ℝ} {a : ℝ}
    (hf : ∀ x ∈ Icc a (a + 1), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc a (a + 1), HasDerivAt f' (f'' x) x)
    (hfi : IntervalIntegrable f'' volume a (a + 1))
    (hnn : ∀ x ∈ Icc a (a + 1), 0 ≤ f'' x) :
    0 ≤ trapezoidal_error f 1 a (a + 1) ∧
      trapezoidal_error f 1 a (a + 1) ≤ (f' (a + 1) - f' a) / 8 := by
  rw [error_eq_integral_kernel hf hf' hfi]
  have hab : a ≤ a + 1 := by linarith
  have hK : Continuous (kernel a) := by unfold kernel; fun_prop
  have hki : IntervalIntegrable (fun x => kernel a x * f'' x) volume a (a + 1) :=
    hfi.continuousOn_mul hK.continuousOn
  constructor
  · exact integral_nonneg hab (fun x hx => mul_nonneg (kernel_nonneg hx) (hnn x hx))
  · have hbound := integral_mono_on hab hki (hfi.const_mul (1 / 8 : ℝ))
      (fun x hx => mul_le_mul_of_nonneg_right kernel_le (hnn x hx))
    have he := integral_eq_sub_of_hasDerivAt
      (fun x hx => hf' x ((uIcc_of_le hab) ▸ hx)) hfi
    rw [intervalIntegral.integral_const_mul, he] at hbound
    linarith

theorem sum_error_eq {f : ℝ → ℝ} {a : ℝ} (N : ℕ)
    (hi : ∀ k < N, IntervalIntegrable f volume (a + k) (a + k + 1)) :
    (∑ k ∈ Finset.range N, trapezoidal_error f 1 (a + k) (a + k + 1)) =
      (∑ k ∈ Finset.range N, f (a + k)) + (f (a + N) - f a) / 2 -
        ∫ x in a..(a + N), f x := by
  have hi' := sum_integral_adjacent_intervals (a := fun k : ℕ => a + k)
    (f := f) (n := N) (fun k hk => by simpa [Nat.cast_add, add_assoc] using hi k hk)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, ← add_assoc] at hi'
  have hs := Finset.sum_range_succ' (fun k : ℕ => f (a + k)) N
  rw [Finset.sum_range_succ] at hs
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, ← add_assoc] at hs
  simp_rw [trapezoidal_error, trapezoidal_integral_one,
    show ∀ k : ℕ, (a + k + 1 - (a + k)) / 2 = (1 / 2 : ℝ) by intro k; ring]
  rw [Finset.sum_sub_distrib, hi', ← Finset.mul_sum, Finset.sum_add_distrib]
  linarith

end

end TernaryGoldbach.RSBounds.BacklundTrapezoid
end

-- RSBounds.BacklundGammaPhaseEstimate
section
open Real Filter MeasureTheory intervalIntegral
open scoped Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundGammaPhase

theorem arctan_unit_error_bounds {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ) :
    0 ≤ trapezoidal_error (fun x : ℝ ↦ Real.arctan (τ / x)) 1 a (a + 1) ∧
    trapezoidal_error (fun x : ℝ ↦ Real.arctan (τ / x)) 1 a (a + 1) ≤
      ((-τ / ((a + 1) ^ 2 + τ ^ 2)) - (-τ / (a ^ 2 + τ ^ 2))) / 8 := by
  apply BacklundTrapezoid.error_bounds
    (f' := fun x : ℝ ↦ -τ / (x ^ 2 + τ ^ 2))
    (f'' := fun x : ℝ ↦ 2 * τ * x / (x ^ 2 + τ ^ 2) ^ 2)
  · intro x hx
    exact hasDerivAt_arctan_quotient (ha.trans_le hx.1)
  · intro x hx
    exact hasDerivAt_arctan_quotient_deriv (ha.trans_le hx.1)
  · apply Continuous.intervalIntegrable
    apply Continuous.div (f := fun x : ℝ ↦ 2 * τ * x) (g := fun x : ℝ ↦ (x ^ 2 + τ ^ 2) ^ 2)
      (by fun_prop) (by fun_prop)
    intro x
    positivity
  · intro x hx
    have hx0 : 0 < x := ha.trans_le hx.1
    positivity

noncomputable def arctanTrapSum (τ : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, trapezoidal_error (fun x : ℝ ↦ Real.arctan (τ / x)) 1
    (1 / 4 + (k : ℝ)) (1 / 4 + (k : ℝ) + 1)

theorem arctanTrapSum_bounds {τ : ℝ} (hτ : 0 < τ) (N : ℕ) :
    0 ≤ arctanTrapSum τ N ∧
      arctanTrapSum τ N ≤
        ((-τ / ((1 / 4 + (N : ℝ)) ^ 2 + τ ^ 2)) -
          (-τ / ((1 / 4 : ℝ) ^ 2 + τ ^ 2))) / 8 := by
  induction N with
  | zero => simp [arctanTrapSum]
  | succ N ih =>
    have hu := arctan_unit_error_bounds (a := 1 / 4 + (N : ℝ)) (by positivity) hτ
    have he : arctanTrapSum τ (N + 1) = arctanTrapSum τ N +
        trapezoidal_error (fun x : ℝ ↦ Real.arctan (τ / x)) 1
          (1 / 4 + (N : ℝ)) (1 / 4 + (N : ℝ) + 1) := by
      simp [arctanTrapSum, Finset.sum_range_succ]
    rw [he]
    push_cast
    constructor
    · linarith [ih.1, hu.1]
    · have hp : 1 / 4 + ((N : ℝ) + 1) = 1 / 4 + (N : ℝ) + 1 := by ring
      rw [hp]
      linarith [ih.2, hu.2]

theorem arctanTrapSum_le {τ : ℝ} (hτ : 0 < τ) (N : ℕ) :
    arctanTrapSum τ N ≤ 1 / (8 * τ) := by
  have hu := (arctanTrapSum_bounds hτ N).2
  have hn : -τ / ((1 / 4 + (N : ℝ)) ^ 2 + τ ^ 2) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have he : τ / ((1 / 4 : ℝ) ^ 2 + τ ^ 2) ≤ 1 / τ := by
    rw [div_le_div_iff₀ (by positivity) hτ]
    nlinarith
  have he' : 1 / (8 * τ) = (1 / τ) / 8 := by ring
  rw [he']
  simp only [neg_div] at hu hn
  linarith

theorem arctanTrapSum_eq (τ : ℝ) (N : ℕ) :
    arctanTrapSum τ N =
      (∑ k ∈ Finset.range N, Real.arctan (τ / (1 / 4 + (k : ℝ)))) +
        (Real.arctan (τ / (1 / 4 + (N : ℝ))) - Real.arctan (τ / (1 / 4))) / 2 -
        (arctanPrimitive τ (1 / 4 + (N : ℝ)) - arctanPrimitive τ (1 / 4)) := by
  unfold arctanTrapSum
  rw [BacklundTrapezoid.sum_error_eq N]
  · rw [integral_arctan_quotient (by norm_num : (0 : ℝ) < 1 / 4)]
  · intro k _
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by linarith : 1 / 4 + (k : ℝ) ≤ 1 / 4 + (k : ℝ) + 1)] at hx
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx.1
    exact (hasDerivAt_arctan_quotient (τ := τ) hx0).continuousAt.continuousWithinAt

theorem tendsto_arctanTrapSum {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (arctanTrapSum τ) atTop
      (𝓝 (arctanPrimitive τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2 - τ -
        phaseAt (1 / 4) τ)) := by
  have hG := tendsto_arctan_gauss_phase hτ.le
  have hP := tendsto_arctanPrimitive_sub_log (by norm_num : (0 : ℝ) < 1 / 4) hτ
  have hq : Tendsto (fun N : ℕ ↦ τ / (1 / 4 + (N : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  have hA : Tendsto (fun N : ℕ ↦ Real.arctan (τ / (1 / 4 + (N : ℝ)))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuous_arctan.tendsto 0).comp hq
  have hC : Tendsto (fun _ : ℕ ↦ arctanPrimitive τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2)
      atTop (𝓝 (arctanPrimitive τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2)) :=
    tendsto_const_nhds
  convert ((hC.sub hG).sub hP).add (hA.div_const 2) using 1
  · funext N
    rw [arctanTrapSum_eq]
    ring
  · ring

theorem phaseAt_remainder_bound {τ : ℝ} (hτ : 0 < τ) :
    |phaseAt (1 / 4) τ - τ * Real.log τ + τ + Real.pi / 8| ≤ 1 / (8 * τ) := by
  have hlim := tendsto_arctanTrapSum hτ
  have hE0 : 0 ≤ arctanPrimitive τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2 - τ -
      phaseAt (1 / 4) τ := by
    apply ge_of_tendsto hlim
    exact Filter.Eventually.of_forall (fun N ↦ (arctanTrapSum_bounds hτ N).1)
  have hE1 : arctanPrimitive τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2 - τ -
      phaseAt (1 / 4) τ ≤ 1 / (8 * τ) :=
    le_of_tendsto' hlim (arctanTrapSum_le hτ)
  have hC := phase_correction_bounds hτ
  have hu : 3 / (32 * τ) ≤ 1 / (8 * τ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [abs_le]
  constructor <;> linarith [hC.1, hC.2]

theorem gamma_phase_remainder_bound {T : ℝ} (hT : 0 < T) :
    |phaseIntegral T - T / 2 * Real.log (T / 2) + T / 2 + Real.pi / 8| ≤
      1 / (4 * T) := by
  have hh := phaseAt_remainder_bound (τ := T / 2) (by positivity)
  have he : phaseAt (1 / 4) (T / 2) = phaseIntegral T := by
    simp [phaseAt, phaseIntegral]
  rw [he] at hh
  convert hh using 1 <;> ring

end TernaryGoldbach.RSBounds.BacklundGammaPhase
end

-- RSBounds.BacklundCountJensen
section
open Complex MeasureTheory Real
open scoped Interval

namespace TernaryGoldbach.RSBounds.BacklundCountIdentity

theorem count_le_circle_majorant {T R : ℝ} {B : ℂ → ℝ}
    (hT : 1 ≤ T) (hgood : zetaGoodHeight T)
    (hR : 3 / 4 < R) (hRT : R < T)
    (hB : CircleIntegrable B (5 / 4 : ℂ) R)
    (hB0 : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) R, 0 ≤ B z)
    (hfb : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) R,
      ‖riemannZeta (z + T * I)‖ ≤ Real.exp (B z))
    (hgb : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) R,
      ‖riemannZeta (z - T * I)‖ ≤ Real.exp (B z)) :
    |(N T : ℝ) - mainTerm T| ≤
      (circleAverage B (5 / 4 : ℂ) R + Real.log (3.426 : ℝ)) /
        (2 * Real.log (R / (3 / 4))) + 1 / 2 +
        2 / (Real.pi * T) + 1 / (4 * Real.pi * T) := by
  have hT0 : 0 < T := by linarith
  have hp : 0 < Real.pi := Real.pi_pos
  have hq : 0 < Real.log (R / (3 / 4)) :=
    Real.log_pos ((one_lt_div (by norm_num)).mpr hR)
  have hhor := BacklundZetaPhase.horizontal_argument_bound hT hgood hR hRT hB hB0 hfb hgb
  have hcenter : -Real.log (3.426 : ℝ) ≤
      Real.log ‖riemannZeta ((5 / 4 : ℂ) + T * I)‖ := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 3.426)
      (zeta_norm_lower_five_fourths_3426 T)
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at hh
    simpa only [Real.log_div one_ne_zero (by norm_num : (3.426 : ℝ) ≠ 0),
      Real.log_one, zero_sub] using hh
  have hhor' :
      |∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
        (logDeriv riemannZeta ((σ : ℂ) + T * I)).im| / Real.pi ≤
      (circleAverage B (5 / 4 : ℂ) R + Real.log (3.426 : ℝ)) /
        (2 * Real.log (R / (3 / 4))) + 2 / (Real.pi * T) := by
    apply hhor.trans
    gcongr
    linarith
  have hv := BacklundAnchor.abs_vertical_integral_le T
  have ha : |zetaArgVar T| / Real.pi ≤
      1 / 2 +
      (circleAverage B (5 / 4 : ℂ) R + Real.log (3.426 : ℝ)) /
        (2 * Real.log (R / (3 / 4))) + 2 / (Real.pi * T) := by
    unfold zetaArgVar arcVariation
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
    have hh := abs_sub_le
      (∫ t in (0 : ℝ)..T, (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)).re)
      (0 : ℝ)
      (∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
        (logDeriv riemannZeta ((σ : ℂ) + T * I)).im)
    simp only [sub_zero, zero_sub, abs_neg] at hh
    have hd := div_le_div_of_nonneg_right hh hp.le
    have hv' := div_le_div_of_nonneg_right hv hp.le
    have he : (Real.pi / 2) / Real.pi = (1 / 2 : ℝ) := by field_simp
    rw [he] at hv'
    rw [add_div] at hd
    linarith
  have hg := div_le_div_of_nonneg_right
    (BacklundGammaPhase.gamma_phase_remainder_bound hT0) hp.le
  change |gammaStirlingRemainder T| / Real.pi ≤ (1 / (4 * T)) / Real.pi at hg
  rw [count_identity_mainTerm hT0 hgood]
  have hh := abs_add_le (zetaArgVar T / Real.pi) (gammaStirlingRemainder T / Real.pi)
  rw [abs_div, abs_div, abs_of_pos hp] at hh
  have he : (1 / (4 * T)) / Real.pi = 1 / (4 * Real.pi * T) := by ring
  rw [he] at hg
  have he' : mainTerm T + zetaArgVar T / Real.pi + gammaStirlingRemainder T / Real.pi -
      mainTerm T = zetaArgVar T / Real.pi + gammaStirlingRemainder T / Real.pi := by ring
  rw [he']
  linarith

end TernaryGoldbach.RSBounds.BacklundCountIdentity
end

-- RSBounds.WeightedZeroSums
section
open Set MeasureTheory
open scoped BigOperators

namespace TernaryGoldbach.RSBounds

noncomputable def rosserF (t : ℝ) : ℝ :=
  t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8

noncomputable def rosserR (C t : ℝ) : ℝ :=
  0.137 * Real.log t + 0.443 * Real.log (Real.log t) + C

theorem hasDerivAt_rosserF {t : ℝ} (ht : 0 < t) :
    HasDerivAt rosserF (Real.log (t / (2 * Real.pi)) / (2 * Real.pi)) t := by
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hq : t / (2 * Real.pi) ≠ 0 := div_ne_zero ht.ne' hp
  have hdiv := (hasDerivAt_id t).div_const (2 * Real.pi)
  have hh := ((hdiv.mul (hdiv.log hq)).sub hdiv).add_const (7 / 8 : ℝ)
  convert hh using 1
  · rfl
  · dsimp only [id_eq]
    field_simp [hp, ht.ne']
    <;> ring

end TernaryGoldbach.RSBounds
end

-- RSBounds.BacklundLowScalarBase
section
open Real

namespace TernaryGoldbach.RSBounds.BacklundLowScalar
open SmallTotientProduct

structure LogCert where
  k : ℕ
  a : ℕ
  b : ℕ
  deriving DecidableEq

def LogCert.Valid (c : LogCert) : Prop := 0 < c.a ∧ 0 < c.b ∧ c.b ≤ c.a
instance (c : LogCert) : Decidable c.Valid := by unfold LogCert.Valid; infer_instance

def LogCert.ratio (c : LogCert) : ℚ := (2 : ℚ) ^ c.k * (1 + (c.b : ℚ) / c.a)
def LogCert.lower (c : LogCert) : ℚ :=
  ((c.k : ℚ) * qLo 1 1 + qLo c.a c.b) / (10 ^ 30 : ℚ)
def LogCert.upper (c : LogCert) : ℚ :=
  ((c.k : ℚ) * qHi 1 1 + qHi c.a c.b) / (10 ^ 30 : ℚ)

lemma LogCert.log_bounds {c : LogCert} (hc : c.Valid) :
    (c.lower : ℝ) ≤ Real.log (c.ratio : ℝ) ∧
      Real.log (c.ratio : ℝ) ≤ (c.upper : ℝ) := by
  have ha : (0 : ℝ) < c.a := by exact_mod_cast hc.1
  have hb : (0 : ℝ) < c.b := by exact_mod_cast hc.2.1
  have h1 := q_bounds hc.1 hc.2.1 hc.2.2
  have h2 := q_bounds (a := 1) (b := 1) (by decide) (by decide) (by decide)
  norm_num only [Nat.cast_one, div_one] at h2
  have hk : (0 : ℝ) ≤ c.k := Nat.cast_nonneg _
  have hl := mul_le_mul_of_nonneg_left h2.1 hk
  have hu := mul_le_mul_of_nonneg_left h2.2 hk
  have he : Real.log (c.ratio : ℝ) =
      (c.k : ℝ) * Real.log 2 + Real.log (1 + (c.b : ℝ) / c.a) := by
    unfold LogCert.ratio
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  rw [he]
  unfold LogCert.lower LogCert.upper
  push_cast
  constructor
  · rw [div_le_iff₀ (by positivity : (0 : ℝ) < 10 ^ 30)]
    nlinarith
  · rw [le_div_iff₀ (by positivity : (0 : ℝ) < 10 ^ 30)]
    nlinarith

lemma LogCert.log_gt {c : LogCert} (hc : c.Valid) {l : ℚ} (hl : l < c.lower) :
    (l : ℝ) < Real.log (c.ratio : ℝ) :=
  (show (l : ℝ) < (c.lower : ℝ) by exact_mod_cast hl).trans_le (LogCert.log_bounds hc).1

structure MainCert where
  t : ℚ
  lower : LogCert
  upper : LogCert
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

def MainCert.Valid (c : MainCert) : Prop :=
  c.lower.Valid ∧ c.upper.Valid ∧
  1 < c.lower.ratio ∧ 0 ≤ c.upper.ratio ∧
  c.lower.ratio * (44 / 7 : ℚ) ≤ c.t ∧
  c.t ≤ c.upper.ratio * (157 / 25 : ℚ) ∧
  c.lo < c.lower.ratio * c.lower.lower - c.upper.ratio + 7 / 8 ∧
  c.upper.ratio * c.upper.upper - c.lower.ratio + 7 / 8 < c.hi
instance (c : MainCert) : Decidable c.Valid := by unfold MainCert.Valid; infer_instance

end TernaryGoldbach.RSBounds.BacklundLowScalar
end

-- RSBounds.BacklundFinalScalar
section
open Real

namespace TernaryGoldbach.RSBounds.BacklundFinalScalar
open BacklundLowScalar

lemma log_hundred_gt : (4.6 : ℝ) < Real.log 100 := by
  have h := LogCert.log_gt (c := ⟨6, 16, 9⟩) (by decide)
    (l := (23 / 5 : ℚ)) (by decide +kernel)
  norm_num [LogCert.ratio] at h ⊢
  exact h

lemma log_four_point_six_gt : (1.5 : ℝ) < Real.log (4.6 : ℝ) := by
  have h := LogCert.log_gt (c := ⟨2, 20, 3⟩) (by decide)
    (l := (3 / 2 : ℚ)) (by decide +kernel)
  norm_num [LogCert.ratio] at h ⊢
  exact h

noncomputable def roundedEnvelope (T : ℝ) : ℝ :=
  0.1361 * Real.log (T + 33 / 25) +
  0.4423 * Real.log (Real.log (T + 33 / 25)) + 1.5803 +
  Real.log ((T - 33 / 25) ^ 2 / ((T - 33 / 25) ^ 2 - 4)) +
  2 / (Real.pi * T) + 1 / (4 * Real.pi * T)

lemma roundedEnvelope_lt_rosser {T : ℝ} (hT : 100 ≤ T) :
    roundedEnvelope T < rosserR 1.588 T := by
  have hT0 : 0 < T := by linarith
  have hp : 0 < Real.pi := Real.pi_pos
  have hl : (4.6 : ℝ) < Real.log T :=
    log_hundred_gt.trans_le (Real.log_le_log (by norm_num) hT)
  have hl0 : 0 < Real.log T := by linarith
  have hll : (1.5 : ℝ) < Real.log (Real.log T) :=
    log_four_point_six_gt.trans_le (Real.log_le_log (by norm_num) hl.le)
  have hs : Real.log (T + 33 / 25) ≤ Real.log T + (33 / 25) / T := by
    have hf : T + 33 / 25 = T * (1 + (33 / 25) / T) := by field_simp
    rw [hf, Real.log_mul hT0.ne' (by positivity)]
    have hh := Real.log_le_sub_one_of_pos
      (by positivity : (0 : ℝ) < 1 + (33 / 25) / T)
    linarith
  have hsp : 0 < Real.log (T + 33 / 25) := Real.log_pos (by linarith)
  have hss : Real.log (Real.log (T + 33 / 25)) ≤
      Real.log (Real.log T) + (33 / 25) / (T * Real.log T) := by
    apply (Real.log_le_log hsp hs).trans
    have hf : Real.log T + (33 / 25) / T =
        Real.log T * (1 + (33 / 25) / (T * Real.log T)) := by
      field_simp
    rw [hf, Real.log_mul hl0.ne' (by positivity)]
    have hh := Real.log_le_sub_one_of_pos
      (by positivity : (0 : ℝ) < 1 + (33 / 25) / (T * Real.log T))
    linarith
  have hA : 0.1361 * Real.log (T + 33 / 25) ≤
      0.1361 * Real.log T + 0.18 / T := by
    calc
      _ ≤ 0.1361 * (Real.log T + (33 / 25) / T) :=
        mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = 0.1361 * Real.log T + (0.1361 * (33 / 25)) / T := by ring
      _ ≤ _ := by gcongr; norm_num
  have hBc : (0.4423 * (33 / 25)) / (T * Real.log T) ≤ 0.13 / T := by
    rw [div_le_div_iff₀ (mul_pos hT0 hl0) hT0]
    nlinarith [mul_nonneg hT0.le (sub_nonneg.mpr hl.le)]
  have hB : 0.4423 * Real.log (Real.log (T + 33 / 25)) ≤
      0.4423 * Real.log (Real.log T) + 0.13 / T := by
    calc
      _ ≤ 0.4423 * (Real.log (Real.log T) + (33 / 25) / (T * Real.log T)) :=
        mul_le_mul_of_nonneg_left hss (by norm_num)
      _ = 0.4423 * Real.log (Real.log T) +
          (0.4423 * (33 / 25)) / (T * Real.log T) := by ring
      _ ≤ _ := add_le_add le_rfl hBc
  let D : ℝ := (T - 33 / 25) ^ 2 - 4
  have hD : 80 * T ≤ D := by
    dsimp [D]
    nlinarith [mul_nonneg (sub_nonneg.mpr hT) hT0.le]
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD
  have hV : Real.log ((T - 33 / 25) ^ 2 / D) ≤ 0.05 / T := by
    have hf : (T - 33 / 25) ^ 2 / D = 1 + 4 / D := by
      calc
        _ = (D + 4) / D := by congr 1; dsimp [D]; ring
        _ = _ := by rw [add_div, div_self hD0.ne']
    rw [hf]
    have hh := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 4 / D)
    have hdiv : 4 / D ≤ 0.05 / T := by
      rw [div_le_div_iff₀ hD0 hT0]
      linarith
    linarith
  have hpi2 : (2 : ℝ) / Real.pi ≤ 0.637 := by
    rw [div_le_iff₀ hp]
    linarith [Real.pi_gt_d2]
  have hG0 : (1 : ℝ) / (4 * Real.pi) ≤ 0.08 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [Real.pi_gt_d2]
  have hP : 2 / (Real.pi * T) ≤ 0.637 / T := by
    convert div_le_div_of_nonneg_right hpi2 hT0.le using 1 <;> ring
  have hG : 1 / (4 * Real.pi * T) ≤ 0.08 / T := by
    convert div_le_div_of_nonneg_right hG0 hT0.le using 1 <;> ring
  have hsmall : (1.1 : ℝ) / T ≤ 0.011 := by
    rw [div_le_iff₀ hT0]
    linarith
  have hrec : 0 < 1 / T := by positivity
  change Real.log ((T - 33 / 25) ^ 2 / ((T - 33 / 25) ^ 2 - 4)) ≤ 0.05 / T at hV
  unfold roundedEnvelope rosserR
  simp only [div_eq_mul_inv] at hA hB hV hP hG hsmall hrec ⊢
  linarith only [hA, hB, hV, hP, hG, hsmall, hrec, hl, hll]

end TernaryGoldbach.RSBounds.BacklundFinalScalar
end

-- RSBounds.BacklundCircleCount
section
open Complex Real MeasureTheory

namespace TernaryGoldbach.RSBounds.BacklundCircleMajorant

theorem majorant_circleIntegrable (T : ℝ) :
    CircleIntegrable (majorant T) (5 / 4 : ℂ) radius := by
  have hi : IntervalIntegrable
      (fun θ => scalar (heightLog T) (powerLog T) (stripLog T)
        ((5 / 4 : ℝ) + radius * Real.cos θ)) volume 0 Real.pi := by
    have hi' := BacklundAngularAssembly.intervalIntegrable_scalar_arc
      (heightLog T) (powerLog T) (stripLog T)
    unfold BacklundAngularAssembly.arc BacklundAngularAssembly.sigma
      BacklundAngularCoefficients.radius at hi'
    simpa only [radius] using hi'
  unfold majorant
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using circleIntegrable_re_of_upper hi

theorem majorant_average_le (T : ℝ) :
    circleAverage (majorant T) (5 / 4 : ℂ) radius /
        (2 * BacklundAngularCoefficients.q) ≤
      0.1361 / BacklundAngularCoefficients.q +
        BacklundAngularCoefficients.slopeA * powerLog T +
        BacklundAngularCoefficients.slopeB * heightLog T +
        (BacklundAngularCoefficients.beta - BacklundAngularCoefficients.alpha) * stripLog T /
          (2 * Real.pi * BacklundAngularCoefficients.q) := by
  have hi := BacklundAngularAssembly.intervalIntegrable_scalar_arc
    (heightLog T) (powerLog T) (stripLog T)
  unfold BacklundAngularAssembly.arc BacklundAngularAssembly.sigma
    BacklundAngularCoefficients.radius at hi
  have he := circleAverage_re_eq_upper (c := 5 / 4) (r := radius)
    (f := scalar (heightLog T) (powerLog T) (stripLog T)) (by
      simpa only [radius] using hi)
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at he
  change circleAverage (majorant T) (5 / 4 : ℂ) radius = _ at he
  rw [he]
  have hb := BacklundAngularAssembly.scalar_arc_integral_le
    (heightLog T) (powerLog T) (stripLog T)
  unfold BacklundAngularAssembly.arc BacklundAngularAssembly.sigma
    BacklundAngularCoefficients.radius at hb
  convert hb using 1
  dsimp [radius]
  field_simp [BacklundAngularCoefficients.q_pos.ne', Real.pi_ne_zero]

theorem correction_coefficient_le_one :
    (BacklundAngularCoefficients.beta - BacklundAngularCoefficients.alpha) /
      (2 * Real.pi * BacklundAngularCoefficients.q) ≤ 1 := by
  have hq := BacklundAngularCoefficients.q_bounds.1
  have hα : 0 ≤ BacklundAngularCoefficients.alpha := Real.arccos_nonneg _
  have hβ : BacklundAngularCoefficients.beta ≤ Real.pi := Real.arccos_le_pi _
  have hm := mul_nonneg Real.pi_pos.le
    (show 0 ≤ 2 * BacklundAngularCoefficients.q - 1 by linarith)
  rw [div_le_one (by positivity [BacklundAngularCoefficients.q_pos])]
  nlinarith [Real.pi_pos]

theorem count_le_roundedEnvelope {T : ℝ} (hT : 100 ≤ T)
    (hgood : BacklundCountIdentity.zetaGoodHeight T) :
    |(BacklundCountIdentity.N T : ℝ) - BacklundCountIdentity.mainTerm T| ≤
      BacklundFinalScalar.roundedEnvelope T := by
  have hh := BacklundCountIdentity.count_le_circle_majorant
    (T := T) (R := radius) (B := majorant T) (by linarith) hgood
    (by norm_num [radius]) (by dsimp [radius]; linarith)
    (majorant_circleIntegrable T) (fun z _ => majorant_nonneg hT z)
    (fun _ hz => zeta_plus_le_exp_majorant hT hz)
    (fun _ hz => zeta_minus_le_exp_majorant hT hz)
  have hq : Real.log (radius / (3 / 4)) = BacklundAngularCoefficients.q := by
    unfold radius BacklundAngularCoefficients.q
    norm_num
  rw [hq, add_div] at hh
  have hmean := majorant_average_le T
  have hp : powerLog T = Real.log (T + radius) - Real.log (2 * Real.pi) := by
    unfold powerLog
    rw [Real.log_div (by dsimp [radius]; linarith) (by positivity)]
  have hraw : |(BacklundCountIdentity.N T : ℝ) - BacklundCountIdentity.mainTerm T| ≤
      BacklundAngularCoefficients.slopeA * Real.log (T + radius) +
      BacklundAngularCoefficients.slopeB * heightLog T +
      BacklundAngularCoefficients.intercept 0.1361 +
      (BacklundAngularCoefficients.beta - BacklundAngularCoefficients.alpha) * stripLog T /
        (2 * Real.pi * BacklundAngularCoefficients.q) +
      2 / (Real.pi * T) + 1 / (4 * Real.pi * T) := by
    rw [hp] at hmean
    unfold BacklundAngularCoefficients.intercept
    linarith
  have hA := mul_le_mul_of_nonneg_right BacklundAngularCoefficients.slopeA_bounds.2
    (log_height_pos hT).le
  have hB := mul_le_mul_of_nonneg_right BacklundAngularCoefficients.slopeB_le
    (heightLog_nonneg hT)
  have hK := BacklundAngularCoefficients.intercept_le_strong
  have hV := mul_le_mul_of_nonneg_right correction_coefficient_le_one (stripLog_nonneg hT)
  have hVe : ((BacklundAngularCoefficients.beta - BacklundAngularCoefficients.alpha) /
      (2 * Real.pi * BacklundAngularCoefficients.q)) * stripLog T =
      (BacklundAngularCoefficients.beta - BacklundAngularCoefficients.alpha) * stripLog T /
        (2 * Real.pi * BacklundAngularCoefficients.q) := by ring
  rw [hVe, one_mul] at hV
  change _ ≤ 0.1361 * Real.log (T + radius) + 0.4423 * heightLog T + 1.5803 +
    stripLog T + 2 / (Real.pi * T) + 1 / (4 * Real.pi * T)
  linarith

end TernaryGoldbach.RSBounds.BacklundCircleMajorant
end

-- RSBounds.BacklundCountEndpoint
section
open Complex MeasureTheory Set Filter
open scoped Real Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundCountIdentity

noncomputable def closedPositiveZeros (T : ℝ) : Finset ℂ :=
  (positiveZeros (T + 1)).filter (fun ρ => ρ.im ≤ T)

noncomputable def N_le (T : ℝ) : ℕ :=
  ∑ ρ ∈ closedPositiveZeros T, (analyticOrderAt riemannZeta ρ).toNat

theorem mem_closedPositiveZeros_iff {T : ℝ} (hT : 0 < T) {ρ : ℂ} :
    ρ ∈ closedPositiveZeros T ↔ riemannZeta ρ = 0 ∧ 0 < ρ.im ∧ ρ.im ≤ T := by
  rw [closedPositiveZeros, Finset.mem_filter, mem_positiveZeros_iff_zeta (by linarith)]
  constructor
  · rintro ⟨⟨hz, h0, _⟩, hT⟩
    exact ⟨hz, h0, hT⟩
  · rintro ⟨hz, h0, hT⟩
    exact ⟨⟨hz, h0, by linarith⟩, hT⟩

private theorem finite_right_gap (S : Finset ℂ) (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ ρ ∈ S, T < ρ.im → T + δ ≤ ρ.im := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, le_rfl, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨δ, hδ0, hδ1, hgap⟩ := ih
    by_cases haT : T < a.im
    · refine ⟨min δ ((a.im - T) / 2), lt_min hδ0 (by linarith),
        (min_le_left _ _).trans hδ1, ?_⟩
      intro ρ hρ hρT
      rcases Finset.mem_insert.mp hρ with rfl | hρ
      · linarith [min_le_right δ ((ρ.im - T) / 2)]
      · exact (add_le_add le_rfl (min_le_left _ _)).trans (hgap ρ hρ hρT)
    · refine ⟨δ, hδ0, hδ1, ?_⟩
      intro ρ hρ hρT
      rcases Finset.mem_insert.mp hρ with rfl | hρ
      · exact (haT hρT).elim
      · exact hgap ρ hρ hρT

theorem exists_right_interval_good_count {T : ℝ} (hT : 0 < T) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ S ∈ Ioo T (T + δ),
      zetaGoodHeight S ∧ N S = N_le T := by
  obtain ⟨δ, hδ0, hδ1, hgap⟩ := finite_right_gap (positiveZeros (T + 1)) T
  refine ⟨δ, hδ0, hδ1, ?_⟩
  intro S hS
  have hS0 : 0 < S := hT.trans hS.1
  have hS1 : S < T + 1 := lt_of_lt_of_le hS.2 (by linarith)
  have hg : zetaGoodHeight S := by
    intro ρ hz he
    have hρ : ρ ∈ positiveZeros (T + 1) :=
      (mem_positiveZeros_iff_zeta (by linarith)).mpr ⟨hz, by simpa [he] using hS0,
        by simpa [he] using hS1⟩
    have hh := hgap ρ hρ (by simpa [he] using hS.1)
    rw [he] at hh
    linarith [hS.2]
  refine ⟨hg, ?_⟩
  have hsets : positiveZeros S = closedPositiveZeros T := by
    apply Finset.ext
    intro ρ
    rw [mem_positiveZeros_iff_zeta hS0, mem_closedPositiveZeros_iff hT]
    constructor
    · rintro ⟨hz, h0, hρS⟩
      refine ⟨hz, h0, ?_⟩
      by_contra h
      have hTρ : T < ρ.im := lt_of_not_ge h
      have hρ : ρ ∈ positiveZeros (T + 1) :=
        (mem_positiveZeros_iff_zeta (by linarith)).mpr ⟨hz, h0, hρS.trans hS1⟩
      linarith [hgap ρ hρ hTρ, hS.2]
    · rintro ⟨hz, h0, hρT⟩
      exact ⟨hz, h0, hρT.trans_lt hS.1⟩
  rw [N_eq_sum_zetaMultiplicity hS0, hsets]
  rfl

theorem closed_count_abs_le_of_good_height_bound {T : ℝ} (hT : 0 < T)
    {M B : ℝ → ℝ} (hM : ContinuousAt M T) (hB : ContinuousAt B T)
    (hbound : ∀ S : ℝ, T < S → zetaGoodHeight S → |(N S : ℝ) - M S| ≤ B S) :
    |(N_le T : ℝ) - M T| ≤ B T := by
  obtain ⟨δ, hδ0, hδ1, hloc⟩ := exists_right_interval_good_count hT
  let S : ℕ → ℝ := fun n => T + (δ / 2) * (1 / ((n : ℝ) + 1))
  have hSmem (n : ℕ) : S n ∈ Ioo T (T + δ) := by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hrec : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one hn).mpr hn1
    have hp : 0 < (δ / 2) * (1 / ((n : ℝ) + 1)) := by positivity
    have hq := mul_le_mul_of_nonneg_left hrec (show 0 ≤ δ / 2 by positivity)
    dsimp [S]
    constructor <;> nlinarith
  have hlim : Tendsto S atTop (𝓝 T) := by
    have hh : Tendsto (fun n : ℕ => T + (δ / 2) * (1 / ((n : ℝ) + 1))) atTop
        (𝓝 (T + (δ / 2) * 0)) := tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (δ / 2))
    simpa [S] using hh
  have hb : ∀ n : ℕ, |(N_le T : ℝ) - M (S n)| ≤ B (S n) := by
    intro n
    have hl := hloc (S n) (hSmem n)
    rw [← hl.2]
    exact hbound (S n) (hSmem n).1 hl.1
  exact le_of_tendsto_of_tendsto
    ((tendsto_const_nhds.sub (hM.tendsto.comp hlim)).abs)
    (hB.tendsto.comp hlim) (Eventually.of_forall hb)

theorem closed_count_abs_lt_of_good_height_bound {T : ℝ} (hT : 0 < T)
    {M B : ℝ → ℝ} {C : ℝ} (hM : ContinuousAt M T) (hB : ContinuousAt B T)
    (hbound : ∀ S : ℝ, T < S → zetaGoodHeight S → |(N S : ℝ) - M S| ≤ B S)
    (hgap : B T < C) : |(N_le T : ℝ) - M T| < C :=
  (closed_count_abs_le_of_good_height_bound hT hM hB hbound).trans_lt hgap

end TernaryGoldbach.RSBounds.BacklundCountIdentity
end

-- RSBounds.RosserCountDefinition
section
open Complex Real MeasureTheory

namespace TernaryGoldbach.RSBounds.Rosser1941
open BacklundCountIdentity

noncomputable def positiveZeroCount (T : ℝ) : ℝ := by
  classical
  exact ∑' ρ : ℂ, if 0 < ρ.im ∧ ρ.im ≤ T then
    ((analyticOrderAt riemannZeta ρ).toNat : ℝ) else 0

lemma positiveZeroCount_eq {T : ℝ} (hT : 0 < T) :
    positiveZeroCount T = (N_le T : ℝ) := by
  classical
  have hs : ∀ ρ ∉ closedPositiveZeros T,
      (if 0 < ρ.im ∧ ρ.im ≤ T then
        ((analyticOrderAt riemannZeta ρ).toNat : ℝ) else 0) = 0 := by
    intro ρ hρ
    by_cases hi : 0 < ρ.im ∧ ρ.im ≤ T
    · have hz : riemannZeta ρ ≠ 0 := by
        intro hz
        exact hρ ((mem_closedPositiveZeros_iff hT).mpr ⟨hz, hi.1, hi.2⟩)
      rw [if_pos hi, analyticOrderAt_eq_zero.mpr (Or.inr hz)]
      simp
    · simp [hi]
  unfold positiveZeroCount
  rw [tsum_eq_sum hs]
  unfold N_le
  push_cast
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hi := (mem_closedPositiveZeros_iff hT).mp hρ
  simp only [if_pos (show 0 < ρ.im ∧ ρ.im ≤ T from ⟨hi.2.1, hi.2.2⟩)]

end TernaryGoldbach.RSBounds.Rosser1941
end

-- RSBounds.BacklundHighCount
section
open Complex Real MeasureTheory

namespace TernaryGoldbach.RSBounds.BacklundCountIdentity

lemma continuous_roundedEnvelope {T : ℝ} (hT : 100 ≤ T) :
    ContinuousAt BacklundFinalScalar.roundedEnvelope T := by
  have hT0 : 0 < T := by linarith
  have hTr : 0 < T - 33 / 25 := by linarith
  have hD : 0 < (T - 33 / 25) ^ 2 - 4 := by nlinarith
  have hL : 0 < Real.log (T + 33 / 25) := Real.log_pos (by linarith)
  unfold BacklundFinalScalar.roundedEnvelope
  fun_prop (disch := positivity)

theorem rosser_bound_high {T : ℝ} (hT : 100 ≤ T) :
    |(N_le T : ℝ) - mainTerm T| < rosserR 1.588 T := by
  have hT0 : 0 < T := by linarith
  apply closed_count_abs_lt_of_good_height_bound hT0
    (M := mainTerm) (B := BacklundFinalScalar.roundedEnvelope)
  · change ContinuousAt rosserF T
    exact (hasDerivAt_rosserF hT0).continuousAt
  · exact continuous_roundedEnvelope hT
  · intro S hTS hg
    exact BacklundCircleMajorant.count_le_roundedEnvelope (hT.trans hTS.le) hg
  · exact BacklundFinalScalar.roundedEnvelope_lt_rosser hT

end TernaryGoldbach.RSBounds.BacklundCountIdentity

namespace TernaryGoldbach.RSBounds.Rosser1941

theorem zero_count_bounds_high (T : ℝ) (hT : 100 ≤ T) :
    |positiveZeroCount T -
      (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8)| <
      0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 := by
  rw [positiveZeroCount_eq (by linarith)]
  exact BacklundCountIdentity.rosser_bound_high hT

end TernaryGoldbach.RSBounds.Rosser1941
end

-- ============================================================================
-- Batch 1: DirichletBasics, GammaRatioAllT, StripPhragmenLindelof
-- ============================================================================

section
open Complex Real MeasureTheory Filter Set
open scoped Topology BigOperators ComplexConjugate Interval

namespace DirichletBasics

theorem ne_one_of_isPrimitive_of_two_le {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) : χ ≠ 1 := by
  intro h
  rw [DirichletCharacter.IsPrimitive, h, DirichletCharacter.conductor_one] at hχ
  omega

theorem conj_apply_eq_inv {q : ℕ} (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    conj (χ a) = χ⁻¹ a := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    have h1 : ‖χ u‖ = 1 := χ.unit_norm_eq_one u
    have hmul : χ u * conj (χ u) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1, one_pow, Complex.ofReal_one]
    have hinv_mul : χ⁻¹ (u : ZMod q) * χ u = 1 := by
      rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply u.isUnit]
    have hinv : χ⁻¹ (u : ZMod q) = (χ u)⁻¹ := eq_inv_of_mul_eq_one_left hinv_mul
    rw [hinv]
    exact eq_inv_of_mul_eq_one_right hmul
  · rw [χ.map_nonunit ha, χ⁻¹.map_nonunit ha, map_zero]

theorem inv_apply_eq_conj {q : ℕ} (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    χ⁻¹ a = conj (χ a) :=
  (conj_apply_eq_inv χ a).symm

lemma even_inv_iff {q : ℕ} (χ : DirichletCharacter ℂ q) :
    χ⁻¹.Even ↔ χ.Even := by
  rw [DirichletCharacter.Even, DirichletCharacter.Even, ← conj_apply_eq_inv]
  constructor
  · intro h
    simpa using congrArg conj h
  · intro h
    rw [h, map_one]

theorem LSeries_conj {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (χ ·) (conj s) = conj (LSeries (χ⁻¹ ·) s) := by
  unfold LSeries
  rw [Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  unfold LSeries.term
  split_ifs with hn
  · simp
  · rw [map_div₀, ← inv_apply_eq_conj, inv_inv]
    congr 1
    have hcpow : (n : ℂ) ^ conj s = conj ((n : ℂ) ^ s) := by
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have harg : ((n : ℝ) : ℂ).arg ≠ Real.pi := by
        rw [Complex.arg_ofReal_of_nonneg hn_pos.le]
        exact Real.pi_ne_zero.symm
      have h0 := Complex.cpow_conj ((n : ℝ) : ℂ) s harg
      rw [Complex.conj_ofReal, Complex.ofReal_natCast] at h0
      exact h0
    exact hcpow

theorem LFunction_conj {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.LFunction χ (conj s) = conj (DirichletCharacter.LFunction χ⁻¹ s) := by
  have hχinv : χ⁻¹ ≠ 1 := fun h => hχ (by simpa using congrArg Inv.inv h)
  let f : ℂ → ℂ := fun z => DirichletCharacter.LFunction χ z
  let g : ℂ → ℂ := fun z => conj (DirichletCharacter.LFunction χ⁻¹ (conj z))
  have hf : AnalyticOnNhd ℂ f Set.univ := fun z _ =>
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hg_diff : Differentiable ℂ g := fun z => by
    have hz : HasDerivAt (DirichletCharacter.LFunction χ⁻¹)
        (deriv (DirichletCharacter.LFunction χ⁻¹) (conj z)) (conj z) :=
      (DirichletCharacter.differentiable_LFunction hχinv _).hasDerivAt
    simpa [g, Function.comp_def] using hz.conj_conj.differentiableAt
  have hg : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg_diff.analyticAt z
  have heq_right : Set.EqOn f g {z : ℂ | 1 < z.re} := by
    intro z hz
    have hzre : 1 < z.re := hz
    dsimp [f, g]
    rw [DirichletCharacter.LFunction_eq_LSeries χ hzre,
      DirichletCharacter.LFunction_eq_LSeries χ⁻¹ (by simpa using hzre)]
    have hcon := congrArg conj (LSeries_conj χ⁻¹ hzre)
    simpa [inv_inv] using hcon.symm
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), f z = g z := by
    have hnh : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    exact (Filter.eventually_of_mem (nhdsWithin_le_nhds hnh) fun z hz => heq_right hz).frequently
  have heq : f (conj s) = g (conj s) :=
    AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hf hg isPreconnected_univ
      (Set.mem_univ (2 : ℂ)) hfreq (Set.mem_univ (conj s))
  simpa [f, g, Complex.conj_conj] using heq

theorem completedLFunction_conj {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.completedLFunction χ (conj s) =
      conj (DirichletCharacter.completedLFunction χ⁻¹ s) := by
  classical
  have hχinv : χ⁻¹ ≠ 1 := fun h => hχ (by simpa using congrArg Inv.inv h)
  let f : ℂ → ℂ := fun z => DirichletCharacter.completedLFunction χ z
  let g : ℂ → ℂ := fun z => conj (DirichletCharacter.completedLFunction χ⁻¹ (conj z))
  have hf : AnalyticOnNhd ℂ f Set.univ := fun z _ =>
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have hg_diff : Differentiable ℂ g := fun z => by
    have hz : HasDerivAt (DirichletCharacter.completedLFunction χ⁻¹)
        (deriv (DirichletCharacter.completedLFunction χ⁻¹) (conj z)) (conj z) :=
      (DirichletCharacter.differentiable_completedLFunction hχinv _).hasDerivAt
    simpa [g, Function.comp_def] using hz.conj_conj.differentiableAt
  have hg : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg_diff.analyticAt z
  have heq_right : Set.EqOn f g {z : ℂ | 1 < z.re} := by
    intro z hz
    have hzre : 1 < z.re := hz
    have hcz : 1 < (conj z).re := by simpa using hzre
    have hz0 : z ≠ 0 := fun h0 => by rw [h0] at hzre; simp at hzre; linarith
    have hcz0 : conj z ≠ 0 := by simpa using hz0
    dsimp [f, g]
    have hL1 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (.inl hz0)
    have hL2 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (conj z) (.inl hcz0)
    have hg1 : DirichletCharacter.gammaFactor χ z ≠ 0 := by
      rw [DirichletCharacter.gammaFactor]
      split_ifs
      · exact Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
      · exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    have hg2 : DirichletCharacter.gammaFactor χ⁻¹ (conj z) ≠ 0 := by
      rw [DirichletCharacter.gammaFactor]
      split_ifs
      · exact Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using by linarith)
      · exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    have hfc1 : DirichletCharacter.completedLFunction χ z =
        DirichletCharacter.LFunction χ z * DirichletCharacter.gammaFactor χ z :=
      ((eq_div_iff hg1).mp hL1).symm
    have hfc2 : DirichletCharacter.completedLFunction χ⁻¹ (conj z) =
        DirichletCharacter.LFunction χ⁻¹ (conj z) * DirichletCharacter.gammaFactor χ⁻¹ (conj z) :=
      ((eq_div_iff hg2).mp hL2).symm
    have hgf : conj (DirichletCharacter.gammaFactor χ⁻¹ (conj z)) =
        DirichletCharacter.gammaFactor χ z := by
      have harg_pi : (Real.pi : ℂ).arg ≠ Real.pi := by
        rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
        exact Real.pi_ne_zero.symm
      rw [DirichletCharacter.gammaFactor, DirichletCharacter.gammaFactor]
      simp only [even_inv_iff χ]
      split_ifs with h
      · rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul]
        have hpow : conj ((Real.pi : ℂ) ^ (-(conj z) / 2)) = (Real.pi : ℂ) ^ (-z / 2) := by
          have h1 : -(conj z) / 2 = conj (-z / 2) := by simp [map_ofNat]
          have h0 := Complex.cpow_conj (Real.pi : ℂ) (-z / 2) harg_pi
          rw [Complex.conj_ofReal] at h0
          rw [h1, h0, Complex.conj_conj]
        have hgam : conj (Complex.Gamma (conj z / 2)) = Complex.Gamma (z / 2) := by
          have h1 : conj z / 2 = conj (z / 2) := by simp [map_ofNat]
          rw [h1, ← Complex.Gamma_conj, Complex.conj_conj]
        rw [hpow, hgam]
      · rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul]
        have hpow : conj ((Real.pi : ℂ) ^ (-(conj z + 1) / 2)) = (Real.pi : ℂ) ^ (-(z + 1) / 2) := by
          have h1 : -(conj z + 1) / 2 = conj (-(z + 1) / 2) := by simp [map_ofNat]
          have h0 := Complex.cpow_conj (Real.pi : ℂ) (-(z + 1) / 2) harg_pi
          rw [Complex.conj_ofReal] at h0
          rw [h1, h0, Complex.conj_conj]
        have hgam : conj (Complex.Gamma ((conj z + 1) / 2)) = Complex.Gamma ((z + 1) / 2) := by
          have h1 : (conj z + 1) / 2 = conj ((z + 1) / 2) := by simp [map_ofNat]
          rw [h1, ← Complex.Gamma_conj, Complex.conj_conj]
        rw [hpow, hgam]
    rw [hfc1, hfc2, map_mul, hgf, ← LFunction_conj χ hχ (conj z), Complex.conj_conj]
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), f z = g z := by
    have hnh : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    exact (Filter.eventually_of_mem (nhdsWithin_le_nhds hnh) fun z hz => heq_right hz).frequently
  have heq : f (conj s) = g (conj s) :=
    AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hf hg isPreconnected_univ
      (Set.mem_univ (2 : ℂ)) hfreq (Set.mem_univ (conj s))
  simpa [f, g, Complex.conj_conj] using heq

theorem norm_LFunction_le_zeta {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ ‖riemannZeta (s.re : ℂ)‖ := by
  have hσ : 1 < ((s.re : ℝ) : ℂ).re := by simpa using hs
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hprod1 := (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).norm
  have hprod2 := (riemannZeta_eulerProduct_hasProd hσ).norm
  apply le_of_tendsto_of_tendsto' hprod1 hprod2
  intro S
  refine Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) fun p _ => ?_
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hp0 : 0 < (p : ℝ) := by linarith
  let a : ℝ := (p : ℝ) ^ (-s.re)
  have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hpow_re : (p : ℂ) ^ (-(s.re : ℂ)) = (a : ℂ) := by
    simpa only [a, Complex.ofReal_neg, Complex.ofReal_natCast] using
      (Complex.ofReal_cpow hp0.le (-s.re)).symm
  have hnorm_sub : ‖(p : ℂ) ^ (-s)‖ = a := by
    simpa only [a, Complex.neg_re, Complex.ofReal_natCast] using
      Complex.norm_cpow_eq_rpow_re_of_pos hp0 (-s)
  have hχp : ‖χ p‖ ≤ 1 := χ.norm_le_one (p : ZMod q)
  have hterm : ‖χ p * (p : ℂ) ^ (-s)‖ ≤ a := by
    rw [norm_mul, hnorm_sub]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hp0.le _) hχp
  have hden1 : 1 - a ≤ ‖1 - χ p * (p : ℂ) ^ (-s)‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) (χ p * (p : ℂ) ^ (-s))
    rw [norm_one] at h1
    linarith
  have hden2 : ‖1 - (p : ℂ) ^ (-(s.re : ℂ))‖ = 1 - a := by
    rw [hpow_re, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_of_nonneg (sub_nonneg.mpr ha1.le)]
  rw [norm_inv, norm_inv, hden2]
  exact inv_anti₀ (sub_pos.mpr ha1) hden1

theorem LFunction_five_fourths_upper {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + t * I)‖ < 23 / 5 := by
  have hs : 1 < ((5 / 4 : ℂ) + t * I).re := by simp; norm_num
  have h := norm_LFunction_le_zeta χ hs
  have hre : (((5 / 4 : ℂ) + t * I).re : ℂ) = ((5 / 4 : ℝ) : ℂ) := by simp
  rw [hre] at h
  exact h.trans_lt TernaryGoldbach.RSBounds.zeta_five_fourths_upper

theorem LFunction_six_fifths_upper {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖DirichletCharacter.LFunction χ ((6 / 5 : ℂ) + t * I)‖ ≤ 6 := by
  have hs : 1 < ((6 / 5 : ℂ) + t * I).re := by simp; norm_num
  have h := norm_LFunction_le_zeta χ hs
  have hre : (((6 / 5 : ℂ) + t * I).re : ℂ) = ((6 / 5 : ℝ) : ℂ) := by simp
  rw [hre] at h
  have hz := TernaryGoldbach.RSBounds.CenterNumerics.zeta_tail_upper (σ := 6 / 5)
    (by norm_num) (N := 1) (by norm_num)
  norm_num [TernaryGoldbach.RSBounds.CenterNumerics.rpowSum] at hz
  exact h.trans (by convert hz using 2; norm_num)

private theorem center_factor_le_of_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    {z : ℂ} (hz : ‖z‖ ≤ a) :
    ‖(1 - (a : ℂ) ^ 2)⁻¹‖ ≤ ‖(1 - (a : ℂ))⁻¹‖ * ‖(1 - z)⁻¹‖ := by
  have h1 : 0 < 1 - a := sub_pos.mpr ha1
  have h2 : 0 < 1 - a ^ 2 := by nlinarith
  have hz1 : 0 < ‖(1 : ℂ) - z‖ := by
    have : 1 - a ≤ ‖(1 : ℂ) - z‖ := by
      have hh := norm_sub_norm_le (1 : ℂ) z
      rw [norm_one] at hh
      linarith
    linarith
  have htri : ‖(1 : ℂ) - z‖ ≤ 1 + a := by
    have hh := norm_sub_le (1 : ℂ) z
    rw [norm_one] at hh
    linarith
  have hreal1 : ‖(1 : ℂ) - (a : ℂ)‖ = 1 - a := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_of_nonneg h1.le]
  have hreal2 : ‖(1 : ℂ) - (a : ℂ) ^ 2‖ = 1 - a ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_of_nonneg h2.le]
  rw [norm_inv, norm_inv, norm_inv, hreal1, hreal2, ← mul_inv]
  apply (inv_le_inv₀ h2 (mul_pos h1 hz1)).mpr
  nlinarith [mul_le_mul_of_nonneg_left htri h1.le]

theorem LFunction_norm_lower_five_fourths_3426 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) :
    (1 : ℝ) / 3.426 ≤ ‖DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + t * I)‖ := by
  let s : ℂ := (5 / 4 : ℂ) + t * I
  have hs : 1 < s.re := by simp [s]; norm_num
  have hσ : 1 < ((s.re : ℝ) : ℂ).re := by simpa using hs
  have h2σ : 1 < (((2 * s.re : ℝ) : ℂ)).re := by simpa using (show 1 < 2 * s.re by linarith)
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hprod := (riemannZeta_eulerProduct_hasProd hσ).norm.mul
    (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).norm
  have hprod2 := (riemannZeta_eulerProduct_hasProd h2σ).norm
  have hlim : ‖riemannZeta ((2 * s.re : ℝ) : ℂ)‖ ≤
      ‖riemannZeta (s.re : ℂ)‖ * ‖LSeries (χ ·) s‖ := by
    apply le_of_tendsto_of_tendsto' hprod2 hprod
    intro S
    refine Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) fun p _ => ?_
    have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    have hp0 : 0 < (p : ℝ) := by linarith
    let a : ℝ := (p : ℝ) ^ (-s.re)
    have ha : 0 ≤ a := Real.rpow_nonneg hp0.le _
    have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
    have hpow : (p : ℂ) ^ (-(s.re : ℂ)) = (a : ℂ) := by
      simpa only [a, Complex.ofReal_neg, Complex.ofReal_natCast] using
        (Complex.ofReal_cpow hp0.le (-s.re)).symm
    have hpow2 : (p : ℂ) ^ (-((2 * s.re : ℝ) : ℂ)) = (a : ℂ) ^ 2 := by
      rw [show -((2 * s.re : ℝ) : ℂ) = -(s.re : ℂ) * (2 : ℕ) by push_cast; ring,
        Complex.cpow_mul_nat, hpow]
    have hz : ‖χ p * (p : ℂ) ^ (-s)‖ ≤ a := by
      rw [norm_mul, show ‖(p : ℂ) ^ (-s)‖ = a by
        simpa only [a, Complex.neg_re, Complex.ofReal_natCast] using
          Complex.norm_cpow_eq_rpow_re_of_pos hp0 (-s)]
      exact mul_le_of_le_one_left (Real.rpow_nonneg hp0.le _) (χ.norm_le_one _)
    rw [hpow, hpow2]
    exact center_factor_le_of_le ha ha1 hz
  have hζ : 0 < ‖riemannZeta (s.re : ℂ)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hσ)
  have hratio : ‖riemannZeta ((2 * s.re : ℝ) : ℂ)‖ / ‖riemannZeta (s.re : ℂ)‖ ≤
      ‖LSeries (χ ·) s‖ := (div_le_iff₀ hζ).mpr (by simpa only [mul_comm] using hlim)
  have hsre : s.re = 5 / 4 := by simp [s]
  rw [hsre] at hratio
  have h1 : 0 < ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  have h2 : 0 < ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  have hrb := (div_lt_iff₀ h2).mp TernaryGoldbach.RSBounds.zeta_five_fourths_ratio_bounds.2
  have hc : (1 : ℝ) / 3.426 ≤
      ‖riemannZeta ((2 * (5 / 4) : ℝ) : ℂ)‖ / ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ := by
    rw [le_div_iff₀ h1]
    norm_num at hrb ⊢
    linarith
  exact hc.trans hratio

noncomputable def chiEulerLog {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, -Complex.log (1 - χ p * (p : ℂ) ^ (-s))

lemma norm_chiEulerLog_le {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    ‖chiEulerLog χ s‖ ≤ Real.log ‖riemannZeta (s.re : ℂ)‖ := by
  let r : Nat.Primes → ℝ := fun p => (p : ℝ) ^ (-s.re)
  have hrs : Summable r := Nat.Primes.summable_rpow.mpr (by linarith)
  have hlogs : Summable (fun p => -Real.log (1 - r p)) := by
    simpa only [sub_eq_add_neg] using (Real.summable_log_one_add_of_summable hrs.neg).neg
  have he : Real.log ‖riemannZeta (s.re : ℂ)‖ =
      ∑' p : Nat.Primes, -Real.log (1 - r p) := by
    rw [← riemannZeta_eulerProduct_exp_log (by simpa using hs),
      show (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s.re : ℂ)))) =
        TernaryGoldbach.RSBounds.BacklundAnchor.eulerLog (s.re : ℂ) from rfl,
      TernaryGoldbach.RSBounds.BacklundAnchor.real_eulerLog hs,
      Complex.norm_exp, Complex.ofReal_re, Real.log_exp]
  rw [he, chiEulerLog]
  apply tsum_of_norm_bounded hlogs.hasSum
  intro p
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hp0 : 0 < (p : ℝ) := by linarith
  have hn : ‖χ p * (p : ℂ) ^ (-s)‖ ≤ r p := by
    rw [norm_mul, show ‖(p : ℂ) ^ (-s)‖ = r p by
      simpa only [r, Complex.neg_re, Complex.ofReal_natCast] using
        Complex.norm_cpow_eq_rpow_re_of_pos hp0 (-s)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hp0.le _) (χ.norm_le_one _)
  have hlt : r p < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hbound := TernaryGoldbach.RSBounds.BacklundAnchor.norm_neg_log_one_sub_le
    (z := χ p * (p : ℂ) ^ (-s)) (hn.trans_lt hlt)
  refine hbound.trans ?_
  apply neg_le_neg
  exact Real.log_le_log (sub_pos.mpr hlt) (by linarith)

theorem re_LFunction_anchor_pos {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    0 < (DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + t * I)).re := by
  let s : ℂ := (5 / 4 : ℂ) + t * I
  have hs : 1 < s.re := by simp [s]; norm_num
  have hre : s.re = 5 / 4 := by simp [s]
  have hb : ‖chiEulerLog χ s‖ < Real.pi / 2 :=
    (norm_chiEulerLog_le χ hs).trans_lt
      (by simpa [hre] using TernaryGoldbach.RSBounds.BacklundAnchor.log_zeta_five_fourths_lt_half_pi)
  have hi : |(chiEulerLog χ s).im| < Real.pi / 2 :=
    (Complex.abs_im_le_norm _).trans_lt hb
  have hc : 0 < Real.cos (chiEulerLog χ s).im := Real.cos_pos_of_mem_Ioo (abs_lt.mp hi)
  change 0 < (DirichletCharacter.LFunction χ s).re
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs,
    ← DirichletCharacter.LSeries_eulerProduct_exp_log χ hs]
  change 0 < (Complex.exp (chiEulerLog χ s)).re
  rw [Complex.exp_re]
  exact mul_pos (Real.exp_pos _) hc

theorem LFunction_anchor_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + t * I) ≠ 0 := by
  intro h
  have hre := re_LFunction_anchor_pos χ t
  rw [h, Complex.zero_re] at hre
  exact lt_irrefl 0 hre

set_option maxHeartbeats 800000 in
theorem vertical_integral_LFunction_five_fourths_le_pi {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (T : ℝ) :
    |(∫ t in (-T)..T,
        logDeriv (DirichletCharacter.LFunction χ) ((5 / 4 : ℂ) + t * I) * I).im| ≤
      Real.pi := by
  let L := DirichletCharacter.LFunction χ
  let F : ℝ → ℂ := fun t => Complex.log (L ((5 / 4 : ℂ) + t * I))
  have hL_diff : Differentiable ℂ L := DirichletCharacter.differentiable_LFunction hχ
  have hL_ana : AnalyticOnNhd ℂ L Set.univ := fun z _ => hL_diff.analyticAt z
  have hderiv : ∀ t ∈ Set.uIcc (-T) T,
      HasDerivAt F (logDeriv L ((5 / 4 : ℂ) + t * I) * I) t := by
    intro t _
    have hre : 0 < (L ((5 / 4 : ℂ) + t * I)).re := re_LFunction_anchor_pos χ t
    have hline : HasDerivAt (fun u : ℝ => (5 / 4 : ℂ) + u * I) I t := by
      have h : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt (x := t)
      simpa using (h.mul_const I).const_add (5 / 4 : ℂ)
    have hL : HasDerivAt L (deriv L ((5 / 4 : ℂ) + t * I)) ((5 / 4 : ℂ) + t * I) :=
      (hL_diff _).hasDerivAt
    have hcomp := hL.comp t hline
    have hlog := (Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.mpr (.inl hre))).comp t hcomp
    refine hlog.congr_deriv ?_
    rw [logDeriv_apply]
    ring
  have hcont : Continuous fun t : ℝ => logDeriv L ((5 / 4 : ℂ) + t * I) * I := by
    have h1 : Continuous fun t : ℝ => (5 / 4 : ℂ) + t * I :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have h2 : Continuous L := hL_diff.continuous
    have h3 : Continuous (deriv L) :=
      continuousOn_univ.mp (hL_ana.deriv).continuousOn
    have h4 : ∀ t : ℝ, L ((5 / 4 : ℂ) + t * I) ≠ 0 := LFunction_anchor_ne_zero χ
    exact (((h3.comp h1).div (h2.comp h1) h4)).mul continuous_const
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable (-T) T)
  rw [hint]
  dsimp [F]
  simp only [Complex.log_im]
  have hpos1 : 0 < (L ((5 / 4 : ℂ) + T * I)).re := re_LFunction_anchor_pos χ T
  have hpos2 : 0 < (L ((5 / 4 : ℂ) + ((-T : ℝ) : ℂ) * I)).re := re_LFunction_anchor_pos χ (-T)
  have h1 : |(L ((5 / 4 : ℂ) + T * I)).arg| < Real.pi / 2 :=
    abs_lt.mpr ⟨Complex.neg_pi_div_two_lt_arg_iff.mpr (.inl hpos1),
      Complex.arg_lt_pi_div_two_iff.mpr (.inl hpos1)⟩
  have h2 : |(L ((5 / 4 : ℂ) + ((-T : ℝ) : ℂ) * I)).arg| < Real.pi / 2 :=
    abs_lt.mpr ⟨Complex.neg_pi_div_two_lt_arg_iff.mpr (.inl hpos2),
      Complex.arg_lt_pi_div_two_iff.mpr (.inl hpos2)⟩
  simpa using ((abs_sub _ _).trans (add_le_add h1.le h2.le)).trans_eq (by ring)

end DirichletBasics

namespace GammaRatioAllT

lemma norm_sin_le_cosh_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.cosh z.im := by
  have he : Complex.sin z = -Complex.cos (z + (Real.pi : ℂ) / 2) := by
    rw [Complex.cos_add_pi_div_two, neg_neg]
  rw [he, norm_neg]
  have h := TernaryGoldbach.RSBounds.BacklundFunctionalMultiplier.norm_cos_le_cosh_im
    (z + (Real.pi : ℂ) / 2)
  simpa using h

lemma norm_Gamma_le_one_of_Icc {w : ℂ} (hw1 : 1 ≤ w.re) (hw2 : w.re ≤ 2) :
    ‖Complex.Gamma w‖ ≤ 1 := by
  have hw0 : 0 < w.re := by linarith
  rw [Complex.Gamma_eq_integral hw0]
  have hnorm : ‖Complex.GammaIntegral w‖ ≤
      ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * x ^ (w.re - 1) := by
    unfold Complex.GammaIntegral
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans_eq ?_
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re]
  have hGamma : ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * x ^ (w.re - 1) = Real.Gamma w.re := by
    rw [Real.Gamma_eq_integral hw0]
  have hconv : Real.Gamma w.re ≤ 1 := by
    let a : ℝ := 2 - w.re
    let b : ℝ := w.re - 1
    have ha : 0 ≤ a := by simp [a]; linarith
    have hb : 0 ≤ b := by simp [b]; linarith
    have hab : a + b = 1 := by simp [a, b]; ring
    have hc := Real.convexOn_Gamma.2 (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num) ha hb hab
    have hpt : a • (1 : ℝ) + b • (2 : ℝ) = w.re := by simp [a, b, smul_eq_mul]; ring
    rw [hpt, Real.Gamma_one, Real.Gamma_two] at hc
    simpa [a, b, smul_eq_mul, hab] using hc
  exact (hnorm.trans_eq hGamma).trans hconv

lemma gammaFactor_one_sub_div_even {s : ℂ} (hs : s.im ≠ 0) :
    Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s =
      (2 * (Real.pi : ℂ)) ^ (s - 1) * 2 * Complex.sin ((Real.pi : ℂ) * s / 2) *
        Complex.Gamma (1 - s) := by
  have hs2 : Complex.sin ((Real.pi : ℂ) * (s / 2)) ≠ 0 := by
    intro h
    rw [Complex.sin_eq_zero_iff] at h
    rcases h with ⟨k, hk⟩
    have him := congrArg Complex.im hk
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat_im,
      zero_mul, add_zero, Complex.intCast_im, Complex.intCast_re, zero_add] at him
    have : s.im = 0 := by nlinarith [Real.pi_pos]
    exact hs this
  have hπ0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h20 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hrefl : (Complex.Gamma (s / 2))⁻¹ =
      Complex.Gamma (1 - s / 2) * Complex.sin ((Real.pi : ℂ) * (s / 2)) / (Real.pi : ℂ) := by
    have hr := Complex.Gamma_mul_Gamma_one_sub (s / 2)
    have hG1s : Complex.Gamma (1 - s / 2) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hr
      exact div_ne_zero hπ0 hs2 hr.symm
    have hinv : Complex.Gamma (s / 2) =
        (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * (s / 2)) / Complex.Gamma (1 - s / 2) :=
      eq_div_of_mul_eq hG1s hr
    rw [hinv]
    field_simp
  have hdup := Complex.Gamma_mul_Gamma_add_half ((1 - s) / 2)
  have hadd : (1 - s) / 2 + 1 / 2 = 1 - s / 2 := by ring
  have h2u : 2 * ((1 - s) / 2) = 1 - s := by ring
  rw [hadd, h2u, show (1 : ℂ) - (1 - s) = s by ring] at hdup
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, div_eq_mul_inv, mul_inv]
  have hpi_pow : (Real.pi : ℂ) ^ (-(1 - s) / 2) * ((Real.pi : ℂ) ^ (-s / 2))⁻¹ =
      (Real.pi : ℂ) ^ (s - 1 / 2) := by
    rw [← Complex.cpow_neg, ← Complex.cpow_add _ _ hπ0]
    congr 1; ring
  have h2pi : (2 * (Real.pi : ℂ)) ^ (s - 1) = (2 : ℂ) ^ (s - 1) * (Real.pi : ℂ) ^ (s - 1) :=
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity) _
  have h2s : (2 : ℂ) ^ (s - 1) * 2 = (2 : ℂ) ^ s := by
    rw [Complex.cpow_sub _ _ h20, Complex.cpow_one]
    field_simp
  have hpi_sqrt : (Real.pi : ℂ) ^ (s - 1 / 2) * ↑√Real.pi / (Real.pi : ℂ) =
      (Real.pi : ℂ) ^ (s - 1) := by
    have hs1 : (↑√Real.pi : ℂ) = (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
      norm_num
    rw [hs1, ← Complex.cpow_add _ _ hπ0, Complex.cpow_sub _ _ hπ0, Complex.cpow_one]
    congr 1; ring
  calc
    (Real.pi : ℂ) ^ (-(1 - s) / 2) * Complex.Gamma ((1 - s) / 2) *
        (((Real.pi : ℂ) ^ (-s / 2))⁻¹ * (Complex.Gamma (s / 2))⁻¹)
      = ((Real.pi : ℂ) ^ (-(1 - s) / 2) * ((Real.pi : ℂ) ^ (-s / 2))⁻¹) *
          (Complex.Gamma ((1 - s) / 2) * Complex.Gamma (1 - s / 2)) *
          Complex.sin ((Real.pi : ℂ) * (s / 2)) / (Real.pi : ℂ) := by
        rw [hrefl]; ring
    _ = ((Real.pi : ℂ) ^ (s - 1 / 2) * ↑√Real.pi / (Real.pi : ℂ)) *
          ((2 : ℂ) ^ s * Complex.sin ((Real.pi : ℂ) * s / 2) * Complex.Gamma (1 - s)) := by
        rw [hpi_pow, hdup, show (Real.pi : ℂ) * (s / 2) = (Real.pi : ℂ) * s / 2 by ring]
        ring
    _ = (2 * (Real.pi : ℂ)) ^ (s - 1) * 2 * Complex.sin ((Real.pi : ℂ) * s / 2) *
          Complex.Gamma (1 - s) := by
        rw [hpi_sqrt, h2pi]
        calc
          (Real.pi : ℂ) ^ (s - 1) * ((2 : ℂ) ^ s * Complex.sin ((Real.pi : ℂ) * s / 2) * Complex.Gamma (1 - s))
            = (Real.pi : ℂ) ^ (s - 1) * ((2 : ℂ) ^ (s - 1) * 2) *
                Complex.sin ((Real.pi : ℂ) * s / 2) * Complex.Gamma (1 - s) := by
              rw [h2s]; ring
          _ = _ := by ring

lemma gammaFactor_one_sub_div_odd {s : ℂ} (hs : s.im ≠ 0) :
    Complex.Gammaℝ (1 - s + 1) / Complex.Gammaℝ (s + 1) =
      (2 * (Real.pi : ℂ)) ^ (s - 1) * 2 * Complex.cos ((Real.pi : ℂ) * s / 2) *
        Complex.Gamma (1 - s) := by
  have hs2 : Complex.sin ((Real.pi : ℂ) * ((s + 1) / 2)) ≠ 0 := by
    intro h
    rw [Complex.sin_eq_zero_iff] at h
    rcases h with ⟨k, hk⟩
    have him := congrArg Complex.im hk
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat_im,
      Complex.add_im, Complex.one_im, add_zero, zero_mul, Complex.intCast_im,
      Complex.intCast_re] at him
    have : s.im = 0 := by nlinarith [Real.pi_pos]
    exact hs this
  have hπ0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h20 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hrefl : (Complex.Gamma ((s + 1) / 2))⁻¹ =
      Complex.Gamma ((1 - s) / 2) * Complex.cos ((Real.pi : ℂ) * s / 2) / (Real.pi : ℂ) := by
    have hr := Complex.Gamma_mul_Gamma_one_sub ((s + 1) / 2)
    have h1u : 1 - (s + 1) / 2 = (1 - s) / 2 := by ring
    have hsin : Complex.sin ((Real.pi : ℂ) * ((s + 1) / 2)) = Complex.cos ((Real.pi : ℂ) * s / 2) := by
      rw [show (Real.pi : ℂ) * ((s + 1) / 2) = (Real.pi : ℂ) * s / 2 + (Real.pi : ℂ) / 2 by ring,
        Complex.sin_add_pi_div_two]
    rw [h1u, hsin] at hr
    have hcos : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by rwa [← hsin]
    have hG1s : Complex.Gamma ((1 - s) / 2) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hr
      exact div_ne_zero hπ0 hcos hr.symm
    have hinv : Complex.Gamma ((s + 1) / 2) =
        (Real.pi : ℂ) / Complex.cos ((Real.pi : ℂ) * s / 2) / Complex.Gamma ((1 - s) / 2) :=
      eq_div_of_mul_eq hG1s hr
    rw [hinv]
    field_simp
  have hdup := Complex.Gamma_mul_Gamma_add_half ((1 - s) / 2)
  have hadd : (1 - s) / 2 + 1 / 2 = (1 - s + 1) / 2 := by ring
  have h2u : 2 * ((1 - s) / 2) = 1 - s := by ring
  rw [hadd, h2u, show (1 : ℂ) - (1 - s) = s by ring] at hdup
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, div_eq_mul_inv, mul_inv]
  have hpi_pow : (Real.pi : ℂ) ^ (-(1 - s + 1) / 2) * ((Real.pi : ℂ) ^ (-(s + 1) / 2))⁻¹ =
      (Real.pi : ℂ) ^ (s - 1 / 2) := by
    rw [← Complex.cpow_neg, ← Complex.cpow_add _ _ hπ0]
    congr 1; ring
  have h2pi : (2 * (Real.pi : ℂ)) ^ (s - 1) = (2 : ℂ) ^ (s - 1) * (Real.pi : ℂ) ^ (s - 1) :=
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity) _
  have h2s : (2 : ℂ) ^ (s - 1) * 2 = (2 : ℂ) ^ s := by
    rw [Complex.cpow_sub _ _ h20, Complex.cpow_one]
    field_simp
  have hpi_sqrt : (Real.pi : ℂ) ^ (s - 1 / 2) * ↑√Real.pi / (Real.pi : ℂ) =
      (Real.pi : ℂ) ^ (s - 1) := by
    have hs1 : (↑√Real.pi : ℂ) = (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
      norm_num
    rw [hs1, ← Complex.cpow_add _ _ hπ0, Complex.cpow_sub _ _ hπ0, Complex.cpow_one]
    congr 1; ring
  calc
    (Real.pi : ℂ) ^ (-(1 - s + 1) / 2) * Complex.Gamma ((1 - s + 1) / 2) *
        (((Real.pi : ℂ) ^ (-(s + 1) / 2))⁻¹ * (Complex.Gamma ((s + 1) / 2))⁻¹)
      = ((Real.pi : ℂ) ^ (-(1 - s + 1) / 2) * ((Real.pi : ℂ) ^ (-(s + 1) / 2))⁻¹) *
          (Complex.Gamma ((1 - s) / 2) * Complex.Gamma ((1 - s + 1) / 2)) *
          Complex.cos ((Real.pi : ℂ) * s / 2) / (Real.pi : ℂ) := by
        rw [hrefl]; ring
    _ = ((Real.pi : ℂ) ^ (s - 1 / 2) * ↑√Real.pi / (Real.pi : ℂ)) *
          ((2 : ℂ) ^ s * Complex.cos ((Real.pi : ℂ) * s / 2) * Complex.Gamma (1 - s)) := by
        rw [hpi_pow, hdup]
        ring
    _ = (2 * (Real.pi : ℂ)) ^ (s - 1) * 2 * Complex.cos ((Real.pi : ℂ) * s / 2) *
          Complex.Gamma (1 - s) := by
        rw [hpi_sqrt, h2pi]
        calc
          (Real.pi : ℂ) ^ (s - 1) * ((2 : ℂ) ^ s * Complex.cos ((Real.pi : ℂ) * s / 2) * Complex.Gamma (1 - s))
            = (Real.pi : ℂ) ^ (s - 1) * ((2 : ℂ) ^ (s - 1) * 2) *
                Complex.cos ((Real.pi : ℂ) * s / 2) * Complex.Gamma (1 - s) := by
              rw [h2s]; ring
          _ = _ := by ring

open Classical in
theorem norm_gammaFactor_ratio_eq {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s.im ≠ 0) :
    ‖DirichletCharacter.gammaFactor χ⁻¹ (1 - s) / DirichletCharacter.gammaFactor χ s‖ =
      (2 * Real.pi) ^ (s.re - 1) * 2 *
        (if χ.Even then ‖Complex.sin ((Real.pi : ℂ) * s / 2)‖
          else ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖) *
        ‖Complex.Gamma (1 - s)‖ := by
  rw [DirichletCharacter.gammaFactor, DirichletCharacter.gammaFactor]
  simp only [DirichletBasics.even_inv_iff χ]
  have h2pi_norm : ‖(2 * (Real.pi : ℂ)) ^ (s - 1)‖ = (2 * Real.pi) ^ (s.re - 1) := by
    have h0 : 0 < 2 * Real.pi := by positivity
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos h0]
    simp
  split_ifs with h
  · rw [gammaFactor_one_sub_div_even hs, norm_mul, norm_mul, norm_mul, h2pi_norm, Complex.norm_ofNat]
  · rw [gammaFactor_one_sub_div_odd hs, norm_mul, norm_mul, norm_mul, h2pi_norm, Complex.norm_ofNat]

lemma norm_gammaFactor_ratio_le_low {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s.im ≠ 0) (hσ1 : -1 ≤ s.re) (hσ2 : s.re ≤ 0) (ht : |s.im| ≤ 7 / 5) :
    ‖DirichletCharacter.gammaFactor χ⁻¹ (1 - s) / DirichletCharacter.gammaFactor χ s‖ ≤
      (17 / 10 : ℝ) * ((|s.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re) := by
  classical
  rw [norm_gammaFactor_ratio_eq χ hs]
  have hG : ‖Complex.Gamma (1 - s)‖ ≤ 1 :=
    norm_Gamma_le_one_of_Icc (by simp; linarith) (by simp; linarith)
  have htrig : (if χ.Even then ‖Complex.sin ((Real.pi : ℂ) * s / 2)‖
      else ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖) ≤ Real.cosh (Real.pi * 7 / 10) := by
    have him : ((Real.pi : ℂ) * s / 2).im = Real.pi * s.im / 2 := by
      simp [Complex.div_ofNat_im, Complex.mul_im]
    have hch : Real.cosh (Real.pi * s.im / 2) ≤ Real.cosh (Real.pi * 7 / 10) := by
      apply Real.cosh_le_cosh.mpr
      have habs : |Real.pi * s.im / 2| = Real.pi * |s.im| / 2 := by
        rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [habs, abs_of_pos (by positivity : 0 < Real.pi * 7 / 10)]
      nlinarith [Real.pi_pos]
    split_ifs
    · exact ((norm_sin_le_cosh_im _).trans_eq (by rw [him])).trans hch
    · exact ((TernaryGoldbach.RSBounds.BacklundFunctionalMultiplier.norm_cos_le_cosh_im _).trans_eq
        (by rw [him])).trans hch
  have hcosh_num : Real.cosh (Real.pi * 7 / 10) ≤ 4.595 := by
    have hpi : Real.pi * 7 / 10 ≤ 2.205 := by nlinarith [Real.pi_lt_d4]
    have hc1 : Real.cosh (Real.pi * 7 / 10) ≤ Real.cosh 2.205 :=
      Real.cosh_le_cosh.mpr (by
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by norm_num)]
        exact hpi)
    have hexp_pos : Real.exp 2.205 ≤ 9.071 := by
      have h0 := Real.exp_bound' (x := (0.735 : ℝ)) (by norm_num) (by norm_num) (n := 10) (by norm_num)
      norm_num [Finset.sum_range_succ] at h0
      have h1 : Real.exp (0.735 : ℝ) ≤ 2.0855 := by linarith
      have h2 := pow_le_pow_left₀ (Real.exp_nonneg _) h1 3
      rw [← Real.exp_nat_mul] at h2
      have h3 : (3 : ℕ) * (0.735 : ℝ) = 2.205 := by norm_num
      rw [h3] at h2
      linarith
    have hexp_neg : Real.exp (-2.205) ≤ 0.119 := by
      have hsum := Real.sum_le_exp_of_nonneg (x := (2.205 : ℝ)) (by norm_num) 5
      norm_num [Finset.sum_range_succ] at hsum
      rw [Real.exp_neg]
      exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
    have hch_eq : Real.cosh (2.205 : ℝ) = (Real.exp 2.205 + Real.exp (-2.205)) / 2 := Real.cosh_eq 2.205
    linarith [hc1, hch_eq, hexp_pos, hexp_neg]
  have hp2 : 0 < 2 * Real.pi := by positivity
  have ht5 : 5 ≤ |s.im| + 5 := by linarith [abs_nonneg s.im]
  have hrhs_pow : ((|s.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re) =
      (|s.im| + 5) ^ (1 / 2 - s.re) * (2 * Real.pi) ^ (s.re - 1 / 2) := by
    rw [Real.div_rpow (by linarith) hp2.le, div_eq_mul_inv,
      ← Real.rpow_neg hp2.le, neg_sub]
  have h5_pow : Real.sqrt 5 ≤ (|s.im| + 5) ^ (1 / 2 - s.re) := by
    rw [Real.sqrt_eq_rpow]
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 5) (by linarith)).trans
      (Real.rpow_le_rpow (by norm_num) ht5 (by linarith))
  have hsqrt_10pi : 5.603 ≤ Real.sqrt (10 * Real.pi) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [Real.pi_gt_d4]
  have hsqrt_rel : Real.sqrt 5 * Real.sqrt (2 * Real.pi) = Real.sqrt (10 * Real.pi) := by
    rw [← Real.sqrt_mul (by norm_num)]
    congr 1; ring
  have h2pi_pow : (2 * Real.pi) ^ (s.re - 1) * Real.sqrt (2 * Real.pi) =
      (2 * Real.pi) ^ (s.re - 1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp2]
    congr 1; ring
  have hconst : 2 * Real.cosh (Real.pi * 7 / 10) ≤ (17 / 10 : ℝ) * Real.sqrt (10 * Real.pi) := by
    nlinarith [hcosh_num, hsqrt_10pi]
  have hstep1 : (2 * Real.pi) ^ (s.re - 1) * 2 *
      (if χ.Even then ‖Complex.sin ((Real.pi : ℂ) * s / 2)‖
        else ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖) *
      ‖Complex.Gamma (1 - s)‖ ≤ (2 * Real.pi) ^ (s.re - 1) * (2 * Real.cosh (Real.pi * 7 / 10)) := by
    have h0 : 0 ≤ (2 * Real.pi) ^ (s.re - 1) * 2 *
        (if χ.Even then ‖Complex.sin ((Real.pi : ℂ) * s / 2)‖
          else ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖) := by
      refine mul_nonneg (mul_nonneg (Real.rpow_nonneg hp2.le _) (by norm_num)) ?_
      split_ifs <;> exact norm_nonneg _
    calc _ ≤ (2 * Real.pi) ^ (s.re - 1) * 2 *
          (if χ.Even then ‖Complex.sin ((Real.pi : ℂ) * s / 2)‖
            else ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖) * 1 :=
          mul_le_mul_of_nonneg_left hG h0
      _ ≤ (2 * Real.pi) ^ (s.re - 1) * 2 * Real.cosh (Real.pi * 7 / 10) * 1 := by
          gcongr
      _ = (2 * Real.pi) ^ (s.re - 1) * (2 * Real.cosh (Real.pi * 7 / 10)) := by ring
  calc
    _ ≤ (2 * Real.pi) ^ (s.re - 1) * (2 * Real.cosh (Real.pi * 7 / 10)) := hstep1
    _ ≤ (2 * Real.pi) ^ (s.re - 1) * ((17 / 10 : ℝ) * Real.sqrt (10 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hconst (Real.rpow_nonneg hp2.le _)
    _ = (17 / 10 : ℝ) * (Real.sqrt 5 * ((2 * Real.pi) ^ (s.re - 1) * Real.sqrt (2 * Real.pi))) := by
        rw [← hsqrt_rel]; ring
    _ = (17 / 10 : ℝ) * (Real.sqrt 5 * (2 * Real.pi) ^ (s.re - 1 / 2)) := by rw [h2pi_pow]
    _ ≤ (17 / 10 : ℝ) * ((|s.im| + 5) ^ (1 / 2 - s.re) * (2 * Real.pi) ^ (s.re - 1 / 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h5_pow (Real.rpow_nonneg hp2.le _)) (by norm_num)
    _ = (17 / 10 : ℝ) * ((|s.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re) := by rw [hrhs_pow]

lemma abs_digamma_re_sub_log_le_of_half {a t : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 3 / 2) (ht : 1 / 2 ≤ t) :
    |(Complex.digamma ((a : ℂ) + t * I)).re - Real.log t| ≤ 23 / (5 * t ^ 2) := by
  let w : ℂ := (a : ℂ) + t * I
  have ha0 : 0 < a := by linarith
  have ht0 : 0 < t := by linarith
  have hre : w.re = a := by simp [w]
  have him : w.im = t := by simp [w]
  have hw : 0 < w.re := by simpa [hre] using ha0
  have hD : 0 < a ^ 2 + t ^ 2 := by positivity
  have hmain := TernaryGoldbach.RSBounds.BacklundZeta23.StirlingVert.digamma_stirling hw
    (by rw [him, abs_of_pos ht0]; linarith)
  rw [him] at hmain
  have hlogre : (Complex.log w).re = Real.log (a ^ 2 + t ^ 2) / 2 := by
    rw [Complex.log_re, show ‖w‖ = Real.sqrt (a ^ 2 + t ^ 2) by
      rw [Complex.norm_eq_sqrt_sq_add_sq, hre, him], Real.log_sqrt hD.le]
  have hinvre : ((1 / 2 : ℂ) / w).re = a / (2 * (a ^ 2 + t ^ 2)) := by
    rw [show (1 / 2 : ℂ) / w = ((1 / 2 : ℝ) : ℂ) * w⁻¹ by push_cast; ring,
      Complex.re_ofReal_mul, Complex.inv_re, Complex.normSq_apply, hre, him]
    field_simp
  have hR : |(Complex.digamma w).re - Real.log (a ^ 2 + t ^ 2) / 2 +
      a / (2 * (a ^ 2 + t ^ 2))| ≤ 3 / t ^ 2 := by
    have h := (Complex.abs_re_le_norm _).trans hmain
    simpa only [Complex.add_re, Complex.sub_re, hlogre, hinvre] using h
  have hlog : 0 ≤ Real.log (a ^ 2 + t ^ 2) / 2 - Real.log t ∧
      Real.log (a ^ 2 + t ^ 2) / 2 - Real.log t ≤ 9 / (8 * t ^ 2) := by
    have he : a ^ 2 + t ^ 2 = t ^ 2 * (1 + a ^ 2 / t ^ 2) := by
      field_simp; ring
    rw [he, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have hl0 : 0 ≤ Real.log (1 + a ^ 2 / t ^ 2) :=
      Real.log_nonneg (le_add_of_nonneg_right (by positivity))
    have hl1 := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + a ^ 2 / t ^ 2)
    have ha2 : a ^ 2 ≤ 9 / 4 := by nlinarith
    have hq : a ^ 2 / t ^ 2 ≤ (9 / 4) / t ^ 2 :=
      div_le_div_of_nonneg_right ha2 (sq_nonneg t)
    ring_nf at hq hl0 hl1 ⊢
    constructor <;> linarith
  have hi : 0 ≤ a / (2 * (a ^ 2 + t ^ 2)) ∧
      a / (2 * (a ^ 2 + t ^ 2)) ≤ 3 / (4 * t ^ 2) := by
    constructor
    · positivity
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (by linarith : 0 ≤ 3 / 2 - a) (sq_nonneg t)]
  rw [abs_le] at hR ⊢
  change -(23 / (5 * t ^ 2)) ≤ (Complex.digamma w).re - Real.log t ∧
    (Complex.digamma w).re - Real.log t ≤ 23 / (5 * t ^ 2)
  have ht2 : 0 < t ^ 2 := by positivity
  ring_nf at hR hlog hi ⊢
  constructor <;> nlinarith [hR.1, hR.2, hlog.1, hlog.2, hi.1, hi.2, sq_nonneg t⁻¹]

lemma norm_Gamma_horizontal_le_of_half {a t : ℝ}
    (ha : 1 ≤ a) (ha' : a ≤ 3 / 2) (ht : 1 / 2 ≤ t) :
    ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
      ‖Complex.Gamma (1 + t * I)‖ * t ^ (a - 1) * Real.exp ((a - 1) * 23 / (5 * t ^ 2)) := by
  let f : ℝ → ℝ := fun x => Real.log ‖Complex.Gamma ((x : ℂ) + t * I)‖ - x * Real.log t
  let f' : ℝ → ℝ := fun x => (Complex.digamma ((x : ℂ) + t * I)).re - Real.log t
  have hd : ∀ x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2), HasDerivWithinAt f (f' x)
      (Set.Icc (1 / 2 : ℝ) (3 / 2)) x := by
    intro x hx
    convert! ((TernaryGoldbach.RSBounds.BacklundGammaModulus.hasDerivAt_log_norm_Gamma (t := t)
      (by linarith [hx.1] : 0 < x)).sub
        ((hasDerivAt_id x).mul_const (Real.log t))).hasDerivWithinAt using 1
    simp [f']
  have hb : ∀ x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2), ‖f' x‖ ≤ 23 / (5 * t ^ 2) := by
    intro x hx
    simpa [f', Real.norm_eq_abs] using abs_digamma_re_sub_log_le_of_half hx.1 hx.2 ht
  have h := (convex_Icc (1 / 2 : ℝ) (3 / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd hb (x := 1) (y := a) (by norm_num) ⟨by linarith, ha'⟩
  have hdist : |a - 1| = a - 1 := abs_of_nonneg (by linarith)
  have hc : 0 ≤ 23 / (5 * t ^ 2) := by positivity
  have h' := h.trans (mul_le_mul_of_nonneg_left
    (show ‖a - 1‖ ≤ a - 1 by simp [Real.norm_eq_abs, hdist]) hc)
  rw [Real.norm_eq_abs] at h'
  have hlog_le : Real.log ‖Complex.Gamma ((a : ℂ) + t * I)‖ -
      Real.log ‖Complex.Gamma (1 + t * I)‖ - (a - 1) * Real.log t ≤
      (a - 1) * 23 / (5 * t ^ 2) := by
    have h2 := (abs_le.mp h').2
    dsimp [f] at h2
    norm_num at h2
    have heq : 23 / (5 * t ^ 2) * (a - 1) = (a - 1) * 23 / (5 * t ^ 2) := by ring
    linarith
  have hGa : 0 < ‖Complex.Gamma ((a : ℂ) + t * I)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
  have hG1 : 0 < ‖Complex.Gamma (1 + t * I)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  have ht0 : 0 < t := by linarith
  have he := Real.exp_le_exp.mpr (show
    Real.log ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
      Real.log ‖Complex.Gamma (1 + t * I)‖ + (a - 1) * Real.log t +
        (a - 1) * 23 / (5 * t ^ 2) by linarith)
  rw [Real.exp_log hGa, Real.exp_add, Real.exp_add, Real.exp_log hG1] at he
  rw [Real.rpow_def_of_pos ht0]
  simpa [mul_comm (a - 1) (Real.log t)] using he

lemma sqrt_cosh_ratio_le_high {t : ℝ} (ht : 7 / 5 ≤ t) :
    Real.sqrt ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t))) ≤ 1.026 := by
  have hpi : 4.2 ≤ Real.pi * t := by nlinarith [Real.pi_gt_three]
  have h42 : Real.exp (-Real.pi * t) ≤ Real.exp (-4.2) := by
    rw [neg_mul]
    exact Real.exp_le_exp.mpr (by linarith)
  have hexp42 : Real.exp (-4.2 : ℝ) ≤ 1 / 40 := by
    have hsum := Real.sum_le_exp_of_nonneg (x := (4.2 : ℝ)) (by norm_num) 6
    norm_num [Finset.sum_range_succ] at hsum
    rw [show (-4.2 : ℝ) = -(4.2 : ℝ) by norm_num, Real.exp_neg]
    exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
  have he0 : 0 ≤ Real.exp (-Real.pi * t) := (Real.exp_pos _).le
  have he1 : Real.exp (-Real.pi * t) ≤ 1 / 40 := h42.trans hexp42
  have hquot : (1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t)) ≤ (41 / 39 : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  exact (Real.sqrt_le_sqrt hquot).trans ((Real.sqrt_le_left (by norm_num)).mpr (by norm_num))

lemma norm_gammaFactor_ratio_le_high_pos {q : ℕ} (χ : DirichletCharacter ℂ q)
    {σ t : ℝ} (hσ1 : -(7 / 20 : ℝ) ≤ σ) (hσ2 : σ ≤ 0) (ht : 7 / 5 ≤ t) :
    ‖DirichletCharacter.gammaFactor χ⁻¹ (1 - ((σ : ℂ) + t * I)) /
        DirichletCharacter.gammaFactor χ ((σ : ℂ) + t * I)‖ ≤
      (t / (2 * Real.pi)) ^ (1 / 2 - σ) *
        Real.exp ((-σ) * 23 / (5 * t ^ 2)) * 1.026 := by
  classical
  let s : ℂ := (σ : ℂ) + t * I
  have ht0 : 0 < t := by linarith
  have hs_im : s.im ≠ 0 := by simp [s, ht0.ne']
  have hs_re : s.re = σ := by simp [s]
  rw [norm_gammaFactor_ratio_eq χ hs_im, hs_re]
  have h1s : 1 - s = conj (((1 - σ : ℝ) : ℂ) + t * I) := by
    apply Complex.ext <;> simp [s]
  have hG : ‖Complex.Gamma (1 - s)‖ ≤
      ‖Complex.Gamma (1 + (t : ℂ) * I)‖ * t ^ (-σ) *
        Real.exp ((-σ) * 23 / (5 * t ^ 2)) := by
    rw [h1s, Complex.Gamma_conj, norm_conj]
    convert norm_Gamma_horizontal_le_of_half (a := 1 - σ) (t := t)
      (by linarith) (by linarith) (by linarith) using 2 <;> ring
  have htrig : (if χ.Even then ‖Complex.sin ((Real.pi : ℂ) * s / 2)‖
      else ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖) ≤ Real.cosh (Real.pi * t / 2) := by
    have him : ((Real.pi : ℂ) * s / 2).im = Real.pi * t / 2 := by
      simp [s, Complex.div_ofNat_im, Complex.mul_im]
    split_ifs
    · exact (norm_sin_le_cosh_im _).trans_eq (by rw [him])
    · exact (TernaryGoldbach.RSBounds.BacklundFunctionalMultiplier.norm_cos_le_cosh_im _).trans_eq
        (by rw [him])
  have hp : 0 < 2 * Real.pi := by positivity
  have h2pi : (2 * Real.pi) ^ (σ - 1) * 2 = (2 * Real.pi) ^ σ / Real.pi := by
    rw [Real.rpow_sub hp, Real.rpow_one]; field_simp
  have hcosh := TernaryGoldbach.RSBounds.BacklundFunctionalMultiplier.gamma_cosh_ratio_eq ht0
  have hpow := TernaryGoldbach.RSBounds.BacklundFunctionalMultiplier.power_normalization ht0 σ
  have hhyp := sqrt_cosh_ratio_le_high ht
  calc
    (2 * Real.pi) ^ (σ - 1) * 2 *
        (if χ.Even then ‖Complex.sin ((Real.pi : ℂ) * s / 2)‖
          else ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖) *
        ‖Complex.Gamma (1 - s)‖
      ≤ ((2 * Real.pi) ^ σ / Real.pi) * Real.cosh (Real.pi * t / 2) *
          (‖Complex.Gamma (1 + (t : ℂ) * I)‖ * t ^ (-σ) *
            Real.exp ((-σ) * 23 / (5 * t ^ 2))) := by
        rw [← h2pi]; gcongr
    _ = ((2 * Real.pi) ^ σ * t ^ (-σ)) *
          (‖Complex.Gamma (1 + (t : ℂ) * I)‖ * Real.cosh (Real.pi * t / 2) / Real.pi) *
          Real.exp ((-σ) * 23 / (5 * t ^ 2)) := by ring
    _ = ((2 * Real.pi) ^ σ * t ^ (-σ) * Real.sqrt (t / (2 * Real.pi))) *
          Real.sqrt ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t))) *
          Real.exp ((-σ) * 23 / (5 * t ^ 2)) := by rw [hcosh]; ring
    _ ≤ (t / (2 * Real.pi)) ^ (1 / 2 - σ) * 1.026 * Real.exp ((-σ) * 23 / (5 * t ^ 2)) := by
        rw [hpow]; gcongr
    _ = (t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.exp ((-σ) * 23 / (5 * t ^ 2)) * 1.026 := by
        ring

lemma exp_strip_const_le : Real.exp (23 / 49 : ℝ) * 1.026 ≤ 17 / 10 := by
  have h := Real.exp_bound' (x := (23 / 49 : ℝ)) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

lemma exp_left_const_le : Real.exp (161 / 196 : ℝ) * 1.026 ≤ 5 / 2 := by
  have h := Real.exp_bound' (x := (161 / 196 : ℝ)) (by norm_num) (by norm_num) (n := 10) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

private lemma norm_gammaFactor_ratio_conj_symm {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs_im : s.im ≠ 0) :
    ‖DirichletCharacter.gammaFactor χ⁻¹ (1 - conj s) /
        DirichletCharacter.gammaFactor χ (conj s)‖ =
      ‖DirichletCharacter.gammaFactor χ⁻¹ (1 - s) /
        DirichletCharacter.gammaFactor χ s‖ := by
  have him_conj : (conj s).im ≠ 0 := by simp [hs_im]
  rw [norm_gammaFactor_ratio_eq χ hs_im, norm_gammaFactor_ratio_eq χ him_conj]
  simp only [Complex.conj_re]
  have hc_arg : (Real.pi : ℂ) * conj s / 2 = conj ((Real.pi : ℂ) * s / 2) := by
    simp [map_div₀, map_mul, Complex.conj_ofReal, map_ofNat]
  have hsin : ‖Complex.sin ((Real.pi : ℂ) * conj s / 2)‖ =
      ‖Complex.sin ((Real.pi : ℂ) * s / 2)‖ := by
    rw [hc_arg, Complex.sin_conj, Complex.norm_conj]
  have hcos : ‖Complex.cos ((Real.pi : ℂ) * conj s / 2)‖ =
      ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖ := by
    rw [hc_arg, Complex.cos_conj, Complex.norm_conj]
  have hG : ‖Complex.Gamma (1 - conj s)‖ = ‖Complex.Gamma (1 - s)‖ := by
    rw [show 1 - conj s = conj (1 - s) by simp, Complex.Gamma_conj, Complex.norm_conj]
  rw [hsin, hcos, hG]

theorem norm_gammaFactor_ratio_strip_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hσ : s.re = -(1 / 5 : ℝ)) (hs_im : s.im ≠ 0) :
    ‖DirichletCharacter.gammaFactor χ⁻¹ (1 - s) / DirichletCharacter.gammaFactor χ s‖ ≤
      (17 / 10 : ℝ) * ((|s.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re) := by
  by_cases ht_low : |s.im| ≤ 7 / 5
  · exact norm_gammaFactor_ratio_le_low χ hs_im (by linarith) (by linarith) ht_low
  · push Not at ht_low
    have habs_im : 7 / 5 ≤ |s.im| := ht_low.le
    have hs_eq : s = (s.re : ℂ) + s.im * I := (Complex.re_add_im s).symm
    have hpos_im : ‖DirichletCharacter.gammaFactor χ⁻¹ (1 - s) / DirichletCharacter.gammaFactor χ s‖ =
        ‖DirichletCharacter.gammaFactor χ⁻¹ (1 - ((s.re : ℂ) + |s.im| * I)) /
          DirichletCharacter.gammaFactor χ ((s.re : ℂ) + |s.im| * I)‖ := by
      by_cases him0 : 0 ≤ s.im
      · rw [abs_of_nonneg him0, ← hs_eq]
      · push Not at him0
        have hconj_s : ((s.re : ℂ) + |s.im| * I) = conj s := by
          rw [abs_of_neg him0]
          apply Complex.ext <;> simp
        rw [hconj_s, norm_gammaFactor_ratio_conj_symm χ hs_im]
    rw [hpos_im]
    have hbd := norm_gammaFactor_ratio_le_high_pos χ
      (σ := s.re) (t := |s.im|) (by linarith) (by linarith) habs_im
    have hexp_le : Real.exp ((-s.re) * 23 / (5 * |s.im| ^ 2)) ≤ Real.exp (23 / 49 : ℝ) := by
      apply Real.exp_le_exp.mpr
      rw [hσ]
      have hsq : (49 / 25 : ℝ) ≤ |s.im| ^ 2 := by nlinarith
      rw [show -(-(1 / 5 : ℝ)) * 23 / (5 * |s.im| ^ 2) = (23 / 25) / |s.im| ^ 2 by ring]
      exact (div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq).trans_eq (by norm_num)
    have hpow_le : (|s.im| / (2 * Real.pi)) ^ (1 / 2 - s.re) ≤
        ((|s.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re) :=
      Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_right (by linarith) (by positivity)) (by linarith)
    calc
      ‖DirichletCharacter.gammaFactor χ⁻¹ (1 - ((s.re : ℂ) + |s.im| * I)) /
          DirichletCharacter.gammaFactor χ ((s.re : ℂ) + |s.im| * I)‖
        ≤ (|s.im| / (2 * Real.pi)) ^ (1 / 2 - s.re) *
            Real.exp ((-s.re) * 23 / (5 * |s.im| ^ 2)) * 1.026 := hbd
      _ ≤ ((|s.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re) *
            (Real.exp (23 / 49 : ℝ) * 1.026) := by
          have := mul_le_mul hpow_le hexp_le (by positivity) (by positivity)
          nlinarith
      _ ≤ (17 / 10 : ℝ) * ((|s.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re) := by
          have := mul_le_mul_of_nonneg_left exp_strip_const_le
            (by positivity : 0 ≤ ((|s.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re))
          linarith

theorem norm_gammaFactor_ratio_left_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hσ1 : -(7 / 20 : ℝ) ≤ s.re) (hσ2 : s.re ≤ -(1 / 5 : ℝ)) (hs_im : s.im ≠ 0) :
    ‖DirichletCharacter.gammaFactor χ⁻¹ (1 - s) / DirichletCharacter.gammaFactor χ s‖ ≤
      (5 / 2 : ℝ) * ((|s.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re) := by
  by_cases ht_low : |s.im| ≤ 7 / 5
  · exact (norm_gammaFactor_ratio_le_low χ hs_im (by linarith) (by linarith) ht_low).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  · push Not at ht_low
    have habs_im : 7 / 5 ≤ |s.im| := ht_low.le
    have hs_eq : s = (s.re : ℂ) + s.im * I := (Complex.re_add_im s).symm
    have hpos_im : ‖DirichletCharacter.gammaFactor χ⁻¹ (1 - s) / DirichletCharacter.gammaFactor χ s‖ =
        ‖DirichletCharacter.gammaFactor χ⁻¹ (1 - ((s.re : ℂ) + |s.im| * I)) /
          DirichletCharacter.gammaFactor χ ((s.re : ℂ) + |s.im| * I)‖ := by
      by_cases him0 : 0 ≤ s.im
      · rw [abs_of_nonneg him0, ← hs_eq]
      · push Not at him0
        have hconj_s : ((s.re : ℂ) + |s.im| * I) = conj s := by
          rw [abs_of_neg him0]
          apply Complex.ext <;> simp
        rw [hconj_s, norm_gammaFactor_ratio_conj_symm χ hs_im]
    rw [hpos_im]
    have hbd := norm_gammaFactor_ratio_le_high_pos χ
      (σ := s.re) (t := |s.im|) hσ1 (by linarith) habs_im
    have hexp_le : Real.exp ((-s.re) * 23 / (5 * |s.im| ^ 2)) ≤ Real.exp (161 / 196 : ℝ) := by
      apply Real.exp_le_exp.mpr
      have hns : (-s.re) * 23 ≤ (7 / 20 : ℝ) * 23 := by linarith
      have hsq : 5 * (49 / 25 : ℝ) ≤ 5 * |s.im| ^ 2 := by nlinarith
      exact (div_le_div₀ (by norm_num) hns (by positivity) hsq).trans_eq (by norm_num)
    have hpow_le : (|s.im| / (2 * Real.pi)) ^ (1 / 2 - s.re) ≤
        ((|s.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re) :=
      Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_right (by linarith) (by positivity)) (by linarith)
    calc
      ‖DirichletCharacter.gammaFactor χ⁻¹ (1 - ((s.re : ℂ) + |s.im| * I)) /
          DirichletCharacter.gammaFactor χ ((s.re : ℂ) + |s.im| * I)‖
        ≤ (|s.im| / (2 * Real.pi)) ^ (1 / 2 - s.re) *
            Real.exp ((-s.re) * 23 / (5 * |s.im| ^ 2)) * 1.026 := hbd
      _ ≤ ((|s.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re) *
            (Real.exp (161 / 196 : ℝ) * 1.026) := by
          have := mul_le_mul hpow_le hexp_le (by positivity) (by positivity)
          nlinarith
      _ ≤ (5 / 2 : ℝ) * ((|s.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re) := by
          have := mul_le_mul_of_nonneg_left exp_left_const_le
            (by positivity : 0 ≤ ((|s.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re))
          linarith

lemma norm_mellin_strip_bounded {F : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (ha : MellinConvergent F (a : ℂ)) (hb : MellinConvergent F (b : ℂ)) :
    ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → MellinConvergent F s → ‖mellin F s‖ ≤ C := by
  have h1 : IntegrableOn (fun x : ℝ => ‖(x : ℂ) ^ ((a : ℂ) - 1) • F x‖) (Set.Ioc 0 1) :=
    (ha.mono_set Set.Ioc_subset_Ioi_self).norm
  have hI1 : IntegrableOn (fun x : ℝ => ‖(x : ℂ) ^ ((b : ℂ) - 1) • F x‖) (Set.Ioi 1) :=
    (hb.mono_set (Set.Ioi_subset_Ioi zero_le_one)).norm
  refine ⟨(∫ x in Set.Ioc (0 : ℝ) 1, ‖(x : ℂ) ^ ((a : ℂ) - 1) • F x‖) +
    (∫ x in Set.Ioi (1 : ℝ), ‖(x : ℂ) ^ ((b : ℂ) - 1) • F x‖), ?_⟩
  intro s hsa hsb hs_conv
  let g : ℝ → ℝ := fun x =>
    if x ≤ 1 then ‖(x : ℂ) ^ ((a : ℂ) - 1) • F x‖ else ‖(x : ℂ) ^ ((b : ℂ) - 1) • F x‖
  have hmaj : ∀ x ∈ Set.Ioi (0 : ℝ), ‖(x : ℂ) ^ (s - 1) • F x‖ ≤ g x := by
    intro x hx
    dsimp [g]
    simp only [smul_eq_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
      Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    split_ifs with hx1
    · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith)
    · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hpart : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 :=
    (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi 1) := Set.Ioc_disjoint_Ioi le_rfl
  have hu1 : IntegrableOn g (Set.Ioc 0 1) :=
    h1.congr_fun (fun x hx => (ite_eq_left_iff.mpr fun h => (h hx.2).elim).symm) measurableSet_Ioc
  have hu2 : IntegrableOn g (Set.Ioi 1) :=
    hI1.congr_fun (fun x hx => (ite_eq_right_iff.mpr fun h => (not_lt_of_ge h hx).elim).symm)
      measurableSet_Ioi
  have hint_piece : IntegrableOn g (Set.Ioi 0) := by
    rw [hpart]
    exact hu1.union hu2
  have hint_eq : ∫ x in Set.Ioi (0 : ℝ), g x =
      (∫ x in Set.Ioc (0 : ℝ) 1, ‖(x : ℂ) ^ ((a : ℂ) - 1) • F x‖) +
      (∫ x in Set.Ioi (1 : ℝ), ‖(x : ℂ) ^ ((b : ℂ) - 1) • F x‖) := by
    rw [hpart, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hu1 hu2]
    congr 1
    · exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx =>
        ite_eq_left_iff.mpr fun h => (h hx.2).elim
    · exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx =>
        ite_eq_right_iff.mpr fun h => (not_lt_of_ge h hx).elim
  unfold mellin
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  exact (MeasureTheory.setIntegral_mono_on hs_conv.norm hint_piece measurableSet_Ioi hmaj).trans_eq
    hint_eq

lemma norm_completedHurwitzZetaEven₀_strip_bounded (a : UnitAddCircle)
    {σ₁ σ₂ : ℝ} (hσ : σ₁ ≤ σ₂) :
    ∃ C : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖HurwitzZeta.completedHurwitzZetaEven₀ a s‖ ≤ C := by
  have h1 : σ₁ / 2 ≤ σ₂ / 2 := by linarith
  have ha : MellinConvergent (HurwitzZeta.hurwitzEvenFEPair a).f_modif ((σ₁ / 2 : ℝ) : ℂ) :=
    ((HurwitzZeta.hurwitzEvenFEPair a).isStrongFEPair_toStrongFEPair.hasMellin _).1
  have hb : MellinConvergent (HurwitzZeta.hurwitzEvenFEPair a).f_modif ((σ₂ / 2 : ℝ) : ℂ) :=
    ((HurwitzZeta.hurwitzEvenFEPair a).isStrongFEPair_toStrongFEPair.hasMellin _).1
  obtain ⟨C, hC⟩ := norm_mellin_strip_bounded h1 ha hb
  refine ⟨C / 2, fun s hs1 hs2 => ?_⟩
  rw [HurwitzZeta.completedHurwitzZetaEven₀, WeakFEPair.Λ₀, norm_div, Complex.norm_ofNat]
  have hs_conv : MellinConvergent (HurwitzZeta.hurwitzEvenFEPair a).f_modif (s / 2) :=
    ((HurwitzZeta.hurwitzEvenFEPair a).isStrongFEPair_toStrongFEPair.hasMellin _).1
  exact div_le_div_of_nonneg_right (hC (s / 2) (by simp; linarith) (by simp; linarith) hs_conv)
    two_pos.le

lemma norm_completedHurwitzZetaOdd_strip_bounded (a : UnitAddCircle)
    {σ₁ σ₂ : ℝ} (hσ : σ₁ ≤ σ₂) :
    ∃ C : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖HurwitzZeta.completedHurwitzZetaOdd a s‖ ≤ C := by
  have h1 : (σ₁ + 1) / 2 ≤ (σ₂ + 1) / 2 := by linarith
  have ha : MellinConvergent (HurwitzZeta.hurwitzOddFEPair a).f (((σ₁ + 1) / 2 : ℝ) : ℂ) :=
    ((HurwitzZeta.isStrong_hurwitzOddFEPair a).hasMellin _).1
  have hb : MellinConvergent (HurwitzZeta.hurwitzOddFEPair a).f (((σ₂ + 1) / 2 : ℝ) : ℂ) :=
    ((HurwitzZeta.isStrong_hurwitzOddFEPair a).hasMellin _).1
  obtain ⟨C, hC⟩ := norm_mellin_strip_bounded h1 ha hb
  refine ⟨C / 2, fun s hs1 hs2 => ?_⟩
  rw [HurwitzZeta.completedHurwitzZetaOdd,
    (HurwitzZeta.isStrong_hurwitzOddFEPair a).Λ_eq, norm_div, Complex.norm_ofNat]
  have hs_conv : MellinConvergent (HurwitzZeta.hurwitzOddFEPair a).f ((s + 1) / 2) :=
    ((HurwitzZeta.isStrong_hurwitzOddFEPair a).hasMellin _).1
  exact div_le_div_of_nonneg_right
    (hC ((s + 1) / 2) (by simp; linarith) (by simp; linarith) hs_conv) two_pos.le

lemma norm_completedLFunction_strip_bounded {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {σ₁ σ₂ : ℝ} (hσ : σ₁ ≤ σ₂) :
    ∃ C : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → 1 ≤ |s.im| →
      ‖DirichletCharacter.completedLFunction χ s‖ ≤ C := by
  have heven : ∀ j : ZMod q, ∃ C : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖ ≤ C :=
    fun j => norm_completedHurwitzZetaEven₀_strip_bounded _ hσ
  have hodd : ∀ j : ZMod q, ∃ C : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖ ≤ C :=
    fun j => norm_completedHurwitzZetaOdd_strip_bounded _ hσ
  choose Ce hCe using heven
  choose Co hCo using hodd
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  let Q : ℝ := max ((q : ℝ) ^ (-σ₁)) ((q : ℝ) ^ (-σ₂))
  let Csum : ℝ := Q * (∑ j : ZMod q, max 0 (Ce j)) + Q * (∑ j : ZMod q, max 0 (Co j)) + Q + Q * q
  refine ⟨Csum, fun s hs1 hs2 him => ?_⟩
  have hq_norm : ‖(q : ℂ) ^ (-s)‖ ≤ Q := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
    simp only [Complex.neg_re]
    have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
    exact le_max_of_le_left (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith))
  have h1s : 1 ≤ ‖(1 : ℂ) - s‖ := by
    have h0 := Complex.abs_im_le_norm ((1 : ℂ) - s)
    have him1 : |(1 - s).im| = |s.im| := by simp [abs_neg]
    linarith
  have hs_n : 1 ≤ ‖s‖ := him.trans (Complex.abs_im_le_norm s)
  change ‖ZMod.completedLFunction (χ : ZMod q → ℂ) s‖ ≤ Csum
  rw [ZMod.completedLFunction_eq (χ : ZMod q → ℂ) s]
  have hn0 : ‖ZMod.completedLFunction₀ (χ : ZMod q → ℂ) s‖ ≤
      Q * (∑ j : ZMod q, max 0 (Ce j)) + Q * (∑ j : ZMod q, max 0 (Co j)) := by
    rw [ZMod.completedLFunction₀]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      refine mul_le_mul hq_norm ?_ (norm_nonneg _) (by positivity)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one j)).trans
        ((hCe j s hs1 hs2).trans (le_max_right 0 _))
    · rw [norm_mul]
      refine mul_le_mul hq_norm ?_ (norm_nonneg _) (by positivity)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one j)).trans
        ((hCo j s hs1 hs2).trans (le_max_right 0 _))
  have ht1 : ‖(q : ℂ) ^ (-s) * χ 0 / s‖ ≤ Q := by
    rw [norm_div, norm_mul]
    have hnum : ‖(q : ℂ) ^ (-s)‖ * ‖χ 0‖ ≤ Q * 1 :=
      mul_le_mul hq_norm (χ.norm_le_one 0) (norm_nonneg _) (by positivity)
    exact (div_le_div₀ (by positivity) hnum (by norm_num) hs_n).trans_eq (by ring)
  have ht2 : ‖(q : ℂ) ^ (-s) * (∑ j : ZMod q, χ j) / (1 - s)‖ ≤ Q * q := by
    rw [norm_div, norm_mul]
    have hsum : ‖∑ j : ZMod q, χ j‖ ≤ (q : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ j : ZMod q, ‖χ j‖ ≤ ∑ _j : ZMod q, (1 : ℝ) := Finset.sum_le_sum fun j _ => χ.norm_le_one j
        _ = (q : ℝ) := by simp [ZMod.card]
    have hnum : ‖(q : ℂ) ^ (-s)‖ * ‖∑ j : ZMod q, χ j‖ ≤ Q * q :=
      mul_le_mul hq_norm hsum (norm_nonneg _) (by positivity)
    exact (div_le_div₀ (by positivity) hnum (by norm_num) h1s).trans_eq (by ring)
  have htri : ‖ZMod.completedLFunction₀ (χ : ZMod q → ℂ) s - (q : ℂ) ^ (-s) * χ 0 / s -
      (q : ℂ) ^ (-s) * (∑ j : ZMod q, χ j) / (1 - s)‖ ≤
      ‖ZMod.completedLFunction₀ (χ : ZMod q → ℂ) s‖ + ‖(q : ℂ) ^ (-s) * χ 0 / s‖ +
      ‖(q : ℂ) ^ (-s) * (∑ j : ZMod q, χ j) / (1 - s)‖ := by
    have s1 := norm_sub_le (ZMod.completedLFunction₀ (χ : ZMod q → ℂ) s - (q : ℂ) ^ (-s) * χ 0 / s)
      ((q : ℂ) ^ (-s) * (∑ j : ZMod q, χ j) / (1 - s))
    have s2 := norm_sub_le (ZMod.completedLFunction₀ (χ : ZMod q → ℂ) s) ((q : ℂ) ^ (-s) * χ 0 / s)
    linarith
  linarith [htri, hn0, ht1, ht2]

lemma norm_Gammaℝ_inv_strip_le {σ₁ σ₂ : ℝ} (hσ1 : -(1 : ℝ) ≤ σ₁) (hσ2 : σ₂ ≤ 3) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → 1 ≤ |s.im| →
      ‖(Complex.Gammaℝ s)⁻¹‖ ≤ C * Real.exp (A * |s.im|) := by
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hGbound : ∀ w : ℂ, 1 / 4 ≤ w.re → w.re ≤ 5 / 2 → ‖Complex.Gamma w‖ ≤
      Real.Gamma (1 / 4) + Real.Gamma (5 / 2) := by
    intro w hw1 hw2
    have hw0 : 0 < w.re := by linarith
    rw [Complex.Gamma_eq_integral hw0]
    have hI1 : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (1 / 4 - 1 : ℝ)) (Set.Ioi 0) :=
      IntegrableOn.congr_fun
        (Complex.GammaIntegral_convergent (s := (1 / 4 : ℂ)) (by norm_num)).norm
        (fun x hx => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
            Complex.norm_cpow_eq_rpow_re_of_pos hx]
          simp) measurableSet_Ioi
    have hI2 : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (5 / 2 - 1 : ℝ)) (Set.Ioi 0) :=
      IntegrableOn.congr_fun
        (Complex.GammaIntegral_convergent (s := (5 / 2 : ℂ)) (by norm_num)).norm
        (fun x hx => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
            Complex.norm_cpow_eq_rpow_re_of_pos hx]
          simp) measurableSet_Ioi
    have hi : IntegrableOn (fun x : ℝ => Real.exp (-x) * (x ^ (1 / 4 - 1 : ℝ) + x ^ (5 / 2 - 1 : ℝ)))
        (Set.Ioi 0) :=
      (hI1.add hI2).congr_fun (fun x _ => by simp only [Pi.add_apply, mul_add]) measurableSet_Ioi
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
    refine (MeasureTheory.setIntegral_mono_on (Complex.GammaIntegral_convergent hw0).norm hi
      measurableSet_Ioi fun x hx => ?_).trans_eq ?_
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      by_cases hx1 : x ≤ 1
      · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith)).trans
          (le_add_of_nonneg_right (Real.rpow_nonneg hx.le _))
      · exact (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)).trans
          (le_add_of_nonneg_left (Real.rpow_nonneg hx.le _))
    · have hmul : (fun x : ℝ => Real.exp (-x) * (x ^ (1 / 4 - 1 : ℝ) + x ^ (5 / 2 - 1 : ℝ))) =
          (fun x : ℝ => Real.exp (-x) * x ^ (1 / 4 - 1 : ℝ) + Real.exp (-x) * x ^ (5 / 2 - 1 : ℝ)) := by
        ext x; ring
      rw [hmul, MeasureTheory.integral_add hI1 hI2,
        ← Real.Gamma_eq_integral (by norm_num : (0 : ℝ) < 1 / 4),
        ← Real.Gamma_eq_integral (by norm_num : (0 : ℝ) < 5 / 2)]
  let M_G : ℝ := max 0 (Real.Gamma (1 / 4) + Real.Gamma (5 / 2))
  let P_bd : ℝ := max (Real.pi ^ (σ₂ / 2)) (Real.pi ^ (σ₁ / 2))
  refine ⟨P_bd * (3 * M_G / Real.pi), Real.pi / 2, by positivity, by positivity, ?_⟩
  intro s hs1 hs2 him
  rw [Complex.Gammaℝ_def, mul_inv]
  have hpi_norm : ‖((Real.pi : ℂ) ^ (-s / 2))⁻¹‖ ≤ P_bd := by
    rw [← Complex.cpow_neg, Complex.norm_cpow_eq_rpow_re_of_pos hpi0]
    simp only [Complex.neg_re, Complex.div_ofNat_re]
    exact le_max_of_le_left (Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
      (by linarith))
  have hinv_gamma : ‖(Complex.Gamma (s / 2))⁻¹‖ ≤ 3 * M_G / Real.pi * Real.exp (Real.pi / 2 * |s.im|) := by
    have hsin_ne : Complex.sin ((Real.pi : ℂ) * (s / 2)) ≠ 0 := by
      intro h
      rw [Complex.sin_eq_zero_iff] at h
      rcases h with ⟨k, hk⟩
      have h0 := congrArg Complex.im hk
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat_im,
        zero_mul, add_zero, Complex.intCast_im, Complex.intCast_re] at h0
      have : s.im = 0 := by nlinarith [Real.pi_pos]
      rw [this, abs_zero] at him; linarith
    have h1s : Complex.Gamma (1 - s / 2) ≠ 0 := by
      intro h0
      have hr := Complex.Gamma_mul_Gamma_one_sub (s / 2)
      rw [h0, mul_zero] at hr
      exact div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hsin_ne hr.symm
    have hinv_eq : (Complex.Gamma (s / 2))⁻¹ =
        Complex.Gamma (1 - s / 2) * Complex.sin ((Real.pi : ℂ) * (s / 2)) / (Real.pi : ℂ) := by
      have hr := Complex.Gamma_mul_Gamma_one_sub (s / 2)
      rw [eq_div_of_mul_eq h1s hr]
      field_simp
    have hG_norm : ‖Complex.Gamma (1 - s / 2)‖ ≤ 3 * M_G := by
      by_cases hre : 1 / 4 ≤ (1 - s / 2).re
      · exact (hGbound _ hre (by simp; linarith)).trans
          (le_trans (le_max_right 0 _) (by linarith [le_max_left 0 (Real.Gamma (1/4) + Real.Gamma (5/2))]))
      · have hre_gt : 1 / 4 ≤ (1 - s / 2 + 1).re := by
          simp at hre ⊢; linarith
        have hre_le : (1 - s / 2 + 1).re ≤ 5 / 2 := by simp; linarith
        have hnz : 1 - s / 2 ≠ 0 := fun h0 => by
          have := congrArg Complex.im h0
          simp only [Complex.sub_im, Complex.one_im, Complex.div_ofNat_im, Complex.zero_im, zero_sub,
            neg_eq_zero] at this
          have : s.im = 0 := by linarith
          rw [this, abs_zero] at him; linarith
        have hadd := Complex.Gamma_add_one (1 - s / 2) hnz
        rw [show Complex.Gamma (1 - s / 2) = Complex.Gamma (1 - s / 2 + 1) / (1 - s / 2) from
          (eq_div_iff hnz).mpr (by rw [mul_comm]; exact hadd.symm), norm_div]
        have hden : 1 / 2 ≤ ‖1 - s / 2‖ := by
          have h0 := Complex.abs_im_le_norm (1 - s / 2)
          simp only [Complex.sub_im, Complex.one_im, Complex.div_ofNat_im, zero_sub, abs_neg,
            abs_div, Nat.abs_ofNat] at h0
          linarith
        have hG1 := (hGbound _ hre_gt hre_le).trans (le_max_right 0 _)
        have hM_nonneg : 0 ≤ M_G := le_max_left 0 _
        have hdiv : ‖Complex.Gamma (1 - s / 2 + 1)‖ / ‖1 - s / 2‖ ≤ M_G / (1 / 2) :=
          div_le_div₀ hM_nonneg hG1 (by norm_num) hden
        linarith
    have hsin_norm : ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ ≤ Real.exp (Real.pi / 2 * |s.im|) := by
      have h1 := norm_sin_le_cosh_im ((Real.pi : ℂ) * (s / 2))
      have him_eq : ((Real.pi : ℂ) * (s / 2)).im = Real.pi * s.im / 2 := by
        simp [Complex.mul_im, Complex.div_ofNat_im]; ring
      rw [him_eq, ← Real.cosh_abs] at h1
      have h2 : Real.cosh |Real.pi * s.im / 2| ≤ Real.exp |Real.pi * s.im / 2| := by
        rw [Real.cosh_eq]
        have hneg : Real.exp (-|Real.pi * s.im / 2|) ≤ Real.exp |Real.pi * s.im / 2| :=
          Real.exp_le_exp.mpr (by linarith [abs_nonneg (Real.pi * s.im / 2)])
        linarith
      refine h1.trans (h2.trans_eq ?_)
      congr 1
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring
    rw [hinv_eq, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    calc
      ‖Complex.Gamma (1 - s / 2)‖ * ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ / Real.pi
        ≤ (3 * M_G) * Real.exp (Real.pi / 2 * |s.im|) / Real.pi := by gcongr
      _ = 3 * M_G / Real.pi * Real.exp (Real.pi / 2 * |s.im|) := by ring
  rw [norm_mul]
  exact (mul_le_mul hpi_norm hinv_gamma (norm_nonneg _) (by positivity)).trans_eq (by ring)

private lemma eventually_mul_exp_le_exp_exp (C A : ℝ) (hC : 0 ≤ C) (_hA : 0 ≤ A) :
    ∀ᶠ t : ℝ in atTop, 1 ≤ t ∧ C * Real.exp (A * t) ≤ Real.exp (Real.exp t) := by
  let B : ℝ := max 0 (Real.log (C + 1))
  let M : ℝ := max 1 (4 * (B + A))
  filter_upwards [Filter.eventually_ge_atTop M] with t ht
  have ht1 : 1 ≤ t := (le_max_left 1 _).trans ht
  have ht_pos : 0 ≤ t := by linarith
  have hM : 4 * (B + A) ≤ t := (le_max_right 1 _).trans ht
  have hquad : B + A * t ≤ t ^ 2 / 2 := by
    have : B * 1 ≤ B * t := mul_le_mul_of_nonneg_left ht1 (le_max_left 0 _)
    nlinarith [sq_nonneg t]
  have hexp_t : t ^ 2 / 2 ≤ Real.exp t := by
    have hp := Real.pow_div_factorial_le_exp t ht_pos 2
    norm_num at hp
    exact hp
  refine ⟨ht1, ?_⟩
  by_cases hC0 : C = 0
  · simp [hC0, (Real.exp_pos _).le]
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    have hlogC : C ≤ Real.exp B := by
      rw [← Real.log_le_iff_le_exp hCpos]
      exact (Real.log_le_log hCpos (by linarith)).trans (le_max_right _ _)
    calc C * Real.exp (A * t)
        ≤ Real.exp B * Real.exp (A * t) := by gcongr
      _ = Real.exp (B + A * t) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (t ^ 2 / 2) := Real.exp_le_exp.mpr hquad
      _ ≤ Real.exp (Real.exp t) := Real.exp_le_exp.mpr hexp_t

private lemma isBigO_strip_of_mul_exp {f : ℂ → ℂ} {a b M A : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hf : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| → ‖f z‖ ≤ M * Real.exp (A * |z.im|)) :
    f =O[comap ((abs : ℝ → ℝ) ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
      fun z : ℂ => Real.exp (1 * Real.exp (1 * |z.im|)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  rw [Filter.eventually_inf_principal, Filter.eventually_comap]
  refine (eventually_mul_exp_le_exp_exp M A hM hA).mono fun t ⟨ht1, hexp_t⟩ z hzt hz_strip => ?_
  rw [Function.comp_apply] at hzt
  have him1 : 1 ≤ |z.im| := by rw [hzt]; exact ht1
  have hexp : M * Real.exp (A * |z.im|) ≤ Real.exp (Real.exp |z.im|) := by
    rw [hzt]; exact hexp_t
  simp only [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact (hf z hz_strip.1.le hz_strip.2.le him1).trans hexp

lemma LFunction_isBigO_strip {q : ℕ} [NeZero q] (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) :
    DirichletCharacter.LFunction χ =O[comap ((abs : ℝ → ℝ) ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Set.Ioo (-(1 / 5 : ℝ)) (6 / 5))]
      fun z : ℂ => Real.exp (1 * Real.exp (1 * |z.im|)) := by
  classical
  obtain ⟨C₁, hC₁⟩ := norm_completedLFunction_strip_bounded χ (show -(1 / 5 : ℝ) ≤ 6 / 5 by norm_num)
  obtain ⟨C₂, A₂, hC₂, hA₂, hG⟩ := norm_Gammaℝ_inv_strip_le (σ₁ := -(1 / 5)) (σ₂ := 2 + 1 / 5)
    (by norm_num) (by norm_num)
  refine isBigO_strip_of_mul_exp (mul_nonneg (le_max_left 0 C₁) hC₂) hA₂ fun z hz1 hz2 him1 => ?_
  have hq1 : q ≠ 1 := by omega
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (.inr hq1), norm_div, div_eq_mul_inv,
    ← norm_inv]
  have hc1 := (hC₁ z hz1 hz2 him1).trans (le_max_right 0 C₁)
  have hg1 : ‖(DirichletCharacter.gammaFactor χ z)⁻¹‖ ≤ C₂ * Real.exp (A₂ * |z.im|) := by
    rw [DirichletCharacter.gammaFactor]
    split_ifs
    · exact hG z (by linarith) (by linarith) him1
    · have hg_add := hG (z + 1) (by simp; linarith) (by simp; linarith) (by simpa using him1)
      simpa using hg_add
  calc
    ‖DirichletCharacter.completedLFunction χ z‖ * ‖(DirichletCharacter.gammaFactor χ z)⁻¹‖
      ≤ max 0 C₁ * (C₂ * Real.exp (A₂ * |z.im|)) := by gcongr
    _ = max 0 C₁ * C₂ * Real.exp (A₂ * |z.im|) := (mul_assoc _ _ _).symm

lemma zetaMod_isBigO_strip :
    (fun z : ℂ => (z - 1) / (z + 2) * riemannZeta z) =O[comap ((abs : ℝ → ℝ) ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Set.Ioo (-(1 / 5 : ℝ)) (6 / 5))]
      fun z : ℂ => Real.exp (1 * Real.exp (1 * |z.im|)) := by
  let χ₁ : DirichletCharacter ℂ 1 := 1
  obtain ⟨C₁, hC₁⟩ := norm_completedLFunction_strip_bounded χ₁ (show -(1 / 5 : ℝ) ≤ 6 / 5 by norm_num)
  obtain ⟨C₂, A₂, hC₂, hA₂, hG⟩ := norm_Gammaℝ_inv_strip_le (σ₁ := -(1 / 5)) (σ₂ := 6 / 5)
    (by norm_num) (by norm_num)
  refine isBigO_strip_of_mul_exp (mul_nonneg (le_max_left 0 C₁) hC₂) hA₂ fun z hz1 hz2 him1 => ?_
  have hrat : ‖(z - 1) / (z + 2)‖ ≤ 1 := by
    rw [norm_div]
    refine div_le_one_of_le₀ ?_ (norm_nonneg _)
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im]
    norm_num
    nlinarith
  have hz0 : z ≠ 0 := fun h => by rw [h] at him1; simp at him1; linarith
  have hz_eq : riemannZeta z = DirichletCharacter.completedLFunction χ₁ z / Complex.Gammaℝ z := by
    have h1 := DirichletCharacter.LFunction_modOne_eq (χ := χ₁)
    have h2 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ₁ z (.inl hz0)
    have hev : χ₁.Even := by simp [χ₁, DirichletCharacter.Even]
    rw [hev.gammaFactor_def] at h2
    simpa [h1] using h2
  have hmul : ‖DirichletCharacter.completedLFunction χ₁ z / Complex.Gammaℝ z‖ =
      ‖DirichletCharacter.completedLFunction χ₁ z‖ * ‖(Complex.Gammaℝ z)⁻¹‖ := by
    rw [norm_div, div_eq_mul_inv, ← norm_inv]
  rw [norm_mul, hz_eq, hmul]
  have hc1 := (hC₁ z hz1 hz2 him1).trans (le_max_right 0 C₁)
  have hg1 := hG z hz1 hz2 him1
  calc
    ‖(z - 1) / (z + 2)‖ * (‖DirichletCharacter.completedLFunction χ₁ z‖ * ‖(Complex.Gammaℝ z)⁻¹‖)
      ≤ 1 * (max 0 C₁ * (C₂ * Real.exp (A₂ * |z.im|))) := by gcongr
    _ = max 0 C₁ * C₂ * Real.exp (A₂ * |z.im|) := by rw [one_mul, ← mul_assoc]

end GammaRatioAllT

namespace StripPhragmenLindelof

open GammaRatioAllT

set_option maxHeartbeats 800000 in
theorem strip_phragmen_lindelof {g : ℂ → ℂ} {a b M_R M_L Q : ℝ}
    (hab : a < b) (hwidth : b - a ≤ 2) (hMR : 0 ≤ M_R) (hML : 0 ≤ M_L) (hQ : 1 ≤ Q)
    (hfd : DiffContOnCl ℂ g (Complex.re ⁻¹' Set.Ioo a b))
    (hgrowth : g =O[comap ((abs : ℝ → ℝ) ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
      fun z : ℂ => Real.exp (1 * Real.exp (1 * |z.im|)))
    (hle_b : ∀ z : ℂ, z.re = b → ‖g z‖ ≤ M_R)
    (hle_a : ∀ z : ℂ, z.re = a → ‖g z‖ ≤ M_L * (Q * (|z.im| + 5) / (2 * Real.pi)) ^ ((b - a) / 2))
    {s₀ : ℂ} (hs_a : a ≤ s₀.re) (hs_b : s₀.re ≤ b) :
    ‖g s₀‖ ≤ Real.exp ((b - a) ^ 2 / 10) * max M_R M_L *
      (Q * (|s₀.im| + 5) / (2 * Real.pi)) ^ ((b - s₀.re) / 2) := by
  let P : ℝ := Q * (|s₀.im| + 5) / (2 * Real.pi)
  have hP : 0 < P := by positivity
  let δ : ℝ := 1 / 20
  let H : ℂ → ℂ := fun z =>
    g z * (P : ℂ) ^ ((z - (b : ℂ)) / 2) * Complex.exp ((δ : ℂ) * (z - s₀) ^ 2)
  have hpow_diff : Differentiable ℂ (fun z : ℂ => (P : ℂ) ^ ((z - (b : ℂ)) / 2)) := by
    intro z
    refine DifferentiableAt.const_cpow ?_ (Or.inl (Complex.ofReal_ne_zero.mpr hP.ne'))
    exact (differentiableAt_id.sub (differentiableAt_const _)).div_const 2
  have hexp_diff : Differentiable ℂ (fun z : ℂ => Complex.exp ((δ : ℂ) * (z - s₀) ^ 2)) :=
    ((differentiable_id.sub (differentiable_const _)).pow 2 |>.const_mul _).cexp
  have hH_fd : DiffContOnCl ℂ H (Complex.re ⁻¹' Set.Ioo a b) :=
    ⟨(hfd.differentiableOn.mul hpow_diff.differentiableOn).mul hexp_diff.differentiableOn,
      (hfd.continuousOn.mul hpow_diff.continuous.continuousOn).mul
        hexp_diff.continuous.continuousOn⟩
  have hpow_norm : ∀ z : ℂ, ‖(P : ℂ) ^ ((z - (b : ℂ)) / 2)‖ = P ^ ((z.re - b) / 2) := by
    intro z
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hP]
    simp [Complex.div_ofNat_re]
  have hexp_norm : ∀ z : ℂ, ‖Complex.exp ((δ : ℂ) * (z - s₀) ^ 2)‖ =
      Real.exp (δ * ((z.re - s₀.re) ^ 2 - (z.im - s₀.im) ^ 2)) := by
    intro z
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    congr 1
    rw [sq, Complex.mul_re, Complex.sub_re, Complex.sub_im]
    ring
  have hgrowth_H : ∃ c < Real.pi / (b - a), ∃ B : ℝ,
      H =O[comap ((abs : ℝ → ℝ) ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => Real.exp (B * Real.exp (c * |z.im|)) := by
    have hc : (1 : ℝ) < Real.pi / (b - a) := by
      rw [lt_div_iff₀ (sub_pos.mpr hab)]
      linarith [Real.pi_gt_three]
    obtain ⟨C₀, hC₀_pos, hC₀⟩ := hgrowth.exists_pos
    let P_strip : ℝ := max (P ^ ((a - b) / 2)) (P ^ ((b - b) / 2))
    let C_bd : ℝ := C₀ * P_strip * Real.exp (δ * (b - a) ^ 2)
    have hP_strip_nonneg : 0 ≤ P_strip := le_max_of_le_left (Real.rpow_nonneg hP.le _)
    refine ⟨1, hc, 1, Asymptotics.IsBigO.of_bound (max 1 C_bd) ?_⟩
    have hstrip : ∀ᶠ z in 𝓟 (Complex.re ⁻¹' Set.Ioo a b), a ≤ z.re ∧ z.re ≤ b :=
      Filter.eventually_principal.mpr fun z hz => ⟨hz.1.le, hz.2.le⟩
    refine (hC₀.and (hstrip.filter_mono inf_le_right)).mono fun z ⟨hgz, hz1, hz2⟩ => ?_
    have hP_le : ‖(P : ℂ) ^ ((z - (b : ℂ)) / 2)‖ ≤ P_strip := by
      rw [hpow_norm]
      by_cases hP1 : 1 ≤ P
      · exact le_max_of_le_right (Real.rpow_le_rpow_of_exponent_le hP1 (by linarith))
      · push Not at hP1
        exact le_max_of_le_left (Real.rpow_le_rpow_of_exponent_ge hP hP1.le (by linarith))
    have hE_le : ‖Complex.exp ((δ : ℂ) * (z - s₀) ^ 2)‖ ≤ Real.exp (δ * (b - a) ^ 2) := by
      rw [hexp_norm]
      apply Real.exp_le_exp.mpr
      have hre_sq : (z.re - s₀.re) ^ 2 ≤ (b - a) ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg (sub_pos.mpr hab).le, abs_le]
        constructor <;> linarith
      dsimp [δ]
      nlinarith [sq_nonneg (z.im - s₀.im)]
    have hgn : ‖g z‖ ≤ C₀ * Real.exp (1 * Real.exp (1 * |z.im|)) := by
      simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hgz
    have hH_norm : ‖H z‖ ≤ C_bd * Real.exp (1 * Real.exp (1 * |z.im|)) := by
      dsimp [H]
      rw [norm_mul, norm_mul]
      calc ‖g z‖ * ‖(P : ℂ) ^ ((z - (b : ℂ)) / 2)‖ * ‖Complex.exp ((δ : ℂ) * (z - s₀) ^ 2)‖
          ≤ (C₀ * Real.exp (1 * Real.exp (1 * |z.im|))) * P_strip * Real.exp (δ * (b - a) ^ 2) :=
            mul_le_mul (mul_le_mul hgn hP_le (norm_nonneg _) (by positivity)) hE_le
              (norm_nonneg _) (by positivity)
        _ = C_bd * Real.exp (1 * Real.exp (1 * |z.im|)) := by ring
    refine hH_norm.trans ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (le_max_right 1 C_bd) (Real.exp_pos _).le
  let C_max : ℝ := Real.exp ((b - a) ^ 2 / 10) * max M_R M_L
  have hC_max : 0 ≤ C_max := by positivity
  have hle_b_H : ∀ z : ℂ, z.re = b → ‖H z‖ ≤ C_max := by
    intro z hzb
    dsimp [H]
    rw [norm_mul, norm_mul, hpow_norm, hexp_norm, hzb, sub_self, zero_div, Real.rpow_zero, mul_one]
    have hre_sq : (b - s₀.re) ^ 2 ≤ (b - a) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (sub_pos.mpr hab).le, abs_of_nonneg (by linarith)]
      linarith
    have hexp_le : Real.exp (δ * ((b - s₀.re) ^ 2 - (z.im - s₀.im) ^ 2)) ≤
        Real.exp ((b - a) ^ 2 / 10) := by
      apply Real.exp_le_exp.mpr
      have hsub : (b - s₀.re) ^ 2 - (z.im - s₀.im) ^ 2 ≤ (b - a) ^ 2 := by
        linarith [sq_nonneg (z.im - s₀.im)]
      have : δ * ((b - s₀.re) ^ 2 - (z.im - s₀.im) ^ 2) ≤ (b - a) ^ 2 / 20 := by
        dsimp [δ]; linarith
      linarith [sq_nonneg (b - a)]
    calc ‖g z‖ * Real.exp (δ * ((b - s₀.re) ^ 2 - (z.im - s₀.im) ^ 2))
        ≤ M_R * Real.exp ((b - a) ^ 2 / 10) := mul_le_mul (hle_b z hzb) hexp_le (by positivity) hMR
      _ ≤ max M_R M_L * Real.exp ((b - a) ^ 2 / 10) := by gcongr; exact le_max_left _ _
      _ = C_max := by ring
  have hle_a_H : ∀ z : ℂ, z.re = a → ‖H z‖ ≤ C_max := by
    intro z hza
    dsimp [H]
    rw [norm_mul, norm_mul, hpow_norm, hexp_norm, hza]
    let α : ℝ := (b - a) / 2
    have hα0 : 0 ≤ α := by dsimp [α]; linarith
    have hα1 : α ≤ 1 := by dsimp [α]; linarith
    have hP_cancel : (Q * (|z.im| + 5) / (2 * Real.pi)) ^ α * P ^ ((a - b) / 2) =
        ((|z.im| + 5) / (|s₀.im| + 5)) ^ α := by
      have hQpos : 0 < Q / (2 * Real.pi) := by positivity
      have h1 : Q * (|z.im| + 5) / (2 * Real.pi) = (Q / (2 * Real.pi)) * (|z.im| + 5) := by ring
      have h2 : P = (Q / (2 * Real.pi)) * (|s₀.im| + 5) := by dsimp [P]; ring
      rw [h1, Real.mul_rpow hQpos.le (by positivity), h2,
        show (a - b) / 2 = -α by dsimp [α]; ring,
        Real.rpow_neg (by positivity), Real.mul_rpow hQpos.le (by positivity)]
      have h_ne : (Q / (2 * Real.pi)) ^ α ≠ 0 := (Real.rpow_pos_of_pos hQpos α).ne'
      have hs_pos : 0 ≤ |s₀.im| + 5 := by positivity
      have hz_pos : 0 ≤ |z.im| + 5 := by positivity
      have hden_ne : (|s₀.im| + 5) ^ α ≠ 0 := (Real.rpow_pos_of_pos (by positivity) α).ne'
      rw [Real.div_rpow hz_pos hs_pos]
      field_simp [h_ne, hden_ne]
    let u : ℝ := |z.im - s₀.im|
    have hratio : (|z.im| + 5) / (|s₀.im| + 5) ≤ 1 + u / 5 := by
      have htri : |z.im| ≤ |s₀.im| + u := by
        have h0 := abs_add_le s₀.im (z.im - s₀.im)
        simpa [u, abs_sub_comm] using h0
      have hden : 5 ≤ |s₀.im| + 5 := by linarith [abs_nonneg s₀.im]
      rw [div_le_iff₀ (by positivity)]
      calc |z.im| + 5 ≤ (|s₀.im| + 5) + u := by linarith
        _ = 1 * (|s₀.im| + 5) + u * (5 / 5) := by ring
        _ ≤ 1 * (|s₀.im| + 5) + u * ((|s₀.im| + 5) / 5) := by gcongr
        _ = (1 + u / 5) * (|s₀.im| + 5) := by ring
    have hrpow_exp : ((|z.im| + 5) / (|s₀.im| + 5)) ^ α ≤ Real.exp (α * u / 5) := by
      have h1u : (|z.im| + 5) / (|s₀.im| + 5) ≤ Real.exp (u / 5) :=
        hratio.trans (by linarith [Real.add_one_le_exp (u / 5)])
      have h1 : ((|z.im| + 5) / (|s₀.im| + 5)) ^ α ≤ (Real.exp (u / 5)) ^ α :=
        Real.rpow_le_rpow (by positivity) h1u hα0
      refine h1.trans_eq ?_
      rw [← Real.exp_mul]
      congr 1; ring
    have hu_sq : u ^ 2 = (z.im - s₀.im) ^ 2 := sq_abs _
    have hre_sq : (a - s₀.re) ^ 2 ≤ (b - a) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (sub_pos.mpr hab).le, abs_le]
      constructor <;> linarith
    have hquad : α * u / 5 + δ * ((a - s₀.re) ^ 2 - (z.im - s₀.im) ^ 2) ≤ (b - a) ^ 2 / 10 := by
      dsimp [α, δ]
      rw [← hu_sq]
      have hsq1 : 0 ≤ (u - (b - a)) ^ 2 := sq_nonneg _
      nlinarith
    calc ‖g z‖ * P ^ ((a - b) / 2) * Real.exp (δ * ((a - s₀.re) ^ 2 - (z.im - s₀.im) ^ 2))
        ≤ (M_L * (Q * (|z.im| + 5) / (2 * Real.pi)) ^ α) * P ^ ((a - b) / 2) *
            Real.exp (δ * ((a - s₀.re) ^ 2 - (z.im - s₀.im) ^ 2)) := by
          gcongr
          exact hle_a z hza
      _ = M_L * ((Q * (|z.im| + 5) / (2 * Real.pi)) ^ α * P ^ ((a - b) / 2)) *
            Real.exp (δ * ((a - s₀.re) ^ 2 - (z.im - s₀.im) ^ 2)) := by ring
      _ = M_L * ((|z.im| + 5) / (|s₀.im| + 5)) ^ α *
            Real.exp (δ * ((a - s₀.re) ^ 2 - (z.im - s₀.im) ^ 2)) := by rw [hP_cancel]
      _ ≤ M_L * Real.exp (α * u / 5) *
            Real.exp (δ * ((a - s₀.re) ^ 2 - (z.im - s₀.im) ^ 2)) := by gcongr
      _ = M_L * Real.exp (α * u / 5 + δ * ((a - s₀.re) ^ 2 - (z.im - s₀.im) ^ 2)) := by
          rw [mul_assoc, ← Real.exp_add]
      _ ≤ M_L * Real.exp ((b - a) ^ 2 / 10) := by gcongr
      _ ≤ max M_R M_L * Real.exp ((b - a) ^ 2 / 10) := by gcongr; exact le_max_right _ _
      _ = C_max := by ring
  have hPL := PhragmenLindelof.vertical_strip hH_fd hgrowth_H hle_a_H hle_b_H hs_a hs_b
  have hHs0 : ‖H s₀‖ = ‖g s₀‖ * P ^ ((s₀.re - b) / 2) := by
    dsimp [H]
    rw [norm_mul, norm_mul, hpow_norm, sub_self, sq, mul_zero, mul_zero, Complex.exp_zero,
      norm_one, mul_one]
  rw [hHs0] at hPL
  have hmul := mul_le_mul_of_nonneg_right hPL (by positivity : 0 ≤ P ^ ((b - s₀.re) / 2))
  have hcancel : P ^ ((s₀.re - b) / 2) * P ^ ((b - s₀.re) / 2) = 1 := by
    rw [← Real.rpow_add hP, show (s₀.re - b) / 2 + (b - s₀.re) / 2 = 0 by ring, Real.rpow_zero]
  calc ‖g s₀‖ = ‖g s₀‖ * (P ^ ((s₀.re - b) / 2) * P ^ ((b - s₀.re) / 2)) := by rw [hcancel, mul_one]
    _ = (‖g s₀‖ * P ^ ((s₀.re - b) / 2)) * P ^ ((b - s₀.re) / 2) := by ring
    _ ≤ C_max * P ^ ((b - s₀.re) / 2) := hmul

private lemma norm_LFunction_fe_of_im_ne_zero {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {s : ℂ} (hs2 : s.re ≤ -(1 / 5 : ℝ))
    (him : s.im ≠ 0) :
    ‖DirichletCharacter.LFunction χ s‖ =
      (q : ℝ) ^ (1 / 2 - s.re) *
        ‖DirichletCharacter.gammaFactor χ⁻¹ (1 - s) / DirichletCharacter.gammaFactor χ s‖ *
        ‖DirichletCharacter.LFunction χ⁻¹ (1 - s)‖ := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hq1 : q ≠ 1 := by omega
  have hgf_ne : DirichletCharacter.gammaFactor χ⁻¹ (1 - s) ≠ 0 := by
    classical
    rw [DirichletCharacter.gammaFactor]
    split_ifs
    · exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    · exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hL_eq : DirichletCharacter.LFunction χ s =
      (q : ℂ) ^ (1 / 2 - s) * DirichletCharacter.rootNumber χ *
        (DirichletCharacter.gammaFactor χ⁻¹ (1 - s) / DirichletCharacter.gammaFactor χ s) *
        DirichletCharacter.LFunction χ⁻¹ (1 - s) := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (.inr hq1)]
    have hfe := hχ.completedLFunction_one_sub (1 - s)
    rw [sub_sub_cancel] at hfe
    rw [hfe, show (1 - s - 1 / 2 : ℂ) = 1 / 2 - s by ring]
    have hL1 : DirichletCharacter.completedLFunction χ⁻¹ (1 - s) =
        DirichletCharacter.LFunction χ⁻¹ (1 - s) * DirichletCharacter.gammaFactor χ⁻¹ (1 - s) :=
      ((eq_div_iff hgf_ne).mp
        (DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s) (.inr hq1))).symm
    rw [hL1]; ring
  rw [hL_eq, norm_mul, norm_mul, norm_mul, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hq0, DirichletCharacter.norm_rootNumber hχ, mul_one]
  congr 2
  simp

private lemma norm_LFunction_one_sub_le_six {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s.re ≤ -(1 / 5 : ℝ)) :
    ‖DirichletCharacter.LFunction χ⁻¹ (1 - s)‖ ≤ 6 := by
  have h1s_re : 1 < (1 - s).re := by simp; linarith
  have hle := DirichletBasics.norm_LFunction_le_zeta χ⁻¹ h1s_re
  have hz_mono : ‖riemannZeta ((1 - s).re : ℂ)‖ ≤ ‖riemannZeta ((6 / 5 : ℝ) : ℂ)‖ := by
    rw [TernaryGoldbach.RSBounds.CenterNumerics.norm_zeta_eq_tsum_rpow (by simpa using h1s_re),
      TernaryGoldbach.RSBounds.CenterNumerics.norm_zeta_eq_tsum_rpow (by norm_num)]
    refine Summable.tsum_le_tsum (fun n => by
      by_cases hn : n = 0
      · subst hn
        simp only [Nat.cast_zero, Real.zero_rpow (by linarith : -(1 - s).re ≠ 0),
          Real.zero_rpow (by norm_num : -(6 / 5 : ℝ) ≠ 0), le_refl]
      · exact Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn))
          (by simp only [Complex.sub_re, Complex.one_re]; linarith))
      (Real.summable_nat_rpow.mpr (by linarith))
      (Real.summable_nat_rpow.mpr (by norm_num))
  have hz6 : ‖riemannZeta ((6 / 5 : ℝ) : ℂ)‖ ≤ 6 := by
    have hz := TernaryGoldbach.RSBounds.CenterNumerics.zeta_tail_upper (σ := 6 / 5)
      (by norm_num) (N := 1) (by norm_num)
    norm_num [TernaryGoldbach.RSBounds.CenterNumerics.rpowSum] at hz
    simpa using hz
  exact hle.trans (hz_mono.trans hz6)

theorem norm_LFunction_left_le {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {s : ℂ}
    (hs1 : -(7 / 20 : ℝ) ≤ s.re) (hs2 : s.re ≤ -(1 / 5 : ℝ)) :
    ‖DirichletCharacter.LFunction χ s‖ ≤
      (5 / 2 * 6 : ℝ) * ((q : ℝ) * (|s.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re) := by
  have hχ1 : χ ≠ 1 := DirichletBasics.ne_one_of_isPrimitive_of_two_le hq hχ
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hbase : ∀ z : ℂ, -(7 / 20 : ℝ) ≤ z.re → z.re ≤ -(1 / 5 : ℝ) → z.im ≠ 0 →
      ‖DirichletCharacter.LFunction χ z‖ ≤
        (5 / 2 * 6 : ℝ) * ((q : ℝ) * (|z.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - z.re) := by
    intro z hz1 hz2 hzim
    rw [norm_LFunction_fe_of_im_ne_zero hq hχ hz2 hzim]
    have hgamma := norm_gammaFactor_ratio_left_le χ hz1 hz2 hzim
    have hL6 := norm_LFunction_one_sub_le_six χ hz2
    have hpow_comb : (q : ℝ) ^ (1 / 2 - z.re) * ((|z.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - z.re) =
        ((q : ℝ) * (|z.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - z.re) := by
      rw [← Real.mul_rpow hq0.le (by positivity)]
      congr 1; ring
    calc
      (q : ℝ) ^ (1 / 2 - z.re) *
          ‖DirichletCharacter.gammaFactor χ⁻¹ (1 - z) / DirichletCharacter.gammaFactor χ z‖ *
          ‖DirichletCharacter.LFunction χ⁻¹ (1 - z)‖
        ≤ (q : ℝ) ^ (1 / 2 - z.re) * ((5 / 2 : ℝ) * ((|z.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - z.re)) *
            6 := by gcongr
      _ = (5 / 2 * 6 : ℝ) * ((q : ℝ) ^ (1 / 2 - z.re) *
            ((|z.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - z.re)) := by ring
      _ = (5 / 2 * 6 : ℝ) * ((q : ℝ) * (|z.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - z.re) := by
          rw [hpow_comb]
  by_cases him0 : s.im = 0
  · have hcont1 : ContinuousAt (fun ε : ℝ => ‖DirichletCharacter.LFunction χ (s + (ε : ℂ) * I)‖) 0 :=
      ((DirichletCharacter.differentiable_LFunction hχ1).continuous.comp
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))).norm.continuousAt
    have hcont2 : ContinuousAt (fun ε : ℝ =>
        (5 / 2 * 6 : ℝ) * ((q : ℝ) * (|s.im + ε| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re)) 0 := by
      refine Continuous.continuousAt ?_
      refine continuous_const.mul (Continuous.rpow ?_ continuous_const fun ε => Or.inl ?_)
      · exact ((continuous_const.mul ((continuous_abs.comp (continuous_const.add continuous_id)).add
          continuous_const)).div_const _)
      · positivity
    have hnear : ∀ᶠ ε : ℝ in 𝓝[≠] 0,
        ‖DirichletCharacter.LFunction χ (s + (ε : ℂ) * I)‖ ≤
          (5 / 2 * 6 : ℝ) * ((q : ℝ) * (|s.im + ε| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re) := by
      refine eventually_nhdsWithin_iff.mpr (Filter.Eventually.of_forall fun ε hε => ?_)
      have him_ne : (s + (ε : ℂ) * I).im ≠ 0 := by simpa [him0] using hε
      have hre_eq : (s + (ε : ℂ) * I).re = s.re := by simp
      have hb := hbase (s + (ε : ℂ) * I) (by simpa [hre_eq] using hs1)
        (by simpa [hre_eq] using hs2) him_ne
      simpa [hre_eq] using hb
    have ht1 : Tendsto (fun ε : ℝ => ‖DirichletCharacter.LFunction χ (s + (ε : ℂ) * I)‖)
        (𝓝[≠] 0) (𝓝 ‖DirichletCharacter.LFunction χ s‖) := by
      simpa using hcont1.mono_left nhdsWithin_le_nhds
    have ht2 : Tendsto (fun ε : ℝ =>
        (5 / 2 * 6 : ℝ) * ((q : ℝ) * (|s.im + ε| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re))
        (𝓝[≠] 0)
        (𝓝 ((5 / 2 * 6 : ℝ) * ((q : ℝ) * (|s.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re))) := by
      simpa using hcont2.mono_left nhdsWithin_le_nhds
    exact le_of_tendsto_of_tendsto ht1 ht2 hnear
  · exact hbase s hs1 hs2 him0

theorem norm_LFunction_strip_le {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {s : ℂ}
    (hs1 : -(1 / 5 : ℝ) ≤ s.re) (hs2 : s.re ≤ 6 / 5) :
    ‖DirichletCharacter.LFunction χ s‖ ≤
      (13 / 10 : ℝ) * (17 / 10 * 6) *
        ((q : ℝ) * (|s.im| + 5) / (2 * Real.pi)) ^ ((6 / 5 - s.re) / 2) := by
  have hχ1 : χ ≠ 1 := DirichletBasics.ne_one_of_isPrimitive_of_two_le hq hχ
  have hfd : DiffContOnCl ℂ (DirichletCharacter.LFunction χ)
      (Complex.re ⁻¹' Set.Ioo (-(1 / 5 : ℝ)) (6 / 5)) :=
    (DirichletCharacter.differentiable_LFunction hχ1).differentiableOn.diffContOnCl
  have hle_b : ∀ z : ℂ, z.re = 6 / 5 → ‖DirichletCharacter.LFunction χ z‖ ≤ 17 / 10 * 6 := by
    intro z hzb
    have hz_eq : z = (6 / 5 : ℂ) + z.im * I := by
      apply Complex.ext <;> simp [hzb]
    rw [hz_eq]
    exact (DirichletBasics.LFunction_six_fifths_upper χ z.im).trans (by norm_num)
  have hle_a : ∀ z : ℂ, z.re = -(1 / 5 : ℝ) →
      ‖DirichletCharacter.LFunction χ z‖ ≤
        (17 / 10 * 6 : ℝ) * ((q : ℝ) * (|z.im| + 5) / (2 * Real.pi)) ^ ((6 / 5 - -(1 / 5 : ℝ)) / 2) := by
    intro z hza
    have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
    have hbase : ∀ w : ℂ, w.re = -(1 / 5 : ℝ) → w.im ≠ 0 →
        ‖DirichletCharacter.LFunction χ w‖ ≤ (17 / 10 * 6 : ℝ) *
          ((q : ℝ) * (|w.im| + 5) / (2 * Real.pi)) ^ ((6 / 5 - -(1 / 5 : ℝ)) / 2) := by
      intro w hwa hwim
      rw [norm_LFunction_fe_of_im_ne_zero hq hχ hwa.le hwim]
      have hgamma := norm_gammaFactor_ratio_strip_le χ hwa hwim
      have hL6 := norm_LFunction_one_sub_le_six χ hwa.le
      have hpow_comb : (q : ℝ) ^ (1 / 2 - w.re) *
            ((|w.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - w.re) =
          ((q : ℝ) * (|w.im| + 5) / (2 * Real.pi)) ^ ((6 / 5 - -(1 / 5 : ℝ)) / 2) := by
        rw [hwa, show (1 / 2 - -(1 / 5 : ℝ)) = (6 / 5 - -(1 / 5 : ℝ)) / 2 by norm_num,
          ← Real.mul_rpow hq0.le (by positivity)]
        congr 1; ring
      calc
        (q : ℝ) ^ (1 / 2 - w.re) *
            ‖DirichletCharacter.gammaFactor χ⁻¹ (1 - w) / DirichletCharacter.gammaFactor χ w‖ *
            ‖DirichletCharacter.LFunction χ⁻¹ (1 - w)‖
          ≤ (q : ℝ) ^ (1 / 2 - w.re) *
              ((17 / 10 : ℝ) * ((|w.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - w.re)) * 6 := by
            gcongr
        _ = (17 / 10 * 6 : ℝ) * ((q : ℝ) ^ (1 / 2 - w.re) *
              ((|w.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - w.re)) := by ring
        _ = (17 / 10 * 6 : ℝ) *
              ((q : ℝ) * (|w.im| + 5) / (2 * Real.pi)) ^ ((6 / 5 - -(1 / 5 : ℝ)) / 2) := by
            rw [hpow_comb]
    by_cases him0 : z.im = 0
    · have hcont : ContinuousAt (fun ε : ℝ => ‖DirichletCharacter.LFunction χ (z + (ε : ℂ) * I)‖) 0 :=
        ((DirichletCharacter.differentiable_LFunction hχ1).continuous.comp
          (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))).norm.continuousAt
      have hrhs_cont : ContinuousAt (fun ε : ℝ =>
          (17 / 10 * 6 : ℝ) * ((q : ℝ) * (|z.im + ε| + 5) / (2 * Real.pi)) ^
            ((6 / 5 - -(1 / 5 : ℝ)) / 2)) 0 := by
        refine Continuous.continuousAt ?_
        refine continuous_const.mul (Continuous.rpow ?_ continuous_const fun ε => Or.inl ?_)
        · exact ((continuous_const.mul ((continuous_abs.comp (continuous_const.add continuous_id)).add
            continuous_const)).div_const _)
        · positivity
      have hnear : ∀ᶠ ε : ℝ in 𝓝[≠] 0,
          ‖DirichletCharacter.LFunction χ (z + (ε : ℂ) * I)‖ ≤
            (17 / 10 * 6 : ℝ) * ((q : ℝ) * (|z.im + ε| + 5) / (2 * Real.pi)) ^
              ((6 / 5 - -(1 / 5 : ℝ)) / 2) := by
        refine eventually_nhdsWithin_iff.mpr (Filter.Eventually.of_forall fun ε hε => ?_)
        have him_ne : (z + (ε : ℂ) * I).im ≠ 0 := by simpa [him0] using hε
        have hre_eq : (z + (ε : ℂ) * I).re = -(1 / 5 : ℝ) := by simpa using hza
        simpa using hbase (z + (ε : ℂ) * I) hre_eq him_ne
      have ht1 : Tendsto (fun ε : ℝ => ‖DirichletCharacter.LFunction χ (z + (ε : ℂ) * I)‖)
          (𝓝[≠] 0) (𝓝 ‖DirichletCharacter.LFunction χ z‖) := by
        simpa using hcont.mono_left nhdsWithin_le_nhds
      have ht2 : Tendsto (fun ε : ℝ => (17 / 10 * 6 : ℝ) *
            ((q : ℝ) * (|z.im + ε| + 5) / (2 * Real.pi)) ^ ((6 / 5 - -(1 / 5 : ℝ)) / 2))
          (𝓝[≠] 0)
          (𝓝 ((17 / 10 * 6 : ℝ) * ((q : ℝ) * (|z.im| + 5) / (2 * Real.pi)) ^
            ((6 / 5 - -(1 / 5 : ℝ)) / 2))) := by
        simpa using hrhs_cont.mono_left nhdsWithin_le_nhds
      exact le_of_tendsto_of_tendsto ht1 ht2 hnear
    · exact hbase z hza him0
  have hPL := strip_phragmen_lindelof (a := -(1 / 5)) (b := 6 / 5) (M_R := 17 / 10 * 6)
    (M_L := 17 / 10 * 6) (Q := q) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast (by omega : 1 ≤ q)) hfd (LFunction_isBigO_strip hq χ) hle_b hle_a hs1 hs2
  have hexp_pl : Real.exp (((6 / 5 : ℝ) - -(1 / 5 : ℝ)) ^ 2 / 10) ≤ 13 / 10 := by
    have h := Real.exp_bound' (x := (49 / 250 : ℝ)) (by norm_num) (by norm_num) (n := 6) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    convert (by linarith : Real.exp (49 / 250 : ℝ) ≤ 13 / 10) using 2
    norm_num
  have hmax : max (17 / 10 * 6 : ℝ) (17 / 10 * 6) = 17 / 10 * 6 := max_self _
  rw [hmax] at hPL
  refine hPL.trans ?_
  gcongr

theorem norm_zeta_left_le {s : ℂ}
    (hs1 : -(7 / 20 : ℝ) ≤ s.re) (hs2 : s.re ≤ -(1 / 5 : ℝ)) :
    ‖riemannZeta s‖ ≤
      (5 / 2 * 6 : ℝ) * ((|s.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re) := by
  let χ₁ : DirichletCharacter ℂ 1 := 1
  have hbase : ∀ z : ℂ, -(7 / 20 : ℝ) ≤ z.re → z.re ≤ -(1 / 5 : ℝ) → z.im ≠ 0 →
      ‖riemannZeta z‖ ≤ (5 / 2 * 6 : ℝ) * ((|z.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - z.re) := by
    intro z hz1 hz2 hzim
    have hz0 : z ≠ 0 := fun h => by rw [h] at hz2; norm_num at hz2
    have h1z_re : 1 < (1 - z).re := by simp; linarith
    have hgf_ne : DirichletCharacter.gammaFactor χ₁⁻¹ (1 - z) ≠ 0 := by
      have hev' : χ₁⁻¹.Even := (DirichletBasics.even_inv_iff χ₁).mpr (by simp [χ₁, DirichletCharacter.Even])
      rw [hev'.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
    have hz_eq : riemannZeta z =
        (DirichletCharacter.gammaFactor χ₁⁻¹ (1 - z) / DirichletCharacter.gammaFactor χ₁ z) *
          riemannZeta (1 - z) := by
      have h1 := DirichletCharacter.LFunction_modOne_eq (χ := χ₁)
      have h2 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ₁ z (.inl hz0)
      have hfe := (DirichletCharacter.isPrimitive_one_level_one).completedLFunction_one_sub (1 - z)
      simp only [sub_sub_cancel, Nat.cast_one, one_cpow, one_mul,
        DirichletCharacter.rootNumber_modOne] at hfe
      have hL1 : DirichletCharacter.completedLFunction χ₁⁻¹ (1 - z) =
          riemannZeta (1 - z) * DirichletCharacter.gammaFactor χ₁⁻¹ (1 - z) := by
        have h3 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ₁⁻¹ (1 - z)
          (.inl (fun h => by rw [h] at h1z_re; simp at h1z_re; linarith))
        have h1' : DirichletCharacter.LFunction χ₁⁻¹ (1 - z) = riemannZeta (1 - z) := by
          have : χ₁⁻¹ = (1 : DirichletCharacter ℂ 1) := by ext; simp [χ₁]
          rw [this, h1]
        rw [h1'] at h3
        exact ((eq_div_iff hgf_ne).mp h3).symm
      calc riemannZeta z = DirichletCharacter.LFunction χ₁ z := by rw [h1]
        _ = DirichletCharacter.completedLFunction χ₁ z / DirichletCharacter.gammaFactor χ₁ z := h2
        _ = DirichletCharacter.completedLFunction χ₁⁻¹ (1 - z) / DirichletCharacter.gammaFactor χ₁ z := by
            rw [hfe]
        _ = (DirichletCharacter.gammaFactor χ₁⁻¹ (1 - z) / DirichletCharacter.gammaFactor χ₁ z) *
              riemannZeta (1 - z) := by
            rw [hL1]; ring
    rw [hz_eq, norm_mul]
    have hgamma := norm_gammaFactor_ratio_left_le χ₁ hz1 hz2 hzim
    have hZ6 : ‖riemannZeta (1 - z)‖ ≤ 6 := by
      have hz_eq' : riemannZeta (1 - z) = DirichletCharacter.LFunction χ₁⁻¹ (1 - z) := by
        have : χ₁⁻¹ = (1 : DirichletCharacter ℂ 1) := by ext; simp [χ₁]
        rw [this, DirichletCharacter.LFunction_modOne_eq]
      rw [hz_eq']
      exact norm_LFunction_one_sub_le_six χ₁ hz2
    exact (mul_le_mul hgamma hZ6 (norm_nonneg _) (by positivity)).trans_eq (by ring)
  by_cases him0 : s.im = 0
  · have hs1_ne : s ≠ 1 := fun h => by rw [h] at hs2; norm_num at hs2
    have hcont1 : ContinuousAt (fun ε : ℝ => ‖riemannZeta (s + (ε : ℂ) * I)‖) 0 := by
      have hline : ContinuousAt (fun ε : ℝ => s + (ε : ℂ) * I) 0 :=
        continuousAt_const.add (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
      have hzeta : ContinuousAt riemannZeta (s + ((0 : ℝ) : ℂ) * I) := by
        simpa using (differentiableAt_riemannZeta hs1_ne).continuousAt
      exact (hzeta.comp_of_eq hline (by simp)).norm
    have hcont2 : ContinuousAt (fun ε : ℝ =>
        (5 / 2 * 6 : ℝ) * ((|s.im + ε| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re)) 0 := by
      refine Continuous.continuousAt ?_
      refine continuous_const.mul (Continuous.rpow ?_ continuous_const fun ε => Or.inl ?_)
      · exact (((continuous_abs.comp (continuous_const.add continuous_id)).add
          continuous_const).div_const _)
      · positivity
    have hnear : ∀ᶠ ε : ℝ in 𝓝[≠] 0,
        ‖riemannZeta (s + (ε : ℂ) * I)‖ ≤
          (5 / 2 * 6 : ℝ) * ((|s.im + ε| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re) := by
      refine eventually_nhdsWithin_iff.mpr (Filter.Eventually.of_forall fun ε hε => ?_)
      have him_ne : (s + (ε : ℂ) * I).im ≠ 0 := by simpa [him0] using hε
      have hre_eq : (s + (ε : ℂ) * I).re = s.re := by simp
      simpa [hre_eq] using hbase (s + (ε : ℂ) * I) (by linarith) (by linarith) him_ne
    have ht1 : Tendsto (fun ε : ℝ => ‖riemannZeta (s + (ε : ℂ) * I)‖) (𝓝[≠] 0) (𝓝 ‖riemannZeta s‖) := by
      simpa using hcont1.mono_left nhdsWithin_le_nhds
    have ht2 : Tendsto (fun ε : ℝ =>
        (5 / 2 * 6 : ℝ) * ((|s.im + ε| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re))
        (𝓝[≠] 0) (𝓝 ((5 / 2 * 6 : ℝ) * ((|s.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - s.re))) := by
      simpa using hcont2.mono_left nhdsWithin_le_nhds
    exact le_of_tendsto_of_tendsto ht1 ht2 hnear
  · exact hbase s hs1 hs2 him0

noncomputable def zetaMod (z : ℂ) : ℂ :=
  Function.update (fun s : ℂ => (s - 1) / (s + 2) * riemannZeta s) 1 (1 / 3) z

lemma zetaMod_eq_of_ne_one {z : ℂ} (hz : z ≠ 1) :
    zetaMod z = (z - 1) / (z + 2) * riemannZeta z :=
  Function.update_of_ne hz (1 / 3) (fun s : ℂ => (s - 1) / (s + 2) * riemannZeta s)

set_option maxHeartbeats 800000 in
theorem norm_zetaMod_strip_le {s : ℂ}
    (hs1 : -(1 / 5 : ℝ) ≤ s.re) (hs2 : s.re ≤ 6 / 5) :
    ‖zetaMod s‖ ≤
      (13 / 10 : ℝ) * (17 / 10 * 6) * ((|s.im| + 5) / (2 * Real.pi)) ^ ((6 / 5 - s.re) / 2) := by
  have hdiff_on : DifferentiableOn ℂ zetaMod {z : ℂ | z ≠ -2} := by
    let g : ℂ → ℂ := Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1
    have hg_diff : Differentiable ℂ g := by
      rw [← differentiableOn_univ,
        ← differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
      refine ⟨DifferentiableOn.congr (f := fun s : ℂ => (s - 1) * riemannZeta s)
        (fun z hz => DifferentiableAt.differentiableWithinAt <|
          (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta (Set.mem_sdiff_singleton.mp hz).2))
        (fun z hz => Function.update_of_ne (Set.mem_sdiff_singleton.mp hz).2 _ _),
        continuousAt_update_same.mpr riemannZeta_residue_one⟩
    have heq : Set.EqOn zetaMod (fun z => g z / (z + 2)) {z : ℂ | z ≠ -2} := by
      intro z hz
      by_cases h1 : z = 1
      · subst h1
        simp only [zetaMod, g, Function.update_self]
        norm_num
      · simp only [zetaMod, g, Function.update_of_ne h1]
        ring
    refine DifferentiableOn.congr ?_ heq
    intro z hz
    exact ((hg_diff z).div (differentiableAt_id.add_const 2)
      (fun h0 => hz (eq_neg_of_add_eq_zero_left h0))).differentiableWithinAt
  have hsub : Complex.re ⁻¹' Set.Icc (-(1 / 5 : ℝ)) (6 / 5) ⊆ {z : ℂ | z ≠ -2} := by
    intro z hz h2; rw [h2] at hz; simp at hz; linarith [hz.1]
  have hfd : DiffContOnCl ℂ zetaMod (Complex.re ⁻¹' Set.Ioo (-(1 / 5 : ℝ)) (6 / 5)) := by
    have hcl : closure (Complex.re ⁻¹' Set.Ioo (-(1 / 5 : ℝ)) (6 / 5)) ⊆
        Complex.re ⁻¹' Set.Icc (-(1 / 5 : ℝ)) (6 / 5) :=
      IsClosed.closure_subset_iff (isClosed_Icc.preimage Complex.continuous_re) |>.mpr
        (Set.preimage_mono Set.Ioo_subset_Icc_self)
    have hdon := hdiff_on.mono hsub
    exact ⟨hdon.mono (fun z hz => Set.Ioo_subset_Icc_self hz),
      (hdon.continuousOn.mono hcl).mono subset_rfl⟩
  have hgrowth : zetaMod =O[comap ((abs : ℝ → ℝ) ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Set.Ioo (-(1 / 5 : ℝ)) (6 / 5))]
      fun z : ℂ => Real.exp (1 * Real.exp (1 * |z.im|)) := by
    refine zetaMod_isBigO_strip.congr' ?_ Filter.EventuallyEq.rfl
    have hev : ∀ᶠ z in comap ((abs : ℝ → ℝ) ∘ Complex.im) atTop, z ≠ 1 := by
      refine Filter.eventually_comap.mpr ((Filter.eventually_ge_atTop 1).mono fun t ht x hx => ?_)
      intro h1; subst h1; simp [Function.comp_def] at hx; linarith
    exact (hev.filter_mono inf_le_left).mono fun z hz => (zetaMod_eq_of_ne_one hz).symm
  have hrat_le : ∀ z : ℂ, -(1 / 5 : ℝ) ≤ z.re → ‖(z - 1) / (z + 2)‖ ≤ 1 := by
    intro z hz
    rw [norm_div]
    refine div_le_one_of_le₀ ?_ (norm_nonneg _)
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im]
    norm_num
    nlinarith
  have hle_b : ∀ z : ℂ, z.re = 6 / 5 → ‖zetaMod z‖ ≤ 17 / 10 * 6 := by
    intro z hzb
    have hz1 : z ≠ 1 := fun h => by rw [h] at hzb; simp at hzb; norm_num at hzb
    rw [zetaMod_eq_of_ne_one hz1, norm_mul]
    have hZ6 : ‖riemannZeta z‖ ≤ 6 := by
      have hz_eq : riemannZeta z = DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)
          ((6 / 5 : ℂ) + z.im * I) := by
        rw [DirichletCharacter.LFunction_modOne_eq]
        congr 1; apply Complex.ext <;> simp [hzb]
      rw [hz_eq]
      exact DirichletBasics.LFunction_six_fifths_upper _ z.im
    calc ‖(z - 1) / (z + 2)‖ * ‖riemannZeta z‖
        ≤ 1 * 6 := mul_le_mul (hrat_le z (by linarith)) hZ6 (norm_nonneg _) zero_le_one
      _ ≤ 17 / 10 * 6 := by norm_num
  have hle_a : ∀ z : ℂ, z.re = -(1 / 5 : ℝ) →
      ‖zetaMod z‖ ≤ (17 / 10 * 6 : ℝ) * ((1 : ℝ) * (|z.im| + 5) / (2 * Real.pi)) ^
        ((6 / 5 - -(1 / 5 : ℝ)) / 2) := by
    intro z hza
    have hz1 : z ≠ 1 := fun h => by rw [h] at hza; simp at hza; norm_num at hza
    rw [zetaMod_eq_of_ne_one hz1, norm_mul]
    let χ₁ : DirichletCharacter ℂ 1 := 1
    have hbase : ∀ w : ℂ, w.re = -(1 / 5 : ℝ) → w.im ≠ 0 →
        ‖riemannZeta w‖ ≤ (17 / 10 * 6 : ℝ) * ((1 : ℝ) * (|w.im| + 5) / (2 * Real.pi)) ^
          ((6 / 5 - -(1 / 5 : ℝ)) / 2) := by
      intro w hwa hwim
      have hw0 : w ≠ 0 := fun h => by rw [h] at hwa; simp at hwa
      have h1w_re : (1 - w).re = 6 / 5 := by simp [hwa]; norm_num
      have hgf_ne : DirichletCharacter.gammaFactor χ₁⁻¹ (1 - w) ≠ 0 := by
        have hev' : χ₁⁻¹.Even := (DirichletBasics.even_inv_iff χ₁).mpr (by simp [χ₁, DirichletCharacter.Even])
        rw [hev'.gammaFactor_def]
        exact Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
      have hw_eq : riemannZeta w =
          (DirichletCharacter.gammaFactor χ₁⁻¹ (1 - w) / DirichletCharacter.gammaFactor χ₁ w) *
            riemannZeta (1 - w) := by
        have h1 := DirichletCharacter.LFunction_modOne_eq (χ := χ₁)
        have h2 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ₁ w (.inl hw0)
        have hfe := (DirichletCharacter.isPrimitive_one_level_one).completedLFunction_one_sub (1 - w)
        simp only [sub_sub_cancel, Nat.cast_one, one_cpow, one_mul,
          DirichletCharacter.rootNumber_modOne] at hfe
        have hL1 : DirichletCharacter.completedLFunction χ₁⁻¹ (1 - w) =
            riemannZeta (1 - w) * DirichletCharacter.gammaFactor χ₁⁻¹ (1 - w) := by
          have h3 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ₁⁻¹ (1 - w)
            (.inl (fun h => by rw [h] at h1w_re; simp at h1w_re; norm_num at h1w_re))
          have h1' : DirichletCharacter.LFunction χ₁⁻¹ (1 - w) = riemannZeta (1 - w) := by
            have : χ₁⁻¹ = (1 : DirichletCharacter ℂ 1) := by ext; simp [χ₁]
            rw [this, h1]
          rw [h1'] at h3
          exact ((eq_div_iff hgf_ne).mp h3).symm
        calc riemannZeta w = DirichletCharacter.LFunction χ₁ w := by rw [h1]
          _ = DirichletCharacter.completedLFunction χ₁ w / DirichletCharacter.gammaFactor χ₁ w := h2
          _ = DirichletCharacter.completedLFunction χ₁⁻¹ (1 - w) / DirichletCharacter.gammaFactor χ₁ w := by
              rw [hfe]
          _ = (DirichletCharacter.gammaFactor χ₁⁻¹ (1 - w) / DirichletCharacter.gammaFactor χ₁ w) *
                riemannZeta (1 - w) := by rw [hL1]; ring
      rw [hw_eq, norm_mul]
      have hgamma := norm_gammaFactor_ratio_strip_le χ₁ hwa hwim
      rw [hwa] at hgamma
      have hZ6 : ‖riemannZeta (1 - w)‖ ≤ 6 := by
        have hz_eq' : riemannZeta (1 - w) = DirichletCharacter.LFunction χ₁⁻¹ (1 - w) := by
          have : χ₁⁻¹ = (1 : DirichletCharacter ℂ 1) := by ext; simp [χ₁]
          rw [this, DirichletCharacter.LFunction_modOne_eq]
        rw [hz_eq']
        exact norm_LFunction_one_sub_le_six χ₁ hwa.le
      calc ‖DirichletCharacter.gammaFactor χ₁⁻¹ (1 - w) / DirichletCharacter.gammaFactor χ₁ w‖ *
            ‖riemannZeta (1 - w)‖
          ≤ ((17 / 10 : ℝ) * ((|w.im| + 5) / (2 * Real.pi)) ^ (1 / 2 - -(1 / 5 : ℝ))) * 6 := by
            gcongr
        _ = (17 / 10 * 6 : ℝ) * ((1 : ℝ) * (|w.im| + 5) / (2 * Real.pi)) ^
              ((6 / 5 - -(1 / 5 : ℝ)) / 2) := by
            rw [show (1 / 2 - -(1 / 5 : ℝ)) = (6 / 5 - -(1 / 5 : ℝ)) / 2 by norm_num]
            ring
    have hZ_norm : ‖riemannZeta z‖ ≤ (17 / 10 * 6 : ℝ) * ((1 : ℝ) * (|z.im| + 5) / (2 * Real.pi)) ^
        ((6 / 5 - -(1 / 5 : ℝ)) / 2) := by
      by_cases him0 : z.im = 0
      · have hcont1 : ContinuousAt (fun ε : ℝ => ‖riemannZeta (z + (ε : ℂ) * I)‖) 0 := by
          have hline : ContinuousAt (fun ε : ℝ => z + (ε : ℂ) * I) 0 :=
            continuousAt_const.add (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
          have hzeta : ContinuousAt riemannZeta (z + ((0 : ℝ) : ℂ) * I) := by
            simpa using (differentiableAt_riemannZeta hz1).continuousAt
          exact (hzeta.comp_of_eq hline (by simp)).norm
        have hcont2 : ContinuousAt (fun ε : ℝ =>
            (17 / 10 * 6 : ℝ) * ((1 : ℝ) * (|z.im + ε| + 5) / (2 * Real.pi)) ^
              ((6 / 5 - -(1 / 5 : ℝ)) / 2)) 0 := by
          refine Continuous.continuousAt ?_
          refine continuous_const.mul (Continuous.rpow ?_ continuous_const fun ε => Or.inl ?_)
          · exact ((continuous_const.mul ((continuous_abs.comp (continuous_const.add continuous_id)).add
              continuous_const)).div_const _)
          · positivity
        have hnear : ∀ᶠ ε : ℝ in 𝓝[≠] 0, ‖riemannZeta (z + (ε : ℂ) * I)‖ ≤
            (17 / 10 * 6 : ℝ) * ((1 : ℝ) * (|z.im + ε| + 5) / (2 * Real.pi)) ^
              ((6 / 5 - -(1 / 5 : ℝ)) / 2) := by
          refine eventually_nhdsWithin_iff.mpr (Filter.Eventually.of_forall fun ε hε => ?_)
          have him_ne : (z + (ε : ℂ) * I).im ≠ 0 := by simpa [him0] using hε
          have hre_eq : (z + (ε : ℂ) * I).re = -(1 / 5 : ℝ) := by simpa using hza
          simpa using hbase (z + (ε : ℂ) * I) hre_eq him_ne
        have ht1 : Tendsto (fun ε : ℝ => ‖riemannZeta (z + (ε : ℂ) * I)‖) (𝓝[≠] 0) (𝓝 ‖riemannZeta z‖) := by
          simpa using hcont1.mono_left nhdsWithin_le_nhds
        have ht2 : Tendsto (fun ε : ℝ => (17 / 10 * 6 : ℝ) *
              ((1 : ℝ) * (|z.im + ε| + 5) / (2 * Real.pi)) ^ ((6 / 5 - -(1 / 5 : ℝ)) / 2))
            (𝓝[≠] 0) (𝓝 ((17 / 10 * 6 : ℝ) * ((1 : ℝ) * (|z.im| + 5) / (2 * Real.pi)) ^
              ((6 / 5 - -(1 / 5 : ℝ)) / 2))) := by
          simpa using hcont2.mono_left nhdsWithin_le_nhds
        exact le_of_tendsto_of_tendsto ht1 ht2 hnear
      · exact hbase z hza him0
    calc ‖(z - 1) / (z + 2)‖ * ‖riemannZeta z‖
        ≤ 1 * ((17 / 10 * 6 : ℝ) * ((1 : ℝ) * (|z.im| + 5) / (2 * Real.pi)) ^
            ((6 / 5 - -(1 / 5 : ℝ)) / 2)) :=
          mul_le_mul (hrat_le z (by linarith)) hZ_norm (norm_nonneg _) zero_le_one
      _ = _ := by ring
  have hPL := strip_phragmen_lindelof (a := -(1 / 5)) (b := 6 / 5) (M_R := 17 / 10 * 6)
    (M_L := 17 / 10 * 6) (Q := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (le_refl 1) hfd hgrowth hle_b hle_a hs1 hs2
  have hexp_pl : Real.exp (((6 / 5 : ℝ) - -(1 / 5 : ℝ)) ^ 2 / 10) ≤ 13 / 10 := by
    have h := Real.exp_bound' (x := (49 / 250 : ℝ)) (by norm_num) (by norm_num) (n := 6) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    convert (by linarith : Real.exp (49 / 250 : ℝ) ≤ 13 / 10) using 2
    norm_num
  have hmax : max (17 / 10 * 6 : ℝ) (17 / 10 * 6) = 17 / 10 * 6 := max_self _
  rw [hmax, one_mul] at hPL
  refine hPL.trans ?_
  gcongr

end StripPhragmenLindelof

-- ============================================================================
-- Batch 2: DirichletGammaPhaseOdd, DirichletCountIdentity
-- ============================================================================

namespace DirichletGammaPhaseOdd

lemma im_digamma_nonneg {w : ℂ} (hw_re : 0 < w.re) (hw_im : 0 ≤ w.im) :
    0 ≤ (Complex.digamma w).im := by
  rw [GammaSolution.digamma_eq_gaussSum hw_re, GammaSolution.gaussSum, Complex.add_im,
    Complex.neg_im, Complex.ofReal_im, neg_zero, zero_add]
  have hs := GammaSolution.summable_gaussTerm
    (GammaSolution.ne_neg_natCast_of_mem (GammaSolution.mem_rightHalfPlane_iff.mpr hw_re))
  have him : (∑' k, GammaSolution.gaussTerm w k).im =
      ∑' k, (GammaSolution.gaussTerm w k).im :=
    Complex.imCLM.map_tsum hs
  rw [him]
  refine tsum_nonneg fun k => ?_
  rw [GammaSolution.gaussTerm, Complex.sub_im]
  have h1 : (((k : ℂ) + 1)⁻¹).im = 0 := by
    rw [show ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_inv,
      Complex.ofReal_im]
  have h2 : (((k : ℂ) + w)⁻¹).im = -w.im / Complex.normSq ((k : ℂ) + w) := by
    rw [Complex.inv_im]
    simp
  rw [h1, h2, zero_sub, neg_div, neg_neg]
  exact div_nonneg hw_im (Complex.normSq_nonneg _)

lemma im_digamma_ofReal {x : ℝ} (hx : 0 < x) : (Complex.digamma (x : ℂ)).im = 0 := by
  rw [GammaSolution.digamma_ofReal hx, Complex.ofReal_im]

lemma im_neg_inv_of_re_ge {a : ℝ} (ha : 0 < a) {w : ℂ} (hw_re : a ≤ w.re) (hw_im : 0 < w.im) :
    (-w⁻¹).im ≤ 1 / (2 * a) := by
  rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  have hpos : 0 < Complex.normSq w :=
    Complex.normSq_pos.mpr (fun h => by rw [h] at hw_im; simp at hw_im)
  have hns : 2 * a * w.im ≤ Complex.normSq w := by
    rw [Complex.normSq_apply]
    have h2 : a ^ 2 ≤ w.re ^ 2 := sq_le_sq' (by linarith) hw_re
    have h3 : 0 ≤ (a - w.im) ^ 2 := sq_nonneg _
    nlinarith
  rw [div_le_div_iff₀ hpos (by positivity : 0 < 2 * a)]
  nlinarith

lemma digamma_im_upper_low {σ T : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 3 / 2)
    (hT1 : 2 ≤ T) (hT2 : T ≤ 4) :
    (Complex.digamma (((σ : ℂ) + T * I) / 2)).im ≤ 16 / 17 + 1 + 2 / 5 + 2 / 9 + 2 / 13 := by
  let w : ℂ := ((σ : ℂ) + T * I) / 2
  have hw_re : 1 / 4 ≤ w.re := by simp [w, Complex.div_ofNat_re]; linarith
  have hw_im : w.im = T / 2 := by simp [w, Complex.div_ofNat_im]
  have hne : ∀ k : ℕ, w + (k : ℂ) ≠ 0 := fun k hk => by
    have := congrArg Complex.re hk
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at this
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hrec : Complex.digamma w =
      Complex.digamma (w + 4) - w⁻¹ - (w + 1)⁻¹ - (w + 2)⁻¹ - (w + 3)⁻¹ := by
    have h0 := Complex.digamma_apply_add_one w (fun m h => hne m (by linear_combination h))
    have h1 := Complex.digamma_apply_add_one (w + 1) (fun m h => hne (m + 1) (by push_cast; linear_combination h))
    have h2 := Complex.digamma_apply_add_one (w + 2) (fun m h => hne (m + 2) (by push_cast; linear_combination h))
    have h3 := Complex.digamma_apply_add_one (w + 3) (fun m h => hne (m + 3) (by push_cast; linear_combination h))
    rw [show w + 4 = w + 3 + 1 by ring, h3, show w + 3 = w + 2 + 1 by ring, h2,
      show w + 2 = w + 1 + 1 by ring, h1, h0]
    ring
  have him_shift : (Complex.digamma (w + 4)).im ≤ 16 / 17 := by
    have hre1 : (17 / 4 : ℝ) ≤ (w + 4).re := by simp [w, Complex.div_ofNat_re]; linarith
    have hre2 : (17 / 4 : ℝ) ≤ (((w + 4).re : ℝ) : ℂ).re := by simpa using hre1
    have hdiff := TernaryGoldbach.RSBounds.BacklundGammaPhase.norm_digamma_sub_le_of_re_ge
      (N := 17 / 4) (by norm_num) hre1 hre2
    have hsub : (w + 4) - (((w + 4).re : ℝ) : ℂ) = ((T / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [w, Complex.div_ofNat_re, Complex.div_ofNat_im]
    rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < T / 2),
      Complex.norm_I, mul_one] at hdiff
    have him0 : (Complex.digamma (w + 4)).im =
        (Complex.digamma (w + 4) - Complex.digamma (((w + 4).re : ℝ) : ℂ)).im := by
      rw [Complex.sub_im, im_digamma_ofReal (by linarith), sub_zero]
    have h1 : (Complex.digamma (w + 4) - Complex.digamma (((w + 4).re : ℝ) : ℂ)).im ≤
        ‖Complex.digamma (w + 4) - Complex.digamma (((w + 4).re : ℝ) : ℂ)‖ :=
      (Complex.abs_im_le_norm _).trans' (le_abs_self _)
    rw [him0]
    refine h1.trans (hdiff.trans ?_)
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 17 / 4)]
    linarith
  have hi0 : (-w⁻¹).im ≤ 1 := by
    have hpos : 0 < Complex.normSq w :=
      Complex.normSq_pos.mpr (fun h => by rw [h] at hw_im; simp at hw_im; linarith)
    rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg, hw_im]
    have hns : (T / 2) ^ 2 ≤ Complex.normSq w := by
      rw [Complex.normSq_apply, hw_im]
      linarith [sq_nonneg w.re]
    rw [div_le_one hpos]
    nlinarith [sq_nonneg (T / 2 - 1)]
  have hi1 : (-(w + 1)⁻¹).im ≤ 2 / 5 := by
    refine (im_neg_inv_of_re_ge (a := 5 / 4) (by norm_num) (by simp; linarith) (by simp [hw_im]; linarith)).trans ?_
    norm_num
  have hi2 : (-(w + 2)⁻¹).im ≤ 2 / 9 := by
    refine (im_neg_inv_of_re_ge (a := 9 / 4) (by norm_num) (by simp; linarith) (by simp [hw_im]; linarith)).trans ?_
    norm_num
  have hi3 : (-(w + 3)⁻¹).im ≤ 2 / 13 := by
    refine (im_neg_inv_of_re_ge (a := 13 / 4) (by norm_num) (by simp; linarith) (by simp [hw_im]; linarith)).trans ?_
    norm_num
  rw [hrec]
  simp only [Complex.sub_im]
  simp only [Complex.neg_im] at hi0 hi1 hi2 hi3
  linarith

lemma digamma_im_upper_high {σ T : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 3 / 2) (hT : 4 ≤ T) :
    (Complex.digamma (((σ : ℂ) + T * I) / 2)).im ≤ Real.pi / 2 + 1 := by
  let w : ℂ := ((σ : ℂ) + T * I) / 2
  have hw_re : 0 < w.re := by simp [w, Complex.div_ofNat_re]; linarith
  have hw_im : w.im = T / 2 := by simp [w, Complex.div_ofNat_im]
  have hw_im_pos : 0 < w.im := by linarith
  have hst := TernaryGoldbach.RSBounds.BacklundZeta23.StirlingVert.digamma_stirling hw_re
    (by rw [hw_im, abs_of_pos (by linarith)]; linarith)
  have hlog : (Complex.log w).im ≤ Real.pi / 2 := by
    rw [Complex.log_im]
    exact (Complex.arg_lt_pi_div_two_iff.mpr (.inl hw_re)).le
  have hhalf : ‖(1 / 2 : ℂ) / w‖ ≤ 1 / 4 := by
    rw [norm_div, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
    have hwn : 2 ≤ ‖w‖ := by
      have := Complex.abs_im_le_norm w
      rw [hw_im, abs_of_pos (by linarith)] at this
      linarith
    rw [div_le_iff₀ (by linarith : 0 < ‖w‖)]
    linarith
  have hdiff : |(Complex.digamma w).im - (Complex.log w).im| ≤ 1 := by
    have h0 : ‖Complex.digamma w - Complex.log w‖ ≤ 3 / w.im ^ 2 + 1 / 4 := by
      calc ‖Complex.digamma w - Complex.log w‖
          = ‖(Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w) - (1 / 2 : ℂ) / w‖ := by ring_nf
        _ ≤ ‖Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w‖ + ‖(1 / 2 : ℂ) / w‖ := norm_sub_le _ _
        _ ≤ 3 / w.im ^ 2 + 1 / 4 := add_le_add hst hhalf
    have hsq : 4 ≤ w.im ^ 2 := by rw [hw_im]; nlinarith
    have him : |(Complex.digamma w).im - (Complex.log w).im| ≤ ‖Complex.digamma w - Complex.log w‖ := by
      rw [← Complex.sub_im]
      exact Complex.abs_im_le_norm _
    refine him.trans (h0.trans ?_)
    have : 3 / w.im ^ 2 ≤ 3 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsq
    linarith
  linarith [(abs_le.mp hdiff).2]

theorem odd_gamma_phase_error {T : ℝ} (hT : 2 ≤ T) :
    |(2 * TernaryGoldbach.RSBounds.BacklundGammaPhase.phaseIntegral T / Real.pi +
      (1 / Real.pi) *
        ∫ σ in (1 / 2 : ℝ)..(3 / 2), (Complex.digamma (((σ : ℂ) + T * I) / 2)).im) -
      (T / Real.pi) * Real.log (T / (2 * Real.exp 1))| ≤ 0.70 := by
  have hT0 : 0 < T := by linarith
  have hp : 0 < Real.pi := Real.pi_pos
  have hp314 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hgp := TernaryGoldbach.RSBounds.BacklundGammaPhase.gamma_phase_remainder_bound hT0
  have hmain_eq : 2 * (T / 2 * Real.log (T / 2) - T / 2 - Real.pi / 8) / Real.pi =
      (T / Real.pi) * Real.log (T / (2 * Real.exp 1)) - 1 / 4 := by
    have hlog : Real.log (T / (2 * Real.exp 1)) = Real.log (T / 2) - 1 := by
      rw [show T / (2 * Real.exp 1) = (T / 2) / Real.exp 1 by ring,
        Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
    rw [hlog]
    field_simp [hp.ne']
    ring
  have hmain_rem : |2 * TernaryGoldbach.RSBounds.BacklundGammaPhase.phaseIntegral T / Real.pi -
      ((T / Real.pi) * Real.log (T / (2 * Real.exp 1)) - 1 / 4)| ≤ 1 / (2 * Real.pi * T) := by
    have he : 2 * TernaryGoldbach.RSBounds.BacklundGammaPhase.phaseIntegral T / Real.pi -
        ((T / Real.pi) * Real.log (T / (2 * Real.exp 1)) - 1 / 4) =
        (2 / Real.pi) *
          (TernaryGoldbach.RSBounds.BacklundGammaPhase.phaseIntegral T -
            T / 2 * Real.log (T / 2) + T / 2 + Real.pi / 8) := by
      rw [← hmain_eq]
      ring
    rw [he, abs_mul, abs_of_pos (by positivity : 0 < 2 / Real.pi)]
    refine (mul_le_mul_of_nonneg_left hgp (by positivity)).trans_eq ?_
    ring
  let I_odd : ℝ :=
    (1 / Real.pi) * ∫ σ in (1 / 2 : ℝ)..(3 / 2), (Complex.digamma (((σ : ℂ) + T * I) / 2)).im
  have hcont : ContinuousOn (fun σ : ℝ => (Complex.digamma (((σ : ℂ) + T * I) / 2)).im)
      (Set.Icc (1 / 2) (3 / 2)) := by
    have hline : Continuous (fun σ : ℝ => ((σ : ℂ) + T * I) / 2) :=
      (Complex.continuous_ofReal.add continuous_const).div_const 2
    have hmem : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) (3 / 2),
        ((σ : ℂ) + T * I) / 2 ∈ GammaSolution.rightHalfPlane := by
      intro σ hσ
      rw [GammaSolution.mem_rightHalfPlane_iff, Complex.div_ofNat_re, Complex.add_re,
        Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      linarith [hσ.1]
    exact Complex.continuous_im.comp_continuousOn
      (GammaSolution.analyticOnNhd_digamma.continuousOn.comp hline.continuousOn hmem)
  have hint_nonneg : 0 ≤ I_odd := by
    dsimp [I_odd]
    refine mul_nonneg (by positivity) (intervalIntegral.integral_nonneg (by norm_num) fun σ hσ => ?_)
    exact im_digamma_nonneg (by simp [Complex.div_ofNat_re]; linarith [hσ.1])
      (by simp [Complex.div_ofNat_im]; linarith)
  have hint_upper : I_odd ≤ if T ≤ 4 then
      (16 / 17 + 1 + 2 / 5 + 2 / 9 + 2 / 13) / Real.pi else 1 / 2 + 1 / Real.pi := by
    dsimp [I_odd]
    split_ifs with hT4
    · have hi : ∫ σ in (1 / 2 : ℝ)..(3 / 2), (Complex.digamma (((σ : ℂ) + T * I) / 2)).im ≤
          ∫ _σ in (1 / 2 : ℝ)..(3 / 2), (16 / 17 + 1 + 2 / 5 + 2 / 9 + 2 / 13 : ℝ) := by
        refine intervalIntegral.integral_mono_on (by norm_num)
          (hcont.intervalIntegrable_of_Icc (by norm_num))
          (continuousOn_const.intervalIntegrable_of_Icc (by norm_num))
          fun σ hσ => digamma_im_upper_low hσ.1 hσ.2 hT hT4
      rw [intervalIntegral.integral_const, smul_eq_mul, show (3 / 2 : ℝ) - 1 / 2 = 1 by norm_num, one_mul] at hi
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right hi hp.le
    · have hT4' : 4 ≤ T := le_of_not_ge hT4
      have hi : ∫ σ in (1 / 2 : ℝ)..(3 / 2), (Complex.digamma (((σ : ℂ) + T * I) / 2)).im ≤
          ∫ _σ in (1 / 2 : ℝ)..(3 / 2), (Real.pi / 2 + 1 : ℝ) := by
        refine intervalIntegral.integral_mono_on (by norm_num)
          (hcont.intervalIntegrable_of_Icc (by norm_num))
          (continuousOn_const.intervalIntegrable_of_Icc (by norm_num))
          fun σ hσ => digamma_im_upper_high hσ.1 hσ.2 hT4'
      rw [intervalIntegral.integral_const, smul_eq_mul, show (3 / 2 : ℝ) - 1 / 2 = 1 by norm_num, one_mul] at hi
      calc (1 / Real.pi) * ∫ σ in (1 / 2 : ℝ)..(3 / 2), (Complex.digamma (((σ : ℂ) + T * I) / 2)).im
          ≤ (1 / Real.pi) * (Real.pi / 2 + 1) := mul_le_mul_of_nonneg_left hi (by positivity)
        _ = 1 / 2 + 1 / Real.pi := by field_simp [hp.ne']
  have hsplit : (2 * TernaryGoldbach.RSBounds.BacklundGammaPhase.phaseIntegral T / Real.pi + I_odd) -
      (T / Real.pi) * Real.log (T / (2 * Real.exp 1)) =
      (2 * TernaryGoldbach.RSBounds.BacklundGammaPhase.phaseIntegral T / Real.pi -
        ((T / Real.pi) * Real.log (T / (2 * Real.exp 1)) - 1 / 4)) + (I_odd - 1 / 4) := by ring
  rw [show (1 / Real.pi) * ∫ σ in (1 / 2 : ℝ)..(3 / 2), (Complex.digamma (((σ : ℂ) + T * I) / 2)).im = I_odd from rfl,
    hsplit]
  refine (abs_add_le _ _).trans ?_
  by_cases hT4 : T ≤ 4
  · rw [if_pos hT4] at hint_upper
    have hrem : 1 / (2 * Real.pi * T) ≤ 1 / (4 * 3.14) := by
      refine one_div_le_one_div_of_le (by norm_num) ?_
      nlinarith
    have hpi_ub : (16 / 17 + 1 + 2 / 5 + 2 / 9 + 2 / 13 : ℝ) / Real.pi ≤
        (16 / 17 + 1 + 2 / 5 + 2 / 9 + 2 / 13 : ℝ) / 3.14 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp314.le
    have hIabs : |I_odd - 1 / 4| ≤ (16 / 17 + 1 + 2 / 5 + 2 / 9 + 2 / 13 : ℝ) / 3.14 - 1 / 4 := by
      rw [abs_le]
      constructor <;> linarith
    linarith [hmain_rem, hrem, hIabs]
  · rw [if_neg hT4] at hint_upper
    have hT4' : 4 ≤ T := le_of_not_ge hT4
    have hrem : 1 / (2 * Real.pi * T) ≤ 1 / (8 * 3.14) := by
      refine one_div_le_one_div_of_le (by norm_num) ?_
      nlinarith
    have hpi_ub : 1 / Real.pi ≤ 1 / (3.14 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hp314.le
    have hIabs : |I_odd - 1 / 4| ≤ 1 / 4 + 1 / (3.14 : ℝ) := by
      rw [abs_le]
      constructor <;> linarith
    linarith [hmain_rem, hrem, hIabs]

theorem even_gamma_phase_error {T : ℝ} (hT : 2 ≤ T) :
    |2 * TernaryGoldbach.RSBounds.BacklundGammaPhase.phaseIntegral T / Real.pi -
      (T / Real.pi) * Real.log (T / (2 * Real.exp 1))| ≤ 0.33 := by
  have hT0 : 0 < T := by linarith
  have hp : 0 < Real.pi := Real.pi_pos
  have hp314 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hgp := TernaryGoldbach.RSBounds.BacklundGammaPhase.gamma_phase_remainder_bound hT0
  have hmain_eq : 2 * (T / 2 * Real.log (T / 2) - T / 2 - Real.pi / 8) / Real.pi =
      (T / Real.pi) * Real.log (T / (2 * Real.exp 1)) - 1 / 4 := by
    have hlog : Real.log (T / (2 * Real.exp 1)) = Real.log (T / 2) - 1 := by
      rw [show T / (2 * Real.exp 1) = (T / 2) / Real.exp 1 by ring,
        Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
    rw [hlog]
    field_simp [hp.ne']
    ring
  have he : 2 * TernaryGoldbach.RSBounds.BacklundGammaPhase.phaseIntegral T / Real.pi -
      (T / Real.pi) * Real.log (T / (2 * Real.exp 1)) =
      (2 / Real.pi) *
        (TernaryGoldbach.RSBounds.BacklundGammaPhase.phaseIntegral T -
          T / 2 * Real.log (T / 2) + T / 2 + Real.pi / 8) - 1 / 4 := by
    have hlog_eq : (T / Real.pi) * Real.log (T / (2 * Real.exp 1)) =
        2 * (T / 2 * Real.log (T / 2) - T / 2 - Real.pi / 8) / Real.pi + 1 / 4 := by
      linarith [hmain_eq]
    rw [hlog_eq]
    ring
  rw [he]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_of_pos (by positivity : 0 < 2 / Real.pi), abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  have hrem : (2 / Real.pi) * (1 / (4 * T)) ≤ 1 / (4 * 3.14) := by
    rw [show (2 / Real.pi) * (1 / (4 * T)) = 1 / (2 * Real.pi * T) by ring]
    refine one_div_le_one_div_of_le (by norm_num) ?_
    nlinarith
  have h1 := (mul_le_mul_of_nonneg_left hgp (by positivity : 0 ≤ 2 / Real.pi)).trans hrem
  linarith

theorem abs_integral_oddGammaReflectionDifference_le {T δ : ℝ}
    (hT : 1 ≤ T) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4) :
    |∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ),
      (1 / 2) *
        ((Complex.digamma ((((2 - σ : ℝ) : ℂ) + T * I) / 2)).im -
         (Complex.digamma ((((σ + 1 : ℝ) : ℂ) + T * I) / 2)).im)| ≤ 4 / T := by
  have hT0 : 0 < T := by linarith
  let f : ℝ → ℝ := fun σ =>
    (1 / 2) *
      ((Complex.digamma ((((2 - σ : ℝ) : ℂ) + T * I) / 2)).im -
       (Complex.digamma ((((σ + 1 : ℝ) : ℂ) + T * I) / 2)).im)
  have hbound : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) (1 / 2 + δ), |f σ| ≤ 8 * (σ - 1 / 2) / T := by
    intro σ hσ
    have hσ0 : 1 / 2 ≤ σ := hσ.1
    have hσ2 : σ ≤ 5 / 4 := by linarith [hσ.2]
    let w₁ : ℂ := (((σ + 1 : ℝ) : ℂ) + T * I) / 2
    let w₂ : ℂ := (((2 - σ : ℝ) : ℂ) + T * I) / 2
    have hw1_re : 3 / 4 ≤ w₁.re := by simp [w₁, Complex.div_ofNat_re]; linarith
    have hw2_re : 3 / 8 ≤ w₂.re := by simp [w₂, Complex.div_ofNat_re]; linarith
    have hw1_im : w₁.im = T / 2 := by simp [w₁, Complex.div_ofNat_im]
    have hw2_im : w₂.im = T / 2 := by simp [w₂, Complex.div_ofNat_im]
    have hsub_w : w₂ - w₁ = (((1 / 2 - σ : ℝ) : ℂ)) := by
      apply Complex.ext <;> simp [w₁, w₂, Complex.div_ofNat_re, Complex.div_ofNat_im] <;> ring
    have hnorm_w : ‖w₂ - w₁‖ = σ - 1 / 2 := by
      rw [hsub_w, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      ring
    have hb : 0 < T / 2 := by positivity
    have h1re : 1 ≤ (w₂ + 2).re := by simp [w₂, Complex.div_ofNat_re]; linarith
    have h2re : 1 ≤ (w₁ + 2).re := by simp [w₁, Complex.div_ofNat_re]; linarith
    have hshift : ‖Complex.digamma (w₂ + 2) - Complex.digamma (w₁ + 2)‖ ≤ 8 * (σ - 1 / 2) / T := by
      by_cases hT4 : T ≤ 4
      · have hh := TernaryGoldbach.RSBounds.BacklundGammaReflection.norm_digamma_sub_le_of_one_le_re h1re h2re
        rw [add_sub_add_right_eq_sub, hnorm_w] at hh
        refine hh.trans ?_
        rw [le_div_iff₀ hT0]
        nlinarith
      · have hh := CH2Section81.norm_digamma_sub_le
          (show 0 < (w₂ + 2).re by linarith)
          (show 0 < (w₁ + 2).re by linarith)
          (by simp [hw1_im, hw2_im])
          (by simp [hw2_im]; linarith)
        have him2 : (w₂ + 2).im = T / 2 := by simp [hw2_im]
        rw [add_sub_add_right_eq_sub, hnorm_w, him2] at hh
        refine hh.trans_eq ?_
        field_simp [hT0.ne']
        ring
    have hrec0 := TernaryGoldbach.RSBounds.BacklundGammaReflection.norm_inverse_difference hb hw2_im hw1_im
    rw [hnorm_w] at hrec0
    have hrec1 := TernaryGoldbach.RSBounds.BacklundGammaReflection.norm_inverse_difference hb
      (show (w₂ + 1).im = T / 2 by simp [hw2_im]) (show (w₁ + 1).im = T / 2 by simp [hw1_im])
    rw [add_sub_add_right_eq_sub, hnorm_w] at hrec1
    have hdig : ‖Complex.digamma w₂ - Complex.digamma w₁‖ ≤ 16 * (σ - 1 / 2) / T := by
      rw [TernaryGoldbach.RSBounds.BacklundGammaReflection.digamma_eq_add_two_of_im_ne_zero (z := w₂)
          (by rw [hw2_im]; exact hb.ne'),
        TernaryGoldbach.RSBounds.BacklundGammaReflection.digamma_eq_add_two_of_im_ne_zero (z := w₁)
          (by rw [hw1_im]; exact hb.ne')]
      have he : (Complex.digamma (w₂ + 2) - w₂⁻¹ - (w₂ + 1)⁻¹) -
          (Complex.digamma (w₁ + 2) - w₁⁻¹ - (w₁ + 1)⁻¹) =
          (Complex.digamma (w₂ + 2) - Complex.digamma (w₁ + 2)) -
          (w₂⁻¹ - w₁⁻¹) - ((w₂ + 1)⁻¹ - (w₁ + 1)⁻¹) := by ring
      rw [he]
      have hquad : (σ - 1 / 2) / (T / 2) ^ 2 ≤ 4 * (σ - 1 / 2) / T := by
        rw [div_le_div_iff₀ (sq_pos_of_pos hb) hT0]
        have : 0 ≤ (σ - 1 / 2) * T * (T - 1) := mul_nonneg (mul_nonneg (by linarith) hT0.le) (by linarith)
        nlinarith
      calc ‖(Complex.digamma (w₂ + 2) - Complex.digamma (w₁ + 2)) -
              (w₂⁻¹ - w₁⁻¹) - ((w₂ + 1)⁻¹ - (w₁ + 1)⁻¹)‖
          ≤ ‖Complex.digamma (w₂ + 2) - Complex.digamma (w₁ + 2)‖ +
              ‖w₂⁻¹ - w₁⁻¹‖ + ‖(w₂ + 1)⁻¹ - (w₁ + 1)⁻¹‖ := by
            linarith [norm_sub_le (Complex.digamma (w₂ + 2) - Complex.digamma (w₁ + 2)) (w₂⁻¹ - w₁⁻¹),
              norm_sub_le ((Complex.digamma (w₂ + 2) - Complex.digamma (w₁ + 2)) - (w₂⁻¹ - w₁⁻¹)) ((w₂ + 1)⁻¹ - (w₁ + 1)⁻¹)]
        _ ≤ 8 * (σ - 1 / 2) / T + (σ - 1 / 2) / (T / 2) ^ 2 + (σ - 1 / 2) / (T / 2) ^ 2 := by
            gcongr
        _ ≤ 8 * (σ - 1 / 2) / T + 4 * (σ - 1 / 2) / T + 4 * (σ - 1 / 2) / T := by gcongr
        _ = 16 * (σ - 1 / 2) / T := by ring
    have him : |(Complex.digamma w₂).im - (Complex.digamma w₁).im| ≤
        ‖Complex.digamma w₂ - Complex.digamma w₁‖ := by
      rw [← Complex.sub_im]
      exact Complex.abs_im_le_norm _
    dsimp [f]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    refine (mul_le_mul_of_nonneg_left (him.trans hdig) (by norm_num)).trans_eq (by ring)
  have hints : |∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), f σ| ≤ 4 * δ ^ 2 / T := by
    rw [← Real.norm_eq_abs, ← TernaryGoldbach.RSBounds.BacklundGammaReflection.integral_linear_majorant T δ]
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith) ?_
      ((show Continuous (fun σ : ℝ => 8 * (σ - 1 / 2) / T) by fun_prop).intervalIntegrable _ _)
    filter_upwards [] with σ hσ
    rw [Real.norm_eq_abs]
    exact hbound σ (Set.Ioc_subset_Icc_self hσ)
  refine hints.trans ?_
  apply div_le_div_of_nonneg_right _ hT0.le
  nlinarith

end DirichletGammaPhaseOdd

namespace DirichletCountIdentity

open TernaryGoldbach.Explicit

def dirGoodHeight {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) : Prop :=
  ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → |ρ.im| = T → DirichletCharacter.LFunction χ ρ ≠ 0

lemma dirGoodHeight_inv {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {T : ℝ}
    (hg : dirGoodHeight χ T) : dirGoodHeight χ⁻¹ T := by
  intro ρ h1 h2 him h0
  have hconj := DirichletBasics.LFunction_conj χ hχ ρ
  rw [h0, map_zero] at hconj
  exact hg (conj ρ) (by simpa using h1) (by simpa using h2) (by simpa using him) hconj

lemma completedLFunction_ne_zero_of_re_le_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {s : ℂ} (hs : s.re ≤ 0) :
    DirichletCharacter.completedLFunction χ s ≠ 0 := by
  have hχ1' : χ⁻¹ ≠ 1 := fun h => hχ1 (by simpa using congrArg Inv.inv h)
  have hfe := hχ.completedLFunction_one_sub (1 - s)
  rw [sub_sub_cancel] at hfe
  rw [hfe]
  refine mul_ne_zero (mul_ne_zero ?_ (DirichletCharacter.rootNumber_ne_zero hχ)) ?_
  · rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q))
  · exact DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ⁻¹ (.inl hχ1')
      (by simp; linarith)

lemma LFunction_ne_zero_of_re_le_zero_of_im_ne_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    {s : ℂ} (hs : s.re ≤ 0) (him : s.im ≠ 0) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at him; simp at him
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (.inl hs0)]
  refine div_ne_zero (completedLFunction_ne_zero_of_re_le_zero hχ hχ1 hs) ?_
  classical
  rw [DirichletCharacter.gammaFactor]
  split_ifs
  · intro hg
    rw [Complex.Gammaℝ_eq_zero_iff] at hg
    rcases hg with ⟨n, hn⟩
    have him0 : (-(2 * (n : ℂ))).im = 0 := by simp
    rw [← hn] at him0
    exact him him0
  · intro hg
    rw [Complex.Gammaℝ_eq_zero_iff] at hg
    rcases hg with ⟨n, hn⟩
    have him0 : (-(2 * (n : ℂ))).im = 0 := by simp
    have hs1 : (s + 1).im = s.im := by simp
    rw [← hn, hs1] at him0
    exact him him0

lemma LFunction_horizontal_ne_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {T : ℝ} (hT : 0 < T) (hg : dirGoodHeight χ T) (σ : ℝ) :
    DirichletCharacter.LFunction χ ((σ : ℂ) + T * I) ≠ 0 := by
  by_cases h1 : 1 ≤ σ
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ1) (by simp; exact h1)
  · by_cases h0 : σ ≤ 0
    · exact LFunction_ne_zero_of_re_le_zero_of_im_ne_zero hχ hχ1 (by simp; exact h0)
        (by simp; exact hT.ne')
    · push Not at h0 h1
      exact hg ((σ : ℂ) + T * I) (by simp [h0]) (by simp [h1]) (by simp [abs_of_pos hT])

lemma completedLFunction_noZerosOnSides {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {T : ℝ} (hT : 0 < T) (hg : dirGoodHeight χ T) :
    NoZerosOnSides (DirichletCharacter.completedLFunction χ)
      (-(1 / 4 : ℂ) - T * I) ((5 / 4 : ℂ) + T * I) := by
  have hline : ∀ σ t : ℝ, |t| = T →
      DirichletCharacter.completedLFunction χ ((σ : ℂ) + t * I) ≠ 0 := by
    intro σ t ht
    by_cases h1 : 1 ≤ σ
    · exact DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (.inl hχ1) (by simp; exact h1)
    · by_cases h0 : σ ≤ 0
      · exact completedLFunction_ne_zero_of_re_le_zero hχ hχ1 (by simp; exact h0)
      · push Not at h0 h1
        have hnz : DirichletCharacter.LFunction χ ((σ : ℂ) + t * I) ≠ 0 :=
          hg ((σ : ℂ) + t * I) (by simp [h0]) (by simp [h1]) (by simp [ht])
        have hpos : (σ : ℂ) + t * I ≠ 0 := fun h => by
          have := congrArg Complex.re h; simp at this; linarith
        rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ _ (.inl hpos)] at hnz
        exact left_ne_zero_of_mul hnz
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x _
    convert hline x (-T) (by simp [abs_of_pos hT]) using 2
    apply Complex.ext <;> simp
  · intro x _
    convert hline x T (by simp [abs_of_pos hT]) using 2
    apply Complex.ext <;> simp
  · intro y _
    exact DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (.inl hχ1) (by simp; norm_num)
  · intro y _
    exact completedLFunction_ne_zero_of_re_le_zero hχ hχ1 (by simp)

private lemma ne_neg_natCast_of_re_pos_or_im_ne_zero {w : ℂ} (hw : 0 < w.re ∨ w.im ≠ 0) (m : ℕ) :
    w ≠ -(m : ℂ) := by
  intro h
  rcases hw with hr | hi
  · have := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.natCast_re] at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  · have := congrArg Complex.im h
    simp only [Complex.neg_im, Complex.natCast_im, neg_zero] at this
    exact hi this

lemma gammaFactor_analyticAt_of_re_pos_or_im_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re ∨ s.im ≠ 0) :
    AnalyticAt ℂ (DirichletCharacter.gammaFactor χ) s := by
  classical
  have hU : IsOpen {z : ℂ | 0 < z.re ∨ z.im ≠ 0} := by
    have h1 : {z : ℂ | 0 < z.re ∨ z.im ≠ 0} =
        {z : ℂ | (0 : ℝ) < z.re} ∪ Complex.im ⁻¹' {y : ℝ | y ≠ 0} := by
      ext z; simp
    rw [h1]
    exact (isOpen_lt continuous_const Complex.continuous_re).union
      (isOpen_ne.preimage Complex.continuous_im)
  have hconst_fn : AnalyticOnNhd ℂ (fun z : ℂ =>
      if χ.Even then Complex.Gammaℝ z else Complex.Gammaℝ (z + 1))
      {z : ℂ | 0 < z.re ∨ z.im ≠ 0} := by
    split_ifs
    · intro z hz
      rw [show Complex.Gammaℝ = fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) from
        funext Complex.Gammaℝ_def]
      refine AnalyticAt.mul ?_ ?_
      · exact ((differentiable_id.neg.div_const 2).const_cpow
          (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).analyticAt z
      · have hga : AnalyticAt ℂ Complex.Gamma (z / 2) :=
          Complex.analyticAt_iff_eventually_differentiableAt.mpr
            (Filter.eventually_of_mem
              (hU.mem_nhds (hz.imp (fun h => by simp; linarith)
                (fun h => by simp [Complex.div_ofNat_im, h])))
              fun w hw => Complex.differentiableAt_Gamma w
                (ne_neg_natCast_of_re_pos_or_im_ne_zero hw))
        exact hga.comp (f := fun w : ℂ => w / 2) ((differentiable_id.div_const 2).analyticAt z)
    · intro z hz
      rw [show (fun w : ℂ => Complex.Gammaℝ (w + 1)) =
          fun w : ℂ => (Real.pi : ℂ) ^ (-(w + 1) / 2) * Complex.Gamma ((w + 1) / 2) from
        funext fun w => Complex.Gammaℝ_def (w + 1)]
      refine AnalyticAt.mul ?_ ?_
      · exact (((differentiable_id.add_const 1).neg.div_const 2).const_cpow
          (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).analyticAt z
      · have hga : AnalyticAt ℂ Complex.Gamma ((z + 1) / 2) :=
          Complex.analyticAt_iff_eventually_differentiableAt.mpr
            (Filter.eventually_of_mem
              (hU.mem_nhds (hz.imp (fun h => by simp [Complex.div_ofNat_re]; linarith)
                (fun h => by simp [Complex.div_ofNat_im, h])))
              fun w hw => Complex.differentiableAt_Gamma w
                (ne_neg_natCast_of_re_pos_or_im_ne_zero hw))
        exact hga.comp (f := fun w : ℂ => (w + 1) / 2)
          (((differentiable_id.add_const 1).div_const 2).analyticAt z)
  have hfun : DirichletCharacter.gammaFactor χ =
      fun z => if χ.Even then Complex.Gammaℝ z else Complex.Gammaℝ (z + 1) := by
    ext z; rw [DirichletCharacter.gammaFactor]
  rw [hfun]
  exact hconst_fn s hs

lemma gammaFactor_ne_zero_of_re_pos_or_im_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re ∨ s.im ≠ 0) :
    DirichletCharacter.gammaFactor χ s ≠ 0 := by
  classical
  rw [DirichletCharacter.gammaFactor]
  split_ifs
  · intro hg
    rw [Complex.Gammaℝ_eq_zero_iff] at hg
    rcases hg with ⟨n, hn⟩
    have : s = -((2 * n : ℕ) : ℂ) := by push_cast; linear_combination hn
    exact ne_neg_natCast_of_re_pos_or_im_ne_zero hs (2 * n) this
  · intro hg
    rw [Complex.Gammaℝ_eq_zero_iff] at hg
    rcases hg with ⟨n, hn⟩
    have : s + 1 = -((2 * n : ℕ) : ℂ) := by push_cast; linear_combination hn
    exact ne_neg_natCast_of_re_pos_or_im_ne_zero
      (hs.imp (fun h => by simp; linarith) (fun h => by simp [h])) (2 * n) this

lemma gammaFactor_analyticAt_of_re_pos {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (DirichletCharacter.gammaFactor χ) s :=
  gammaFactor_analyticAt_of_re_pos_or_im_ne_zero χ (.inl hs)

lemma gammaFactor_ne_zero_of_re_pos {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.gammaFactor χ s ≠ 0 :=
  gammaFactor_ne_zero_of_re_pos_or_im_ne_zero χ (.inl hs)

lemma analyticOrderNatAt_completed_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1) {u : ℂ} (hu : 0 < u.re) :
    analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u =
      analyticOrderNatAt (DirichletCharacter.LFunction χ) u := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have heq : DirichletCharacter.completedLFunction χ =ᶠ[𝓝 u]
      fun z => DirichletCharacter.LFunction χ z * DirichletCharacter.gammaFactor χ z := by
    refine Filter.eventually_of_mem (hopen.mem_nhds hu) fun z hz => ?_
    have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
    exact ((eq_div_iff (gammaFactor_ne_zero_of_re_pos χ hz)).mp
      (DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (.inl hz0))).symm
  rw [analyticOrderNatAt, analyticOrderAt_congr heq, ← analyticOrderNatAt]
  have hLa : AnalyticAt ℂ (DirichletCharacter.LFunction χ) u :=
    (DirichletCharacter.differentiable_LFunction hχ1).analyticAt u
  have hga : AnalyticAt ℂ (DirichletCharacter.gammaFactor χ) u :=
    gammaFactor_analyticAt_of_re_pos χ hu
  have hg0 : analyticOrderNatAt (DirichletCharacter.gammaFactor χ) u = 0 := by
    rw [analyticOrderNatAt, hga.analyticOrderAt_eq_zero.mpr (gammaFactor_ne_zero_of_re_pos χ hu)]
    rfl
  have hLntop : analyticOrderAt (DirichletCharacter.LFunction χ) u ≠ ⊤ := by
    intro htop
    have hzero := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun z _ => (DirichletCharacter.differentiable_LFunction hχ1).analyticAt z)
      isPreconnected_univ (Set.mem_univ u) (analyticOrderAt_eq_top.mp htop) (Set.mem_univ (2 : ℂ))
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ1) (by simp) hzero
  have hgntop : analyticOrderAt (DirichletCharacter.gammaFactor χ) u ≠ ⊤ := by
    rw [hga.analyticOrderAt_eq_zero.mpr (gammaFactor_ne_zero_of_re_pos χ hu)]
    simp
  rw [analyticOrderNatAt_fun_mul (hf' := hLntop) (hg' := hgntop) hLa hga, hg0, add_zero]

noncomputable def dirZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) : Finset ℂ :=
  (zerosIn (DirichletCharacter.completedLFunction χ) (5 / 4 : ℂ) (2 * (T + 3)) (T + 3)).filter
    fun u => 0 < u.re ∧ u.re < 1 ∧ |u.im| ≤ T

lemma mem_dirZeros_iff {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1)
    {T : ℝ} (hT : 0 < T) {s : ℂ} :
    s ∈ dirZeros χ T ↔
      0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ DirichletCharacter.LFunction χ s = 0 := by
  classical
  have hf : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    DirichletCharacter.differentiable_completedLFunction hχ1
  rw [dirZeros, Finset.mem_filter, zerosIn, Finset.mem_filter, Set.Finite.mem_toFinset,
    Function.mem_support]
  constructor
  · rintro ⟨⟨hdiv, _⟩, hs1, hs2, hsT⟩
    have hsb : s ∈ Metric.closedBall (5 / 4 : ℂ) (2 * (T + 3)) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hre : |s.re - 5 / 4| ≤ 5 / 4 := by rw [abs_le]; constructor <;> linarith
      have hnorm : ‖s - (5 / 4 : ℂ)‖ ≤ |s.re - 5 / 4| + |s.im| := by
        simpa [Complex.sub_re, Complex.sub_im] using Complex.norm_le_abs_re_add_abs_im (s - (5 / 4 : ℂ))
      linarith
    rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
      (fun z _ => hf.analyticAt z) hsb] at hdiv
    have hcomp0 : DirichletCharacter.completedLFunction χ s = 0 := by
      by_contra hsne
      exact hdiv (by simp [(hf.analyticAt s).analyticOrderAt_eq_zero.mpr hsne])
    have hs0 : s ≠ 0 := fun h => by rw [h] at hs1; simp at hs1
    refine ⟨hs1, hs2, hsT, ?_⟩
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (.inl hs0), hcomp0, zero_div]
  · rintro ⟨hs1, hs2, hsT, hs0⟩
    have hne : s ≠ 0 := fun h => by rw [h] at hs1; simp at hs1
    have hcomp0 : DirichletCharacter.completedLFunction χ s = 0 := by
      have heq := (eq_div_iff (gammaFactor_ne_zero_of_re_pos χ hs1)).mp
        (DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (.inl hne))
      rw [hs0, zero_mul] at heq
      exact heq.symm
    have hball : ‖s - (5 / 4 : ℂ)‖ < T + 3 := by
      have hre : |s.re - 5 / 4| ≤ 5 / 4 := by rw [abs_le]; constructor <;> linarith
      have hnorm : ‖s - (5 / 4 : ℂ)‖ ≤ |s.re - 5 / 4| + |s.im| := by
        simpa [Complex.sub_re, Complex.sub_im] using Complex.norm_le_abs_re_add_abs_im (s - (5 / 4 : ℂ))
      linarith
    have hsb : s ∈ Metric.closedBall (5 / 4 : ℂ) (2 * (T + 3)) := by
      rw [Metric.mem_closedBall, dist_eq_norm]; linarith
    refine ⟨⟨?_, hball⟩, hs1, hs2, hsT⟩
    rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply (fun z _ => hf.analyticAt z) hsb]
    have hpos : analyticOrderAt (DirichletCharacter.completedLFunction χ) s ≠ 0 :=
      (hf.analyticAt s).analyticOrderAt_ne_zero.mpr hcomp0
    have hntop : analyticOrderAt (DirichletCharacter.completedLFunction χ) s ≠ ⊤ := by
      intro htop
      have hzero := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (fun z _ => hf.analyticAt z) isPreconnected_univ (Set.mem_univ s)
        (analyticOrderAt_eq_top.mp htop) (Set.mem_univ (5 / 4 : ℂ))
      exact DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (.inl hχ1)
        (by simp; norm_num) hzero
    intro hdiv0
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hntop
    rw [← hk] at hpos hdiv0
    simp only [ENat.map_natCast, WithTop.untop₀_coe, Nat.cast_eq_zero] at hdiv0
    exact hpos (by rw [hdiv0]; rfl)

open Classical in
lemma logDeriv_gammaFactor_of_re_pos_or_im_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re ∨ s.im ≠ 0) :
    logDeriv (DirichletCharacter.gammaFactor χ) s =
      -(1 / 2 : ℂ) * (Real.log Real.pi : ℂ) +
        (1 / 2 : ℂ) * Complex.digamma (if χ.Even then s / 2 else (s + 1) / 2) := by
  classical
  have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpow_hd : ∀ u : ℂ,
      HasDerivAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2))
        ((-1 / 2 : ℂ) * Complex.log (Real.pi : ℂ) * (Real.pi : ℂ) ^ (-u / 2)) u := by
    intro u
    have h1 : HasDerivAt (fun w : ℂ => -w / 2) (-1 / 2) u :=
      ((hasDerivAt_id u).neg.div_const 2).congr_deriv (by ring)
    exact (h1.const_cpow (Or.inl hpi0)).congr_deriv (by ring)
  have hpow_ne : ∀ u : ℂ, (Real.pi : ℂ) ^ (-u / 2) ≠ 0 :=
    fun u => (Complex.cpow_ne_zero_iff.mpr (Or.inl hpi0))
  have hlogpi : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
    (Complex.ofReal_log Real.pi_pos.le).symm
  have hs_half : 0 < (s / 2).re ∨ (s / 2).im ≠ 0 :=
    hs.imp (fun h => by simp; linarith) (fun h => by simp [Complex.div_ofNat_im, h])
  have hs_half1 : 0 < ((s + 1) / 2).re ∨ ((s + 1) / 2).im ≠ 0 :=
    hs.imp (fun h => by simp [Complex.div_ofNat_re]; linarith)
      (fun h => by simp [Complex.div_ofNat_im, h])
  have hfn_eq : DirichletCharacter.gammaFactor χ =
      fun w => if χ.Even then Complex.Gammaℝ w else Complex.Gammaℝ (w + 1) := by
    ext w; rw [DirichletCharacter.gammaFactor]
  rw [hfn_eq]
  split_ifs with hev
  · have heq : (fun w : ℂ => Complex.Gammaℝ w) =ᶠ[𝓝 s]
        fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) :=
      Filter.Eventually.of_forall fun w => Complex.Gammaℝ_def w
    rw [(logDeriv_congr_nhds heq).eq_of_nhds]
    have hGne : Complex.Gamma (s / 2) ≠ 0 :=
      Complex.Gamma_ne_zero (ne_neg_natCast_of_re_pos_or_im_ne_zero hs_half)
    have hGdiff : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2)) s :=
      (Complex.differentiableAt_Gamma (s / 2)
        (ne_neg_natCast_of_re_pos_or_im_ne_zero hs_half)).comp s ((differentiableAt_id).div_const 2)
    have hGlog : logDeriv (fun w : ℂ => Complex.Gamma (w / 2)) s =
        (1 / 2 : ℂ) * Complex.digamma (s / 2) := by
      simpa only [id_eq] using ((hasDerivAt_id s).div_const 2).logDeriv_Gamma
        (ne_neg_natCast_of_re_pos_or_im_ne_zero hs_half)
    rw [logDeriv_fun_mul s (hpow_ne s) hGne (hpow_hd s).differentiableAt hGdiff,
      logDeriv_apply, (hpow_hd s).deriv, hGlog, hlogpi]
    field_simp [hpow_ne s]
  · have heq : (fun w : ℂ => Complex.Gammaℝ (w + 1)) =ᶠ[𝓝 s]
        fun w : ℂ => (Real.pi : ℂ) ^ (-(w + 1) / 2) * Complex.Gamma ((w + 1) / 2) :=
      Filter.Eventually.of_forall fun w => Complex.Gammaℝ_def (w + 1)
    rw [(logDeriv_congr_nhds heq).eq_of_nhds]
    have hpow2_hd : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) ^ (-(w + 1) / 2))
        ((-1 / 2 : ℂ) * Complex.log (Real.pi : ℂ) * (Real.pi : ℂ) ^ (-(s + 1) / 2)) s := by
      have h1 : HasDerivAt (fun w : ℂ => -(w + 1) / 2) (-1 / 2) s :=
        (((hasDerivAt_id s).add_const 1).neg.div_const 2).congr_deriv (by ring)
      exact (h1.const_cpow (Or.inl hpi0)).congr_deriv (by ring)
    have hGne : Complex.Gamma ((s + 1) / 2) ≠ 0 :=
      Complex.Gamma_ne_zero (ne_neg_natCast_of_re_pos_or_im_ne_zero hs_half1)
    have hGdiff : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma ((w + 1) / 2)) s :=
      (Complex.differentiableAt_Gamma ((s + 1) / 2)
        (ne_neg_natCast_of_re_pos_or_im_ne_zero hs_half1)).comp s
        (((differentiableAt_id).add_const 1).div_const 2)
    have hGlog : logDeriv (fun w : ℂ => Complex.Gamma ((w + 1) / 2)) s =
        (1 / 2 : ℂ) * Complex.digamma ((s + 1) / 2) := by
      simpa only [id_eq] using (((hasDerivAt_id s).add_const 1).div_const 2).logDeriv_Gamma
        (ne_neg_natCast_of_re_pos_or_im_ne_zero hs_half1)
    rw [logDeriv_fun_mul s (hpow_ne (s + 1)) hGne hpow2_hd.differentiableAt hGdiff,
      logDeriv_apply, hpow2_hd.deriv, hGlog, hlogpi]
    field_simp [hpow_ne (s + 1)]

open Classical in
lemma logDeriv_gammaFactor_of_re_pos {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    logDeriv (DirichletCharacter.gammaFactor χ) s =
      -(1 / 2 : ℂ) * (Real.log Real.pi : ℂ) +
        (1 / 2 : ℂ) * Complex.digamma (if χ.Even then s / 2 else (s + 1) / 2) := by
  classical
  exact logDeriv_gammaFactor_of_re_pos_or_im_ne_zero χ (.inl hs)

lemma logDeriv_completed_eq_add_of_re_pos_or_im_ne_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1) {s : ℂ} (hs : 0 < s.re ∨ s.im ≠ 0)
    (hL : DirichletCharacter.LFunction χ s ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) s =
      logDeriv (DirichletCharacter.LFunction χ) s +
        logDeriv (DirichletCharacter.gammaFactor χ) s := by
  have hopen : IsOpen {z : ℂ | 0 < z.re ∨ z.im ≠ 0} := by
    have h1 : {z : ℂ | 0 < z.re ∨ z.im ≠ 0} =
        {z : ℂ | (0 : ℝ) < z.re} ∪ Complex.im ⁻¹' {y : ℝ | y ≠ 0} := by
      ext z; simp
    rw [h1]
    exact (isOpen_lt continuous_const Complex.continuous_re).union
      (isOpen_ne.preimage Complex.continuous_im)
  have heq : DirichletCharacter.completedLFunction χ =ᶠ[𝓝 s]
      fun z => DirichletCharacter.LFunction χ z * DirichletCharacter.gammaFactor χ z := by
    refine Filter.eventually_of_mem (hopen.mem_nhds hs) fun z hz => ?_
    have hz0 : z ≠ 0 := fun h => by subst h; simp at hz
    exact ((eq_div_iff (gammaFactor_ne_zero_of_re_pos_or_im_ne_zero χ hz)).mp
      (DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (.inl hz0))).symm
  rw [(logDeriv_congr_nhds heq).eq_of_nhds]
  exact logDeriv_fun_mul s hL (gammaFactor_ne_zero_of_re_pos_or_im_ne_zero χ hs)
    ((DirichletCharacter.differentiable_LFunction hχ1) s)
    (gammaFactor_analyticAt_of_re_pos_or_im_ne_zero χ hs).differentiableAt

lemma logDeriv_completed_eq_add_of_re_pos {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1) {s : ℂ} (hs : 0 < s.re)
    (hL : DirichletCharacter.LFunction χ s ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) s =
      logDeriv (DirichletCharacter.LFunction χ) s +
        logDeriv (DirichletCharacter.gammaFactor χ) s :=
  logDeriv_completed_eq_add_of_re_pos_or_im_ne_zero χ hχ1 (.inl hs) hL

lemma logDeriv_completedLFunction_conj {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ1 : χ ≠ 1) (s : ℂ) :
    logDeriv (DirichletCharacter.completedLFunction χ) (conj s) =
      conj (logDeriv (DirichletCharacter.completedLFunction χ⁻¹) s) := by
  have hχ1' : χ⁻¹ ≠ 1 := fun h => hχ1 (by simpa using congrArg Inv.inv h)
  have hd_conj : deriv (DirichletCharacter.completedLFunction χ) (conj s) =
      conj (deriv (DirichletCharacter.completedLFunction χ⁻¹) s) := by
    have hfn : DirichletCharacter.completedLFunction χ⁻¹ =
        fun z => conj (DirichletCharacter.completedLFunction χ (conj z)) := by
      ext z
      have h0 := DirichletBasics.completedLFunction_conj χ⁻¹ hχ1' (conj z)
      rw [Complex.conj_conj, inv_inv] at h0
      exact h0
    have hs_der : HasDerivAt (DirichletCharacter.completedLFunction χ)
        (deriv (DirichletCharacter.completedLFunction χ) (conj s)) (conj s) :=
      ((DirichletCharacter.differentiable_completedLFunction hχ1) _).hasDerivAt
    have hconj_der : HasDerivAt (DirichletCharacter.completedLFunction χ⁻¹)
        (conj (deriv (DirichletCharacter.completedLFunction χ) (conj s))) s := by
      simpa only [← hfn, Function.comp_def, Complex.conj_conj] using hs_der.conj_conj
    have heq := congrArg conj hconj_der.deriv
    simpa [Complex.conj_conj] using heq.symm
  rw [logDeriv_apply, logDeriv_apply, hd_conj, DirichletBasics.completedLFunction_conj χ hχ1 s,
    map_div₀]

lemma logDeriv_LFunction_conj {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ1 : χ ≠ 1) (s : ℂ) :
    logDeriv (DirichletCharacter.LFunction χ) (conj s) =
      conj (logDeriv (DirichletCharacter.LFunction χ⁻¹) s) := by
  have hχ1' : χ⁻¹ ≠ 1 := fun h => hχ1 (by simpa using congrArg Inv.inv h)
  have hd : deriv (DirichletCharacter.LFunction χ) (conj s) =
      conj (deriv (DirichletCharacter.LFunction χ⁻¹) s) := by
    have hfn : DirichletCharacter.LFunction χ⁻¹ =
        fun z => conj (DirichletCharacter.LFunction χ (conj z)) := by
      ext z
      have h0 := DirichletBasics.LFunction_conj χ⁻¹ hχ1' (conj z)
      rw [Complex.conj_conj, inv_inv] at h0
      exact h0
    have hs_der : HasDerivAt (DirichletCharacter.LFunction χ)
        (deriv (DirichletCharacter.LFunction χ) (conj s)) (conj s) :=
      ((DirichletCharacter.differentiable_LFunction hχ1) _).hasDerivAt
    have hconj_der : HasDerivAt (DirichletCharacter.LFunction χ⁻¹)
        (conj (deriv (DirichletCharacter.LFunction χ) (conj s))) s := by
      simpa only [← hfn, Function.comp_def, Complex.conj_conj] using hs_der.conj_conj
    have heq := congrArg conj hconj_der.deriv
    simpa [Complex.conj_conj] using heq.symm
  rw [logDeriv_apply, logDeriv_apply, hd, DirichletBasics.LFunction_conj χ hχ1 s,
    map_div₀]

lemma logDeriv_completedLFunction_one_sub {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {s : ℂ}
    (hs : DirichletCharacter.completedLFunction χ⁻¹ (1 - s) ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) s =
      -(Real.log q : ℂ) - logDeriv (DirichletCharacter.completedLFunction χ⁻¹) (1 - s) := by
  have hχ1' : χ⁻¹ ≠ 1 := fun h => hχ1 (by simpa using congrArg Inv.inv h)
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hfn : DirichletCharacter.completedLFunction χ = fun z : ℂ =>
      DirichletCharacter.rootNumber χ * (q : ℂ) ^ (1 / 2 - z) *
        DirichletCharacter.completedLFunction χ⁻¹ (1 - z) := by
    ext z
    have hfe := hχ.completedLFunction_one_sub (1 - z)
    rw [sub_sub_cancel] at hfe
    rw [hfe, show (1 - z - 1 / 2 : ℂ) = 1 / 2 - z by ring]
    ring
  rw [hfn]
  have hpow_ne : (q : ℂ) ^ (1 / 2 - s) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hq0)
  have hpow_hd : HasDerivAt (fun z : ℂ => DirichletCharacter.rootNumber χ * (q : ℂ) ^ (1 / 2 - z))
      (DirichletCharacter.rootNumber χ * (-Complex.log (q : ℂ) * (q : ℂ) ^ (1 / 2 - s))) s := by
    have hd1 : HasDerivAt (fun z : ℂ => (1 / 2 : ℂ) - z) (-1) s :=
      ((hasDerivAt_const s (1 / 2 : ℂ)).sub (hasDerivAt_id s)).congr_deriv (by ring)
    have hd := (hd1.const_cpow (Or.inl hq0)).const_mul (DirichletCharacter.rootNumber χ)
    exact hd.congr_deriv (by ring)
  have hc_ne : DirichletCharacter.rootNumber χ * (q : ℂ) ^ (1 / 2 - s) ≠ 0 :=
    mul_ne_zero (DirichletCharacter.rootNumber_ne_zero hχ) hpow_ne
  have hc2_hd : HasDerivAt (fun z : ℂ => DirichletCharacter.completedLFunction χ⁻¹ (1 - z))
      (deriv (DirichletCharacter.completedLFunction χ⁻¹) (1 - s) * (-1)) s := by
    have hd1 := ((DirichletCharacter.differentiable_completedLFunction hχ1') (1 - s)).hasDerivAt
    have hd2 : HasDerivAt (fun z : ℂ => (1 : ℂ) - z) (-1) s :=
      ((hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id s)).congr_deriv (by ring)
    exact hd1.comp s hd2
  have h1 := logDeriv_fun_mul (f := fun z : ℂ => DirichletCharacter.rootNumber χ * (q : ℂ) ^ (1 / 2 - z))
    (g := fun z : ℂ => DirichletCharacter.completedLFunction χ⁻¹ (1 - z))
    s hc_ne hs hpow_hd.differentiableAt hc2_hd.differentiableAt
  have hlogq : Complex.log (q : ℂ) = (Real.log q : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg q)]
  have hterm1 : logDeriv (fun z : ℂ => DirichletCharacter.rootNumber χ * (q : ℂ) ^ (1 / 2 - z)) s =
      -(Real.log q : ℂ) := by
    rw [logDeriv_apply, hpow_hd.deriv, hlogq,
      mul_div_mul_left _ _ (DirichletCharacter.rootNumber_ne_zero hχ),
      mul_div_cancel_right₀ _ hpow_ne]
  have hterm2 : logDeriv (fun z : ℂ => DirichletCharacter.completedLFunction χ⁻¹ (1 - z)) s =
      -logDeriv (DirichletCharacter.completedLFunction χ⁻¹) (1 - s) := by
    rw [logDeriv_apply, hc2_hd.deriv, logDeriv_apply]
    ring
  rw [h1, hterm1, hterm2]
  ring

open Classical in
theorem count_identity_dir {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {T : ℝ} (hT : 2 ≤ T)
    (hgood : dirGoodHeight χ T) :
    |((∑ ρ ∈ dirZeros χ T, analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ) -
      (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
      1 +
      |∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
        (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + T * I)).im| / Real.pi +
      |∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
        (logDeriv (DirichletCharacter.LFunction χ⁻¹) ((σ : ℂ) + T * I)).im| / Real.pi +
      (if χ.Even then 0.33 else 0.70) := by
  classical
  have hχ1 : χ ≠ 1 := DirichletBasics.ne_one_of_isPrimitive_of_two_le hq hχ
  have hχ1' : χ⁻¹ ≠ 1 := fun h => hχ1 (by simpa using congrArg Inv.inv h)
  have hT0 : 0 < T := by linarith
  have hp : 0 < Real.pi := Real.pi_pos
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  let Λ := DirichletCharacter.completedLFunction χ
  let Λ' := DirichletCharacter.completedLFunction χ⁻¹
  let L := DirichletCharacter.LFunction χ
  let L' := DirichletCharacter.LFunction χ⁻¹
  let z0 : ℂ := -(1 / 4 : ℂ) - T * I
  let w0 : ℂ := (5 / 4 : ℂ) + T * I
  have hzre : z0.re = (-1 / 4 : ℝ) := by simp [z0]; norm_num
  have hwre : w0.re = (5 / 4 : ℝ) := by simp [w0]
  have hzim : z0.im = -T := by simp [z0]
  have hwim : w0.im = T := by simp [w0]
  have hΛ_ana : AnalyticOnNhd ℂ Λ Set.univ := fun z _ =>
    (DirichletCharacter.differentiable_completedLFunction hχ1).analyticAt z
  have hL_ana : AnalyticOnNhd ℂ L Set.univ := fun z _ =>
    (DirichletCharacter.differentiable_LFunction hχ1).analyticAt z
  let Rbox : ℝ := 2 * (T + 3)
  have hRbox : 0 < Rbox := by dsimp [Rbox]; linarith
  have hrect : [[z0.re, w0.re]] ×ℂ [[z0.im, w0.im]] ⊆ Metric.ball (5 / 4 : ℂ) (Rbox / 2) := by
    intro u hu
    rw [mem_reProdIm, hzre, hwre, hzim, hwim, Set.uIcc_of_le (by norm_num),
      Set.uIcc_of_le (by linarith)] at hu
    rw [Metric.mem_ball, dist_eq_norm]
    have hre : |u.re - 5 / 4| ≤ 3 / 2 := by
      rw [abs_le]; constructor <;> linarith [hu.1.1, hu.1.2]
    have him : |u.im| ≤ T := by
      rw [abs_le]; constructor <;> linarith [hu.2.1, hu.2.2]
    have hnorm : ‖u - (5 / 4 : ℂ)‖ ≤ |u.re - 5 / 4| + |u.im| := by
      simpa [Complex.sub_re, Complex.sub_im] using Complex.norm_le_abs_re_add_abs_im (u - (5 / 4 : ℂ))
    dsimp [Rbox]
    linarith
  have hsides := completedLFunction_noZerosOnSides hχ hχ1 hT0 hgood
  have hri := rectInt_logDeriv_mul (DirichletCharacter.differentiable_completedLFunction hχ1)
    hRbox (DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (.inl hχ1) (by norm_num))
    (by rw [hzre, hwre]; norm_num) (by rw [hzim, hwim]; linarith) hrect hsides
    isOpen_univ (Set.subset_univ _) (differentiableOn_const (1 : ℂ))
  have hsum_eq : (zerosIn Λ (5 / 4 : ℂ) Rbox (Rbox / 2)).filter
      (fun u => z0.re < u.re ∧ u.re < w0.re ∧ z0.im < u.im ∧ u.im < w0.im) =
      dirZeros χ T := by
    ext u
    rw [Finset.mem_filter, dirZeros, Finset.mem_filter]
    constructor
    · rintro ⟨hu, hu1, hu2, hu3, hu4⟩
      have hu_mem := mem_zerosIn hu
      have hsb : u ∈ Metric.closedBall (5 / 4 : ℂ) Rbox := by
        rw [Metric.mem_closedBall, dist_eq_norm]; linarith [hu_mem.1]
      have hf := DirichletCharacter.differentiable_completedLFunction hχ1
      have hdiv := hu_mem.2
      rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply (fun z _ => hf.analyticAt z) hsb] at hdiv
      have hcomp0 : Λ u = 0 := by
        by_contra hne
        exact hdiv (by simp [(hf.analyticAt u).analyticOrderAt_eq_zero.mpr hne])
      have hu_pos : 0 < u.re := by
        by_contra hle; push Not at hle
        exact completedLFunction_ne_zero_of_re_le_zero hχ hχ1 hle hcomp0
      have hu_lt1 : u.re < 1 := by
        by_contra hge; push Not at hge
        exact DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (.inl hχ1) hge hcomp0
      have hu_im : |u.im| ≤ T := by
        rw [hzim] at hu3
        rw [hwim] at hu4
        rw [abs_le]; constructor <;> linarith
      have hu' : u ∈ zerosIn (DirichletCharacter.completedLFunction χ) (5 / 4) (2 * (T + 3)) (T + 3) := by
        dsimp [Λ, Rbox] at hu
        rw [show 2 * (T + 3) / 2 = T + 3 by ring] at hu
        exact hu
      exact ⟨hu', hu_pos, hu_lt1, hu_im⟩
    · rintro ⟨hu, hu1, hu2, hu3⟩
      have hu_mem := mem_zerosIn hu
      have hsb : u ∈ Metric.closedBall (5 / 4 : ℂ) Rbox := by
        rw [Metric.mem_closedBall, dist_eq_norm]; linarith [hu_mem.1]
      have hf := DirichletCharacter.differentiable_completedLFunction hχ1
      have hdiv := hu_mem.2
      rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply (fun z _ => hf.analyticAt z) hsb] at hdiv
      have hcomp0 : Λ u = 0 := by
        by_contra hne
        exact hdiv (by simp [(hf.analyticAt u).analyticOrderAt_eq_zero.mpr hne])
      have hu0 : u ≠ 0 := fun h => by rw [h] at hu1; simp at hu1
      have hL0 : L u = 0 := by
        dsimp [L]
        dsimp [Λ] at hcomp0
        rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ u (.inl hu0), hcomp0, zero_div]
      have him_lt : |u.im| < T := lt_of_le_of_ne hu3 fun heq => hgood u hu1 hu2 heq hL0
      have hu' : u ∈ zerosIn Λ (5 / 4) Rbox (Rbox / 2) := by
        dsimp [Λ, Rbox]
        rw [show 2 * (T + 3) / 2 = T + 3 by ring]
        exact hu
      refine ⟨hu', ?_, ?_, ?_, ?_⟩
      · rw [hzre]; linarith
      · rw [hwre]; linarith
      · rw [hzim]; linarith [(abs_lt.mp him_lt).1]
      · rw [hwim]; linarith [(abs_lt.mp him_lt).2]
  have hcount_eq : ((∑ ρ ∈ dirZeros χ T, analyticOrderNatAt L ρ : ℕ) : ℝ) =
      (rectInt (logDeriv Λ) z0 w0).im / (2 * Real.pi) := by
    simp only [mul_one] at hri
    rw [hsum_eq] at hri
    have hsum_cast : (∑ u ∈ dirZeros χ T, ((divB Λ (5 / 4 : ℂ) Rbox u).toNat : ℂ)) =
        (((∑ u ∈ dirZeros χ T, analyticOrderNatAt L u : ℕ) : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun u hu => ?_
      have hu_mem := (mem_dirZeros_iff hχ1 hT0).mp hu
      have hsb : u ∈ Metric.closedBall (5 / 4 : ℂ) Rbox := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        exact (mem_zerosIn (Finset.mem_filter.mp hu).1).1.le.trans (by dsimp [Rbox]; linarith)
      rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
        (fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ1).analyticAt z) hsb]
      have hntop : analyticOrderAt (DirichletCharacter.completedLFunction χ) u ≠ ⊤ := by
        intro htop
        have hzero := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          (fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ1).analyticAt z)
          isPreconnected_univ (Set.mem_univ u)
          (analyticOrderAt_eq_top.mp htop)
          (Set.mem_univ (5 / 4 : ℂ))
        exact DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (.inl hχ1)
          (by simp; norm_num) hzero
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hntop
      have hk' : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u = k := by
        rw [analyticOrderNatAt, ← hk]; rfl
      rw [← analyticOrderNatAt_completed_eq χ hχ1 hu_mem.1]
      norm_cast
      rw [← hk, hk', ENat.map_natCast, WithTop.untop₀_coe]
      rfl
    rw [hsum_cast] at hri
    have him := congrArg Complex.im hri
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero, mul_one, mul_zero,
      sub_zero] at him
    have h2pi : (2 * Real.pi) ≠ 0 := by positivity
    rw [him]
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat, zero_mul,
      sub_zero, zero_add]
    field_simp [h2pi]
  -- Now evaluate (rectInt (logDeriv Λ) z0 w0).im
  have hrect_im : (rectInt (logDeriv Λ) z0 w0).im =
      (∫ x in (-1 / 4 : ℝ)..(5 / 4 : ℝ), (logDeriv Λ ((x : ℂ) - T * I)).im) -
      (∫ x in (-1 / 4 : ℝ)..(5 / 4 : ℝ), (logDeriv Λ ((x : ℂ) + T * I)).im) +
      (∫ y in (-T)..T, (logDeriv Λ ((5 / 4 : ℂ) + y * I)).re) -
      (∫ y in (-T)..T, (logDeriv Λ (-(1 / 4 : ℂ) + y * I)).re) := by
    have hside1 : ContinuousOn (fun x : ℝ => logDeriv Λ ((x : ℂ) + z0.im * I)) (Set.Icc (-1 / 4) (5 / 4)) := by
      refine ContinuousOn.div ?_ ?_ (fun x hx => by
        exact hsides.1 x (by rw [hzre, hwre, Set.uIcc_of_le (by norm_num)]; exact hx))
      · exact (hΛ_ana.deriv.continuousOn.comp
          (continuous_ofReal.add continuous_const).continuousOn fun _ _ => Set.mem_univ _)
      · exact ((DirichletCharacter.differentiable_completedLFunction hχ1).continuous.comp
          (continuous_ofReal.add continuous_const)).continuousOn
    have hside2 : ContinuousOn (fun x : ℝ => logDeriv Λ ((x : ℂ) + w0.im * I)) (Set.Icc (-1 / 4) (5 / 4)) := by
      refine ContinuousOn.div ?_ ?_ (fun x hx => by
        exact hsides.2.1 x (by rw [hzre, hwre, Set.uIcc_of_le (by norm_num)]; exact hx))
      · exact (hΛ_ana.deriv.continuousOn.comp
          (continuous_ofReal.add continuous_const).continuousOn fun _ _ => Set.mem_univ _)
      · exact ((DirichletCharacter.differentiable_completedLFunction hχ1).continuous.comp
          (continuous_ofReal.add continuous_const)).continuousOn
    have hside3 : ContinuousOn (fun y : ℝ => logDeriv Λ ((w0.re : ℂ) + y * I)) (Set.Icc (-T) T) := by
      refine ContinuousOn.div ?_ ?_ (fun y hy => by
        exact hsides.2.2.1 y (by rw [hzim, hwim, Set.uIcc_of_le (by linarith)]; exact hy))
      · exact (hΛ_ana.deriv.continuousOn.comp
          (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn fun _ _ => Set.mem_univ _)
      · exact ((DirichletCharacter.differentiable_completedLFunction hχ1).continuous.comp
          (continuous_const.add (continuous_ofReal.mul continuous_const))).continuousOn
    have hside4 : ContinuousOn (fun y : ℝ => logDeriv Λ ((z0.re : ℂ) + y * I)) (Set.Icc (-T) T) := by
      refine ContinuousOn.div ?_ ?_ (fun y hy => by
        exact hsides.2.2.2 y (by rw [hzim, hwim, Set.uIcc_of_le (by linarith)]; exact hy))
      · exact (hΛ_ana.deriv.continuousOn.comp
          (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn fun _ _ => Set.mem_univ _)
      · exact ((DirichletCharacter.differentiable_completedLFunction hχ1).continuous.comp
          (continuous_const.add (continuous_ofReal.mul continuous_const))).continuousOn
    have hi1 : IntervalIntegrable (fun x : ℝ => logDeriv Λ ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
        volume (-1 / 4 : ℝ) (5 / 4 : ℝ) := by
      simpa [hzim] using hside1.intervalIntegrable_of_Icc (by norm_num)
    have hi2 : IntervalIntegrable (fun x : ℝ => logDeriv Λ ((x : ℂ) + ((T : ℝ) : ℂ) * I))
        volume (-1 / 4 : ℝ) (5 / 4 : ℝ) := by
      simpa [hwim] using hside2.intervalIntegrable_of_Icc (by norm_num)
    have hi3 : IntervalIntegrable (fun y : ℝ => logDeriv Λ (((5 / 4 : ℝ) : ℂ) + y * I))
        volume (-T) T := by
      simpa [hwre] using hside3.intervalIntegrable_of_Icc (by linarith)
    have hi4 : IntervalIntegrable (fun y : ℝ => logDeriv Λ (((-1 / 4 : ℝ) : ℂ) + y * I))
        volume (-T) T := by
      simpa [hzre] using hside4.intervalIntegrable_of_Icc (by linarith)
    unfold rectInt
    rw [hzre, hwre, hzim, hwim]
    rw [Complex.sub_im, Complex.add_im, Complex.sub_im,
      ← Complex.imCLM_apply, ← Complex.imCLM.intervalIntegral_comp_comm hi1,
      ← Complex.imCLM_apply, ← Complex.imCLM.intervalIntegral_comp_comm hi2,
      smul_eq_mul, smul_eq_mul,
      show ∀ c : ℂ, (I * c).im = c.re from fun c => by simp,
      show ∀ c : ℂ, (I * c).im = c.re from fun c => by simp,
      ← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hi3,
      ← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hi4]
    simp only [Complex.imCLM_apply, Complex.reCLM_apply]
    have hc1 : (∫ x in (-1 / 4 : ℝ)..(5 / 4 : ℝ), (logDeriv Λ ((x : ℂ) + ((-T : ℝ) : ℂ) * I)).im) =
        ∫ x in (-1 / 4 : ℝ)..(5 / 4 : ℝ), (logDeriv Λ ((x : ℂ) - T * I)).im :=
      intervalIntegral.integral_congr fun x _ => by
        rw [show (x : ℂ) + ((-T : ℝ) : ℂ) * I = (x : ℂ) - T * I by push_cast; ring]
    have hc3 : (∫ y in (-T)..T, (logDeriv Λ (((5 / 4 : ℝ) : ℂ) + y * I)).re) =
        ∫ y in (-T)..T, (logDeriv Λ ((5 / 4 : ℂ) + y * I)).re :=
      intervalIntegral.integral_congr fun y _ => by
        rw [show (((5 / 4 : ℝ) : ℂ) + y * I) = (5 / 4 : ℂ) + y * I by push_cast; ring]
    have hc4 : (∫ y in (-T)..T, (logDeriv Λ (((-1 / 4 : ℝ) : ℂ) + y * I)).re) =
        ∫ y in (-T)..T, (logDeriv Λ (-(1 / 4 : ℂ) + y * I)).re :=
      intervalIntegral.integral_congr fun y _ => by
        rw [show (((-1 / 4 : ℝ) : ℂ) + y * I) = -(1 / 4 : ℂ) + y * I by push_cast; ring]
    rw [hc1, hc3, hc4]
  -- Left edge via FE + conj symmetry
  have hleft_eq : (∫ y in (-T)..T, (logDeriv Λ (-(1 / 4 : ℂ) + y * I)).re) =
      -2 * T * Real.log q - ∫ y in (-T)..T, (logDeriv Λ ((5 / 4 : ℂ) + y * I)).re := by
    have hpt : ∀ y : ℝ, (logDeriv Λ (-(1 / 4 : ℂ) + y * I)).re =
        -Real.log q - (logDeriv Λ ((5 / 4 : ℂ) + y * I)).re := by
      intro y
      have h1_eq : 1 - (-(1 / 4 : ℂ) + y * I) = conj ((5 / 4 : ℂ) + y * I) := by
        apply Complex.ext <;> simp [map_ofNat] <;> norm_num
      have hnz : Λ' (1 - (-(1 / 4 : ℂ) + y * I)) ≠ 0 :=
        DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ⁻¹ (.inl hχ1') (by simp)
      rw [logDeriv_completedLFunction_one_sub hχ hχ1 hnz, h1_eq,
        logDeriv_completedLFunction_conj χ⁻¹ hχ1' ((5 / 4 : ℂ) + y * I), inv_inv]
      simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.conj_re]
      rfl
    simp_rw [hpt]
    have hintR : IntervalIntegrable (fun y : ℝ => (logDeriv Λ ((5 / 4 : ℂ) + y * I)).re) volume (-T) T := by
      refine (ContinuousOn.intervalIntegrable_of_Icc (by linarith) ?_)
      refine Complex.continuous_re.comp_continuousOn ?_
      refine ContinuousOn.div ?_ ?_ fun y _ =>
        DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (.inl hχ1) (by simp; norm_num)
      · exact (hΛ_ana.deriv.continuousOn.comp
          (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn fun _ _ => Set.mem_univ _)
      · exact ((DirichletCharacter.differentiable_completedLFunction hχ1).continuous.comp
          (continuous_const.add (continuous_ofReal.mul continuous_const))).continuousOn
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _) hintR,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  -- Horizontal edges via conj + FE symmetry
  have hL_chi : ∀ σ : ℝ, L ((σ : ℂ) + T * I) ≠ 0 :=
    LFunction_horizontal_ne_zero hχ hχ1 hT0 hgood
  have hL_inv : ∀ σ : ℝ, L' ((σ : ℂ) + T * I) ≠ 0 :=
    LFunction_horizontal_ne_zero hχ.inv hχ1' hT0 (dirGoodHeight_inv hχ1 hgood)
  have hΛ_chi : ∀ σ : ℝ, Λ ((σ : ℂ) + T * I) ≠ 0 := by
    intro σ
    by_cases h1 : 1 ≤ σ
    · exact DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (.inl hχ1) (by simp; exact h1)
    · by_cases h0 : σ ≤ 0
      · exact completedLFunction_ne_zero_of_re_le_zero hχ hχ1 (by simp; exact h0)
      · push Not at h0 h1
        have hs0 : (σ : ℂ) + T * I ≠ 0 := fun h => by
          have := congrArg Complex.re h; simp at this; linarith
        have := hL_chi σ
        change DirichletCharacter.LFunction χ ((σ : ℂ) + T * I) ≠ 0 at this
        rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ _ (.inl hs0)] at this
        exact left_ne_zero_of_mul this
  have hΛ_inv : ∀ σ : ℝ, Λ' ((σ : ℂ) + T * I) ≠ 0 := by
    intro σ
    by_cases h1 : 1 ≤ σ
    · exact DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ⁻¹ (.inl hχ1') (by simp; exact h1)
    · by_cases h0 : σ ≤ 0
      · exact completedLFunction_ne_zero_of_re_le_zero hχ.inv hχ1' (by simp; exact h0)
      · push Not at h0 h1
        have hs0 : (σ : ℂ) + T * I ≠ 0 := fun h => by
          have := congrArg Complex.re h; simp at this; linarith
        have := hL_inv σ
        change DirichletCharacter.LFunction χ⁻¹ ((σ : ℂ) + T * I) ≠ 0 at this
        rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ _ (.inl hs0)] at this
        exact left_ne_zero_of_mul this
  have hcont_Λ : ∀ (χ0 : DirichletCharacter ℂ q), χ0 ≠ 1 →
      (∀ σ : ℝ, DirichletCharacter.completedLFunction χ0 ((σ : ℂ) + T * I) ≠ 0) →
      Continuous (fun σ : ℝ => (logDeriv (DirichletCharacter.completedLFunction χ0) ((σ : ℂ) + T * I)).im) := by
    intro χ0 h10 hnz
    have hana0 : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ0) Set.univ := fun z _ =>
      (DirichletCharacter.differentiable_completedLFunction h10).analyticAt z
    refine Complex.continuous_im.comp (Continuous.div ?_ ?_ hnz)
    · exact (hana0.deriv.continuousOn.comp_continuous
        (Complex.continuous_ofReal.add continuous_const) fun _ => Set.mem_univ _)
    · exact (DirichletCharacter.differentiable_completedLFunction h10).continuous.comp
        (Complex.continuous_ofReal.add continuous_const)
  have hcont_Λc := hcont_Λ χ hχ1 hΛ_chi
  have hcont_Λi := hcont_Λ χ⁻¹ hχ1' hΛ_inv
  have hbot_eq : (∫ x in (-1 / 4 : ℝ)..(5 / 4 : ℝ), (logDeriv Λ ((x : ℂ) - T * I)).im) =
      -∫ x in (-1 / 4 : ℝ)..(5 / 4 : ℝ), (logDeriv Λ' ((x : ℂ) + T * I)).im := by
    have hpt : ∀ x : ℝ, (logDeriv Λ ((x : ℂ) - T * I)).im =
        -(logDeriv Λ' ((x : ℂ) + T * I)).im := by
      intro x
      have hc : (x : ℂ) - T * I = conj ((x : ℂ) + T * I) := by
        apply Complex.ext <;> simp
      rw [hc, logDeriv_completedLFunction_conj χ hχ1 ((x : ℂ) + T * I), Complex.conj_im]
    simp_rw [hpt, intervalIntegral.integral_neg]
  have hsymm_Λ : ∀ (χ0 : DirichletCharacter ℂ q), χ0.IsPrimitive → χ0 ≠ 1 →
      (∀ σ : ℝ, DirichletCharacter.completedLFunction χ0 ((σ : ℂ) + T * I) ≠ 0) →
      (∫ x in (-1 / 4 : ℝ)..(5 / 4 : ℝ),
        (logDeriv (DirichletCharacter.completedLFunction χ0) ((x : ℂ) + T * I)).im) =
      2 * ∫ x in (1 / 2 : ℝ)..(5 / 4 : ℝ),
        (logDeriv (DirichletCharacter.completedLFunction χ0) ((x : ℂ) + T * I)).im := by
    intro χ0 hχ0 h10 hnz0
    have hcont0 := hcont_Λ χ0 h10 hnz0
    have hsplit : (∫ x in (-1 / 4 : ℝ)..(5 / 4 : ℝ),
        (logDeriv (DirichletCharacter.completedLFunction χ0) ((x : ℂ) + T * I)).im) =
        (∫ x in (-1 / 4 : ℝ)..(1 / 2 : ℝ),
          (logDeriv (DirichletCharacter.completedLFunction χ0) ((x : ℂ) + T * I)).im) +
        (∫ x in (1 / 2 : ℝ)..(5 / 4 : ℝ),
          (logDeriv (DirichletCharacter.completedLFunction χ0) ((x : ℂ) + T * I)).im) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hcont0.intervalIntegrable (-1 / 4) (1 / 2))
        (hcont0.intervalIntegrable (1 / 2) (5 / 4))).symm
    have hpt_refl : ∀ x : ℝ,
        (logDeriv (DirichletCharacter.completedLFunction χ0) ((x : ℂ) + T * I)).im =
        (logDeriv (DirichletCharacter.completedLFunction χ0) (((1 - x : ℝ) : ℂ) + T * I)).im := by
      intro x
      have h10' : χ0⁻¹ ≠ 1 := fun h => h10 (by simpa using congrArg Inv.inv h)
      have hc : 1 - ((x : ℂ) + T * I) = conj (((1 - x : ℝ) : ℂ) + T * I) := by
        apply Complex.ext <;> simp
      have hnz' : DirichletCharacter.completedLFunction χ0⁻¹ (1 - ((x : ℂ) + T * I)) ≠ 0 := by
        rw [hc, DirichletBasics.completedLFunction_conj χ0⁻¹ h10' (((1 - x : ℝ) : ℂ) + T * I), inv_inv]
        exact (map_ne_zero _).mpr (hnz0 (1 - x))
      rw [logDeriv_completedLFunction_one_sub hχ0 h10 hnz', hc,
        logDeriv_completedLFunction_conj χ0⁻¹ h10' (((1 - x : ℝ) : ℂ) + T * I), inv_inv]
      simp only [Complex.sub_im, Complex.neg_im, Complex.ofReal_im, Complex.conj_im]
      ring
    have hleft_half : (∫ x in (-1 / 4 : ℝ)..(1 / 2 : ℝ),
        (logDeriv (DirichletCharacter.completedLFunction χ0) ((x : ℂ) + T * I)).im) =
        ∫ u in (1 / 2 : ℝ)..(5 / 4 : ℝ),
          (logDeriv (DirichletCharacter.completedLFunction χ0) ((u : ℂ) + T * I)).im := by
      rw [show (∫ x in (-1 / 4 : ℝ)..(1 / 2 : ℝ),
          (logDeriv (DirichletCharacter.completedLFunction χ0) ((x : ℂ) + T * I)).im) =
          ∫ x in (-1 / 4 : ℝ)..(1 / 2 : ℝ),
          (logDeriv (DirichletCharacter.completedLFunction χ0) (((1 - x : ℝ) : ℂ) + T * I)).im from
        intervalIntegral.integral_congr fun x _ => hpt_refl x]
      have hsub := intervalIntegral.integral_comp_sub_left
        (fun u : ℝ => (logDeriv (DirichletCharacter.completedLFunction χ0) ((u : ℂ) + T * I)).im)
        (a := (-1 / 4 : ℝ)) (b := (1 / 2 : ℝ)) 1
      rw [show (1 : ℝ) - (1 / 2 : ℝ) = 1 / 2 by ring,
        show (1 : ℝ) - (-1 / 4 : ℝ) = 5 / 4 by ring] at hsub
      exact hsub
    rw [hsplit, hleft_half, two_mul]
  -- Split logDeriv Λ on vertical line Re = 5/4 and horizontal segment [1/2, 5/4]
  have hdig_conj : ∀ {w : ℂ}, 0 < w.re → (Complex.digamma (conj w)).re = (Complex.digamma w).re := by
    intro w hw
    have hw' : 0 < (conj w).re := by simpa using hw
    have hd : Complex.digamma (conj w) = conj (Complex.digamma w) := by
      rw [GammaSolution.digamma_eq_gaussSum hw', GammaSolution.digamma_eq_gaussSum hw,
        GammaSolution.gaussSum, GammaSolution.gaussSum, map_add, map_neg, Complex.conj_ofReal,
        Complex.conj_tsum]
      congr 1
      refine tsum_congr fun k => ?_
      simp only [GammaSolution.gaussTerm, map_sub, map_inv₀, map_add, map_one, Complex.conj_natCast]
    rw [hd, Complex.conj_re]
  -- Evaluate vertical integral on Re = 5/4
  have h54_re : ∀ y : ℝ, 0 < ((5 / 4 : ℂ) + y * I).re := fun _ => by simp
  have hL_54_cont : Continuous (fun y : ℝ => logDeriv L ((5 / 4 : ℂ) + y * I)) := by
    refine Continuous.div ?_ ?_ (DirichletBasics.LFunction_anchor_ne_zero χ)
    · exact (hL_ana.deriv.continuousOn.comp_continuous
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) fun _ => Set.mem_univ _)
    · exact (DirichletCharacter.differentiable_LFunction hχ1).continuous.comp
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  let a_re : ℝ := if χ.Even then 5 / 4 else 9 / 4
  have ha_re : 1 / 2 ≤ a_re := by dsimp [a_re]; split_ifs <;> norm_num
  have hdig_cont_y : Continuous (fun y : ℝ => (Complex.digamma (((a_re : ℂ) + y * I) / 2)).re) := by
    refine Complex.continuous_re.comp (GammaSolution.analyticOnNhd_digamma.continuousOn.comp_continuous
      ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).div_const 2) fun y => ?_)
    rw [GammaSolution.mem_rightHalfPlane_iff]
    dsimp [a_re]; split_ifs <;> simp [Complex.div_ofNat_re] <;> norm_num
  have hdig_even_y : (∫ y in (-T)..T, (Complex.digamma (((a_re : ℂ) + y * I) / 2)).re) =
      2 * ∫ y in (0 : ℝ)..T, (Complex.digamma (((a_re : ℂ) + y * I) / 2)).re := by
    have h1 := (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hdig_cont_y.intervalIntegrable (-T) 0) (hdig_cont_y.intervalIntegrable 0 T)).symm
    have h2 : (∫ y in (-T)..(0 : ℝ), (Complex.digamma (((a_re : ℂ) + y * I) / 2)).re) =
        ∫ y in (0 : ℝ)..T, (Complex.digamma (((a_re : ℂ) + y * I) / 2)).re := by
      have hc := intervalIntegral.integral_comp_neg
        (fun y : ℝ => (Complex.digamma (((a_re : ℂ) + y * I) / 2)).re) (a := (0 : ℝ)) (b := T)
      rw [neg_zero] at hc
      refine hc.symm.trans (intervalIntegral.integral_congr fun y _ => ?_)
      have hcw : ((a_re : ℂ) + ((-y : ℝ) : ℂ) * I) / 2 = conj (((a_re : ℂ) + (y : ℂ) * I) / 2) := by
        rw [map_div₀, map_add, map_mul, Complex.conj_I, map_ofNat, Complex.conj_ofReal,
          Complex.conj_ofReal]
        push_cast
        ring
      rw [hcw]
      exact hdig_conj (by dsimp [a_re]; split_ifs <;> simp [Complex.div_ofNat_re] <;> norm_num)
    rw [h1, h2, two_mul]
  have hvert_split : (∫ y in (-T)..T, (logDeriv Λ ((5 / 4 : ℂ) + y * I)).re) =
      (∫ y in (-T)..T, (logDeriv L ((5 / 4 : ℂ) + y * I)).re) -
      T * Real.log Real.pi +
      (∫ y in (0 : ℝ)..T, (Complex.digamma (((a_re : ℂ) + y * I) / 2)).re) := by
    have hpt : ∀ y : ℝ, (logDeriv Λ ((5 / 4 : ℂ) + y * I)).re =
        (logDeriv L ((5 / 4 : ℂ) + y * I)).re - (1 / 2) * Real.log Real.pi +
        (1 / 2) * (Complex.digamma (((a_re : ℂ) + y * I) / 2)).re := by
      intro y
      rw [logDeriv_completed_eq_add_of_re_pos χ hχ1 (h54_re y) (DirichletBasics.LFunction_anchor_ne_zero χ y),
        logDeriv_gammaFactor_of_re_pos χ (h54_re y)]
      have harg_eq : (if χ.Even then ((5 / 4 : ℂ) + y * I) / 2 else (((5 / 4 : ℂ) + y * I) + 1) / 2) =
          ((a_re : ℂ) + y * I) / 2 := by
        dsimp [a_re]; split_ifs
        · push_cast; rfl
        · push_cast; ring
      rw [harg_eq]
      simp [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re]
      ring
    simp_rw [hpt]
    have hiL : IntervalIntegrable (fun y : ℝ => (logDeriv L ((5 / 4 : ℂ) + y * I)).re) volume (-T) T :=
      (Complex.continuous_re.comp hL_54_cont).intervalIntegrable (-T) T
    have hic : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ) * Real.log Real.pi) volume (-T) T :=
      continuous_const.intervalIntegrable _ _
    have hid := hdig_cont_y.intervalIntegrable (-T) T (μ := volume)
    rw [intervalIntegral.integral_add (hiL.sub hic) (hid.const_mul _),
      intervalIntegral.integral_sub hiL hic, intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, hdig_even_y, smul_eq_mul]
    ring
  have hdig_rect := TernaryGoldbach.RSBounds.BacklundGammaPhase.digamma_rectangle ha_re T
  have hhor_split : ∀ (χ0 : DirichletCharacter ℂ q), χ0 ≠ 1 →
      (∀ σ : ℝ, DirichletCharacter.LFunction χ0 ((σ : ℂ) + T * I) ≠ 0) →
      (∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
        (logDeriv (DirichletCharacter.completedLFunction χ0) ((σ : ℂ) + T * I)).im) =
      (∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
        (logDeriv (DirichletCharacter.LFunction χ0) ((σ : ℂ) + T * I)).im) +
      (1 / 2) * ∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
        (Complex.digamma (if χ0.Even then ((σ : ℂ) + T * I) / 2
          else (((σ : ℂ) + T * I) + 1) / 2)).im := by
    intro χ0 h10 hL0
    have hana0 : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ0) Set.univ := fun z _ =>
      (DirichletCharacter.differentiable_LFunction h10).analyticAt z
    have hpt : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) (5 / 4),
        (logDeriv (DirichletCharacter.completedLFunction χ0) ((σ : ℂ) + T * I)).im =
        (logDeriv (DirichletCharacter.LFunction χ0) ((σ : ℂ) + T * I)).im +
        (1 / 2) * (Complex.digamma (if χ0.Even then ((σ : ℂ) + T * I) / 2
          else (((σ : ℂ) + T * I) + 1) / 2)).im := by
      intro σ hσ
      have hre : 0 < ((σ : ℂ) + T * I).re := by simp; linarith [hσ.1]
      rw [logDeriv_completed_eq_add_of_re_pos χ0 h10 hre (hL0 σ),
        logDeriv_gammaFactor_of_re_pos χ0 hre]
      simp [Complex.add_im, Complex.neg_im, Complex.mul_im]
    have hcongr : (∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
        (logDeriv (DirichletCharacter.completedLFunction χ0) ((σ : ℂ) + T * I)).im) =
        ∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
        ((logDeriv (DirichletCharacter.LFunction χ0) ((σ : ℂ) + T * I)).im +
        (1 / 2) * (Complex.digamma (if χ0.Even then ((σ : ℂ) + T * I) / 2
          else (((σ : ℂ) + T * I) + 1) / 2)).im) :=
      intervalIntegral.integral_congr fun σ hσ =>
        hpt σ (by rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 5 / 4)] at hσ; exact hσ)
    rw [hcongr]
    have hiL : ContinuousOn (fun σ : ℝ =>
        (logDeriv (DirichletCharacter.LFunction χ0) ((σ : ℂ) + T * I)).im) (Set.Icc (1 / 2) (5 / 4)) := by
      refine Complex.continuous_im.comp_continuousOn (ContinuousOn.div ?_ ?_ fun σ _ => hL0 σ)
      · exact (hana0.deriv.continuousOn.comp
          (continuous_ofReal.add continuous_const).continuousOn fun _ _ => Set.mem_univ _)
      · exact (DirichletCharacter.differentiable_LFunction h10).continuous.comp_continuousOn
          (continuous_ofReal.add continuous_const).continuousOn
    have hiD : ContinuousOn (fun σ : ℝ =>
        (Complex.digamma (if χ0.Even then ((σ : ℂ) + T * I) / 2
          else (((σ : ℂ) + T * I) + 1) / 2)).im) (Set.Icc (1 / 2) (5 / 4)) := by
      split_ifs
      · exact Complex.continuous_im.comp_continuousOn
          (GammaSolution.analyticOnNhd_digamma.continuousOn.comp
            ((continuous_ofReal.add continuous_const).div_const 2).continuousOn fun σ hσ => by
              rw [GammaSolution.mem_rightHalfPlane_iff]; simp [Complex.div_ofNat_re]; linarith [hσ.1])
      · exact Complex.continuous_im.comp_continuousOn
          (GammaSolution.analyticOnNhd_digamma.continuousOn.comp
            (((continuous_ofReal.add continuous_const).add continuous_const).div_const 2).continuousOn
              fun σ hσ => by
                rw [GammaSolution.mem_rightHalfPlane_iff]; simp [Complex.div_ofNat_re]; linarith [hσ.1])
    rw [intervalIntegral.integral_add (hiL.intervalIntegrable_of_Icc (by norm_num))
        ((hiD.const_mul _).intervalIntegrable_of_Icc (by norm_num)),
      intervalIntegral.integral_const_mul]
  have hhor_c := hhor_split χ hχ1 hL_chi
  have hhor_i := hhor_split χ⁻¹ hχ1' hL_inv
  have hev_eq : χ⁻¹.Even ↔ χ.Even := DirichletBasics.even_inv_iff χ
  have hrect_full : (rectInt (logDeriv Λ) z0 w0).im / (2 * Real.pi) =
      (T / Real.pi) * Real.log (q / Real.pi) +
      (1 / Real.pi) * (∫ y in (-T)..T, (logDeriv L ((5 / 4 : ℂ) + y * I)).re) -
      (1 / Real.pi) * (∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ), (logDeriv L ((σ : ℂ) + T * I)).im) -
      (1 / Real.pi) * (∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ), (logDeriv L' ((σ : ℂ) + T * I)).im) +
      (2 * TernaryGoldbach.RSBounds.BacklundGammaPhase.phaseIntegral T / Real.pi +
        if χ.Even then 0 else
        (1 / Real.pi) * ∫ σ in (1 / 2 : ℝ)..(3 / 2), (Complex.digamma (((σ : ℂ) + T * I) / 2)).im) := by
    rw [hrect_im, hleft_eq, hbot_eq, hsymm_Λ χ hχ hχ1 hΛ_chi, hsymm_Λ χ⁻¹ hχ.inv hχ1' hΛ_inv,
      hvert_split, hhor_c, hhor_i]
    simp only [hev_eq]
    by_cases hev : χ.Even
    · simp only [hev, ↓reduceIte]
      have hare : a_re = 5 / 4 := by dsimp [a_re]; simp [hev]
      simp only [hare, Complex.ofReal_div, Complex.ofReal_ofNat]
      rw [hare] at hdig_rect
      push_cast at hdig_rect
      have hrect54 : ∫ t in (0 : ℝ)..T, (Complex.digamma (((5 / 4 : ℂ) + t * I) / 2)).re =
          2 * TernaryGoldbach.RSBounds.BacklundGammaPhase.phaseIntegral T +
          ∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ), (Complex.digamma (((σ : ℂ) + T * I) / 2)).im := by
        linarith
      rw [hrect54, show Real.log (q / Real.pi) = Real.log q - Real.log Real.pi from
        Real.log_div hq0.ne' hp.ne']
      field_simp [hp.ne']
      ring
    · simp only [hev, ↓reduceIte]
      have hare : a_re = 9 / 4 := by dsimp [a_re]; simp [hev]
      simp only [hare, Complex.ofReal_div, Complex.ofReal_ofNat]
      rw [hare] at hdig_rect
      push_cast at hdig_rect
      have hrect94 : ∫ t in (0 : ℝ)..T, (Complex.digamma (((9 / 4 : ℂ) + t * I) / 2)).re =
          2 * TernaryGoldbach.RSBounds.BacklundGammaPhase.phaseIntegral T +
          ∫ σ in (1 / 2 : ℝ)..(9 / 4 : ℝ), (Complex.digamma (((σ : ℂ) + T * I) / 2)).im := by
        linarith
      have hshift_int : (∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
          (Complex.digamma ((((σ : ℂ) + T * I) + 1) / 2)).im) =
          ∫ u in (3 / 2 : ℝ)..(9 / 4 : ℝ), (Complex.digamma (((u : ℂ) + T * I) / 2)).im := by
        have hcomp := intervalIntegral.integral_comp_add_right
          (fun u : ℝ => (Complex.digamma (((u : ℂ) + T * I) / 2)).im) (1 : ℝ)
          (a := (1 / 2 : ℝ)) (b := (5 / 4 : ℝ))
        convert hcomp using 2
        · ext σ; congr 2; push_cast; ring
        · norm_num
        · norm_num
      have hdig_im_contOn : ContinuousOn
          (fun σ : ℝ => (Complex.digamma (((σ : ℂ) + T * I) / 2)).im) (Set.Icc (1 / 2) (9 / 4)) := by
        refine Complex.continuous_im.comp_continuousOn
          (GammaSolution.analyticOnNhd_digamma.continuousOn.comp
            ((continuous_ofReal.add continuous_const).div_const 2).continuousOn fun σ hσ => ?_)
        rw [GammaSolution.mem_rightHalfPlane_iff]
        simp [Complex.div_ofNat_re]
        linarith [hσ.1]
      have hsplit94 : (∫ σ in (1 / 2 : ℝ)..(9 / 4 : ℝ), (Complex.digamma (((σ : ℂ) + T * I) / 2)).im) =
          (∫ σ in (1 / 2 : ℝ)..(3 / 2 : ℝ), (Complex.digamma (((σ : ℂ) + T * I) / 2)).im) +
          (∫ σ in (3 / 2 : ℝ)..(9 / 4 : ℝ), (Complex.digamma (((σ : ℂ) + T * I) / 2)).im) :=
        (intervalIntegral.integral_add_adjacent_intervals
          ((hdig_im_contOn.mono (Set.Icc_subset_Icc_right (by norm_num))).intervalIntegrable_of_Icc (by norm_num))
          ((hdig_im_contOn.mono (Set.Icc_subset_Icc_left (by norm_num))).intervalIntegrable_of_Icc (by norm_num))).symm
      rw [hrect94, hsplit94, hshift_int, show Real.log (q / Real.pi) = Real.log q - Real.log Real.pi from
        Real.log_div hq0.ne' hp.ne']
      field_simp [hp.ne']
      ring
  have hlog_main : (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) =
      (T / Real.pi) * Real.log ((q : ℝ) / Real.pi) +
      (T / Real.pi) * Real.log (T / (2 * Real.exp 1)) := by
    rw [show (q : ℝ) * T / (2 * Real.pi * Real.exp 1) =
        ((q : ℝ) / Real.pi) * (T / (2 * Real.exp 1)) by ring,
      Real.log_mul (by positivity) (by positivity)]
    ring
  rw [hcount_eq, hrect_full, hlog_main]
  have hv_le : |(1 / Real.pi) * (∫ y in (-T)..T, (logDeriv L ((5 / 4 : ℂ) + y * I)).re)| ≤ 1 := by
    have hv := DirichletBasics.vertical_integral_LFunction_five_fourths_le_pi χ hχ1 T
    have him_eq : (∫ y in (-T)..T, logDeriv L ((5 / 4 : ℂ) + y * I) * I).im =
        ∫ y in (-T)..T, (logDeriv L ((5 / 4 : ℂ) + y * I)).re := by
      have hi : IntervalIntegrable (fun y : ℝ => logDeriv L ((5 / 4 : ℂ) + y * I) * I) volume (-T) T :=
        (hL_54_cont.mul continuous_const).intervalIntegrable _ _
      rw [← Complex.imCLM_apply, ← Complex.imCLM.intervalIntegral_comp_comm hi]
      simp
    rw [him_eq] at hv
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / Real.pi)]
    exact (mul_le_mul_of_nonneg_left hv (by positivity)).trans_eq (by field_simp [hp.ne'])
  have hgam_le : |(2 * TernaryGoldbach.RSBounds.BacklundGammaPhase.phaseIntegral T / Real.pi +
      if χ.Even then 0 else
      (1 / Real.pi) * ∫ σ in (1 / 2 : ℝ)..(3 / 2), (Complex.digamma (((σ : ℂ) + T * I) / 2)).im) -
      (T / Real.pi) * Real.log (T / (2 * Real.exp 1))| ≤ if χ.Even then 0.33 else 0.70 := by
    split_ifs with hev
    · rw [add_zero]
      exact DirichletGammaPhaseOdd.even_gamma_phase_error hT
    · exact DirichletGammaPhaseOdd.odd_gamma_phase_error hT
  have hre_diff :
      ((T / Real.pi) * Real.log ((q : ℝ) / Real.pi) +
        (1 / Real.pi) * (∫ y in (-T)..T, (logDeriv L ((5 / 4 : ℂ) + y * I)).re) -
        (1 / Real.pi) * (∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ), (logDeriv L ((σ : ℂ) + T * I)).im) -
        (1 / Real.pi) * (∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ), (logDeriv L' ((σ : ℂ) + T * I)).im) +
        (2 * TernaryGoldbach.RSBounds.BacklundGammaPhase.phaseIntegral T / Real.pi +
          if χ.Even then 0 else
          (1 / Real.pi) * ∫ σ in (1 / 2 : ℝ)..(3 / 2), (Complex.digamma (((σ : ℂ) + T * I) / 2)).im)) -
      ((T / Real.pi) * Real.log ((q : ℝ) / Real.pi) +
        (T / Real.pi) * Real.log (T / (2 * Real.exp 1))) =
      ((1 / Real.pi) * (∫ y in (-T)..T, (logDeriv L ((5 / 4 : ℂ) + y * I)).re) -
        (1 / Real.pi) * (∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ), (logDeriv L ((σ : ℂ) + T * I)).im) -
        (1 / Real.pi) * (∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ), (logDeriv L' ((σ : ℂ) + T * I)).im)) +
      ((2 * TernaryGoldbach.RSBounds.BacklundGammaPhase.phaseIntegral T / Real.pi +
          if χ.Even then 0 else
          (1 / Real.pi) * ∫ σ in (1 / 2 : ℝ)..(3 / 2), (Complex.digamma (((σ : ℂ) + T * I) / 2)).im) -
        (T / Real.pi) * Real.log (T / (2 * Real.exp 1))) := by ring
  rw [hre_diff]
  have h1 := abs_add_le
    ((1 / Real.pi) * (∫ y in (-T)..T, (logDeriv L ((5 / 4 : ℂ) + y * I)).re) -
      (1 / Real.pi) * (∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ), (logDeriv L ((σ : ℂ) + T * I)).im) -
      (1 / Real.pi) * (∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ), (logDeriv L' ((σ : ℂ) + T * I)).im))
    ((2 * TernaryGoldbach.RSBounds.BacklundGammaPhase.phaseIntegral T / Real.pi +
        if χ.Even then 0 else
        (1 / Real.pi) * ∫ σ in (1 / 2 : ℝ)..(3 / 2), (Complex.digamma (((σ : ℂ) + T * I) / 2)).im) -
      (T / Real.pi) * Real.log (T / (2 * Real.exp 1)))
  have h2 := abs_sub
    ((1 / Real.pi) * (∫ y in (-T)..T, (logDeriv L ((5 / 4 : ℂ) + y * I)).re) -
      (1 / Real.pi) * (∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ), (logDeriv L ((σ : ℂ) + T * I)).im))
    ((1 / Real.pi) * (∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ), (logDeriv L' ((σ : ℂ) + T * I)).im))
  have h3 := abs_sub
    ((1 / Real.pi) * (∫ y in (-T)..T, (logDeriv L ((5 / 4 : ℂ) + y * I)).re))
    ((1 / Real.pi) * (∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ), (logDeriv L ((σ : ℂ) + T * I)).im))
  have hdiv1 : |(1 / Real.pi) * ∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
      (logDeriv L ((σ : ℂ) + T * I)).im| =
      |∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
      (logDeriv L ((σ : ℂ) + T * I)).im| / Real.pi := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / Real.pi), one_div_mul_eq_div]
  have hdiv2 : |(1 / Real.pi) * ∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
      (logDeriv L' ((σ : ℂ) + T * I)).im| =
      |∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
      (logDeriv L' ((σ : ℂ) + T * I)).im| / Real.pi := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / Real.pi), one_div_mul_eq_div]
  linarith

noncomputable def dirHArg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T a σ : ℝ) : ℝ :=
  (Complex.log (DirichletCharacter.LFunction χ ((a : ℂ) + T * I))).im +
    ∫ x in a..σ, (logDeriv (DirichletCharacter.LFunction χ) ((x : ℂ) + T * I)).im

noncomputable def dirHReInt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T a σ : ℝ) : ℝ :=
  Real.log ‖DirichletCharacter.LFunction χ ((a : ℂ) + T * I)‖ +
    ∫ x in a..σ, (logDeriv (DirichletCharacter.LFunction χ) ((x : ℂ) + T * I)).re

lemma continuous_logDeriv_dir_horiz {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {T : ℝ} (hT : 0 < T) (hgood : dirGoodHeight χ T) :
    Continuous fun σ : ℝ => logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + T * I) := by
  have hL_ana : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ := fun z _ =>
    (DirichletCharacter.differentiable_LFunction hχ1).analyticAt z
  refine Continuous.div ?_ ?_ (LFunction_horizontal_ne_zero hχ hχ1 hT hgood)
  · exact (hL_ana.deriv.continuousOn.comp_continuous
      (Complex.continuous_ofReal.add continuous_const) fun _ => Set.mem_univ _)
  · exact (DirichletCharacter.differentiable_LFunction hχ1).continuous.comp
      (Complex.continuous_ofReal.add continuous_const)

lemma dirHArg_continuous {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {T : ℝ} (hT : 0 < T) (hgood : dirGoodHeight χ T) (a : ℝ) :
    Continuous (dirHArg χ T a) :=
  continuous_const.add
    (intervalIntegral.continuous_primitive
      (fun u v => (Complex.continuous_im.comp (continuous_logDeriv_dir_horiz hχ hχ1 hT hgood)).intervalIntegrable u v) a)

lemma dirHArg_sub_eq_integral {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {T : ℝ} (hT : 0 < T) (hgood : dirGoodHeight χ T) (a u v : ℝ) :
    dirHArg χ T a u - dirHArg χ T a v =
      ∫ x in v..u, (logDeriv (DirichletCharacter.LFunction χ) ((x : ℂ) + T * I)).im := by
  unfold dirHArg
  have hc : Continuous (fun σ : ℝ => (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + T * I)).im) :=
    Complex.continuous_im.comp (continuous_logDeriv_dir_horiz hχ hχ1 hT hgood)
  rw [add_sub_add_left_eq_sub, sub_eq_iff_eq_add, add_comm,
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable a v) (hc.intervalIntegrable v u)]

set_option maxHeartbeats 800000 in
lemma dir_eq_norm_mul_cis {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {T : ℝ} (hT : 0 < T) (hgood : dirGoodHeight χ T) (a σ : ℝ) :
    DirichletCharacter.LFunction χ ((σ : ℂ) + T * I) =
      (‖DirichletCharacter.LFunction χ ((σ : ℂ) + T * I)‖ : ℂ) *
        Complex.exp (I * (dirHArg χ T a σ : ℂ)) := by
  let L := DirichletCharacter.LFunction χ
  let ψ : ℝ → ℂ := fun x => (dirHReInt χ T a x : ℂ) + I * (dirHArg χ T a x : ℂ)
  let G : ℝ → ℂ := fun x => L ((x : ℂ) + T * I) * Complex.exp (-ψ x)
  have hc := continuous_logDeriv_dir_horiz hχ hχ1 hT hgood
  have hc_re : Continuous fun x : ℝ => (logDeriv L ((x : ℂ) + T * I)).re :=
    Complex.continuous_re.comp hc
  have hc_im : Continuous fun x : ℝ => (logDeriv L ((x : ℂ) + T * I)).im :=
    Complex.continuous_im.comp hc
  have hψ_deriv : ∀ x : ℝ, HasDerivAt ψ (logDeriv L ((x : ℂ) + T * I)) x := by
    intro x
    have hre : HasDerivAt (dirHReInt χ T a) ((logDeriv L ((x : ℂ) + T * I)).re) x := by
      unfold dirHReInt
      exact ((hasDerivAt_const x (Real.log ‖L ((a : ℂ) + T * I)‖)).add
        (intervalIntegral.integral_hasDerivAt_right
          (hc_re.intervalIntegrable a x) hc_re.stronglyMeasurable.stronglyMeasurableAtFilter
          hc_re.continuousAt)).congr_deriv (zero_add _)
    have him : HasDerivAt (dirHArg χ T a) ((logDeriv L ((x : ℂ) + T * I)).im) x := by
      unfold dirHArg
      exact ((hasDerivAt_const x (Complex.log (L ((a : ℂ) + T * I))).im).add
        (intervalIntegral.integral_hasDerivAt_right
          (hc_im.intervalIntegrable a x) hc_im.stronglyMeasurable.stronglyMeasurableAtFilter
          hc_im.continuousAt)).congr_deriv (zero_add _)
    have h := hre.ofReal_comp.add ((him.ofReal_comp).const_mul I)
    refine h.congr_deriv ?_
    apply Complex.ext <;> simp
  have hG_deriv : ∀ x : ℝ, HasDerivAt G 0 x := by
    intro x
    have hL_hd : HasDerivAt (fun t : ℝ => L ((t : ℂ) + T * I))
        (deriv L ((x : ℂ) + T * I) * 1) x := by
      have hd := ((DirichletCharacter.differentiable_LFunction hχ1) ((x : ℂ) + T * I)).hasDerivAt
      exact hd.comp x ((Complex.ofRealCLM.hasDerivAt (x := x)).add_const (T * I))
    have hE_hd : HasDerivAt (fun t : ℝ => Complex.exp (-ψ t))
        (Complex.exp (-ψ x) * -(logDeriv L ((x : ℂ) + T * I))) x :=
      ((hψ_deriv x).neg).cexp
    refine (hL_hd.mul hE_hd).congr_deriv ?_
    rw [logDeriv_apply]
    have hnz : L ((x : ℂ) + T * I) ≠ 0 := LFunction_horizontal_ne_zero hχ hχ1 hT hgood x
    field_simp [hnz]
    ring
  have hG_const : G σ = G a :=
    is_const_of_deriv_eq_zero (fun x => (hG_deriv x).differentiableAt)
      (fun x => (hG_deriv x).deriv) σ a
  have hGa : G a = 1 := by
    have hLa : L ((a : ℂ) + T * I) ≠ 0 := LFunction_horizontal_ne_zero hχ hχ1 hT hgood a
    dsimp [G, ψ, dirHReInt, dirHArg]
    rw [intervalIntegral.integral_same, intervalIntegral.integral_same, add_zero, add_zero]
    have hlog : Complex.log (L ((a : ℂ) + T * I)) =
        (Real.log ‖L ((a : ℂ) + T * I)‖ : ℂ) +
          I * ((Complex.log (L ((a : ℂ) + T * I))).im : ℂ) := by
      rw [← Complex.log_re, mul_comm I _, ← Complex.re_add_im (Complex.log _)]
      simp [Complex.log_im]
    rw [← hlog, Complex.exp_neg, Complex.exp_log hLa, mul_inv_cancel₀ hLa]
  have hGσ : L ((σ : ℂ) + T * I) = Complex.exp (ψ σ) := by
    have := hG_const.trans hGa
    dsimp [G] at this
    rw [Complex.exp_neg] at this
    exact eq_of_mul_inv_eq_one this
  have hnorm : ‖L ((σ : ℂ) + T * I)‖ = Real.exp (dirHReInt χ T a σ) := by
    rw [hGσ, Complex.norm_exp]
    simp [ψ]
  change L ((σ : ℂ) + T * I) = (‖L ((σ : ℂ) + T * I)‖ : ℂ) *
    Complex.exp (I * (dirHArg χ T a σ : ℂ))
  rw [hnorm, hGσ, show ψ σ = (dirHReInt χ T a σ : ℂ) + I * (dirHArg χ T a σ : ℂ) from rfl,
    Complex.exp_add, Complex.ofReal_exp]

lemma powerAverage_dir_eq_zero_of_cos {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {T : ℝ} (hT : 0 < T) (hgood : dirGoodHeight χ T)
    (a x : ℝ) (n : ℕ) (hcos : Real.cos ((n : ℝ) * dirHArg χ T a x) = 0) :
    TernaryGoldbach.RSBounds.BacklundJensen.powerAverage
      (fun z : ℂ => DirichletCharacter.LFunction χ (z + T * I))
      (fun z : ℂ => DirichletCharacter.LFunction χ⁻¹ (z - T * I)) n (x : ℂ) = 0 := by
  have hχ1' : χ⁻¹ ≠ 1 := fun h => hχ1 (by simpa using congrArg Inv.inv h)
  have hf := dir_eq_norm_mul_cis hχ hχ1 hT hgood a x
  have hg : DirichletCharacter.LFunction χ⁻¹ ((x : ℂ) - T * I) =
      (‖DirichletCharacter.LFunction χ ((x : ℂ) + T * I)‖ : ℂ) *
        Complex.exp (-I * (dirHArg χ T a x : ℂ)) := by
    have hc : (x : ℂ) - T * I = conj ((x : ℂ) + T * I) := by apply Complex.ext <;> simp
    rw [hc, DirichletBasics.LFunction_conj χ⁻¹ hχ1' ((x : ℂ) + T * I), inv_inv, hf, map_mul,
      Complex.conj_ofReal, ← Complex.exp_conj]
    simp [Complex.conj_I]
  unfold TernaryGoldbach.RSBounds.BacklundJensen.powerAverage
  dsimp
  rw [hf, hg, mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← mul_add,
    show (n : ℂ) * (I * (dirHArg χ T a x : ℂ)) = ((n * dirHArg χ T a x : ℝ) : ℂ) * I by push_cast; ring,
    show (n : ℂ) * (-I * (dirHArg χ T a x : ℂ)) = ((-(n * dirHArg χ T a x) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_mul_I, Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_cos, hcos]
  simp

theorem horizontal_argument_bound_dir {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {T R : ℝ} {B : ℂ → ℝ}
    (hT : 2 ≤ T) (hgood : dirGoodHeight χ T) (hR : 3 / 4 < R)
    (hB : CircleIntegrable B (5 / 4 : ℂ) R)
    (hB0 : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) R, 0 ≤ B z)
    (hfb : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) R,
      ‖DirichletCharacter.LFunction χ (z + T * I)‖ ≤ Real.exp (B z))
    (hgb : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) R,
      ‖DirichletCharacter.LFunction χ⁻¹ (z - T * I)‖ ≤ Real.exp (B z)) :
    |∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
      (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + T * I)).im| / Real.pi ≤
      (circleAverage B (5 / 4 : ℂ) R -
        Real.log ‖DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + T * I)‖) /
          (2 * Real.log (R / (3 / 4))) + 2 / (Real.pi * T) := by
  have hχ1 : χ ≠ 1 := DirichletBasics.ne_one_of_isPrimitive_of_two_le hq hχ
  have hχ1' : χ⁻¹ ≠ 1 := fun h => hχ1 (by simpa using congrArg Inv.inv h)
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hf_ana : AnalyticOnNhd ℂ (fun z : ℂ => DirichletCharacter.LFunction χ (z + T * I))
      (Metric.closedBall (5 / 4 : ℂ) R) := fun z _ =>
    ((DirichletCharacter.differentiable_LFunction hχ1).analyticAt _).comp
      (analyticAt_id.add analyticAt_const)
  have hg_ana : AnalyticOnNhd ℂ (fun z : ℂ => DirichletCharacter.LFunction χ⁻¹ (z - T * I))
      (Metric.closedBall (5 / 4 : ℂ) R) := fun z _ =>
    ((DirichletCharacter.differentiable_LFunction hχ1').analyticAt _).comp
      (analyticAt_id.sub analyticAt_const)
  have hdelta : ∀ δ : ℝ, 0 < δ → δ ≤ 3 / 4 →
      |(dirHArg χ T (5 / 4) (1 / 2 + δ) - dirHArg χ T (5 / 4) (1 / 2)) -
        (dirHArg χ T (5 / 4) (1 / 2) - dirHArg χ T (5 / 4) (1 / 2 - δ))| ≤ 4 / T := by
    intro δ hδ0 hδ1
    rw [dirHArg_sub_eq_integral hχ hχ1 hT0 hgood (5 / 4) (1 / 2 + δ) (1 / 2),
      dirHArg_sub_eq_integral hχ hχ1 hT0 hgood (5 / 4) (1 / 2) (1 / 2 - δ)]
    let f : ℝ → ℝ := fun σ => (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + T * I)).im
    have hc : Continuous f := Complex.continuous_im.comp (continuous_logDeriv_dir_horiz hχ hχ1 hT0 hgood)
    have hsub_int : (∫ σ in (1 / 2 - δ : ℝ)..(1 / 2 : ℝ), f σ) =
        ∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), f (1 - σ) := by
      have h := intervalIntegral.integral_comp_sub_left f (a := (1 / 2 : ℝ)) (b := (1 / 2 + δ)) 1
      rw [show (1 : ℝ) - (1 / 2 + δ) = 1 / 2 - δ by ring,
        show (1 : ℝ) - 1 / 2 = 1 / 2 by ring] at h
      exact h.symm
    change |(∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), f σ) - ∫ σ in (1 / 2 - δ : ℝ)..(1 / 2 : ℝ), f σ| ≤ 4 / T
    have hc2 : Continuous (fun σ : ℝ => f (1 - σ)) := hc.comp (continuous_const.sub continuous_id)
    rw [hsub_int, ← intervalIntegral.integral_sub (hc.intervalIntegrable _ _)
      (hc2.intervalIntegrable _ _)]
    have hpt_diff : ∀ σ : ℝ,
        f σ - f (1 - σ) =
        (logDeriv (DirichletCharacter.gammaFactor χ) (((1 - σ : ℝ) : ℂ) + T * I)).im -
        (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + T * I)).im := by
      intro σ
      have him1 : ((σ : ℂ) + T * I).im ≠ 0 := by simp [hT0.ne']
      have him2 : (((1 - σ : ℝ) : ℂ) + T * I).im ≠ 0 := by simp [hT0.ne']
      have hL1 := LFunction_horizontal_ne_zero hχ hχ1 hT0 hgood σ
      have hL2 := LFunction_horizontal_ne_zero hχ hχ1 hT0 hgood (1 - σ)
      have hc1 : 1 - (((1 - σ : ℝ) : ℂ) + T * I) = conj ((σ : ℂ) + T * I) := by
        apply Complex.ext <;> simp
      have hΛnz : DirichletCharacter.completedLFunction χ ((σ : ℂ) + T * I) ≠ 0 := by
        have hs0 : (σ : ℂ) + T * I ≠ 0 := fun h => him1 (by rw [h]; simp)
        rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ _ (.inl hs0)] at hL1
        exact left_ne_zero_of_mul hL1
      have hΛnz' : DirichletCharacter.completedLFunction χ⁻¹ (1 - (((1 - σ : ℝ) : ℂ) + T * I)) ≠ 0 := by
        rw [hc1, DirichletBasics.completedLFunction_conj χ⁻¹ hχ1' ((σ : ℂ) + T * I), inv_inv]
        exact (map_ne_zero _).mpr hΛnz
      have hfe := logDeriv_completedLFunction_one_sub hχ hχ1 hΛnz'
      rw [hc1, logDeriv_completedLFunction_conj χ⁻¹ hχ1' ((σ : ℂ) + T * I), inv_inv] at hfe
      have him_eq : (logDeriv (DirichletCharacter.completedLFunction χ) (((1 - σ : ℝ) : ℂ) + T * I)).im =
          (logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + T * I)).im := by
        rw [hfe]
        simp only [Complex.sub_im, Complex.neg_im, Complex.ofReal_im, Complex.conj_im]
        ring
      rw [logDeriv_completed_eq_add_of_re_pos_or_im_ne_zero χ hχ1 (.inr him1) hL1,
        logDeriv_completed_eq_add_of_re_pos_or_im_ne_zero χ hχ1 (.inr him2) hL2,
        Complex.add_im, Complex.add_im] at him_eq
      dsimp [f]
      linarith
    have hcongr_diff : (∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), f σ - f (1 - σ)) =
        ∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ),
          ((logDeriv (DirichletCharacter.gammaFactor χ) (((1 - σ : ℝ) : ℂ) + T * I)).im -
          (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + T * I)).im) :=
      intervalIntegral.integral_congr fun σ _ => hpt_diff σ
    rw [hcongr_diff]
    by_cases hev : χ.Even
    · have hgam_eq : ∀ σ : ℝ,
          (logDeriv (DirichletCharacter.gammaFactor χ) (((1 - σ : ℝ) : ℂ) + T * I)).im -
          (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + T * I)).im =
          TernaryGoldbach.RSBounds.BacklundGammaReflection.gammaReflectionDifference σ T := by
        intro σ
        rw [logDeriv_gammaFactor_of_re_pos_or_im_ne_zero χ (.inr (by simp [hT0.ne'])),
          logDeriv_gammaFactor_of_re_pos_or_im_ne_zero χ (.inr (by simp [hT0.ne']))]
        simp only [hev, ↓reduceIte]
        simp [Complex.add_im, Complex.neg_im, Complex.mul_im,
          TernaryGoldbach.RSBounds.BacklundGammaReflection.gammaReflectionDifference,
          TernaryGoldbach.RSBounds.BacklundGammaReflection.reflectedArg,
          TernaryGoldbach.RSBounds.BacklundGammaReflection.directArg]
        ring
      simp_rw [hgam_eq]
      exact (TernaryGoldbach.RSBounds.BacklundGammaReflection.abs_integral_gammaReflectionDifference_le
        hT1 hδ0.le hδ1).trans (div_le_div_of_nonneg_right (by nlinarith) hT0.le)
    · have hgam_eq : ∀ σ : ℝ,
          (logDeriv (DirichletCharacter.gammaFactor χ) (((1 - σ : ℝ) : ℂ) + T * I)).im -
          (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + T * I)).im =
          (1 / 2) *
            ((Complex.digamma ((((2 - σ : ℝ) : ℂ) + T * I) / 2)).im -
             (Complex.digamma ((((σ + 1 : ℝ) : ℂ) + T * I) / 2)).im) := by
        intro σ
        rw [logDeriv_gammaFactor_of_re_pos_or_im_ne_zero χ (.inr (by simp [hT0.ne'])),
          logDeriv_gammaFactor_of_re_pos_or_im_ne_zero χ (.inr (by simp [hT0.ne']))]
        simp only [hev, ↓reduceIte]
        simp only [Complex.add_im, Complex.neg_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
          Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
        have h1 : (((((1 - σ : ℝ) : ℂ) + T * I) + 1) / 2) = (((2 - σ : ℝ) : ℂ) + T * I) / 2 := by
          congr 1; push_cast; ring
        have h2 : ((((σ : ℂ) + T * I) + 1) / 2) = (((σ + 1 : ℝ) : ℂ) + T * I) / 2 := by
          congr 1; push_cast; ring
        rw [h1, h2]
        ring
      simp_rw [hgam_eq]
      exact DirichletGammaPhaseOdd.abs_integral_oddGammaReflectionDifference_le hT1 hδ0.le hδ1
  have h := TernaryGoldbach.RSBounds.BacklundPairedPower.argument_bound
    (f := fun z => DirichletCharacter.LFunction χ (z + T * I))
    (g := fun z => DirichletCharacter.LFunction χ⁻¹ (z - T * I))
    (θ := dirHArg χ T (5 / 4)) (E := 4 / T) hR (by positivity) hf_ana hg_ana
    (by simpa using LFunction_horizontal_ne_zero hχ hχ1 hT0 hgood (5 / 4))
    (by
      have hc : (5 / 4 : ℂ) - T * I = conj ((5 / 4 : ℂ) + T * I) := by
        rw [map_add, map_mul, Complex.conj_I, map_div₀, map_ofNat, map_ofNat, Complex.conj_ofReal]
        ring
      rw [hc, DirichletBasics.LFunction_conj χ⁻¹ hχ1' ((5 / 4 : ℂ) + T * I), inv_inv])
    hB hB0 hfb hgb
    (dirHArg_continuous hχ hχ1 hT0 hgood (5 / 4)).continuousOn
    (fun n x _ hcos => powerAverage_dir_eq_zero_of_cos hχ hχ1 hT0 hgood (5 / 4) x n hcos)
    hdelta
  rw [dirHArg_sub_eq_integral hχ hχ1 hT0 hgood (5 / 4) (5 / 4) (1 / 2)] at h
  convert h using 1 <;> ring

end DirichletCountIdentity
end

-- ============================================================================
-- Batch 3: DirichletCircleMajorant, ZetaCaseQ1, and Top-level Theorem
-- ============================================================================

section
open Complex Real MeasureTheory Filter Set
open scoped Topology BigOperators ComplexConjugate Interval

namespace DirichletCircleMajorant

open TernaryGoldbach.RSBounds.BacklundLowScalar
open TernaryGoldbach.RSBounds.SmallTotientProduct

private lemma nonneg_of_hasDerivAt {f f' : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ici 0))
    (hd : ∀ x : ℝ, 0 < x → HasDerivAt f (f' x) x)
    (h0 : 0 ≤ f 0) (hf' : ∀ x : ℝ, 0 < x → 0 ≤ f' x) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ f x := by
  have hm : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0) hf
      (fun y hy => (hd y (by simpa [interior_Ici] using hy)).differentiableAt.differentiableWithinAt)
      (fun y hy => by
        have hy0 : 0 < y := by simpa [interior_Ici] using hy
        rw [(hd y hy0).deriv]
        exact hf' y hy0)
  exact h0.trans (hm (by simp) hx hx)

lemma cos_taylor_bounds {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x ∧
      Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 := by
  have h1 : ∀ t : ℝ, 0 ≤ t → 0 ≤ t - Real.sin t := fun t ht =>
    nonneg_of_hasDerivAt (f := fun u : ℝ => u - Real.sin u) (f' := fun u : ℝ => 1 - Real.cos u)
      (by fun_prop) (fun u _ => (hasDerivAt_id u).sub (Real.hasDerivAt_sin u))
      (by norm_num) (fun u _ => sub_nonneg.mpr (Real.cos_le_one u)) ht
  have h2 : ∀ t : ℝ, 0 ≤ t → 0 ≤ Real.cos t - (1 - t ^ 2 / 2) := fun t ht =>
    nonneg_of_hasDerivAt (f := fun u : ℝ => Real.cos u - (1 - u ^ 2 / 2))
      (f' := fun u : ℝ => u - Real.sin u) (by fun_prop)
      (fun u _ => ((Real.hasDerivAt_cos u).sub ((hasDerivAt_const u (1 : ℝ)).sub
        ((hasDerivAt_pow 2 u).div_const 2))).congr_deriv (by push_cast; ring))
      (by norm_num) (fun u hu => h1 u hu.le) ht
  have h3 : ∀ t : ℝ, 0 ≤ t → 0 ≤ Real.sin t - (t - t ^ 3 / 6) := fun t ht =>
    nonneg_of_hasDerivAt (f := fun u : ℝ => Real.sin u - (u - u ^ 3 / 6))
      (f' := fun u : ℝ => Real.cos u - (1 - u ^ 2 / 2)) (by fun_prop)
      (fun u _ => ((Real.hasDerivAt_sin u).sub ((hasDerivAt_id u).sub
        ((hasDerivAt_pow 3 u).div_const 6))).congr_deriv (by push_cast; ring))
      (by norm_num) (fun u hu => h2 u hu.le) ht
  have h4 : ∀ t : ℝ, 0 ≤ t → 0 ≤ (1 - t ^ 2 / 2 + t ^ 4 / 24) - Real.cos t := fun t ht =>
    nonneg_of_hasDerivAt (f := fun u : ℝ => (1 - u ^ 2 / 2 + u ^ 4 / 24) - Real.cos u)
      (f' := fun u : ℝ => Real.sin u - (u - u ^ 3 / 6)) (by fun_prop)
      (fun u _ => ((((hasDerivAt_const u (1 : ℝ)).sub ((hasDerivAt_pow 2 u).div_const 2)).add
        ((hasDerivAt_pow 4 u).div_const 24)).sub (Real.hasDerivAt_cos u)).congr_deriv
          (by push_cast; ring))
      (by norm_num) (fun u hu => h3 u hu.le) ht
  have h5 : ∀ t : ℝ, 0 ≤ t → 0 ≤ (t - t ^ 3 / 6 + t ^ 5 / 120) - Real.sin t := fun t ht =>
    nonneg_of_hasDerivAt (f := fun u : ℝ => (u - u ^ 3 / 6 + u ^ 5 / 120) - Real.sin u)
      (f' := fun u : ℝ => (1 - u ^ 2 / 2 + u ^ 4 / 24) - Real.cos u) (by fun_prop)
      (fun u _ => ((((hasDerivAt_id u).sub ((hasDerivAt_pow 3 u).div_const 6)).add
        ((hasDerivAt_pow 5 u).div_const 120)).sub (Real.hasDerivAt_sin u)).congr_deriv
          (by push_cast; ring))
      (by norm_num) (fun u hu => h4 u hu.le) ht
  have h6 : ∀ t : ℝ, 0 ≤ t → 0 ≤ Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720) :=
    fun t ht =>
    nonneg_of_hasDerivAt (f := fun u : ℝ => Real.cos u - (1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720))
      (f' := fun u : ℝ => (u - u ^ 3 / 6 + u ^ 5 / 120) - Real.sin u) (by fun_prop)
      (fun u _ => ((Real.hasDerivAt_cos u).sub ((((hasDerivAt_const u (1 : ℝ)).sub
        ((hasDerivAt_pow 2 u).div_const 2)).add ((hasDerivAt_pow 4 u).div_const 24)).sub
        ((hasDerivAt_pow 6 u).div_const 720))).congr_deriv (by push_cast; ring))
      (by norm_num) (fun u hu => h5 u hu.le) ht
  have h7 : ∀ t : ℝ, 0 ≤ t →
      0 ≤ Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040) := fun t ht =>
    nonneg_of_hasDerivAt (f := fun u : ℝ => Real.sin u - (u - u ^ 3 / 6 + u ^ 5 / 120 - u ^ 7 / 5040))
      (f' := fun u : ℝ => Real.cos u - (1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720)) (by fun_prop)
      (fun u _ => ((Real.hasDerivAt_sin u).sub ((((hasDerivAt_id u).sub
        ((hasDerivAt_pow 3 u).div_const 6)).add ((hasDerivAt_pow 5 u).div_const 120)).sub
        ((hasDerivAt_pow 7 u).div_const 5040))).congr_deriv (by push_cast; ring))
      (by norm_num) (fun u hu => h6 u hu.le) ht
  have h8 : ∀ t : ℝ, 0 ≤ t →
      0 ≤ (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320) - Real.cos t := fun t ht =>
    nonneg_of_hasDerivAt
      (f := fun u : ℝ => (1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320) - Real.cos u)
      (f' := fun u : ℝ => Real.sin u - (u - u ^ 3 / 6 + u ^ 5 / 120 - u ^ 7 / 5040)) (by fun_prop)
      (fun u _ => (((((hasDerivAt_const u (1 : ℝ)).sub ((hasDerivAt_pow 2 u).div_const 2)).add
        ((hasDerivAt_pow 4 u).div_const 24)).sub ((hasDerivAt_pow 6 u).div_const 720)).add
        ((hasDerivAt_pow 8 u).div_const 40320)).sub (Real.hasDerivAt_cos u) |>.congr_deriv
          (by push_cast; ring))
      (by norm_num) (fun u hu => h7 u hu.le) ht
  exact ⟨sub_nonneg.mp (h6 x hx), sub_nonneg.mp (h8 x hx)⟩

noncomputable def Rdir : ℝ := 8 / 5
noncomputable def sigmaDir (θ : ℝ) : ℝ := 5 / 4 + Rdir * Real.cos θ
noncomputable def a2 : ℝ := Real.arccos (15 / 32)
noncomputable def a65 : ℝ := Real.arccos (-(1 / 32))
noncomputable def a15 : ℝ := Real.arccos (-(29 / 32))

private lemma arccos_bounds_of_cos_bounds {y l u : ℝ}
    (hl0 : 0 ≤ l) (hlπ : l ≤ Real.pi) (hu0 : 0 ≤ u) (huπ : u ≤ Real.pi)
    (hlo : y ≤ Real.cos l) (hhi : Real.cos u ≤ y) :
    l ≤ Real.arccos y ∧ Real.arccos y ≤ u := by
  constructor
  · have h := Real.arccos_le_arccos hlo
    rwa [Real.arccos_cos hl0 hlπ] at h
  · have h := Real.arccos_le_arccos hhi
    rwa [Real.arccos_cos hu0 huπ] at h

lemma a2_bounds : (1.080 : ℝ) ≤ a2 ∧ a2 ≤ 1.086 := by
  have h1 := (cos_taylor_bounds (x := 1.080) (by norm_num)).1
  have h2 := (cos_taylor_bounds (x := 1.086) (by norm_num)).2
  norm_num at h1 h2
  have hlo : (15 / 32 : ℝ) ≤ Real.cos 1.080 := by linarith
  have hhi : Real.cos 1.086 ≤ (15 / 32 : ℝ) := by linarith
  have h := arccos_bounds_of_cos_bounds (by norm_num) (by linarith [Real.pi_gt_three])
    (by norm_num) (by linarith [Real.pi_gt_three]) hlo hhi
  simpa [a2] using h

lemma a65_bounds : Real.pi - 1.542 ≤ a65 ∧ a65 ≤ Real.pi - 1.538 := by
  have h1 := (cos_taylor_bounds (x := 1.538) (by norm_num)).1
  have h2 := (cos_taylor_bounds (x := 1.542) (by norm_num)).2
  norm_num at h1 h2
  have hb := arccos_bounds_of_cos_bounds (by norm_num) (by linarith [Real.pi_gt_three])
    (by norm_num) (by linarith [Real.pi_gt_three])
    (by linarith : (1 / 32 : ℝ) ≤ Real.cos 1.538) (by linarith : Real.cos 1.542 ≤ (1 / 32 : ℝ))
  have heq : a65 = Real.pi - Real.arccos (1 / 32) := by
    unfold a65
    rw [show (-(1 / 32 : ℝ)) = -(1 / 32) from rfl, Real.arccos_neg]
  rw [heq]
  constructor <;> linarith

lemma a15_bounds : Real.pi - 0.438 ≤ a15 ∧ a15 ≤ Real.pi - 0.435 := by
  have h1 := (cos_taylor_bounds (x := 0.435) (by norm_num)).1
  have h2 := (cos_taylor_bounds (x := 0.438) (by norm_num)).2
  norm_num at h1 h2
  have hb := arccos_bounds_of_cos_bounds (by norm_num) (by linarith [Real.pi_gt_three])
    (by norm_num) (by linarith [Real.pi_gt_three])
    (by linarith : (29 / 32 : ℝ) ≤ Real.cos 0.435) (by linarith : Real.cos 0.438 ≤ (29 / 32 : ℝ))
  have heq : a15 = Real.pi - Real.arccos (29 / 32) := by
    unfold a15
    rw [show (-(29 / 32 : ℝ)) = -(29 / 32) from rfl, Real.arccos_neg]
  rw [heq]
  constructor <;> linarith

lemma cos_a2 : Real.cos a2 = 15 / 32 := Real.cos_arccos (by norm_num) (by norm_num)
lemma cos_a65 : Real.cos a65 = -(1 / 32) := Real.cos_arccos (by norm_num) (by norm_num)
lemma cos_a15 : Real.cos a15 = -(29 / 32) := Real.cos_arccos (by norm_num) (by norm_num)

lemma a2_nonneg : 0 ≤ a2 := Real.arccos_nonneg _
lemma a2_le_a65 : a2 ≤ a65 := Real.arccos_le_arccos (by norm_num)
lemma a65_le_a15 : a65 ≤ a15 := Real.arccos_le_arccos (by norm_num)
lemma a15_le_pi : a15 ≤ Real.pi := Real.arccos_le_pi _
lemma a65_le_pi : a65 ≤ Real.pi := a65_le_a15.trans a15_le_pi
lemma a2_le_pi : a2 ≤ Real.pi := a2_le_a65.trans a65_le_pi

lemma sin_a65_bounds : (0.9995 : ℝ) ≤ Real.sin a65 ∧ Real.sin a65 ≤ 0.9996 := by
  have h : Real.sin a65 = Real.sqrt (1 - (-(1 / 32 : ℝ)) ^ 2) := Real.sin_arccos _
  rw [h]
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  · rw [Real.sqrt_le_iff]
    norm_num

lemma sin_a15_bounds : (0.4227 : ℝ) ≤ Real.sin a15 ∧ Real.sin a15 ≤ 0.4228 := by
  have h : Real.sin a15 = Real.sqrt (1 - (-(29 / 32 : ℝ)) ^ 2) := Real.sin_arccos _
  rw [h]
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  · rw [Real.sqrt_le_iff]
    norm_num

private lemma log_cert_lt {c : LogCert} (hc : c.Valid) {u : ℚ} (hu : c.upper < u) :
    Real.log (c.ratio : ℝ) < (u : ℝ) :=
  (LogCert.log_bounds hc).2.trans_lt (by exact_mod_cast hu)

lemma log_cert_32_15_lo : (0.7576 : ℝ) ≤ Real.log (32 / 15) := by
  have h := LogCert.log_gt (c := ⟨1, 15, 1⟩) (by decide) (l := (7576 / 10000 : ℚ)) (by decide +kernel)
  norm_num [LogCert.ratio] at h ⊢
  linarith

lemma log_cert_165_hi : Real.log 1.65 ≤ 0.501 := by
  have h := log_cert_lt (c := ⟨0, 100, 65⟩) (by decide) (u := (501 / 1000 : ℚ)) (by decide +kernel)
  norm_num [LogCert.ratio] at h ⊢
  exact h.le

lemma log_cert_6_bounds : (1.791 : ℝ) ≤ Real.log 6 ∧ Real.log 6 ≤ 1.792 := by
  have hl := LogCert.log_gt (c := ⟨2, 2, 1⟩) (by decide) (l := (1791 / 1000 : ℚ)) (by decide +kernel)
  have hu := log_cert_lt (c := ⟨2, 2, 1⟩) (by decide) (u := (1792 / 1000 : ℚ)) (by decide +kernel)
  norm_num [LogCert.ratio] at hl hu ⊢
  exact ⟨hl.le, hu.le⟩

lemma log_cert_1326_bounds : (2.584 : ℝ) ≤ Real.log 13.26 ∧ Real.log 13.26 ≤ 2.585 := by
  have hl := LogCert.log_gt (c := ⟨3, 400, 263⟩) (by decide) (l := (2584 / 1000 : ℚ)) (by decide +kernel)
  have hu := log_cert_lt (c := ⟨3, 400, 263⟩) (by decide) (u := (2585 / 1000 : ℚ)) (by decide +kernel)
  norm_num [LogCert.ratio] at hl hu ⊢
  exact ⟨hl.le, hu.le⟩

lemma log_cert_1433_bounds : (2.662 : ℝ) ≤ Real.log 14.33 ∧ Real.log 14.33 ≤ 2.663 := by
  have hl := LogCert.log_gt (c := ⟨3, 800, 633⟩) (by decide) (l := (2662 / 1000 : ℚ)) (by decide +kernel)
  have hu := log_cert_lt (c := ⟨3, 800, 633⟩) (by decide) (u := (2663 / 1000 : ℚ)) (by decide +kernel)
  norm_num [LogCert.ratio] at hl hu ⊢
  exact ⟨hl.le, hu.le⟩

lemma log_cert_15_bounds : (2.708 : ℝ) ≤ Real.log 15 ∧ Real.log 15 ≤ 2.709 := by
  have hl := LogCert.log_gt (c := ⟨3, 8, 7⟩) (by decide) (l := (2708 / 1000 : ℚ)) (by decide +kernel)
  have hu := log_cert_lt (c := ⟨3, 8, 7⟩) (by decide) (u := (2709 / 1000 : ℚ)) (by decide +kernel)
  norm_num [LogCert.ratio] at hl hu ⊢
  exact ⟨hl.le, hu.le⟩

lemma log_cert_3426_hi : Real.log 3.426 ≤ 1.232 := by
  have hu := log_cert_lt (c := ⟨1, 1000, 713⟩) (by decide) (u := (1232 / 1000 : ℚ)) (by decide +kernel)
  norm_num [LogCert.ratio] at hu ⊢
  exact hu.le

lemma log_cert_4_lo : (1.386 : ℝ) ≤ Real.log 4 := by
  have hl := LogCert.log_gt (c := ⟨1, 1, 1⟩) (by decide) (l := (1386 / 1000 : ℚ)) (by decide +kernel)
  norm_num [LogCert.ratio] at hl ⊢
  exact hl.le

lemma log_cert_10_bounds : (2.302 : ℝ) ≤ Real.log 10 ∧ Real.log 10 ≤ 2.303 := by
  have hl := LogCert.log_gt (c := ⟨3, 4, 1⟩) (by decide) (l := (2302 / 1000 : ℚ)) (by decide +kernel)
  have hu := log_cert_lt (c := ⟨3, 4, 1⟩) (by decide) (u := (2303 / 1000 : ℚ)) (by decide +kernel)
  norm_num [LogCert.ratio] at hl hu ⊢
  exact ⟨hl.le, hu.le⟩

lemma log_cert_12_hi : Real.log 12 ≤ 2.485 := by
  have hu := log_cert_lt (c := ⟨3, 2, 1⟩) (by decide) (u := (2485 / 1000 : ℚ)) (by decide +kernel)
  norm_num [LogCert.ratio] at hu ⊢
  exact hu.le

lemma log_cert_43_div_2pi_hi : Real.log (4.3 / (2 * Real.pi)) ≤ -0.379 := by
  have h43 := log_cert_lt (c := ⟨2, 40, 3⟩) (by decide) (u := (14587 / 10000 : ℚ)) (by decide +kernel)
  norm_num [LogCert.ratio] at h43
  rw [show (4.3 : ℝ) = 43 / 10 by norm_num, Real.log_div (by norm_num) (by positivity)]
  linarith [TernaryGoldbach.RSBounds.BacklundAngularCoefficients.log_two_pi_lower]

lemma log_cert_166_div_2pi_hi : Real.log (1.66 / (2 * Real.pi)) ≤ -1.3309 := by
  have h166 := log_cert_lt (c := ⟨0, 100, 66⟩) (by decide) (u := (50685 / 100000 : ℚ)) (by decide +kernel)
  norm_num [LogCert.ratio] at h166
  rw [show (1.66 : ℝ) = 83 / 50 by norm_num, Real.log_div (by norm_num) (by positivity)]
  linarith [TernaryGoldbach.RSBounds.BacklundAngularCoefficients.log_two_pi_lower]

noncomputable def fourPieceScalar (cStrip P σ : ℝ) : ℝ :=
  if 2 ≤ σ then Real.log 1.65
  else if 6 / 5 ≤ σ then Real.log 6
  else if -(1 / 5) ≤ σ then Real.log cStrip + ((6 / 5 - σ) / 2) * P
  else Real.log 15 + (1 / 2 - σ) * P

lemma fourPieceScalar_nonneg {cStrip P σ : ℝ} (hc : 1 ≤ cStrip) (hP : 0 ≤ P) :
    0 ≤ fourPieceScalar cStrip P σ := by
  unfold fourPieceScalar
  split_ifs with h1 h2 h3
  · exact Real.log_nonneg (by norm_num)
  · exact Real.log_nonneg (by norm_num)
  · have := Real.log_nonneg hc
    nlinarith [show 0 ≤ (6 / 5 - σ) / 2 by linarith]
  · have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 15)
    nlinarith [show 0 ≤ 1 / 2 - σ by linarith]

private lemma fourPiece_sector_values (cStrip P : ℝ) :
    (∀ θ ∈ Set.Ioo 0 a2, fourPieceScalar cStrip P (sigmaDir θ) = Real.log 1.65) ∧
    (∀ θ ∈ Set.Ioo a2 a65, fourPieceScalar cStrip P (sigmaDir θ) = Real.log 6) ∧
    (∀ θ ∈ Set.Ioo a65 a15, fourPieceScalar cStrip P (sigmaDir θ) =
      Real.log cStrip + ((6 / 5 - sigmaDir θ) / 2) * P) ∧
    (∀ θ ∈ Set.Ioo a15 Real.pi, fourPieceScalar cStrip P (sigmaDir θ) =
      Real.log 15 + (1 / 2 - sigmaDir θ) * P) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ hθ
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.1.le a2_le_pi hθ.2
    rw [cos_a2] at hcos
    have hs : 2 < sigmaDir θ := by dsimp [sigmaDir, Rdir]; linarith
    simp [fourPieceScalar, hs.le]
  · intro θ hθ
    have hcos1 := Real.cos_lt_cos_of_nonneg_of_le_pi a2_nonneg (hθ.2.le.trans a65_le_pi) hθ.1
    have hcos2 := Real.cos_lt_cos_of_nonneg_of_le_pi (a2_nonneg.trans hθ.1.le) a65_le_pi hθ.2
    rw [cos_a2] at hcos1
    rw [cos_a65] at hcos2
    have h1 : sigmaDir θ < 2 := by dsimp [sigmaDir, Rdir]; linarith
    have h2 : 6 / 5 < sigmaDir θ := by dsimp [sigmaDir, Rdir]; linarith
    simp [fourPieceScalar, not_le.mpr h1, h2.le]
  · intro θ hθ
    have hcos1 := Real.cos_lt_cos_of_nonneg_of_le_pi (a2_nonneg.trans a2_le_a65)
      (hθ.2.le.trans a15_le_pi) hθ.1
    have hcos2 := Real.cos_lt_cos_of_nonneg_of_le_pi ((a2_nonneg.trans a2_le_a65).trans hθ.1.le)
      a15_le_pi hθ.2
    rw [cos_a65] at hcos1
    rw [cos_a15] at hcos2
    have h1 : sigmaDir θ < 6 / 5 := by dsimp [sigmaDir, Rdir]; linarith
    have h2 : sigmaDir θ < 2 := by linarith
    have h3 : -(1 / 5 : ℝ) ≤ sigmaDir θ := by dsimp [sigmaDir, Rdir]; linarith
    simp only [fourPieceScalar, if_neg (not_le.mpr h2), if_neg (not_le.mpr h1), if_pos h3]
  · intro θ hθ
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (a2_nonneg.trans (a2_le_a65.trans a65_le_a15))
      hθ.2.le hθ.1
    rw [cos_a15] at hcos
    have h1 : sigmaDir θ < -(1 / 5 : ℝ) := by dsimp [sigmaDir, Rdir]; linarith
    have h2 : sigmaDir θ < 6 / 5 := by linarith
    have h3 : sigmaDir θ < 2 := by linarith
    simp only [fourPieceScalar, if_neg (not_le.mpr h3), if_neg (not_le.mpr h2), if_neg (not_le.mpr h1)]

private lemma fourPiece_sector_integrable (cStrip P : ℝ) :
    IntervalIntegrable (fun θ => fourPieceScalar cStrip P (sigmaDir θ)) volume 0 a2 ∧
    IntervalIntegrable (fun θ => fourPieceScalar cStrip P (sigmaDir θ)) volume a2 a65 ∧
    IntervalIntegrable (fun θ => fourPieceScalar cStrip P (sigmaDir θ)) volume a65 a15 ∧
    IntervalIntegrable (fun θ => fourPieceScalar cStrip P (sigmaDir θ)) volume a15 Real.pi := by
  have hv := fourPiece_sector_values cStrip P
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (intervalIntegrable_const (c := Real.log 1.65)).congr_uIoo
    rw [Set.uIoo_of_le a2_nonneg]
    exact fun θ hθ => (hv.1 θ hθ).symm
  · apply (intervalIntegrable_const (c := Real.log 6)).congr_uIoo
    rw [Set.uIoo_of_le a2_le_a65]
    exact fun θ hθ => (hv.2.1 θ hθ).symm
  · have hc : Continuous (fun θ : ℝ => Real.log cStrip + ((6 / 5 - sigmaDir θ) / 2) * P) := by
      unfold sigmaDir; fun_prop
    apply (hc.intervalIntegrable a65 a15).congr_uIoo
    rw [Set.uIoo_of_le a65_le_a15]
    exact fun θ hθ => (hv.2.2.1 θ hθ).symm
  · have hc : Continuous (fun θ : ℝ => Real.log 15 + (1 / 2 - sigmaDir θ) * P) := by
      unfold sigmaDir; fun_prop
    apply (hc.intervalIntegrable a15 Real.pi).congr_uIoo
    rw [Set.uIoo_of_le a15_le_pi]
    exact fun θ hθ => (hv.2.2.2 θ hθ).symm

lemma fourPiece_intervalIntegrable (cStrip P : ℝ) :
    IntervalIntegrable (fun θ => fourPieceScalar cStrip P (sigmaDir θ)) volume 0 Real.pi := by
  obtain ⟨h1, h2, h3, h4⟩ := fourPiece_sector_integrable cStrip P
  exact ((h1.trans h2).trans h3).trans h4

lemma fourPiece_circleIntegrable (cStrip P : ℝ) :
    CircleIntegrable (fun z : ℂ => fourPieceScalar cStrip P z.re) (5 / 4 : ℂ) Rdir := by
  have hi := fourPiece_intervalIntegrable cStrip P
  unfold sigmaDir at hi
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
    TernaryGoldbach.RSBounds.BacklundCircleMajorant.circleIntegrable_re_of_upper hi

lemma fourPiece_circleAverage_eq (cStrip P : ℝ) :
    circleAverage (fun z : ℂ => fourPieceScalar cStrip P z.re) (5 / 4 : ℂ) Rdir =
      (a2 * Real.log 1.65 + (a65 - a2) * Real.log 6 + (a15 - a65) * Real.log cStrip +
        (Real.pi - a15) * Real.log 15 +
        (P / 2 * (-(1 / 20 : ℝ) * (a15 - a65) - Rdir * (Real.sin a15 - Real.sin a65)) +
          P * (-(3 / 4 : ℝ) * (Real.pi - a15) + Rdir * Real.sin a15))) / Real.pi := by
  have hi := fourPiece_intervalIntegrable cStrip P
  have he := TernaryGoldbach.RSBounds.BacklundCircleMajorant.circleAverage_re_eq_upper
    (c := 5 / 4) (r := Rdir) (f := fourPieceScalar cStrip P) (by
      simpa only [sigmaDir] using hi)
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at he
  change circleAverage (fun z : ℂ => fourPieceScalar cStrip P z.re) (5 / 4 : ℂ) Rdir = _ at he
  rw [he]
  congr 1
  obtain ⟨h1, h2, h3, h4⟩ := fourPiece_sector_integrable cStrip P
  have hv := fourPiece_sector_values cStrip P
  have he1 := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) a2_nonneg hv.1
  have he2 := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) a2_le_a65 hv.2.1
  have he3 := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) a65_le_a15 hv.2.2.1
  have he4 := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) a15_le_pi hv.2.2.2
  change (∫ θ in (0 : ℝ)..Real.pi, fourPieceScalar cStrip P (sigmaDir θ)) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals ((h1.trans h2).trans h3) h4,
    ← intervalIntegral.integral_add_adjacent_intervals (h1.trans h2) h3,
    ← intervalIntegral.integral_add_adjacent_intervals h1 h2, he1, he2, he3, he4]
  have i1 : (∫ θ in (0 : ℝ)..a2, Real.log 1.65) = a2 * Real.log 1.65 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have i2 : (∫ θ in a2..a65, Real.log 6) = (a65 - a2) * Real.log 6 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have i3 : (∫ θ in a65..a15, Real.log cStrip + ((6 / 5 - sigmaDir θ) / 2) * P) =
      (a15 - a65) * Real.log cStrip +
        P / 2 * (-(1 / 20 : ℝ) * (a15 - a65) - Rdir * (Real.sin a15 - Real.sin a65)) := by
    have hpt : ∀ θ : ℝ, Real.log cStrip + ((6 / 5 - sigmaDir θ) / 2) * P =
        (Real.log cStrip - P / 40) + (-Rdir * P / 2) * Real.cos θ := fun θ => by
      unfold sigmaDir; ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_add intervalIntegrable_const
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_cos,
      smul_eq_mul]
    ring
  have i4 : (∫ θ in a15..Real.pi, Real.log 15 + (1 / 2 - sigmaDir θ) * P) =
      (Real.pi - a15) * Real.log 15 +
        P * (-(3 / 4 : ℝ) * (Real.pi - a15) + Rdir * Real.sin a15) := by
    have hpt : ∀ θ : ℝ, Real.log 15 + (1 / 2 - sigmaDir θ) * P =
        (Real.log 15 - 3 / 4 * P) + (-Rdir * P) * Real.cos θ := fun θ => by
      unfold sigmaDir; ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_add intervalIntegrable_const
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_cos,
      Real.sin_pi, smul_eq_mul]
    ring
  rw [i1, i2, i3, i4]
  ring

private lemma fourPiece_slope_num_le :
    -(1 / 20 : ℝ) * (a15 - a65) - Rdir * (Real.sin a15 - Real.sin a65) +
      2 * (-(3 / 4 : ℝ) * (Real.pi - a15) + Rdir * Real.sin a15) ≤ 1.569 := by
  have ha65 := a65_bounds
  have ha15 := a15_bounds
  have hs65 := sin_a65_bounds
  have hs15 := sin_a15_bounds
  unfold Rdir
  linarith

lemma fourPiece_average_dir_le {P : ℝ} (hP : 0 ≤ P) :
    circleAverage (fun z : ℂ => fourPieceScalar 13.26 P z.re) (5 / 4 : ℂ) Rdir /
        Real.log (32 / 15) ≤ 2.3186 + 0.3297 * P := by
  rw [fourPiece_circleAverage_eq]
  have ha2 := a2_bounds
  have ha65 := a65_bounds
  have ha15 := a15_bounds
  have hl1 := log_cert_165_hi
  have hl6 := log_cert_6_bounds
  have hl13 := log_cert_1326_bounds
  have hl15 := log_cert_15_bounds
  have hpi_lo : (3.1415 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d4]
  have hpi_hi : Real.pi ≤ 3.1416 := by linarith [Real.pi_lt_d4]
  have hC : a2 * Real.log 1.65 + (a65 - a2) * Real.log 6 + (a15 - a65) * Real.log 13.26 +
      (Real.pi - a15) * Real.log 15 ≤ 5.51806 := by
    have hm1 : a2 * (Real.log 1.65 - Real.log 6) ≤ 1.080 * (0.501 - 1.791) := by nlinarith
    have hm2 : a65 * (Real.log 6 - Real.log 13.26) ≤ (3.1415 - 1.542) * (1.792 - 2.584) := by nlinarith
    have hm3 : a15 * (Real.log 13.26 - Real.log 15) ≤ (3.1415 - 0.438) * (2.585 - 2.708) := by nlinarith
    have hm4 : Real.pi * Real.log 15 ≤ 3.1416 * 2.709 := by nlinarith
    nlinarith
  have hS : P / 2 * (-(1 / 20 : ℝ) * (a15 - a65) - Rdir * (Real.sin a15 - Real.sin a65)) +
      P * (-(3 / 4 : ℝ) * (Real.pi - a15) + Rdir * Real.sin a15) ≤ (1.569 / 2) * P := by
    nlinarith [fourPiece_slope_num_le]
  have hq : 0.7576 ≤ Real.log (32 / 15) := log_cert_32_15_lo
  have hden : (3.1415 : ℝ) * 0.7576 ≤ Real.pi * Real.log (32 / 15) := by nlinarith
  rw [div_div, div_le_iff₀ (mul_pos Real.pi_pos (Real.log_pos (by norm_num)))]
  nlinarith

lemma fourPiece_average_zeta_le {P : ℝ} (hP : 0 ≤ P) :
    circleAverage (fun z : ℂ => fourPieceScalar 14.33 P z.re) (5 / 4 : ℂ) Rdir /
        Real.log (32 / 15) ≤ 2.355 + 0.3297 * P := by
  rw [fourPiece_circleAverage_eq]
  have ha2 := a2_bounds
  have ha65 := a65_bounds
  have ha15 := a15_bounds
  have hl1 := log_cert_165_hi
  have hl6 := log_cert_6_bounds
  have hl14 := log_cert_1433_bounds
  have hl15 := log_cert_15_bounds
  have hpi_lo : (3.1415 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d4]
  have hpi_hi : Real.pi ≤ 3.1416 := by linarith [Real.pi_lt_d4]
  have hC : a2 * Real.log 1.65 + (a65 - a2) * Real.log 6 + (a15 - a65) * Real.log 14.33 +
      (Real.pi - a15) * Real.log 15 ≤ 5.60418 := by
    have hm1 : a2 * (Real.log 1.65 - Real.log 6) ≤ 1.080 * (0.501 - 1.791) := by nlinarith
    have hm2 : a65 * (Real.log 6 - Real.log 14.33) ≤ (3.1415 - 1.542) * (1.792 - 2.662) := by nlinarith
    have hm3 : a15 * (Real.log 14.33 - Real.log 15) ≤ (3.1415 - 0.438) * (2.663 - 2.708) := by nlinarith
    have hm4 : Real.pi * Real.log 15 ≤ 3.1416 * 2.709 := by nlinarith
    nlinarith
  have hS : P / 2 * (-(1 / 20 : ℝ) * (a15 - a65) - Rdir * (Real.sin a15 - Real.sin a65)) +
      P * (-(3 / 4 : ℝ) * (Real.pi - a15) + Rdir * Real.sin a15) ≤ (1.569 / 2) * P := by
    nlinarith [fourPiece_slope_num_le]
  have hq : 0.7576 ≤ Real.log (32 / 15) := log_cert_32_15_lo
  have hden : (3.1415 : ℝ) * 0.7576 ≤ Real.pi * Real.log (32 / 15) := by nlinarith
  rw [div_div, div_le_iff₀ (mul_pos Real.pi_pos (Real.log_pos (by norm_num)))]
  nlinarith

lemma zeta_norm_le_165_of_two_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ 1.65 := by
  have hs1 : 1 < s.re := by linarith
  have hax := TernaryGoldbach.RSBounds.BacklundZetaBoundary.zeta_norm_le_real_axis hs1
  have hsum_le : ‖riemannZeta (s.re : ℂ)‖ ≤ ‖riemannZeta ((2 : ℝ) : ℂ)‖ := by
    rw [TernaryGoldbach.RSBounds.CenterNumerics.norm_zeta_eq_tsum_rpow hs1,
      TernaryGoldbach.RSBounds.CenterNumerics.norm_zeta_eq_tsum_rpow (by norm_num)]
    apply Summable.tsum_le_tsum _ (Real.summable_nat_rpow.mpr (by linarith))
      (Real.summable_nat_rpow.mpr (by norm_num))
    intro n
    rcases n with _ | _ | k
    · simp [Real.zero_rpow (by linarith : -s.re ≠ 0)]
    · simp
    · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ k + 2)) (by linarith)
  have hz := TernaryGoldbach.RSBounds.CenterNumerics.zeta_tail_upper (σ := 2)
    (by norm_num) (N := 10) (by norm_num)
  norm_num [TernaryGoldbach.RSBounds.CenterNumerics.rpowSum] at hz
  rw [Complex.ofReal_ofNat] at hsum_le
  exact hax.trans (hsum_le.trans (by linarith))

lemma zeta_norm_le_6_of_six_fifths_le {s : ℂ} (hs : 6 / 5 ≤ s.re) :
    ‖riemannZeta s‖ ≤ 6 := by
  have hs1 : 1 < s.re := by linarith
  have hax := TernaryGoldbach.RSBounds.BacklundZetaBoundary.zeta_norm_le_real_axis hs1
  have hsum_le : ‖riemannZeta (s.re : ℂ)‖ ≤ ‖riemannZeta ((6 / 5 : ℝ) : ℂ)‖ := by
    rw [TernaryGoldbach.RSBounds.CenterNumerics.norm_zeta_eq_tsum_rpow hs1,
      TernaryGoldbach.RSBounds.CenterNumerics.norm_zeta_eq_tsum_rpow (by norm_num)]
    apply Summable.tsum_le_tsum _ (Real.summable_nat_rpow.mpr (by linarith))
      (Real.summable_nat_rpow.mpr (by norm_num))
    intro n
    rcases n with _ | _ | k
    · simp [Real.zero_rpow (by linarith : -s.re ≠ 0)]
    · simp
    · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ k + 2)) (by linarith)
  have hz := TernaryGoldbach.RSBounds.CenterNumerics.zeta_tail_upper (σ := 6 / 5)
    (by norm_num) (N := 1) (by norm_num)
  norm_num [TernaryGoldbach.RSBounds.CenterNumerics.rpowSum] at hz
  exact hax.trans (hsum_le.trans (by convert hz using 2; norm_num))

lemma sphere_dir_bounds {z : ℂ} (hz : z ∈ Metric.sphere (5 / 4 : ℂ) Rdir) :
    -(7 / 20 : ℝ) ≤ z.re ∧ z.re ≤ 57 / 20 ∧ |z.im| ≤ 8 / 5 := by
  rw [Metric.mem_sphere, dist_eq_norm] at hz
  have hre : |z.re - 5 / 4| ≤ 8 / 5 := by
    have := Complex.abs_re_le_norm (z - (5 / 4 : ℂ))
    rw [hz] at this
    simpa [Rdir, Complex.sub_re] using this
  have him : |z.im| ≤ 8 / 5 := by
    have := Complex.abs_im_le_norm (z - (5 / 4 : ℂ))
    rw [hz] at this
    simpa [Rdir, Complex.sub_im] using this
  rcases abs_le.mp hre with ⟨h1, h2⟩
  exact ⟨by linarith, by linarith, him⟩

lemma LFunction_sphere_le {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {T : ℝ} (hT : 2 ≤ T)
    {z : ℂ} (hz : z ∈ Metric.sphere (5 / 4 : ℂ) Rdir) {t : ℝ} (ht : |t| ≤ T + 8 / 5) :
    ‖DirichletCharacter.LFunction χ ((z.re : ℂ) + t * I)‖ ≤
      Real.exp (fourPieceScalar 13.26 (Real.log ((q : ℝ) * (T + 6.6) / (2 * Real.pi))) z.re) := by
  have hb := sphere_dir_bounds hz
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  set P := Real.log ((q : ℝ) * (T + 6.6) / (2 * Real.pi))
  have hP0 : 0 ≤ P := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith [Real.pi_lt_d4]
  have him5 : (|((z.re : ℂ) + t * I).im| + 5) ≤ T + 6.6 := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
    linarith
  have hbase_le : ((q : ℝ) * (|((z.re : ℂ) + t * I).im| + 5) / (2 * Real.pi)) ≤
      (q : ℝ) * (T + 6.6) / (2 * Real.pi) := by gcongr
  have hbase_pos : 0 < (q : ℝ) * (|((z.re : ℂ) + t * I).im| + 5) / (2 * Real.pi) := by positivity
  unfold fourPieceScalar
  by_cases h2 : 2 ≤ z.re
  · rw [if_pos h2, Real.exp_log (by norm_num)]
    have hs : 1 < ((z.re : ℂ) + t * I).re := by simp; linarith
    exact (DirichletBasics.norm_LFunction_le_zeta χ hs).trans
      (zeta_norm_le_165_of_two_le (by simp; exact h2))
  · by_cases h65 : 6 / 5 ≤ z.re
    · rw [if_neg h2, if_pos h65, Real.exp_log (by norm_num)]
      have hs : 1 < ((z.re : ℂ) + t * I).re := by simp; linarith
      exact (DirichletBasics.norm_LFunction_le_zeta χ hs).trans
        (zeta_norm_le_6_of_six_fifths_le (by simp; exact h65))
    · by_cases h15 : -(1 / 5 : ℝ) ≤ z.re
      · rw [if_neg h2, if_neg h65, if_pos h15, Real.exp_add, Real.exp_log (by norm_num)]
        have hstrip := StripPhragmenLindelof.norm_LFunction_strip_le hq hχ
          (s := (z.re : ℂ) + t * I) (by simp; linarith) (by simp; linarith)
        have hpow : ((q : ℝ) * (|((z.re : ℂ) + t * I).im| + 5) / (2 * Real.pi)) ^
            ((6 / 5 - ((z.re : ℂ) + t * I).re) / 2) ≤ Real.exp (((6 / 5 - z.re) / 2) * P) := by
          have hex : 0 ≤ (6 / 5 - z.re) / 2 := by linarith
          calc ((q : ℝ) * (|((z.re : ℂ) + t * I).im| + 5) / (2 * Real.pi)) ^
                ((6 / 5 - ((z.re : ℂ) + t * I).re) / 2)
              ≤ ((q : ℝ) * (T + 6.6) / (2 * Real.pi)) ^ ((6 / 5 - z.re) / 2) := by
                  simpa [Complex.add_re] using Real.rpow_le_rpow hbase_pos.le hbase_le hex
            _ = Real.exp (((6 / 5 - z.re) / 2) * P) := by
                  rw [Real.rpow_def_of_pos (by positivity), mul_comm]
        exact hstrip.trans ((mul_le_mul_of_nonneg_left hpow (by norm_num)).trans_eq (by norm_num))
      · rw [if_neg h2, if_neg h65, if_neg h15, Real.exp_add, Real.exp_log (by norm_num)]
        have hleft := StripPhragmenLindelof.norm_LFunction_left_le hq hχ
          (s := (z.re : ℂ) + t * I) (by simp; exact hb.1) (by simp; linarith)
        have hpow : ((q : ℝ) * (|((z.re : ℂ) + t * I).im| + 5) / (2 * Real.pi)) ^
            (1 / 2 - ((z.re : ℂ) + t * I).re) ≤ Real.exp ((1 / 2 - z.re) * P) := by
          have hex : 0 ≤ 1 / 2 - z.re := by linarith
          calc ((q : ℝ) * (|((z.re : ℂ) + t * I).im| + 5) / (2 * Real.pi)) ^
                (1 / 2 - ((z.re : ℂ) + t * I).re)
              ≤ ((q : ℝ) * (T + 6.6) / (2 * Real.pi)) ^ (1 / 2 - z.re) := by
                  simpa [Complex.add_re] using Real.rpow_le_rpow hbase_pos.le hbase_le hex
            _ = Real.exp ((1 / 2 - z.re) * P) := by
                  rw [Real.rpow_def_of_pos (by positivity), mul_comm]
        exact hleft.trans ((mul_le_mul_of_nonneg_left hpow (by norm_num)).trans_eq (by norm_num))

open Classical in
theorem dir_zero_count_good {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {T : ℝ} (hT : 2 ≤ T)
    (hgood : DirichletCountIdentity.dirGoodHeight χ T) :
    |((∑ ρ ∈ DirichletCountIdentity.dirZeros χ T,
        analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ) -
      (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
      0.35 * Real.log ((q : ℝ) * T) + 6.5 := by
  have hχ1 : χ ≠ 1 := DirichletBasics.ne_one_of_isPrimitive_of_two_le hq hχ
  have hχ1' : χ⁻¹ ≠ 1 := fun h => hχ1 (by simpa using congrArg Inv.inv h)
  have hT0 : 0 < T := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  let P : ℝ := Real.log ((q : ℝ) * (T + 6.6) / (2 * Real.pi))
  have hP0 : 0 ≤ P := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Real.pi_lt_d4]
  let B : ℂ → ℝ := fun z => fourPieceScalar 13.26 P z.re
  have hB : CircleIntegrable B (5 / 4 : ℂ) Rdir := fourPiece_circleIntegrable 13.26 P
  have hB0 : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) Rdir, 0 ≤ B z := fun z _ =>
    fourPieceScalar_nonneg (by norm_num) hP0
  have hfb : ∀ χ0 : DirichletCharacter ℂ q, χ0.IsPrimitive →
      ∀ z ∈ Metric.sphere (5 / 4 : ℂ) Rdir,
      ‖DirichletCharacter.LFunction χ0 (z + T * I)‖ ≤ Real.exp (B z) := by
    intro χ0 hχ0 z hz
    have hsp := sphere_dir_bounds hz
    have ht : |T + z.im| ≤ T + 8 / 5 := by rw [abs_le]; constructor <;> linarith [abs_le.mp hsp.2.2]
    have heq : z + T * I = (z.re : ℂ) + ((T + z.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [add_comm]
    rw [heq]
    exact LFunction_sphere_le hq hχ0 hT hz ht
  have hgb : ∀ χ0 : DirichletCharacter ℂ q, χ0.IsPrimitive →
      ∀ z ∈ Metric.sphere (5 / 4 : ℂ) Rdir,
      ‖DirichletCharacter.LFunction χ0⁻¹ (z - T * I)‖ ≤ Real.exp (B z) := by
    intro χ0 hχ0 z hz
    have hsp := sphere_dir_bounds hz
    have ht : |z.im - T| ≤ T + 8 / 5 := by rw [abs_le]; constructor <;> linarith [abs_le.mp hsp.2.2]
    have heq : z - T * I = (z.re : ℂ) + ((z.im - T : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [sub_eq_add_neg]
    rw [heq]
    exact LFunction_sphere_le hq hχ0.inv hT hz ht
  have hhor1 := DirichletCountIdentity.horizontal_argument_bound_dir hq hχ (R := Rdir) hT hgood
    (by norm_num [Rdir]) hB hB0 (hfb χ hχ) (hgb χ hχ)
  have hhor2 := DirichletCountIdentity.horizontal_argument_bound_dir hq hχ.inv (R := Rdir) hT
    (DirichletCountIdentity.dirGoodHeight_inv hχ1 hgood) (by norm_num [Rdir]) hB hB0
    (hfb χ⁻¹ hχ.inv) (hgb χ⁻¹ hχ.inv)
  have hanchor : ∀ χ0 : DirichletCharacter ℂ q,
      -Real.log 3.426 ≤ Real.log ‖DirichletCharacter.LFunction χ0 ((5 / 4 : ℂ) + T * I)‖ := by
    intro χ0
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 3.426)
      (DirichletBasics.LFunction_norm_lower_five_fourths_3426 χ0 T)
    simpa [Real.log_div, Real.log_one] using hl
  have hqlog : Real.log (Rdir / (3 / 4)) = Real.log (32 / 15) := by
    unfold Rdir; norm_num
  have hqlog_pos : 0 < Real.log (32 / 15) := Real.log_pos (by norm_num)
  have hcnt := DirichletCountIdentity.count_identity_dir hq hχ hT hgood
  have havg := fourPiece_average_dir_le hP0
  have hl3426 : Real.log 3.426 / Real.log (32 / 15) ≤ 1.6262 := by
    rw [div_le_iff₀ hqlog_pos]
    nlinarith [log_cert_3426_hi, log_cert_32_15_lo]
  have hP_upper : P ≤ Real.log ((q : ℝ) * T) - 0.379 := by
    have heq : (q : ℝ) * (T + 6.6) / (2 * Real.pi) =
        ((q : ℝ) * T) * ((1 + 6.6 / T) / (2 * Real.pi)) := by field_simp
    rw [show P = Real.log ((q : ℝ) * (T + 6.6) / (2 * Real.pi)) from rfl, heq,
      Real.log_mul (by positivity) (by positivity)]
    have hrat : (1 + 6.6 / T) / (2 * Real.pi) ≤ 4.3 / (2 * Real.pi) := by
      gcongr
      have h66 : 6.6 / T ≤ 3.3 := by rw [div_le_iff₀ hT0]; linarith
      linarith
    have hl := (Real.log_le_log (by positivity) hrat).trans log_cert_43_div_2pi_hi
    linarith
  have hlog_qT : (1.386 : ℝ) ≤ Real.log ((q : ℝ) * T) :=
    log_cert_4_lo.trans (Real.log_le_log (by norm_num) (by nlinarith))
  have hpiT : 4 / (Real.pi * T) ≤ 0.637 := by
    rw [div_le_iff₀ (by positivity)]
    have := Real.pi_gt_d2
    nlinarith
  have hif : (if χ.Even then (0.33 : ℝ) else 0.70) ≤ 0.70 := by
    by_cases h : χ.Even <;> simp [h] <;> norm_num
  have hcomb : |∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
        (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + T * I)).im| / Real.pi +
      |∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
        (logDeriv (DirichletCharacter.LFunction χ⁻¹) ((σ : ℂ) + T * I)).im| / Real.pi ≤
      (circleAverage B (5 / 4 : ℂ) Rdir + Real.log 3.426) / Real.log (32 / 15) +
        4 / (Real.pi * T) := by
    rw [hqlog] at hhor1 hhor2
    have ha1 := hanchor χ
    have ha2 := hanchor χ⁻¹
    have hdiv1 : (circleAverage B (5 / 4 : ℂ) Rdir -
        Real.log ‖DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + T * I)‖) /
        (2 * Real.log (32 / 15)) ≤
        (circleAverage B (5 / 4 : ℂ) Rdir + Real.log 3.426) / (2 * Real.log (32 / 15)) := by
      gcongr; linarith
    have hdiv2 : (circleAverage B (5 / 4 : ℂ) Rdir -
        Real.log ‖DirichletCharacter.LFunction χ⁻¹ ((5 / 4 : ℂ) + T * I)‖) /
        (2 * Real.log (32 / 15)) ≤
        (circleAverage B (5 / 4 : ℂ) Rdir + Real.log 3.426) / (2 * Real.log (32 / 15)) := by
      gcongr; linarith
    have hhalf : (circleAverage B (5 / 4 : ℂ) Rdir + Real.log 3.426) / (2 * Real.log (32 / 15)) +
        (circleAverage B (5 / 4 : ℂ) Rdir + Real.log 3.426) / (2 * Real.log (32 / 15)) =
        (circleAverage B (5 / 4 : ℂ) Rdir + Real.log 3.426) / Real.log (32 / 15) := by ring
    have hpi_sum : 2 / (Real.pi * T) + 2 / (Real.pi * T) = 4 / (Real.pi * T) := by ring
    linarith [hhalf, hpi_sum]
  rw [add_div] at hcomb
  change _ ≤ _ at hcnt
  have h1 : circleAverage B (5 / 4 : ℂ) Rdir / Real.log (32 / 15) ≤ 2.3186 + 0.3297 * P := havg
  have hslope : 0.3297 * Real.log ((q : ℝ) * T) ≤ 0.35 * Real.log ((q : ℝ) * T) - 0.0203 * 1.386 := by
    linarith
  linarith

private lemma finite_right_gap_dir (S : Finset ℂ) (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ ρ ∈ S, T < |ρ.im| → T + δ ≤ |ρ.im| := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, le_rfl, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨δ, hδ0, hδ1, hgap⟩ := ih
    by_cases haT : T < |a.im|
    · refine ⟨min δ ((|a.im| - T) / 2), lt_min hδ0 (by linarith),
        (min_le_left _ _).trans hδ1, ?_⟩
      intro ρ hρ hρT
      rcases Finset.mem_insert.mp hρ with rfl | hρ
      · linarith [min_le_right δ ((|ρ.im| - T) / 2)]
      · exact (add_le_add le_rfl (min_le_left _ _)).trans (hgap ρ hρ hρT)
    · refine ⟨δ, hδ0, hδ1, ?_⟩
      intro ρ hρ hρT
      rcases Finset.mem_insert.mp hρ with rfl | hρ
      · exact (haT hρT).elim
      · exact hgap ρ hρ hρT

theorem dir_zero_count_all {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {T : ℝ} (hT : 2 ≤ T) :
    ∃ Z : Finset ℂ,
      (∀ s : ℂ, s ∈ Z ↔ 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ DirichletCharacter.LFunction χ s = 0) ∧
      |((∑ ρ ∈ Z, analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ) -
        (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
        0.35 * Real.log ((q : ℝ) * T) + 6.5 := by
  have hχ1 : χ ≠ 1 := DirichletBasics.ne_one_of_isPrimitive_of_two_le hq hχ
  have hT0 : 0 < T := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  refine ⟨DirichletCountIdentity.dirZeros χ T, fun s =>
    DirichletCountIdentity.mem_dirZeros_iff hχ1 hT0, ?_⟩
  obtain ⟨δ, hδ0, hδ1, hgap⟩ := finite_right_gap_dir (DirichletCountIdentity.dirZeros χ (T + 1)) T
  let S : ℕ → ℝ := fun n => T + (δ / 2) * (1 / ((n : ℝ) + 1))
  have hSmem : ∀ n : ℕ, S n ∈ Set.Ioo T (T + δ) := fun n => by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hrec : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one hn).mpr hn1
    have hp : 0 < (δ / 2) * (1 / ((n : ℝ) + 1)) := by positivity
    have hq_le := mul_le_mul_of_nonneg_left hrec (show 0 ≤ δ / 2 by positivity)
    dsimp [S]
    constructor <;> nlinarith
  have hloc : ∀ R ∈ Set.Ioo T (T + δ),
      DirichletCountIdentity.dirGoodHeight χ R ∧
      DirichletCountIdentity.dirZeros χ R = DirichletCountIdentity.dirZeros χ T := by
    intro R hR
    have hR0 : 0 < R := hT0.trans hR.1
    have hR1 : R < T + 1 := lt_of_lt_of_le hR.2 (by linarith)
    have hg : DirichletCountIdentity.dirGoodHeight χ R := by
      intro ρ h1 h2 he hz
      have hρ : ρ ∈ DirichletCountIdentity.dirZeros χ (T + 1) :=
        (DirichletCountIdentity.mem_dirZeros_iff hχ1 (by linarith)).mpr
          ⟨h1, h2, by rw [he]; exact hR1.le, hz⟩
      have hh := hgap ρ hρ (by rw [he]; exact hR.1)
      rw [he] at hh
      linarith [hR.2]
    refine ⟨hg, ?_⟩
    apply Finset.ext
    intro ρ
    rw [DirichletCountIdentity.mem_dirZeros_iff hχ1 hR0,
      DirichletCountIdentity.mem_dirZeros_iff hχ1 hT0]
    refine and_congr_right fun _ => and_congr_right fun _ => ?_
    constructor
    · rintro ⟨hRle, hz⟩
      refine ⟨?_, hz⟩
      by_contra h
      have hTρ : T < |ρ.im| := lt_of_not_ge h
      have hρ : ρ ∈ DirichletCountIdentity.dirZeros χ (T + 1) :=
        (DirichletCountIdentity.mem_dirZeros_iff hχ1 (by linarith)).mpr
          ⟨by assumption, by assumption, hRle.trans hR1.le, hz⟩
      linarith [hgap ρ hρ hTρ, hR.2]
    · rintro ⟨hTle, hz⟩
      exact ⟨hTle.trans hR.1.le, hz⟩
  have hlim : Filter.Tendsto S Filter.atTop (𝓝 T) := by
    have hh : Filter.Tendsto (fun n : ℕ => T + (δ / 2) * (1 / ((n : ℝ) + 1))) Filter.atTop
        (𝓝 (T + (δ / 2) * 0)) := tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (δ / 2))
    simpa [S] using hh
  let M : ℝ → ℝ := fun t => (t / Real.pi) * Real.log ((q : ℝ) * t / (2 * Real.pi * Real.exp 1))
  let Bnd : ℝ → ℝ := fun t => 0.35 * Real.log ((q : ℝ) * t) + 6.5
  have hqT0 : (q : ℝ) * T ≠ 0 := mul_ne_zero hq0.ne' hT0.ne'
  have hM : ContinuousAt M T := by
    have harg0 : (q : ℝ) * T / (2 * Real.pi * Real.exp 1) ≠ 0 := by positivity
    dsimp only [M]
    fun_prop (disch := assumption)
  have hB : ContinuousAt Bnd T := by
    dsimp only [Bnd]
    fun_prop (disch := assumption)
  have hb : ∀ n : ℕ,
      |((∑ ρ ∈ DirichletCountIdentity.dirZeros χ T,
          analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ) - M (S n)| ≤
        Bnd (S n) := fun n => by
    have hl := hloc (S n) (hSmem n)
    have hbd := dir_zero_count_good hq hχ (by linarith [(hSmem n).1, hT]) hl.1
    rw [hl.2] at hbd
    exact hbd
  exact le_of_tendsto_of_tendsto
    ((tendsto_const_nhds.sub (hM.tendsto.comp hlim)).abs)
    (hB.tendsto.comp hlim) (Filter.Eventually.of_forall hb)

end DirichletCircleMajorant

namespace ZetaCaseQ1

open TernaryGoldbach.Explicit
open TernaryGoldbach.RSBounds.BacklundCountIdentity
open TernaryGoldbach.RSBounds.Rosser1941

lemma riemannZeta_ne_zero_of_re_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  have hσ_re : 0 < (σ : ℂ).re := by simp [h0]
  have hσ_ne : (σ : ℂ) ≠ 1 := fun h => h1.ne (by simpa using congrArg Complex.re h)
  have hI_re : (Izeta (σ : ℂ)).re ≤ 0 := by
    have hi := integrableOn_saw_integrand hσ_re
    rw [Izeta, ← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hi]
    apply MeasureTheory.integral_nonpos_of_ae
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    have ht1 : (1 : ℝ) < t := ht
    have hpow : ((t : ℂ) ^ (-((σ : ℂ) + 1))).re = t ^ (-(σ + 1)) := by
      rw [show (-((σ : ℂ) + 1)) = ((-(σ + 1) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow ht0.le, Complex.ofReal_re]
    have hpow_im : ((t : ℂ) ^ (-((σ : ℂ) + 1))).im = 0 := by
      rw [show (-((σ : ℂ) + 1)) = ((-(σ + 1) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow ht0.le, Complex.ofReal_im]
    simp only [Complex.reCLM_apply, saw, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.sub_im, Complex.ofReal_im, hpow, hpow_im, sub_self, mul_zero, sub_zero]
    have hfl : ((⌊t⌋₊ : ℝ) - t) ≤ 0 := sub_nonpos.mpr (Nat.floor_le ht0.le)
    exact mul_nonpos_of_nonpos_of_nonneg hfl (Real.rpow_nonneg ht0.le _)
  have hz_eq := zetaF_eq hσ_re
  have hre : 0 < (zetaF (σ : ℂ)).re := by
    rw [hz_eq]
    simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.one_re, Complex.ofReal_im, Complex.sub_im, Complex.one_im, Complex.mul_im,
      sub_zero, mul_zero, zero_mul]
    nlinarith [mul_nonneg h0.le (mul_nonneg (sub_nonneg.mpr h1.le) (neg_nonneg.mpr hI_re))]
  have hzf_ne : zetaF (σ : ℂ) ≠ 0 := fun h => hre.ne' (by rw [h, Complex.zero_re])
  rw [zetaF_of_ne hσ_ne] at hzf_ne
  exact right_ne_zero_of_mul hzf_ne

lemma analyticOrderNatAt_riemannZeta_conj {ρ : ℂ} (hρ : ρ ≠ 1) :
    analyticOrderNatAt riemannZeta (conj ρ) = analyticOrderNatAt riemannZeta ρ := by
  have hana_ne1 : ∀ z : ℂ, z ≠ 1 → AnalyticAt ℂ riemannZeta z := fun z hz =>
    Complex.analyticAt_iff_eventually_differentiableAt.mpr
      (Filter.eventually_of_mem (isOpen_ne.mem_nhds hz) fun w hw => differentiableAt_riemannZeta hw)
  have ha : AnalyticAt ℂ riemannZeta ρ := hana_ne1 ρ hρ
  have hρc : conj ρ ≠ 1 := fun h => hρ (by simpa using congrArg conj h)
  have hac : AnalyticAt ℂ riemannZeta (conj ρ) := hana_ne1 (conj ρ) hρc
  have hcon : IsPreconnected {z : ℂ | z ≠ 1} :=
    ((isConnected_compl_singleton_of_one_lt_rank
      (rank_real_complex ▸ by norm_num : 1 < Module.rank ℝ ℂ) 1).isPreconnected)
  have hntop : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    intro htop
    have heq := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun z hz => hana_ne1 z hz) hcon hρ (analyticOrderAt_eq_top.mp htop) (by norm_num : (2 : ℂ) ≠ 1)
    exact riemannZeta_ne_zero_of_one_lt_re (by norm_num) heq
  have hntop_c : analyticOrderAt riemannZeta (conj ρ) ≠ ⊤ := by
    intro htop
    have heq := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun z hz => hana_ne1 z hz) hcon hρc (analyticOrderAt_eq_top.mp htop) (by norm_num : (2 : ℂ) ≠ 1)
    exact riemannZeta_ne_zero_of_one_lt_re (by norm_num) heq
  set n := analyticOrderNatAt riemannZeta ρ
  obtain ⟨g, hga, hgne, hfg⟩ := ha.analyticOrderAt_ne_top.mp hntop
  let g₁ : ℂ → ℂ := fun w => conj (g (conj w))
  have hg1a : AnalyticAt ℂ g₁ (conj ρ) := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt, Metric.eventually_nhds_iff_ball] at hga
    obtain ⟨r, hr, hdiff⟩ := hga
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds (conj ρ) hr) fun w hw => ?_
    have hcw : conj w ∈ Metric.ball ρ r := by
      rw [Metric.mem_ball, dist_eq_norm] at hw
      rw [Metric.mem_ball, dist_eq_norm, ← Complex.norm_conj]
      simpa [map_sub, Complex.conj_conj] using hw
    have hd := (hdiff (conj w) hcw).hasDerivAt
    simpa only [g₁, Function.comp_def, Complex.conj_conj] using hd.conj_conj.differentiableAt
  have hg1ne : g₁ (conj ρ) ≠ 0 := by
    dsimp [g₁]
    rw [Complex.conj_conj]
    exact (map_ne_zero _).mpr hgne
  have hfg1 : ∀ᶠ w in 𝓝 (conj ρ), riemannZeta w = (w - conj ρ) ^ n • g₁ w := by
    have ht : Filter.Tendsto conj (𝓝 (conj ρ)) (𝓝 ρ) := by
      simpa [Complex.conj_conj] using (Complex.continuous_conj.continuousAt (x := conj ρ)).tendsto
    filter_upwards [ht.eventually hfg] with w hw
    have hconj := congrArg conj hw
    rw [← riemannZeta_conj, Complex.conj_conj] at hconj
    rw [hconj]
    simp only [smul_eq_mul, map_mul, map_pow, map_sub, Complex.conj_conj, g₁]
    rfl
  exact ((hac.analyticOrderNatAt_eq_iff hntop_c).mpr ⟨g₁, hg1a, hg1ne, hfg1⟩)

noncomputable def zetaZeros (T : ℝ) : Finset ℂ :=
  closedPositiveZeros T ∪ (closedPositiveZeros T).image conj

lemma mem_zetaZeros_iff {T : ℝ} (hT : 0 < T) {s : ℂ} :
    s ∈ zetaZeros T ↔ 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ riemannZeta s = 0 := by
  classical
  rw [zetaZeros, Finset.mem_union, Finset.mem_image, mem_closedPositiveZeros_iff hT]
  constructor
  · rintro (⟨hz, h0, hle⟩ | ⟨ρ, hρ, rfl⟩)
    · have hs1 : s.re < 1 := by
        by_contra hge
        push Not at hge
        exact riemannZeta_ne_zero_of_one_le_re hge hz
      have hs0 : 0 < s.re := by
        by_contra hle0
        push Not at hle0
        obtain ⟨n, hn⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos hle0).mp hz
        have him := congrArg Complex.im hn
        simp at him
        linarith
      exact ⟨hs0, hs1, abs_le.mpr ⟨by linarith, hle⟩, hz⟩
    · rw [mem_closedPositiveZeros_iff hT] at hρ
      rcases hρ with ⟨hz, h0, hle⟩
      have hzc : riemannZeta (conj ρ) = 0 := by rw [riemannZeta_conj, hz, map_zero]
      have hs1 : (conj ρ).re < 1 := by
        by_contra hge
        push Not at hge
        exact riemannZeta_ne_zero_of_one_le_re hge hzc
      have hs0 : 0 < (conj ρ).re := by
        by_contra hle0
        push Not at hle0
        obtain ⟨n, hn⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos hle0).mp hzc
        have him := congrArg Complex.im hn
        simp at him
        linarith
      exact ⟨hs0, hs1, by simpa using abs_le.mpr ⟨by linarith, hle⟩, hzc⟩
  · rintro ⟨hs0, hs1, hle, hz⟩
    have him_ne : s.im ≠ 0 := by
      intro him0
      have hs_eq : s = (s.re : ℂ) := by apply Complex.ext <;> simp [him0]
      rw [hs_eq] at hz
      exact riemannZeta_ne_zero_of_re_Ioo hs0 hs1 hz
    rcases lt_or_gt_of_ne him_ne with hneg | hpos
    · right
      refine ⟨conj s, (mem_closedPositiveZeros_iff hT).mpr ⟨?_, ?_, ?_⟩, Complex.conj_conj s⟩
      · rw [riemannZeta_conj, hz, map_zero]
      · simpa using neg_pos.mpr hneg
      · simpa using (abs_le.mp hle).1 |> neg_le_neg
    · left
      exact ⟨hz, hpos, (abs_le.mp hle).2⟩

lemma sum_zetaZeros_eq {T : ℝ} (hT : 0 < T) :
    (∑ ρ ∈ zetaZeros T, analyticOrderNatAt riemannZeta ρ) = 2 * N_le T := by
  classical
  have hdisj : Disjoint (closedPositiveZeros T) ((closedPositiveZeros T).image conj) := by
    rw [Finset.disjoint_left]
    intro ρ hρ1 hρ2
    rw [mem_closedPositiveZeros_iff hT] at hρ1
    rw [Finset.mem_image] at hρ2
    rcases hρ2 with ⟨w, hw, rfl⟩
    rw [mem_closedPositiveZeros_iff hT] at hw
    have : (conj w).im < 0 := by simp; exact hw.2.1
    linarith [hρ1.2.1]
  have hsum : (∑ ρ ∈ zetaZeros T, analyticOrderNatAt riemannZeta ρ) =
      (∑ ρ ∈ closedPositiveZeros T, analyticOrderNatAt riemannZeta ρ) +
      (∑ ρ ∈ (closedPositiveZeros T).image conj, analyticOrderNatAt riemannZeta ρ) := by
    rw [zetaZeros, Finset.sum_union hdisj]
  have himg : (∑ ρ ∈ (closedPositiveZeros T).image conj, analyticOrderNatAt riemannZeta ρ) =
      ∑ ρ ∈ closedPositiveZeros T, analyticOrderNatAt riemannZeta ρ := by
    rw [Finset.sum_image (fun a _ b _ h => (starRingEnd ℂ).injective h)]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have hρm := (mem_closedPositiveZeros_iff hT).mp hρ
    have hne1 : ρ ≠ 1 := fun h => by rw [h] at hρm; simp at hρm
    exact analyticOrderNatAt_riemannZeta_conj hne1
  have hN : N_le T = ∑ ρ ∈ closedPositiveZeros T, analyticOrderNatAt riemannZeta ρ := by
    unfold N_le
    rfl
  rw [hsum, himg, ← hN, two_mul]

lemma zeta_mid_sphere_le {T : ℝ} (hT10 : 10 ≤ T)
    {z : ℂ} (hz : z ∈ Metric.sphere (5 / 4 : ℂ) DirichletCircleMajorant.Rdir) {t : ℝ}
    (ht : |t| ≤ T + 8 / 5) (ht_low : T - 8 / 5 ≤ |t|) :
    ‖riemannZeta ((z.re : ℂ) + t * I)‖ ≤
      Real.exp (DirichletCircleMajorant.fourPieceScalar 14.33
        (Real.log ((T + 6.6) / (2 * Real.pi))) z.re) := by
  have hb := DirichletCircleMajorant.sphere_dir_bounds hz
  set P := Real.log ((T + 6.6) / (2 * Real.pi))
  have him5 : |((z.re : ℂ) + t * I).im| + 5 ≤ T + 6.6 := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
    linarith
  have hbase_le : (|((z.re : ℂ) + t * I).im| + 5) / (2 * Real.pi) ≤ (T + 6.6) / (2 * Real.pi) := by
    gcongr
  have hbase_pos : 0 < (|((z.re : ℂ) + t * I).im| + 5) / (2 * Real.pi) := by positivity
  unfold DirichletCircleMajorant.fourPieceScalar
  by_cases h2 : 2 ≤ z.re
  · rw [if_pos h2, Real.exp_log (by norm_num)]
    exact DirichletCircleMajorant.zeta_norm_le_165_of_two_le (by simp; exact h2)
  · by_cases h65 : 6 / 5 ≤ z.re
    · rw [if_neg h2, if_pos h65, Real.exp_log (by norm_num)]
      exact DirichletCircleMajorant.zeta_norm_le_6_of_six_fifths_le (by simp; exact h65)
    · by_cases h15 : -(1 / 5 : ℝ) ≤ z.re
      · rw [if_neg h2, if_neg h65, if_pos h15, Real.exp_add, Real.exp_log (by norm_num)]
        let s : ℂ := (z.re : ℂ) + t * I
        have hs_re1 : -(1 / 5 : ℝ) ≤ s.re := by simp [s]; linarith
        have hs_re2 : s.re ≤ 6 / 5 := by simp [s]; linarith
        have hs_im : 8.4 ≤ |s.im| := by simp [s]; linarith
        have hs1 : s ≠ 1 := fun h => by
          have := congrArg Complex.im h
          simp only [Complex.one_im] at this
          rw [this, abs_zero] at hs_im
          linarith
        have hzm2 : s + 2 ≠ 0 := fun h => by
          have := congrArg Complex.im h
          simp only [Complex.add_im, Complex.zero_im, Complex.im_ofNat, add_zero] at this
          rw [this, abs_zero] at hs_im
          linarith
        have hz_eq : riemannZeta s = ((s + 2) / (s - 1)) * StripPhragmenLindelof.zetaMod s := by
          rw [StripPhragmenLindelof.zetaMod_eq_of_ne_one hs1]
          field_simp [sub_ne_zero.mpr hs1, hzm2]
        have hrat : ‖(s + 2) / (s - 1)‖ ≤ 1.08 := by
          rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs1)),
            ← sq_le_sq₀ (norm_nonneg _) (by positivity)]
          rw [mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
          simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
            Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, Complex.one_im, add_zero, sub_zero]
          have hsq : (8.4 : ℝ) ^ 2 ≤ s.im ^ 2 := by
            rw [← sq_abs s.im]; nlinarith
          nlinarith [sq_nonneg (s.re - 1)]
        have hmod := StripPhragmenLindelof.norm_zetaMod_strip_le hs_re1 hs_re2
        have hpow : ((|s.im| + 5) / (2 * Real.pi)) ^ ((6 / 5 - s.re) / 2) ≤
            Real.exp (((6 / 5 - z.re) / 2) * P) := by
          have hex : 0 ≤ (6 / 5 - z.re) / 2 := by linarith
          calc ((|s.im| + 5) / (2 * Real.pi)) ^ ((6 / 5 - s.re) / 2)
              ≤ ((T + 6.6) / (2 * Real.pi)) ^ ((6 / 5 - z.re) / 2) := by
                  simpa [s, Complex.add_re] using Real.rpow_le_rpow hbase_pos.le hbase_le hex
            _ = Real.exp (((6 / 5 - z.re) / 2) * P) := by
                  rw [Real.rpow_def_of_pos (by positivity), mul_comm]
        rw [hz_eq, norm_mul]
        have hnn : 0 ≤ ((|s.im| + 5) / (2 * Real.pi)) ^ ((6 / 5 - s.re) / 2) :=
          Real.rpow_nonneg (by positivity) _
        calc ‖(s + 2) / (s - 1)‖ * ‖StripPhragmenLindelof.zetaMod s‖
            ≤ 1.08 * ((13 / 10 : ℝ) * (17 / 10 * 6) *
                ((|s.im| + 5) / (2 * Real.pi)) ^ ((6 / 5 - s.re) / 2)) :=
              mul_le_mul hrat hmod (norm_nonneg _) (by norm_num)
          _ ≤ 14.33 * ((|s.im| + 5) / (2 * Real.pi)) ^ ((6 / 5 - s.re) / 2) := by nlinarith
          _ ≤ 14.33 * Real.exp (((6 / 5 - z.re) / 2) * P) := by gcongr
      · rw [if_neg h2, if_neg h65, if_neg h15, Real.exp_add, Real.exp_log (by norm_num)]
        have hleft := StripPhragmenLindelof.norm_zeta_left_le (s := (z.re : ℂ) + t * I)
          (by simp; exact hb.1) (by simp; linarith)
        have hpow : ((|((z.re : ℂ) + t * I).im| + 5) / (2 * Real.pi)) ^
            (1 / 2 - ((z.re : ℂ) + t * I).re) ≤ Real.exp ((1 / 2 - z.re) * P) := by
          have hex : 0 ≤ 1 / 2 - z.re := by linarith
          calc ((|((z.re : ℂ) + t * I).im| + 5) / (2 * Real.pi)) ^
                (1 / 2 - ((z.re : ℂ) + t * I).re)
              ≤ ((T + 6.6) / (2 * Real.pi)) ^ (1 / 2 - z.re) := by
                  simpa [Complex.add_re] using Real.rpow_le_rpow hbase_pos.le hbase_le hex
            _ = Real.exp ((1 / 2 - z.re) * P) := by
                  rw [Real.rpow_def_of_pos (by positivity), mul_comm]
        exact hleft.trans ((mul_le_mul_of_nonneg_left hpow (by norm_num)).trans_eq (by norm_num))

private noncomputable def midBnd (t : ℝ) : ℝ :=
  0.5 + 0.5 * (2.355 + 0.3297 * Real.log ((t + 6.6) / (2 * Real.pi)) + 1.6262) +
    2.25 / (Real.pi * t)

lemma N_le_err_mid {T : ℝ} (hT10 : 10 ≤ T) :
    |(N_le T : ℝ) - mainTerm T| ≤ midBnd T := by
  have hT0 : 0 < T := by linarith
  have hM : ContinuousAt mainTerm T := by
    change ContinuousAt TernaryGoldbach.RSBounds.rosserF T
    exact (TernaryGoldbach.RSBounds.hasDerivAt_rosserF hT0).continuousAt
  have hB : ContinuousAt midBnd T := by
    have harg : (T + 6.6) / (2 * Real.pi) ≠ 0 := by positivity
    have hden : Real.pi * T ≠ 0 := by positivity
    unfold midBnd
    fun_prop (disch := assumption)
  refine closed_count_abs_le_of_good_height_bound hT0 hM hB ?_
  intro S hTS hgood
  have hS10 : 10 ≤ S := by linarith
  have hS1 : 1 ≤ S := by linarith
  have hS0 : 0 < S := by linarith
  let P : ℝ := Real.log ((S + 6.6) / (2 * Real.pi))
  have hP0 : 0 ≤ P := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Real.pi_lt_d4]
  let B : ℂ → ℝ := fun z => DirichletCircleMajorant.fourPieceScalar 14.33 P z.re
  have hB_int : CircleIntegrable B (5 / 4 : ℂ) DirichletCircleMajorant.Rdir :=
    DirichletCircleMajorant.fourPiece_circleIntegrable 14.33 P
  have hB0 : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) DirichletCircleMajorant.Rdir, 0 ≤ B z := fun z _ =>
    DirichletCircleMajorant.fourPieceScalar_nonneg (by norm_num) hP0
  have hfb : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) DirichletCircleMajorant.Rdir,
      ‖riemannZeta (z + S * I)‖ ≤ Real.exp (B z) := by
    intro z hz
    have hsp := DirichletCircleMajorant.sphere_dir_bounds hz
    have hzim := abs_le.mp hsp.2.2
    have heq : z + S * I = (z.re : ℂ) + ((S + z.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [add_comm]
    rw [heq]
    exact zeta_mid_sphere_le hS10 hz (by rw [abs_le]; constructor <;> linarith)
      (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hgb : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) DirichletCircleMajorant.Rdir,
      ‖riemannZeta (z - S * I)‖ ≤ Real.exp (B z) := by
    intro z hz
    have hsp := DirichletCircleMajorant.sphere_dir_bounds hz
    have hzim := abs_le.mp hsp.2.2
    have heq : z - S * I = (z.re : ℂ) + ((z.im - S : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [sub_eq_add_neg]
    rw [heq]
    exact zeta_mid_sphere_le hS10 hz (by rw [abs_le]; constructor <;> linarith)
      (by rw [abs_of_nonpos (by linarith)]; linarith)
  have hh := count_le_circle_majorant (T := S) (R := DirichletCircleMajorant.Rdir) (B := B)
    hS1 hgood (by norm_num [DirichletCircleMajorant.Rdir])
    (by dsimp [DirichletCircleMajorant.Rdir]; linarith) hB_int hB0 hfb hgb
  have hq : Real.log (DirichletCircleMajorant.Rdir / (3 / 4)) = Real.log (32 / 15) := by
    unfold DirichletCircleMajorant.Rdir; norm_num
  have havg := DirichletCircleMajorant.fourPiece_average_zeta_le hP0
  have hqlog_pos : 0 < Real.log (32 / 15) := Real.log_pos (by norm_num)
  have hl3426 : Real.log 3.426 / Real.log (32 / 15) ≤ 1.6262 := by
    rw [div_le_iff₀ hqlog_pos]
    nlinarith [DirichletCircleMajorant.log_cert_3426_hi, DirichletCircleMajorant.log_cert_32_15_lo]
  rw [hq] at hh
  have hsplit : (circleAverage B (5 / 4 : ℂ) DirichletCircleMajorant.Rdir + Real.log 3.426) /
      (2 * Real.log (32 / 15)) =
      0.5 * (circleAverage B (5 / 4 : ℂ) DirichletCircleMajorant.Rdir / Real.log (32 / 15) +
        Real.log 3.426 / Real.log (32 / 15)) := by ring
  have hpi_eq : 2 / (Real.pi * S) + 1 / (4 * Real.pi * S) = 2.25 / (Real.pi * S) := by ring
  unfold midBnd
  rw [hsplit, add_assoc, hpi_eq] at hh
  change circleAverage B (5 / 4 : ℂ) DirichletCircleMajorant.Rdir / Real.log (32 / 15) ≤
    2.355 + 0.3297 * P at havg
  dsimp only [P] at havg
  linarith

lemma N_le_ten_le_two : N_le 10 ≤ 2 := by
  have herr := N_le_err_mid (T := 10) le_rfl
  unfold midBnd at herr
  have hP : Real.log ((10 + 6.6 : ℝ) / (2 * Real.pi)) ≤ 2.303 - 1.3309 := by
    have heq : (10 + 6.6 : ℝ) / (2 * Real.pi) = 10 * (1.66 / (2 * Real.pi)) := by ring
    rw [heq, Real.log_mul (by norm_num) (by positivity)]
    linarith [DirichletCircleMajorant.log_cert_10_bounds.2,
      DirichletCircleMajorant.log_cert_166_div_2pi_hi]
  have hpi : 2.25 / (Real.pi * 10) ≤ 0.072 := by
    rw [div_le_iff₀ (by positivity)]
    have := Real.pi_gt_d4
    nlinarith
  have hm : mainTerm 10 ≤ 0.025 := by
    unfold mainTerm
    have hrat_hi : 10 / (2 * Real.pi) ≤ 1.5916 := by
      rw [div_le_iff₀ (by positivity)]
      have := Real.pi_gt_d4
      nlinarith
    have hrat_lo : 1.5915 ≤ 10 / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]
      have := Real.pi_lt_d4
      nlinarith
    have hlog_hi : Real.log (10 / (2 * Real.pi)) ≤ 2.303 - 1.8378 := by
      rw [Real.log_div (by norm_num) (by positivity)]
      linarith [DirichletCircleMajorant.log_cert_10_bounds.2,
        TernaryGoldbach.RSBounds.BacklundAngularCoefficients.log_two_pi_lower]
    have hlog_pos : 0 ≤ Real.log (10 / (2 * Real.pi)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      linarith [Real.pi_lt_d4]
    nlinarith
  have hub : (N_le 10 : ℝ) < 3 := by
    have := abs_le.mp herr
    linarith
  exact_mod_cast (by
    have hnat : (N_le 10 : ℝ) < ((3 : ℕ) : ℝ) := by simpa using hub
    have := Nat.cast_lt (α := ℝ).mp hnat
    omega : N_le 10 ≤ 2)

theorem zeta_zero_count {T : ℝ} (hT : 2 ≤ T) :
    ∃ Z : Finset ℂ,
      (∀ s : ℂ, s ∈ Z ↔ 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ riemannZeta s = 0) ∧
      |((∑ ρ ∈ Z, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) -
        (T / Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤
        0.35 * Real.log T + 6.5 := by
  have hT0 : 0 < T := by linarith
  refine ⟨zetaZeros T, fun s => mem_zetaZeros_iff hT0, ?_⟩
  rw [sum_zetaZeros_eq hT0, Nat.cast_mul, Nat.cast_ofNat]
  have hmt_diff : |2 * mainTerm T - (T / Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1))| = 7 / 4 := by
    have hlog : Real.log (T / (2 * Real.pi * Real.exp 1)) = Real.log (T / (2 * Real.pi)) - 1 := by
      rw [show T / (2 * Real.pi * Real.exp 1) = (T / (2 * Real.pi)) / Real.exp 1 by ring,
        Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
    unfold mainTerm
    rw [hlog, show 2 * (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8) -
      (T / Real.pi) * (Real.log (T / (2 * Real.pi)) - 1) = (7 / 4 : ℝ) by ring]
    norm_num
  by_cases h100 : 100 ≤ T
  · have hros := zero_count_bounds_high T h100
    rw [positiveZeroCount_eq hT0] at hros
    have hlT : (4.6 : ℝ) < Real.log T := TernaryGoldbach.RSBounds.BacklundFinalScalar.log_hundred_gt.trans_le
      (Real.log_le_log (by norm_num) h100)
    have hll : Real.log (Real.log T) ≤ 1.485 + Real.log T / 12 := by
      have hsub := Real.log_le_sub_one_of_pos (show 0 < Real.log T / 12 by positivity)
      rw [Real.log_div (by linarith) (by norm_num)] at hsub
      linarith [DirichletCircleMajorant.log_cert_12_hi]
    have hloglog_bd : 0.886 * Real.log (Real.log T) ≤ 1.316 + 0.074 * Real.log T := by
      linarith
    have htri : |2 * (N_le T : ℝ) - (T / Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤
        2 * |(N_le T : ℝ) - mainTerm T| + 7 / 4 := by
      have h1 := abs_add_le (2 * ((N_le T : ℝ) - mainTerm T))
        (2 * mainTerm T - (T / Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1)))
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), hmt_diff] at h1
      convert h1 using 2; ring
    change |(N_le T : ℝ) - mainTerm T| < _ at hros
    linarith [hros]
  · by_cases h10 : 10 ≤ T
    · have herr := N_le_err_mid h10
      unfold midBnd at herr
      have hP : Real.log ((T + 6.6) / (2 * Real.pi)) ≤ Real.log T - 1.3309 := by
        have heq : (T + 6.6) / (2 * Real.pi) = T * ((1 + 6.6 / T) / (2 * Real.pi)) := by field_simp
        rw [heq, Real.log_mul hT0.ne' (by positivity)]
        have hrat : (1 + 6.6 / T) / (2 * Real.pi) ≤ 1.66 / (2 * Real.pi) := by
          gcongr
          have h66 : 6.6 / T ≤ 0.66 := by rw [div_le_iff₀ hT0]; linarith
          linarith
        linarith [(Real.log_le_log (by positivity) hrat).trans DirichletCircleMajorant.log_cert_166_div_2pi_hi]
      have hlT : (2.302 : ℝ) ≤ Real.log T :=
        DirichletCircleMajorant.log_cert_10_bounds.1.trans (Real.log_le_log (by norm_num) h10)
      have hpiT : 2.25 / (Real.pi * T) ≤ 0.072 := by
        rw [div_le_iff₀ (by positivity)]
        have := Real.pi_gt_d4
        nlinarith
      have htri : |2 * (N_le T : ℝ) - (T / Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤
          2 * |(N_le T : ℝ) - mainTerm T| + 7 / 4 := by
        have h1 := abs_add_le (2 * ((N_le T : ℝ) - mainTerm T))
          (2 * mainTerm T - (T / Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1)))
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), hmt_diff] at h1
        convert h1 using 2; ring
      linarith
    · have hlt10 : T < 10 := lt_of_not_ge h10
      have hN_le : N_le T ≤ N_le 10 := by
        unfold N_le
        refine Finset.sum_le_sum_of_subset ?_
        intro ρ hρ
        rw [mem_closedPositiveZeros_iff hT0] at hρ
        exact (mem_closedPositiveZeros_iff (by norm_num)).mpr ⟨hρ.1, hρ.2.1, hρ.2.2.trans hlt10.le⟩
      have hN_real : (2 * (N_le T : ℝ)) ≤ 4 := by
        have : N_le T ≤ 2 := hN_le.trans N_le_ten_le_two
        exact_mod_cast (by omega : 2 * N_le T ≤ 4)
      have hM_nonpos : (T / Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1)) ≤ 0 := by
        refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (Real.log_nonpos (by positivity) ?_)
        rw [div_le_one (by positivity)]
        have := Real.pi_gt_three
        have := Real.exp_one_gt_d9
        nlinarith
      have hM_lower : -2 ≤ (T / Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1)) := by
        let u := T / (2 * Real.pi)
        have hu : 0 < u := by positivity
        have hlu := Real.log_le_sub_one_of_pos (show 0 < 1 / u by positivity)
        rw [Real.log_div one_ne_zero hu.ne', Real.log_one, zero_sub] at hlu
        have hm1 : -1 ≤ u * (Real.log u - 1) := by
          have := mul_le_mul_of_nonneg_left hlu hu.le
          rw [mul_sub, mul_one, mul_one_div_cancel hu.ne'] at this
          linarith
        have hMeq : (T / Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1)) =
            2 * (u * (Real.log u - 1)) := by
          rw [show T / (2 * Real.pi * Real.exp 1) = u / Real.exp 1 by dsimp [u]; ring,
            Real.log_div hu.ne' (Real.exp_pos 1).ne', Real.log_exp]
          dsimp [u]
          ring
        linarith
      have hl0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
      rw [abs_le]
      constructor <;> linarith

end ZetaCaseQ1
end

end Conjectures.Goldbach.GmDirichletZeroCountAux

/-- Explicit zero-counting formula for primitive Dirichlet `L`-functions (Trudgian 2015, Theorem 1). -/
theorem Conjectures.Goldbach.GmDirichletZeroCount :
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ T : ℝ, 2 ≤ T →
      ∃ Z : Finset ℂ,
        (∀ s : ℂ, s ∈ Z ↔ 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ DirichletCharacter.LFunction χ s = 0) ∧
        |((∑ ρ ∈ Z, analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ) -
          (T / Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
          0.35 * Real.log ((q : ℝ) * T) + 6.5) := by
  intro q hq0 χ hχ T hT
  by_cases hq1 : q = 1
  · subst hq1
    simp only [DirichletCharacter.LFunction_modOne_eq, Nat.cast_one, one_mul]
    exact Conjectures.Goldbach.GmDirichletZeroCountAux.ZetaCaseQ1.zeta_zero_count hT
  · have hq2 : 2 ≤ q := by have := NeZero.pos q; omega
    exact Conjectures.Goldbach.GmDirichletZeroCountAux.DirichletCircleMajorant.dir_zero_count_all hq2 hχ hT
