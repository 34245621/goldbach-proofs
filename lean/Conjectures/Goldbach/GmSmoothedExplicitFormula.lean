import Mathlib
import Conjectures.Goldbach.GmSmoothingKernelMellin

section
-- R581 Laplace
section
open MeasureTheory
open scoped ContDiff FourierTransform InnerProductSpace SchwartzMap

namespace GoldbachR581

/-- The bilateral Laplace transform `H` in the R581 formula. -/
noncomputable def laplaceTransform (h : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ s : ℝ, (h s : ℂ) * Complex.exp (z * (s : ℂ))

/-- The point with real part `σ` and imaginary part `t` on a vertical contour. -/
def verticalPoint (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I

@[simp] theorem verticalPoint_re (σ t : ℝ) : (verticalPoint σ t).re = σ := by
  simp [verticalPoint, Complex.mul_re]

@[simp] theorem verticalPoint_im (σ t : ℝ) : (verticalPoint σ t).im = t := by
  simp [verticalPoint, Complex.mul_im]

private noncomputable def tiltedWeight (h : ℝ → ℝ) (σ : ℝ) (s : ℝ) : ℂ :=
  (h s : ℂ) * Complex.exp ((σ : ℂ) * (s : ℂ))

private noncomputable def tiltedSchwartz {h : ℝ → ℝ} (hs : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) (σ : ℝ) : 𝓢(ℝ, ℂ) := by
  have htilt : HasCompactSupport (tiltedWeight h σ) := by
    have hint : HasCompactSupport (fun s : ℝ => (h s : ℂ)) := by
      apply hc.mono
      intro s hs
      simpa [Function.mem_support] using hs
    exact hint.mul_right
  have he : ContDiff ℝ ∞ (fun x : ℝ => Complex.exp ((σ : ℂ) * (x : ℂ))) :=
    Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
  exact htilt.toSchwartzMap ((Complex.ofRealCLM.contDiff.comp hs).mul he)

private theorem laplace_fourierInv (h : ℝ → ℝ) (σ w : ℝ) :
    laplaceTransform h (verticalPoint σ (2 * Real.pi * w)) = 𝓕⁻ (tiltedWeight h σ) w := by
  rw [laplaceTransform, Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards with x
  rw [show verticalPoint σ (2 * Real.pi * w) * (x : ℂ) =
      (σ : ℂ) * (x : ℂ) + (↑(2 * Real.pi * ⟪x, w⟫_ℝ) : ℂ) * Complex.I by
    simp only [verticalPoint, Real.inner_apply, Complex.ofReal_mul]
    ring, Complex.exp_add]
  simp only [tiltedWeight, smul_eq_mul]
  ring

private theorem laplace_fourierInv_schwartz {h : ℝ → ℝ} (hs : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) (σ w : ℝ) :
    laplaceTransform h (verticalPoint σ (2 * Real.pi * w)) = (𝓕⁻ (tiltedSchwartz hs hc σ)) w := by
  calc
    _ = 𝓕⁻ ((tiltedSchwartz hs hc σ) : ℝ → ℂ) w := laplace_fourierInv h σ w
    _ = _ := congrFun (SchwartzMap.fourierInv_coe _).symm w

/-- The transform on each fixed vertical line is integrable in the imaginary coordinate. -/
theorem integrable_laplace_vertical {h : ℝ → ℝ} (hs : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) (σ : ℝ) :
    Integrable (fun t : ℝ => laplaceTransform h (verticalPoint σ t)) := by
  have hπ : (2 * Real.pi) ≠ 0 := (mul_pos (by norm_num) Real.pi_pos).ne'
  apply (integrable_comp_mul_left_iff _ hπ).mp
  simp_rw [laplace_fourierInv_schwartz hs hc]
  exact (𝓕⁻ (tiltedSchwartz hs hc σ)).integrable

/-- Polynomial decay of every order on a fixed vertical line, in Fourier frequency units. -/
theorem laplace_vertical_decay {h : ℝ → ℝ} (hs : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) (σ : ℝ) (k : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, |t| ^ k * ‖laplaceTransform h (verticalPoint σ t)‖ ≤ C := by
  have hπ : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  let g := 𝓕⁻ (tiltedSchwartz hs hc σ)
  refine ⟨(2 * Real.pi) ^ k * (SchwartzMap.seminorm ℝ k 0) g, fun t => ?_⟩
  set w := t / (2 * Real.pi) with hw
  have ht : 2 * Real.pi * w = t := by rw [hw]; field_simp
  have hb := SchwartzMap.norm_pow_mul_le_seminorm ℝ g k w
  rw [← ht, laplace_fourierInv_schwartz hs hc, abs_mul, abs_of_pos hπ, mul_pow, mul_assoc]
  exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hb) (pow_nonneg hπ.le _)

/-- The Fourier inversion step of R581, with the vertical integral parametrized by its
imaginary coordinate. The factor `1 / (2π)` accounts for this parametrization. -/
theorem laplace_inversion {h : ℝ → ℝ} (hs : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (σ s : ℝ) : (h s : ℂ) = (↑(2 * Real.pi) : ℂ)⁻¹ *
      ∫ t : ℝ, laplaceTransform h (verticalPoint σ t) *
        Complex.exp (-(verticalPoint σ t) * (s : ℂ)) := by
  let f := tiltedSchwartz hs hc σ
  let F : ℝ → ℂ := fun t => laplaceTransform h (verticalPoint σ t) *
    Complex.exp (-(verticalPoint σ t) * (s : ℂ))
  have hπ : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hval : f s = (h s : ℂ) * Complex.exp ((σ : ℂ) * (s : ℂ)) := rfl
  have hinv : 𝓕 ((𝓕⁻ f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) s = f s := by
    change (𝓕 (𝓕⁻ f)) s = f s
    rw [FourierTransform.fourier_fourierInv_eq]
  calc
    (h s : ℂ) = Complex.exp (-(σ : ℂ) * (s : ℂ)) * f s := by
      rw [hval, neg_mul, Complex.exp_neg]
      have hne := Complex.exp_ne_zero ((σ : ℂ) * (s : ℂ))
      field_simp
    _ = ∫ t : ℝ, F (2 * Real.pi * t) := by
      rw [← hinv, Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      simp only [F, laplace_fourierInv_schwartz hs hc, smul_eq_mul]
      rw [show -(verticalPoint σ (2 * Real.pi * t)) * (s : ℂ) =
          -(σ : ℂ) * (s : ℂ) + (↑(-2 * Real.pi * t * s) : ℂ) * Complex.I by
        simp only [verticalPoint, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
        ring, Complex.exp_add]
      ring
    _ = (↑(2 * Real.pi) : ℂ)⁻¹ * ∫ t : ℝ, F t := by
      rw [Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hπ), Complex.real_smul, Complex.ofReal_inv]

/-- Differentiation under the integral for compactly supported weights. -/
theorem hasDerivAt_laplaceTransform {h : ℝ → ℝ} (hh : Continuous h)
    (hc : HasCompactSupport h) (z : ℂ) : HasDerivAt (laplaceTransform h)
      (∫ s : ℝ, (h s : ℂ) * (Complex.exp (z * (s : ℂ)) * (s : ℂ))) z := by
  let F (w : ℂ) (s : ℝ) := (h s : ℂ) * Complex.exp (w * (s : ℂ))
  let F' (w : ℂ) (s : ℝ) := (h s : ℂ) * (Complex.exp (w * (s : ℂ)) * (s : ℂ))
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : ℝ)
  let bound (s : ℝ) := ‖h s‖ * (Real.exp ((‖z‖ + 1) * R) * |s|)
  have hF (w : ℂ) : Continuous (F w) := by
    unfold F
    fun_prop
  have hF' : Continuous (F' z) := by
    unfold F'
    fun_prop
  have hcast : HasCompactSupport (fun s : ℝ => (h s : ℂ)) := by
    apply hc.mono
    intro s hs
    simpa [Function.mem_support] using hs
  have hbound : Integrable bound := by
    apply Continuous.integrable_of_hasCompactSupport
    · unfold bound
      fun_prop
    · exact hc.norm.mul_right
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
    (Metric.ball_mem_nhds z (by norm_num : 0 < (1 : ℝ)))
    (Filter.Eventually.of_forall fun w => (hF w).aestronglyMeasurable)
    ((hF z).integrable_of_hasCompactSupport hcast.mul_right) hF'.aestronglyMeasurable
    ?_ hbound ?_).2
  · filter_upwards with s w hw
    by_cases hs : h s = 0
    · simp [F', bound, hs]
    have hsr : |s| ≤ R := by
      have hm := hR (subset_closure (Function.mem_support.mpr hs))
      simpa [Metric.mem_closedBall, Real.norm_eq_abs] using hm
    have hwn : ‖w‖ ≤ ‖z‖ + 1 := by
      have hd := Metric.mem_ball.mp hw
      rw [dist_eq_norm] at hd
      have hle := norm_add_le (w - z) z
      rw [sub_add_cancel] at hle
      linarith
    have hexp : ‖Complex.exp (w * (s : ℂ))‖ ≤ Real.exp ((‖z‖ + 1) * R) := by
      apply (Complex.norm_exp_le_exp_norm _).trans
      rw [Real.exp_le_exp, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul hwn hsr (abs_nonneg _) (by positivity)
    simpa only [F', bound, norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp (abs_nonneg s)) (abs_nonneg (h s))
  · exact Filter.Eventually.of_forall fun s w _ =>
      ((((hasDerivAt_id w).mul_const (s : ℂ)).cexp).const_mul (h s : ℂ)).congr_deriv (by simp [F'])

theorem differentiable_laplaceTransform {h : ℝ → ℝ} (hh : Continuous h)
    (hc : HasCompactSupport h) : Differentiable ℂ (laplaceTransform h) := fun z =>
  (hasDerivAt_laplaceTransform hh hc z).differentiableAt

theorem analyticAt_laplaceTransform {h : ℝ → ℝ} (hh : Continuous h)
    (hc : HasCompactSupport h) (z : ℂ) : AnalyticAt ℂ (laplaceTransform h) z :=
  (differentiable_laplaceTransform hh hc).analyticAt z

/-- A positive left endpoint of the support gives exponential decay toward the left. -/
theorem norm_laplaceTransform_le_of_re_nonpos {h : ℝ → ℝ} (hh : Integrable h) {a : ℝ}
    (ha : Function.support h ⊆ Set.Ici a) {z : ℂ} (hz : z.re ≤ 0) :
    ‖laplaceTransform h z‖ ≤ (∫ s : ℝ, ‖h s‖) * Real.exp (z.re * a) := by
  unfold laplaceTransform
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_mul_const]
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (hh.norm.mul_const _)
  filter_upwards with s
  by_cases hs : h s = 0
  · simp [hs]
  have hsa : a ≤ s := ha (Function.mem_support.mpr hs)
  simp only [norm_mul, Complex.norm_real, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hsa hz)) (norm_nonneg _)

/-- Absolute convergence along each of the three arithmetic progressions of trivial zeros. -/
theorem summable_laplaceTransform_re_progression {h : ℝ → ℝ} (hh : Integrable h) {a : ℝ}
    (ha : Function.support h ⊆ Set.Ici a) (ha0 : 0 < a) (r : ℝ) (hr : r ≤ 0) :
    Summable (fun n : ℕ => ‖laplaceTransform h (↑(r - 2 * (n : ℝ)) : ℂ)‖) := by
  have hν : (-2 : ℝ) * a < 0 := mul_neg_of_neg_of_pos (by norm_num) ha0
  refine ((Real.summable_exp_nat_mul_iff.mpr hν).mul_left
    ((∫ s : ℝ, ‖h s‖) * Real.exp (r * a))).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
  have hnonpos : r - 2 * (n : ℝ) ≤ 0 := sub_nonpos.mpr (hr.trans (by positivity))
  refine (norm_laplaceTransform_le_of_re_nonpos hh ha (by simpa using hnonpos)).trans_eq ?_
  simp only [Complex.ofReal_re]
  rw [show (r - 2 * (n : ℝ)) * a = r * a + (n : ℝ) * (-2 * a) by ring,
    Real.exp_add, mul_assoc]

end GoldbachR581
end

-- R581 ContourBounds
section
public section

open Set MeasureTheory
open scoped ContDiff Topology

namespace GoldbachR581

private theorem cast_integrable_mul_continuous {h : ℝ → ℝ} (hh : Continuous h)
    (hc : HasCompactSupport h) {v : ℝ → ℂ} (hv : Continuous v) :
    Integrable (fun x => (h x : ℂ) * v x) := by
  have hcast : HasCompactSupport (fun x => (h x : ℂ)) := by
    apply hc.mono
    intro x hx
    simpa [Function.mem_support] using hx
  exact (Complex.continuous_ofReal.comp hh |>.mul hv).integrable_of_hasCompactSupport hcast.mul_right

/-- Integration by parts on the whole real line. Compact support removes both endpoint terms. -/
theorem laplaceTransform_deriv {h : ℝ → ℝ} (hs : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (z : ℂ) :
    laplaceTransform (deriv h) z = -z * laplaceTransform h z := by
  let u (x : ℝ) : ℂ := Complex.exp (z * (x : ℂ))
  let u' (x : ℝ) : ℂ := z * u x
  let v (x : ℝ) : ℂ := (h x : ℂ)
  let v' (x : ℝ) : ℂ := ((deriv h x : ℝ) : ℂ)
  have hu (x : ℝ) : HasDerivAt u (u' x) x := by
    have hd : HasDerivAt (fun t : ℂ => z * t) z (x : ℂ) := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id (x : ℂ)).const_mul z
    simpa only [u, u', mul_comm] using hd.cexp.comp_ofReal
  have hv (x : ℝ) : HasDerivAt v (v' x) x :=
    ((hs.differentiable (by simp) x).hasDerivAt).ofReal_comp
  have huc : Continuous u := by unfold u; fun_prop
  have huc' : Continuous u' := continuous_const.mul huc
  have h' : Continuous (deriv h) := (contDiff_infty_iff_deriv.mp hs).2.continuous
  have hintegrable {v : ℝ → ℝ} (hv : Continuous v) (hcv : HasCompactSupport v)
      {u : ℝ → ℂ} (hu : Continuous u) : Integrable (fun x => u x * (v x : ℂ)) := by
    simpa only [mul_comm] using cast_integrable_mul_continuous hv hcv hu
  calc
    _ = ∫ x : ℝ, u x * v' x := by simp only [laplaceTransform, u, v', mul_comm]
    _ = -(∫ x : ℝ, u' x * v x) := by
      exact integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hu x) (fun x _ => hv x)
        (hintegrable h' hc.deriv huc) (hintegrable hs.continuous hc huc')
        (hintegrable hs.continuous hc huc)
    _ = _ := by
      rw [neg_mul, laplaceTransform, ← integral_const_mul]
      simp only [u', v, u, mul_left_comm, mul_comm]

private theorem tsupport_iteratedDeriv_subset (h : ℝ → ℝ) (k : ℕ) :
    tsupport (iteratedDeriv k h) ⊆ tsupport h := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans hk

theorem laplaceTransform_iteratedDeriv {h : ℝ → ℝ} (hs : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) (z : ℂ) (k : ℕ) :
    laplaceTransform (iteratedDeriv k h) z = (-z) ^ k * laplaceTransform h z := by
  induction k with
  | zero => simp
  | succ k hk =>
    have hck : HasCompactSupport (iteratedDeriv k h) :=
      hc.mono' (Set.Subset.trans subset_closure (tsupport_iteratedDeriv_subset h k))
    have hsk : ContDiff ℝ ∞ (iteratedDeriv k h) := by
      simpa only [iteratedDeriv_eq_iterate] using hs.iterate_deriv k
    rw [iteratedDeriv_succ, laplaceTransform_deriv hsk hck, hk, pow_succ', mul_assoc]

private theorem norm_laplace_le_of_interval {h : ℝ → ℝ} (hh : Integrable h)
    {a b : ℝ} (hab : Function.support h ⊆ Icc a b) (z : ℂ) :
    ‖laplaceTransform h z‖ ≤ (∫ x : ℝ, ‖h x‖) * Real.exp (max (z.re * a) (z.re * b)) := by
  unfold laplaceTransform
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_mul_const]
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (hh.norm.mul_const _)
  filter_upwards with x
  by_cases hx : h x = 0
  · simp [hx]
  obtain ⟨hla, hhb⟩ := hab (Function.mem_support.mpr hx)
  have hprod : z.re * x ≤ max (z.re * a) (z.re * b) := by
    by_cases hz : 0 ≤ z.re
    · exact (mul_le_mul_of_nonneg_left hhb hz).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left hla (le_of_not_ge hz)).trans (le_max_left _ _)
  simp only [norm_mul, Complex.norm_real, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hprod) (norm_nonneg _)

/-- Uniform transform bound for both horizontal and left edges of the contour. Its exponential
factor uses the left endpoint when `z.re ≤ 0` and the right endpoint when `0 ≤ z.re`. -/
theorem laplaceTransform_contour_bound {h : ℝ → ℝ} (hs : ContDiff ℝ ∞ h) {a b : ℝ}
    (hab : tsupport h ⊆ Icc a b) (k : ℕ) (z : ℂ) :
    (1 + |z.im| ^ k) * ‖laplaceTransform h z‖ ≤
      ((∫ x : ℝ, ‖h x‖) + (∫ x : ℝ, ‖iteratedDeriv k h x‖)) *
        Real.exp (max (z.re * a) (z.re * b)) := by
  have hc : HasCompactSupport h := isCompact_Icc.of_isClosed_subset isClosed_closure hab
  have hck : HasCompactSupport (iteratedDeriv k h) :=
    hc.mono' (Set.Subset.trans subset_closure (tsupport_iteratedDeriv_subset h k))
  have hdk : Continuous (iteratedDeriv k h) := by
    simpa only [iteratedDeriv_eq_iterate] using (hs.iterate_deriv k).continuous
  have hbase := norm_laplace_le_of_interval (hs.continuous.integrable_of_hasCompactSupport hc)
    (Set.Subset.trans subset_closure hab) z
  have hk := norm_laplace_le_of_interval (hdk.integrable_of_hasCompactSupport hck)
    (Set.Subset.trans subset_closure ((tsupport_iteratedDeriv_subset h k).trans hab)) z
  have him : |z.im| ^ k * ‖laplaceTransform h z‖ ≤ ‖laplaceTransform (iteratedDeriv k h) z‖ := by
    rw [laplaceTransform_iteratedDeriv hs hc z k, norm_mul, norm_pow, norm_neg]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm _) _)
      (norm_nonneg _)
  rw [add_mul, one_mul, add_mul]
  exact add_le_add hbase (him.trans hk)

end GoldbachR581
end

-- R581 RightLine
section
open MeasureTheory
open scoped ArithmeticFunction ArithmeticFunction.Moebius ContDiff

namespace GoldbachR581

/-- The character-twisted Mangoldt sum in R581. The terms at zero and one vanish. -/
noncomputable def mangoldtSum {N : ℕ} (χ : DirichletCharacter ℂ N) (h : ℝ → ℝ) : ℂ :=
  ∑' n : ℕ, (χ (n : ZMod N) * (Λ n : ℂ)) * (h (Real.log (n : ℝ)) : ℂ)

private theorem dirichlet_term_exp {f : ℕ → ℂ} (hf : f 0 = 0) (z : ℂ) (n : ℕ) :
    LSeries.term f z n = f n * Complex.exp (-z * (Real.log (n : ℝ) : ℂ)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hf]
  · have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
      simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log (Nat.cast_nonneg n)).symm
    rw [LSeries.term_def₀ hf, Complex.cpow_def_of_ne_zero (by exact_mod_cast hn), hlog,
      mul_comm (Real.log (n : ℝ) : ℂ) (-z)]

private theorem twistedMangoldtLSeries_eq_neg_logDeriv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z : ℂ} (hz : 1 < z.re) :
    LSeries (fun n : ℕ => χ (n : ZMod N) * (Λ n : ℂ)) z = -logDeriv χ.LFunction z := by
  rw [logDeriv_apply, χ.deriv_LFunction_eq_deriv_LSeries hz, χ.LFunction_eq_LSeries hz, ← neg_div]
  exact χ.LSeries_twist_vonMangoldt_eq hz

private theorem norm_LSeries_le_of_re_ge {a : ℕ → ℂ} {σ : ℝ} (hσs : LSeriesSummable a (σ : ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, σ ≤ z.re → ‖LSeries a z‖ ≤ C := by
  have Hσ : Summable (fun n : ℕ => ‖LSeries.term a (σ : ℂ) n‖) := hσs.norm
  refine ⟨∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖, tsum_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro z hz
  have hσz : (σ : ℂ).re ≤ z.re := by simpa using hz
  have Hz : Summable (fun n : ℕ => ‖LSeries.term a z n‖) := (hσs.of_re_le_re hσz).norm
  calc
    ‖LSeries a z‖ ≤ ∑' n : ℕ, ‖LSeries.term a z n‖ := norm_tsum_le_tsum_norm Hz
    _ ≤ _ := Hz.tsum_le_tsum (LSeries.norm_term_le_of_re_le_re a hσz) Hσ

/-- The Dirichlet-series logarithmic derivative is uniformly bounded on each closed
half-plane strictly to the right of one. -/
theorem norm_logDeriv_dirichletL_le_of_re_ge {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, σ ≤ z.re → ‖logDeriv χ.LFunction z‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := norm_LSeries_le_of_re_ge (a := fun n => χ (n : ZMod N) * (Λ n : ℂ))
    (χ.LSeriesSummable_twist_vonMangoldt (s := (σ : ℂ)) (by simpa using hσ))
  refine ⟨C, hC, fun z hz => ?_⟩
  simpa only [twistedMangoldtLSeries_eq_neg_logDeriv χ (hσ.trans_le hz), norm_neg] using hb z hz

/-- The inverse Dirichlet series, obtained by twisting Möbius, gives a uniform positive
lower bound for the L-function on each closed half-plane strictly to the right of one. -/
theorem exists_pos_le_norm_dirichletL_of_re_ge {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℂ, σ ≤ z.re → c ≤ ‖χ.LFunction z‖ := by
  let a (n : ℕ) := χ (n : ZMod N) * (μ n : ℂ)
  have ha : LSeriesSummable a (σ : ℂ) := χ.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by simpa using hσ))
  obtain ⟨C, hC, hb⟩ := norm_LSeries_le_of_re_ge ha
  have hC₁ : 0 < C + 1 := by positivity
  refine ⟨1 / (C + 1), by positivity, fun z hz => ?_⟩
  have hprod : ‖χ.LFunction z‖ * ‖LSeries a z‖ = 1 := by
    rw [← norm_mul, χ.LFunction_eq_LSeries (hσ.trans_le hz)]
    have hm : LSeries (fun n => χ (n : ZMod N)) z * LSeries a z = 1 :=
      DirichletCharacter.LSeries.mul_mu_eq_one χ (hσ.trans_le hz)
    rw [hm, norm_one]
  apply (div_le_iff₀ hC₁).mpr
  rw [← hprod]
  exact mul_le_mul_of_nonneg_left ((hb z hz).trans (by linarith)) (norm_nonneg _)

/-- The right-hand vertical integral before contour shifting. The sum-integral interchange
uses the summable norms of the Dirichlet terms on the line and integrability of `H` there. -/
theorem mangoldtSum_eq_rightLine {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {h : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) {σ : ℝ} (hσ : 1 < σ) :
    mangoldtSum χ h = (↑(2 * Real.pi) : ℂ)⁻¹ *
      ∫ t : ℝ, laplaceTransform h (verticalPoint σ t) * (-logDeriv χ.LFunction (verticalPoint σ t)) := by
  let a : ℕ → ℂ := fun n => χ (n : ZMod N) * (Λ n : ℂ)
  let H : ℝ → ℂ := fun t => laplaceTransform h (verticalPoint σ t)
  let F : ℕ → ℝ → ℂ := fun n t => H t * LSeries.term a (verticalPoint σ t) n
  have ha0 : a 0 = 0 := by simp [a]
  have hintegrable : Integrable H := integrable_laplace_vertical hs hc σ
  have hnorm (n : ℕ) (t : ℝ) : ‖F n t‖ = ‖H t‖ * ‖LSeries.term a (σ : ℂ) n‖ := by
    simp only [F, norm_mul, LSeries.norm_term_eq, verticalPoint_re, Complex.ofReal_re]
  have hF (n : ℕ) : Integrable (F n) := by
    apply (hintegrable.norm.mul_const ‖LSeries.term a (σ : ℂ) n‖).mono'
    · apply hintegrable.aestronglyMeasurable.mul
      apply Continuous.aestronglyMeasurable
      simp_rw [dirichlet_term_exp ha0]
      unfold verticalPoint
      fun_prop
    · exact Filter.Eventually.of_forall fun t => (hnorm n t).le
  have hDirichlet : Summable fun n => ‖LSeries.term a (σ : ℂ) n‖ :=
    (show LSeriesSummable a (σ : ℂ) from χ.LSeriesSummable_twist_vonMangoldt (by simpa using hσ)).norm
  have hS : Summable fun n => ∫ t : ℝ, ‖F n t‖ := by
    simp_rw [hnorm, integral_mul_const]
    exact hDirichlet.mul_left _
  unfold mangoldtSum
  calc
    _ = ∑' n : ℕ, (↑(2 * Real.pi) : ℂ)⁻¹ * ∫ t : ℝ, F n t := by
      apply tsum_congr
      intro n
      change a n * (h (Real.log (n : ℝ)) : ℂ) = _
      rw [laplace_inversion hs hc σ (Real.log (n : ℝ)), ← mul_assoc, mul_comm (a n), mul_assoc,
        ← integral_const_mul]
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      simp only [F, H, dirichlet_term_exp ha0]
      ring
    _ = (↑(2 * Real.pi) : ℂ)⁻¹ * ∫ t : ℝ, ∑' n : ℕ, F n t := by
      rw [tsum_mul_left, integral_tsum_of_summable_integral_norm hF hS]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      simp only [F, tsum_mul_left, H]
      change _ * LSeries a (verticalPoint σ t) = _
      rw [twistedMangoldtLSeries_eq_neg_logDeriv χ (by simpa using hσ)]

end GoldbachR581
end

-- R581 Residue
section
public section

open Filter Set
open scoped Topology

namespace GoldbachR581

/-- The principal part of `L'/L` at a point of finite signed order. Positive order describes
a zero, and negative order describes a pole. -/
private theorem logDeriv_eq_order_div_add {f : ℂ → ℂ} {w : ℂ} {k : ℤ}
    (hf : MeromorphicAt f w) (hk : meromorphicOrderAt f w = k) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧
      logDeriv f =ᶠ[𝓝[≠] w] (fun z => (k : ℂ) / (z - w) + g z) := by
  obtain ⟨g, hg, hg0, heq⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hk
  have heq' : f =ᶠ[𝓝[≠] w] fun z => (z - w) ^ k * g z := by
    filter_upwards [heq] with z hz
    simpa only [smul_eq_mul] using hz
  refine ⟨logDeriv g, hg.deriv.div hg hg0, ?_⟩
  have hgn : ∀ᶠ z in 𝓝[≠] w, g z ≠ 0 :=
    (hg.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds
  filter_upwards [logDeriv_congr_nhdsNE heq', hgn,
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hgz hga hzw
  have hsub : z - w ≠ 0 := sub_ne_zero.mpr hzw
  have hdiff : DifferentiableAt ℂ (fun v : ℂ => v - w) z := by fun_prop
  rw [hz, logDeriv_fun_mul (f := fun v : ℂ => (v - w) ^ k) (g := g) z (zpow_ne_zero _ hsub) hgz
    (hdiff.zpow (Or.inl hsub)) hga.differentiableAt, logDeriv_fun_zpow hdiff]
  have hl : logDeriv (fun v : ℂ => v - w) z = 1 / (z - w) := by
    simp [logDeriv_apply]
  rw [hl, mul_one_div]

/-- Subtracting `(-ord f) H(w) / (z - w)` from `(-f'/f) H` leaves an analytic remainder.
This gives the two residue signs used in the R581 contour shift. -/
theorem exists_analytic_remainder_neg_logDeriv_mul {f H : ℂ → ℂ} {w : ℂ} {k : ℤ}
    (hf : MeromorphicAt f w) (hk : meromorphicOrderAt f w = k) (hH : AnalyticAt ℂ H w) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G w ∧
      (fun z => (-logDeriv f z) * H z) =ᶠ[𝓝[≠] w]
        (fun z => (-(k : ℂ) * H w) / (z - w) + G z) := by
  obtain ⟨g, hg, heq⟩ := logDeriv_eq_order_div_add hf hk
  have hdiff : AnalyticAt ℂ (fun z => H z - H w) w := hH.sub analyticAt_const
  have h₁ : (1 : ℕ) ≤ analyticOrderAt (fun z => H z - H w) w := by
    exact Order.one_le_iff_ne_zero.mpr (hdiff.analyticOrderAt_ne_zero.mpr (sub_self _))
  obtain ⟨u, hu, hue⟩ := (natCast_le_analyticOrderAt hdiff).mp h₁
  refine ⟨fun z => -(k : ℂ) * u z - g z * H z, (analyticAt_const.mul hu).sub (hg.mul hH), ?_⟩
  filter_upwards [heq, hue.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with z hz hzu hzw
  have hsub : z - w ≠ 0 := sub_ne_zero.mpr hzw
  have hzH : H z = H w + (z - w) * u z := by
    have hdiffz : H z - H w = (z - w) * u z := by simpa only [pow_one, smul_eq_mul] using hzu
    linear_combination hdiffz
  simp only [hz]
  rw [hzH]
  field_simp
  ring

end GoldbachR581
end

-- R581 Rectangle
section
open Set MeasureTheory Filter
open Complex
open scoped Topology

namespace GoldbachR581

/-- Counterclockwise integral over the rectangle with real bounds `a,b` and imaginary bounds
`c,d`. Each edge is written in its own real coordinate. -/
noncomputable def rectangleIntegral (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ t in a..b, f (verticalPoint t c)) - (∫ t in a..b, f (verticalPoint t d)) +
  I * (∫ t in c..d, f (verticalPoint b t)) - I * (∫ t in c..d, f (verticalPoint a t))

set_option maxHeartbeats 1000000 in
private theorem integral_affine_inv_sub {a b : ℝ} {r u v w : ℂ} (hr : r ≠ 0)
    (h : ∀ t ∈ uIcc a b, 0 < (r * (u + v * (t : ℂ) - w)).re) :
    (∫ t in a..b, v * (u + v * (t : ℂ) - w)⁻¹) =
      Complex.log (r * (u + v * (b : ℂ) - w)) - Complex.log (r * (u + v * (a : ℂ) - w)) := by
  have hne (t : ℝ) (ht : t ∈ uIcc a b) : u + v * (t : ℂ) - w ≠ 0 := by
    intro hz
    simpa [hz] using h t ht
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    have ht' : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
      simpa only [id_eq] using (hasDerivAt_id (t : ℂ)).comp_ofReal
    have hγ : HasDerivAt (fun t : ℝ => r * (u + v * (t : ℂ) - w)) (r * v) t := by
      simpa only [mul_one] using (((ht'.const_mul v).const_add u).sub_const w).const_mul r
    have hlog := Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.mpr (Or.inl (h t ht)))
    refine (hlog.scomp t hγ).congr_deriv ?_
    simp only [smul_eq_mul]
    field_simp
  · have hc : ContinuousOn (fun t : ℝ => u + v * (t : ℂ) - w) (uIcc a b) := by
      fun_prop
    exact (continuousOn_const.mul (hc.inv₀ hne)).intervalIntegrable

private theorem log_I_mul_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    Complex.log (I * z) = Complex.log z + (↑Real.pi / 2) * I := by
  have hn : z ≠ 0 := by intro h; simp [h] at hz
  have hl := (Complex.neg_pi_div_two_lt_arg_iff).mpr (Or.inl hz)
  have hu := (Complex.arg_lt_pi_div_two_iff).mpr (Or.inl hz)
  rw [Complex.log_mul Complex.I_ne_zero hn, Complex.log_I, add_comm]
  rw [Complex.arg_I]
  exact ⟨by linarith [Real.pi_pos], by linarith⟩

/-- A simple pole inside the rectangle has counterclockwise integral `2πi`. -/
theorem rectangleIntegral_inv_sub {a b c d : ℝ} {w : ℂ}
    (hx : w.re ∈ Ioo a b) (hy : w.im ∈ Ioo c d) :
    rectangleIntegral (fun z => (z - w)⁻¹) a b c d = (↑(2 * Real.pi) : ℂ) * I := by
  have hb : (∫ t in a..b, (verticalPoint t c - w)⁻¹) =
      Complex.log (I * (verticalPoint b c - w)) - Complex.log (I * (verticalPoint a c - w)) := by
    simpa only [verticalPoint, one_mul, add_comm ((c : ℂ) * I)] using
      (integral_affine_inv_sub (a := a) (b := b) (r := I) (u := (c : ℂ) * I) (v := 1) (w := w)
        Complex.I_ne_zero (by
          intro t _
          simp [Complex.mul_re, Complex.mul_im]
          linarith [hy.1]))
  have ht : (∫ t in a..b, (verticalPoint t d - w)⁻¹) =
      Complex.log (-I * (verticalPoint b d - w)) - Complex.log (-I * (verticalPoint a d - w)) := by
    simpa only [verticalPoint, one_mul, add_comm ((d : ℂ) * I)] using
      (integral_affine_inv_sub (a := a) (b := b) (r := -I) (u := (d : ℂ) * I) (v := 1) (w := w)
        (neg_ne_zero.mpr Complex.I_ne_zero) (by
          intro t _
          simp [Complex.mul_re, Complex.mul_im]
          linarith [hy.2]))
  have hr : I * (∫ t in c..d, (verticalPoint b t - w)⁻¹) =
      Complex.log (verticalPoint b d - w) - Complex.log (verticalPoint b c - w) := by
    rw [← intervalIntegral.integral_const_mul]
    simpa only [verticalPoint, mul_comm I, one_mul] using
      (integral_affine_inv_sub (a := c) (b := d) (r := 1) (u := (b : ℂ)) (v := I) (w := w)
        one_ne_zero (by
          intro t _
          simpa [Complex.mul_re] using sub_pos.mpr hx.2))
  have hl : I * (∫ t in c..d, (verticalPoint a t - w)⁻¹) =
      Complex.log (-(verticalPoint a d - w)) - Complex.log (-(verticalPoint a c - w)) := by
    rw [← intervalIntegral.integral_const_mul]
    simpa only [verticalPoint, neg_mul, one_mul, mul_comm I] using
      (integral_affine_inv_sub (a := c) (b := d) (r := -1) (u := (a : ℂ)) (v := I) (w := w)
        (neg_ne_zero.mpr one_ne_zero) (by
          intro t _
          simpa [Complex.mul_re, neg_sub] using sub_pos.mpr hx.1))
  have hbr := log_I_mul_of_re_pos (z := verticalPoint b c - w)
    (by simpa using sub_pos.mpr hx.2)
  have htr := log_I_mul_of_re_pos (z := -I * (verticalPoint b d - w)) (by
    simp [verticalPoint, Complex.mul_re, Complex.mul_im]
    linarith [hy.2])
  have htl := log_I_mul_of_re_pos (z := -(verticalPoint a d - w))
    (by simpa [neg_sub] using sub_pos.mpr hx.1)
  have hbl := log_I_mul_of_re_pos (z := I * (verticalPoint a c - w)) (by
    simp [verticalPoint, Complex.mul_re, Complex.mul_im]
    linarith [hy.1])
  rw [show I * (-I * (verticalPoint b d - w)) = verticalPoint b d - w by
    rw [← mul_assoc]; simp] at htr
  rw [mul_neg, ← neg_mul] at htl
  rw [show I * (I * (verticalPoint a c - w)) = -(verticalPoint a c - w) by
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]] at hbl
  rw [rectangleIntegral, hb, ht, hr, hl, Complex.ofReal_mul, Complex.ofReal_ofNat]
  linear_combination hbr + htr + htl + hbl

private def rectangleBoundary (a b c d : ℝ) : Set ℂ :=
  (Icc a b ×ℂ Icc c d) \ (Ioo a b ×ℂ Ioo c d)

private theorem horizontal_in_boundary {a b c d x y : ℝ}
    (hx : x ∈ Icc a b) (hcd : c ≤ d) (hy : y = c ∨ y = d) :
    verticalPoint x y ∈ rectangleBoundary a b c d := by
  rcases hy with rfl | rfl <;> simp [rectangleBoundary, hx, hcd, mem_reProdIm]

private theorem vertical_in_boundary {a b c d x y : ℝ}
    (hy : y ∈ Icc c d) (hab : a ≤ b) (hx : x = a ∨ x = b) :
    verticalPoint x y ∈ rectangleBoundary a b c d := by
  rcases hx with rfl | rfl <;> simp [rectangleBoundary, hy, hab, mem_reProdIm]

private theorem rectangleIntegral_congr {f g : ℂ → ℂ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hfg : EqOn f g (rectangleBoundary a b c d)) :
    rectangleIntegral f a b c d = rectangleIntegral g a b c d := by
  have hh (y : ℝ) (hy : y = c ∨ y = d) :
      (∫ t in a..b, f (verticalPoint t y)) = ∫ t in a..b, g (verticalPoint t y) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hab]
    exact fun _ ht => hfg (horizontal_in_boundary ht hcd hy)
  have hv (x : ℝ) (hx : x = a ∨ x = b) :
      (∫ t in c..d, f (verticalPoint x t)) = ∫ t in c..d, g (verticalPoint x t) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hcd]
    exact fun _ ht => hfg (vertical_in_boundary ht hab hx)
  rw [rectangleIntegral, rectangleIntegral, hh c (Or.inl rfl), hh d (Or.inr rfl),
    hv b (Or.inr rfl), hv a (Or.inl rfl)]

private theorem rectangleIntegral_add_finsetSum {ι : Type*} {s : Finset ι} {f : ℂ → ℂ}
    {g : ι → ℂ → ℂ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn f (rectangleBoundary a b c d))
    (hg : ∀ i ∈ s, ContinuousOn (g i) (rectangleBoundary a b c d)) :
    rectangleIntegral (fun z => f z + ∑ i ∈ s, g i z) a b c d =
      rectangleIntegral f a b c d + ∑ i ∈ s, rectangleIntegral (g i) a b c d := by
  have hhorizontal {k : ℂ → ℂ} (hk : ContinuousOn k (rectangleBoundary a b c d))
      {y : ℝ} (hy : y = c ∨ y = d) :
      IntervalIntegrable (fun t => k (verticalPoint t y)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hk.comp (by unfold verticalPoint; fun_prop) (fun _ ht => horizontal_in_boundary ht hcd hy)
  have hvertical {k : ℂ → ℂ} (hk : ContinuousOn k (rectangleBoundary a b c d))
      {x : ℝ} (hx : x = a ∨ x = b) :
      IntervalIntegrable (fun t => k (verticalPoint x t)) volume c d := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hcd]
    exact hk.comp (by unfold verticalPoint; fun_prop) (fun _ ht => vertical_in_boundary ht hab hx)
  have hsum : ContinuousOn (fun z => ∑ i ∈ s, g i z) (rectangleBoundary a b c d) :=
    continuousOn_finsetSum _ hg
  have hh (y : ℝ) (hy : y = c ∨ y = d) :
      (∫ t in a..b, f (verticalPoint t y) + ∑ i ∈ s, g i (verticalPoint t y)) =
        (∫ t in a..b, f (verticalPoint t y)) + ∑ i ∈ s, ∫ t in a..b, g i (verticalPoint t y) := by
    rw [intervalIntegral.integral_add (hhorizontal hf hy) (hhorizontal hsum hy),
      intervalIntegral.integral_finsetSum (fun i hi => hhorizontal (hg i hi) hy)]
  have hv (x : ℝ) (hx : x = a ∨ x = b) :
      (∫ t in c..d, f (verticalPoint x t) + ∑ i ∈ s, g i (verticalPoint x t)) =
        (∫ t in c..d, f (verticalPoint x t)) + ∑ i ∈ s, ∫ t in c..d, g i (verticalPoint x t) := by
    rw [intervalIntegral.integral_add (hvertical hf hx) (hvertical hsum hx),
      intervalIntegral.integral_finsetSum (fun i hi => hvertical (hg i hi) hx)]
  simp only [rectangleIntegral, hh c (Or.inl rfl), hh d (Or.inr rfl),
    hv b (Or.inr rfl), hv a (Or.inl rfl), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

private theorem rectangleIntegral_const_mul (f : ℂ → ℂ) (k : ℂ) (a b c d : ℝ) :
    rectangleIntegral (fun z => k * f z) a b c d = k * rectangleIntegral f a b c d := by
  simp only [rectangleIntegral, intervalIntegral.integral_const_mul]
  ring

/-- The rectangle residue theorem for finitely many prescribed simple principal parts. -/
theorem rectangleIntegral_eq_sum_residues {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {f : ℂ → ℂ} (poles : Finset ℂ) (residue : ℂ → ℂ)
    (hpoles : ∀ w ∈ poles, w ∈ Ioo a b ×ℂ Ioo c d)
    (hf : ∀ z ∈ Icc a b ×ℂ Icc c d, z ∉ poles → AnalyticAt ℂ f z)
    (hp : ∀ w ∈ poles, ∃ h : ℂ → ℂ, AnalyticAt ℂ h w ∧
      f =ᶠ[𝓝[≠] w] fun z => residue w * (z - w)⁻¹ + h z) :
    rectangleIntegral f a b c d = (↑(2 * Real.pi) : ℂ) * I * ∑ w ∈ poles, residue w := by
  classical
  choose h ha hpart using hp
  let q (w z : ℂ) := residue w * (z - w)⁻¹
  let G (z : ℂ) := if hz : z ∈ poles then h z hz z - ∑ w ∈ poles.erase z, q w z
    else f z - ∑ w ∈ poles, q w z
  have hq (w z : ℂ) (hzw : z ≠ w) : AnalyticAt ℂ (q w) z := by
    exact analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hzw))
  have hG : ∀ z ∈ Icc a b ×ℂ Icc c d, AnalyticAt ℂ G z := by
    intro z hz
    by_cases hzp : z ∈ poles
    · have he : ∀ᶠ v in 𝓝 z, v ∉ poles.erase z := by
        exact (poles.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
      have hrem : AnalyticAt ℂ (fun v => h z hzp v - ∑ w ∈ poles.erase z, q w v) z :=
        (ha z hzp).sub (Finset.analyticAt_fun_sum _ fun w hw => hq w z (Finset.ne_of_mem_erase hw).symm)
      apply hrem.congr
      apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
      · filter_upwards [he.filter_mono nhdsWithin_le_nhds, hpart z hzp, self_mem_nhdsWithin]
          with v hv hfv hvz
        have hne : v ≠ z := hvz
        have hnp : v ∉ poles := fun hpv => hv (Finset.mem_erase_of_ne_of_mem hne hpv)
        simp only [G, dite_eq_right hnp, hfv]
        rw [← Finset.sum_erase_add _ _ hzp]
        dsimp only [q]
        ring
      · simp only [G, dite_eq_left hzp]
    · have he : ∀ᶠ v in 𝓝 z, v ∉ poles :=
        poles.finite_toSet.isClosed.isOpen_compl.mem_nhds hzp
      have hrem : AnalyticAt ℂ (fun v => f v - ∑ w ∈ poles, q w v) z :=
        (hf z hz hzp).sub (Finset.analyticAt_fun_sum _ fun w hw => hq w z (ne_of_mem_of_not_mem hw hzp).symm)
      exact hrem.congr (he.mono fun v hv => by simp only [G, dite_eq_right hv])
  have hboundary : ∀ z ∈ rectangleBoundary a b c d, z ∉ poles :=
    fun z hz hzp => hz.2 (hpoles z hzp)
  have heq : EqOn f (fun z => G z + ∑ w ∈ poles, q w z) (rectangleBoundary a b c d) := by
    intro z hz
    simp only [G, dite_eq_right (hboundary z hz), sub_add_cancel]
  have hqcont : ∀ w ∈ poles, ContinuousOn (q w) (rectangleBoundary a b c d) := by
    intro w hw z hz
    exact (hq w z (ne_of_mem_of_not_mem hw (hboundary z hz)).symm).continuousAt.continuousWithinAt
  have hGcont : ContinuousOn G (rectangleBoundary a b c d) :=
    fun z hz => (hG z hz.1).continuousAt.continuousWithinAt
  have hGzero : rectangleIntegral G a b c d = 0 := by
    have hd : DifferentiableOn ℂ G (Icc a b ×ℂ Icc c d) :=
      fun z hz => (hG z hz).differentiableAt.differentiableWithinAt
    have hz := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G
      (verticalPoint a c) (verticalPoint b d)
      (by simpa only [verticalPoint_re, verticalPoint_im, uIcc_of_le hab.le, uIcc_of_le hcd.le] using hd)
    simp only [verticalPoint_re, verticalPoint_im, smul_eq_mul] at hz
    exact hz
  rw [rectangleIntegral_congr hab.le hcd.le heq,
    rectangleIntegral_add_finsetSum hab.le hcd.le hGcont hqcont, hGzero, zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hw' := (mem_reProdIm.mp (hpoles w hw))
  rw [show rectangleIntegral (q w) a b c d = residue w * rectangleIntegral (fun z => (z - w)⁻¹) a b c d
      from rectangleIntegral_const_mul _ _ _ _ _ _, rectangleIntegral_inv_sub hw'.1 hw'.2, mul_comm]

/-- Finite contour shift for the weighted negative logarithmic derivative. The signed order
counts zeros positively and poles negatively. -/
theorem rectangleIntegral_neg_logDeriv_mul {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {f H : ℂ → ℂ} (poles : Finset ℂ) (order : ℂ → ℤ)
    (hpoles : ∀ w ∈ poles, w ∈ Ioo a b ×ℂ Ioo c d)
    (hH : ∀ z ∈ Icc a b ×ℂ Icc c d, AnalyticAt ℂ H z)
    (hreg : ∀ z ∈ Icc a b ×ℂ Icc c d, z ∉ poles → AnalyticAt ℂ f z ∧ f z ≠ 0)
    (horder : ∀ w ∈ poles, MeromorphicAt f w ∧ meromorphicOrderAt f w = order w) :
    rectangleIntegral (fun z => (-logDeriv f z) * H z) a b c d =
      (↑(2 * Real.pi) : ℂ) * I * ∑ w ∈ poles, (-(order w : ℂ) * H w) := by
  apply rectangleIntegral_eq_sum_residues hab hcd poles _ hpoles
  · intro z hz hzp
    obtain ⟨hf, hn⟩ := hreg z hz hzp
    exact (hf.deriv.div hf hn).neg.mul (hH z hz)
  · intro w hw
    have ⟨hx, hy⟩ := mem_reProdIm.mp (hpoles w hw)
    have hw' : w ∈ Icc a b ×ℂ Icc c d := mem_reProdIm.mpr
      ⟨Ioo_subset_Icc_self hx, Ioo_subset_Icc_self hy⟩
    obtain ⟨hm, ho⟩ := horder w hw
    obtain ⟨G, hG, he⟩ := exists_analytic_remainder_neg_logDeriv_mul hm ho (hH w hw')
    exact ⟨G, hG, he.mono fun z hz => by simpa only [div_eq_mul_inv] using hz⟩

end GoldbachR581
end

-- R581 DirichletContour
section
open Complex Filter Set DirichletCharacter
open scoped Topology

namespace GoldbachR581

theorem analyticAt_dirichletL_of_regular_parameter {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {z : ℂ} (hz : z ≠ 1 ∨ χ ≠ 1) : AnalyticAt ℂ χ.LFunction z := by
  rcases hz with h | h
  · have hd : DifferentiableOn ℂ χ.LFunction ({1}ᶜ : Set ℂ) := fun w hw =>
      (χ.differentiableAt_LFunction w (.inl hw)).differentiableWithinAt
    exact hd.analyticOnNhd isOpen_compl_singleton z h
  · exact (differentiable_LFunction h).analyticAt z

private theorem meromorphicAt_and_order_trivial_dirichletL {N : ℕ} [NeZero N] :
    MeromorphicAt (LFunctionTrivChar N) 1 ∧ meromorphicOrderAt (LFunctionTrivChar N) 1 = -1 := by
  let g := LFunctionTrivChar₁ N
  have hg : AnalyticAt ℂ g 1 := (differentiable_LFunctionTrivChar₁ N).analyticAt 1
  have heq : LFunctionTrivChar N =ᶠ[𝓝[≠] (1 : ℂ)] (fun z => (z - 1) ^ (-1 : ℤ) • g z) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hne : z ≠ (1 : ℂ) := hz
    simp only [g, LFunctionTrivChar₁, Function.update_of_ne hne, zpow_neg_one, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_mul]
  have hsub : AnalyticAt ℂ (fun z : ℂ => z - 1) 1 := analyticAt_id.sub analyticAt_const
  have hpow : MeromorphicAt (fun z : ℂ => (z - 1) ^ (-1 : ℤ)) 1 :=
    hsub.meromorphicAt.zpow (-1)
  have hprod : MeromorphicAt (fun z : ℂ => (z - 1) ^ (-1 : ℤ) • g z) 1 :=
    hpow.smul hg.meromorphicAt
  have hm : MeromorphicAt (LFunctionTrivChar N) 1 := hprod.congr heq.symm
  exact ⟨hm, (meromorphicOrderAt_eq_int_iff hm).mpr
    ⟨g, hg, LFunctionTrivChar₁_apply_one_ne_zero N, heq⟩⟩

theorem meromorphic_dirichletL {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    Meromorphic χ.LFunction := by
  intro z
  by_cases hz : z ≠ 1 ∨ χ ≠ 1
  · exact (analyticAt_dirichletL_of_regular_parameter hz).meromorphicAt
  · push Not at hz
    obtain ⟨rfl, rfl⟩ := hz
    exact (meromorphicAt_and_order_trivial_dirichletL (N := N)).1

theorem order_eq_zero_of_analytic_nonzero {f : ℂ → ℂ} {z : ℂ}
    (ha : AnalyticAt ℂ f z) (hn : f z ≠ 0) : meromorphicOrderAt f z = 0 := by
  have heq : f =ᶠ[𝓝[≠] z] (fun w => (w - z) ^ (0 : ℤ) • f w) := by simp
  exact (meromorphicOrderAt_eq_int_iff ha.meromorphicAt (n := 0)).mpr ⟨f, ha, hn, heq⟩

theorem meromorphicOrderAt_dirichletL_ne_top {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (z : ℂ) :
    meromorphicOrderAt χ.LFunction z ≠ ⊤ := by
  have h2 : (2 : ℂ) ≠ 1 := by norm_num
  have hRe : 1 ≤ (2 : ℂ).re := by norm_num
  have ho := order_eq_zero_of_analytic_nonzero (analyticAt_dirichletL_of_regular_parameter (χ := χ) (.inl h2))
    (χ.LFunction_ne_zero_of_one_le_re (.inr h2) hRe)
  have hm : MeromorphicOn χ.LFunction univ := fun w _ => meromorphic_dirichletL χ w
  exact hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 2) (mem_univ z)
    (by simp [ho])

theorem analytic_ne_zero_of_dirichlet_order_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {z : ℂ} (ho : meromorphicOrderAt χ.LFunction z = 0) :
    AnalyticAt ℂ χ.LFunction z ∧ χ.LFunction z ≠ 0 := by
  have hz : z ≠ 1 ∨ χ ≠ 1 := by
    by_contra! h
    obtain ⟨rfl, rfl⟩ := h
    rw [(meromorphicAt_and_order_trivial_dirichletL (N := N)).2] at ho
    norm_num at ho
  have ha := analyticAt_dirichletL_of_regular_parameter hz
  obtain ⟨c, hc, ht⟩ := tendsto_ne_zero_of_meromorphicOrderAt_eq_zero ha.meromorphicAt ho
  exact ⟨ha, (tendsto_nhds_unique (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ht) ▸ hc⟩

/-- The signed order of the actual Dirichlet L-function, including the principal pole. -/
noncomputable def dirichletOrder {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (z : ℂ) : ℤ :=
  (meromorphicOrderAt χ.LFunction z).untop₀

theorem dirichletOrder_spec {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (z : ℂ) :
    (dirichletOrder χ z : WithTop ℤ) = meromorphicOrderAt χ.LFunction z :=
  WithTop.coe_untop₀_of_ne_top (meromorphicOrderAt_dirichletL_ne_top χ z)

theorem dirichletOrder_trivial_one (N : ℕ) [NeZero N] :
    dirichletOrder (1 : DirichletCharacter ℂ N) 1 = -1 := by
  rw [dirichletOrder, (meromorphicAt_and_order_trivial_dirichletL (N := N)).2]
  rfl

theorem dirichletOrder_eq_zero_of_one_le_re {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z : ℂ} (hz : 1 ≤ z.re) (hreg : z ≠ 1 ∨ χ ≠ 1) : dirichletOrder χ z = 0 := by
  rw [dirichletOrder, order_eq_zero_of_analytic_nonzero (analyticAt_dirichletL_of_regular_parameter hreg)
    (χ.LFunction_ne_zero_of_one_le_re hreg.symm hz), WithTop.untop₀_zero]

/-- The finitely many points of nonzero signed order in the closed rectangle. -/
noncomputable def dirichletRectangleSingularities {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (a b c d : ℝ) : Finset ℂ :=
  ((MeromorphicOn.divisor χ.LFunction (Icc a b ×ℂ Icc c d)).finiteSupport
    (isCompact_Icc.reProdIm isCompact_Icc)).toFinset

theorem mem_dirichletRectangleSingularities {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {a b c d : ℝ} {z : ℂ} : z ∈ dirichletRectangleSingularities χ a b c d ↔
      z ∈ Icc a b ×ℂ Icc c d ∧ dirichletOrder χ z ≠ 0 := by
  let K := Icc a b ×ℂ Icc c d
  let D := MeromorphicOn.divisor χ.LFunction K
  have hm : MeromorphicOn χ.LFunction K := fun w _ => meromorphic_dirichletL χ w
  change z ∈ (D.finiteSupport (isCompact_Icc.reProdIm isCompact_Icc)).toFinset ↔ _
  rw [Set.Finite.mem_toFinset]
  constructor
  · intro hz
    have hK := D.supportWithinDomain hz
    exact ⟨hK, by simpa only [D, dirichletOrder, Function.mem_support,
      MeromorphicOn.divisor_apply hm hK] using hz⟩
  · rintro ⟨hK, hz⟩
    simpa only [D, dirichletOrder, Function.mem_support, MeromorphicOn.divisor_apply hm hK] using hz

/-- Exact finite contour identity for the actual Dirichlet L-function. The geometric hypothesis
asks only that the boundary contain no point of nonzero order. -/
theorem rectangleIntegral_dirichletL_laplace {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {h : ℝ → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hboundary : ∀ z ∈ Icc a b ×ℂ Icc c d, dirichletOrder χ z ≠ 0 → z ∈ Ioo a b ×ℂ Ioo c d) :
    rectangleIntegral (fun z => (-logDeriv χ.LFunction z) * laplaceTransform h z) a b c d =
      (↑(2 * Real.pi) : ℂ) * I * ∑ w ∈ dirichletRectangleSingularities χ a b c d,
        (-(dirichletOrder χ w : ℂ) * laplaceTransform h w) := by
  apply rectangleIntegral_neg_logDeriv_mul hab hcd _ (dirichletOrder χ)
  · intro w hw
    have ⟨hK, ho⟩ := (mem_dirichletRectangleSingularities χ).mp hw
    exact hboundary w hK ho
  · exact fun w _ => analyticAt_laplaceTransform hh hc w
  · intro z hK hz
    have ho : dirichletOrder χ z = 0 := by
      by_contra! hn
      exact hz ((mem_dirichletRectangleSingularities χ).mpr ⟨hK, hn⟩)
    exact analytic_ne_zero_of_dirichlet_order_zero (by simpa only [ho, WithTop.coe_zero] using
      (dirichletOrder_spec χ z).symm)
  · exact fun w _ => ⟨meromorphic_dirichletL χ w, (dirichletOrder_spec χ w).symm⟩

end GoldbachR581
end

-- R581 TrivialZeros
section
open Complex Filter DirichletCharacter
open scoped Topology Classical

namespace GoldbachR581

private theorem gammaR_inv_eq_mul_shift (z : ℂ) :
    (Gammaℝ z)⁻¹ = (z / (2 * (Real.pi : ℂ))) * (Gammaℝ (z + 2))⁻¹ := by
  by_cases hz : z = 0
  · subst z
    have hΓ : Gammaℝ 0 = 0 := Gammaℝ_eq_zero_iff.mpr ⟨0, by simp⟩
    simp [hΓ]
  · have hq : z / (2 * (Real.pi : ℂ)) ≠ 0 :=
      div_ne_zero hz (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero))
    have hΓ : Gammaℝ (z + 2) = (z / (2 * (Real.pi : ℂ))) * Gammaℝ z := by
      rw [Gammaℝ_add_two hz]
      ring
    rw [hΓ, mul_inv, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]

private theorem deriv_gammaR_inv_neg_even_ne_zero (n : ℕ) :
    deriv (fun z => (Gammaℝ z)⁻¹) (-(2 * (n : ℂ))) ≠ 0 := by
  let g (z : ℂ) := (Gammaℝ z)⁻¹
  have hgd : Differentiable ℂ g := differentiable_Gammaℝ_inv
  have hd (z : ℂ) : deriv g z = (2 * (Real.pi : ℂ))⁻¹ * g (z + 2) +
      (z / (2 * (Real.pi : ℂ))) * deriv g (z + 2) := by
    have hid : HasDerivAt (fun z : ℂ => z / (2 * (Real.pi : ℂ))) (2 * (Real.pi : ℂ))⁻¹ z := by
      simpa [div_eq_mul_inv] using (hasDerivAt_id z).div_const (2 * (Real.pi : ℂ))
    have hshift : HasDerivAt (fun z : ℂ => g (z + 2)) (deriv g (z + 2)) z := by
      simpa only [Function.comp_apply, mul_one] using!
        ((hgd (z + 2)).hasDerivAt).comp z ((hasDerivAt_id z).add_const 2)
    exact ((hid.mul hshift).congr_of_eventuallyEq
      (Eventually.of_forall fun w => gammaR_inv_eq_mul_shift w)).deriv
  change deriv g (-(2 * (n : ℂ))) ≠ 0
  induction n with
  | zero =>
    rw [Nat.cast_zero, mul_zero, neg_zero, hd]
    simp [g, Gammaℝ_ne_zero_of_re_pos (show 0 < (2 : ℂ).re by norm_num), Real.pi_ne_zero]
  | succ n ih =>
    have hshift : -(2 * (n.succ : ℂ)) + 2 = -(2 * (n : ℂ)) := by
      push_cast
      ring
    have hg : g (-(2 * (n : ℂ))) = 0 := by
      simp [g, Gammaℝ_eq_zero_iff.mpr ⟨n, rfl⟩]
    rw [hd, hshift, hg, mul_zero, zero_add]
    exact mul_ne_zero (div_ne_zero
      (neg_ne_zero.mpr (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr n.succ_ne_zero)))
      (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero))) ih

/-- The reciprocal archimedean Gamma factor is entire, with a simple zero at each of its
nonpositive even integers. Mathlib evaluates `Gammaℝ` itself as zero at its poles. -/
theorem meromorphicOrderAt_gammaR_inv (z : ℂ) :
    meromorphicOrderAt (fun s => (Gammaℝ s)⁻¹) z =
      if Gammaℝ z = 0 then 1 else 0 := by
  have ha : AnalyticAt ℂ (fun s => (Gammaℝ s)⁻¹) z := differentiable_Gammaℝ_inv.analyticAt z
  by_cases hz : Gammaℝ z = 0
  · have ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hz
    have ho := ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by simp [hz])
      (hn ▸ deriv_gammaR_inv_neg_even_ne_zero n)
    rw [ite_eq_left hz, ha.meromorphicOrderAt_eq, ho]
    rfl
  · rw [ite_eq_right hz]
    exact order_eq_zero_of_analytic_nonzero ha (inv_ne_zero hz)

theorem gammaFactor_ne_zero_of_re_pos {N : ℕ} (χ : DirichletCharacter ℂ N)
    {z : ℂ} (hz : 0 < z.re) : χ.gammaFactor z ≠ 0 := by
  rcases χ.even_or_odd with he | ho
  · exact he.gammaFactor_def z ▸ Gammaℝ_ne_zero_of_re_pos hz
  · rw [ho.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos (by simp only [add_re, one_re]; linarith)

theorem completed_dirichletL_ne_zero_of_one_le_re {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {z : ℂ} (hz : 1 ≤ z.re) (h₁ : z ≠ 1 ∨ χ ≠ 1) :
    completedLFunction χ z ≠ 0 := by
  have h₀ : z ≠ 0 := by intro h; norm_num [h] at hz
  have hL := χ.LFunction_ne_zero_of_one_le_re h₁.symm hz
  rw [χ.LFunction_eq_completed_div_gammaFactor z (Or.inl h₀)] at hL
  exact (div_ne_zero_iff.mp hL).1

theorem primitive_rootNumber_ne_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) : rootNumber χ ≠ 0 := by
  intro hzero
  have h := hχ.completedLFunction_one_sub (-1)
  rw [hzero, mul_zero, zero_mul, show (1 : ℂ) - (-1) = 2 by norm_num] at h
  exact completed_dirichletL_ne_zero_of_one_le_re χ (z := 2) (by norm_num)
    (Or.inl (by norm_num)) h

private theorem primitive_completed_dirichletL_ne_zero_of_re_nonpos {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {z : ℂ} (hz : z.re ≤ 0)
    (h₀ : z ≠ 0 ∨ χ ≠ 1) : completedLFunction χ z ≠ 0 := by
  have hreflect : (1 : ℂ) - (1 - z) = z := by ring
  rw [← hreflect, hχ.completedLFunction_one_sub (1 - z)]
  apply mul_ne_zero (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne N))))
    (primitive_rootNumber_ne_zero hχ))
  apply completed_dirichletL_ne_zero_of_one_le_re χ⁻¹
  · simpa only [sub_re, one_re, le_sub_self_iff] using hz
  · rcases h₀ with h | h
    · left
      intro he
      exact h (by linear_combination -he)
    · exact Or.inr (by simpa)

/-- On the closed left half-plane away from the conductor-one origin, the only possible
orders of a primitive character are the simple zeros of the reciprocal Gamma factor. -/
theorem dirichletOrder_of_re_nonpos {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) {z : ℂ} (hz : z.re ≤ 0) (h₀ : z ≠ 0 ∨ N ≠ 1) :
    dirichletOrder χ z = if χ.gammaFactor z = 0 then 1 else 0 := by
  have hz₁ : z ≠ 1 := by intro h; norm_num [h] at hz
  have h₀' : z ≠ 0 ∨ χ ≠ 1 := by
    refine h₀.imp_right fun hN ht => ?_
    exact hN (by simpa [ht, conductor_one] using hχ.symm)
  have hn := primitive_completed_dirichletL_ne_zero_of_re_nonpos hχ hz h₀'
  have ha : AnalyticAt ℂ (completedLFunction χ) z := by
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    have hg : ∀ᶠ w in 𝓝 z, w ≠ 0 ∨ N ≠ 1 := by
      rcases h₀ with h | h
      · exact (eventually_ne_nhds h).mono fun _ hw => Or.inl hw
      · exact Eventually.of_forall fun _ => Or.inr h
    filter_upwards [hg, eventually_ne_nhds hz₁] with w hw₀ hw₁
    exact χ.differentiableAt_completedLFunction w hw₀ (Or.inl hw₁)
  have hEq : χ.LFunction =ᶠ[𝓝[≠] z] (fun w => completedLFunction χ w * (χ.gammaFactor w)⁻¹) := by
    have ha : ∀ᶠ w in 𝓝[≠] z, w ≠ 0 ∨ N ≠ 1 := by
      rcases h₀ with h | h
      · exact (eventually_ne_nhdsWithin h).mono fun _ hw => Or.inl hw
      · exact Eventually.of_forall fun _ => Or.inr h
    filter_upwards [ha] with w hw
    exact (χ.LFunction_eq_completed_div_gammaFactor w hw).trans (div_eq_mul_inv _ _)
  have ho : meromorphicOrderAt χ.LFunction z = meromorphicOrderAt (fun w => (χ.gammaFactor w)⁻¹) z := by
    rw [meromorphicOrderAt_congr hEq]
    exact meromorphicOrderAt_mul_of_ne_zero ha hn
  rw [dirichletOrder, ho]
  rcases χ.even_or_odd with he | hd
  · simp_rw [he.gammaFactor_def]
    rw [meromorphicOrderAt_gammaR_inv]
    split_ifs <;> rfl
  · simp_rw [hd.gammaFactor_def]
    rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt (c := (1 : ℂ))
      (f := fun w : ℂ => (Gammaℝ w)⁻¹), meromorphicOrderAt_gammaR_inv]
    split_ifs <;> rfl

/-- The conductor-one origin is regular and nonzero for the uncompleted function. -/
theorem dirichletOrder_modOne_zero (χ : DirichletCharacter ℂ 1) : dirichletOrder χ 0 = 0 := by
  rw [dirichletOrder, order_eq_zero_of_analytic_nonzero
    (analyticAt_dirichletL_of_regular_parameter (χ := χ) (Or.inl zero_ne_one))
    (by simp [LFunction_modOne_eq, riemannZeta_zero]), WithTop.untop₀_zero]

/-- The trivial zeros, in order of decreasing real part. For conductor one the sequence
starts at `-2`, because the uncompleted zeta function does not vanish at zero. -/
noncomputable def dirichletTrivialZero {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ := by
  classical
  exact if N = 1 then -(2 * ((n : ℂ) + 1))
    else if χ.Even then -(2 * (n : ℂ)) else -(2 * (n : ℂ) + 1)

theorem exists_dirichletTrivialZero_iff {N : ℕ} (χ : DirichletCharacter ℂ N) (z : ℂ) :
    (∃ n : ℕ, z = dirichletTrivialZero χ n) ↔ (z ≠ 0 ∨ N ≠ 1) ∧ χ.gammaFactor z = 0 := by
  classical
  by_cases hN : N = 1
  · subst N
    have he : χ.Even := map_one _
    simp only [dirichletTrivialZero, ite_true, ne_eq, not_true_eq_false, or_false,
      he.gammaFactor_def, Gammaℝ_eq_zero_iff]
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨?_, ⟨n + 1, by simp⟩⟩
      exact neg_ne_zero.mpr (mul_ne_zero two_ne_zero (by exact_mod_cast Nat.succ_ne_zero n))
    · rintro ⟨hz, ⟨n, rfl⟩⟩
      cases n with
      | zero => simp at hz
      | succ n => exact ⟨n, by simp⟩
  · rcases χ.even_or_odd with he | ho
    · simp [dirichletTrivialZero, hN, he, he.gammaFactor_def, Gammaℝ_eq_zero_iff]
    · simp only [dirichletTrivialZero, hN, ho.not_even, ite_false, ho.gammaFactor_def,
        Gammaℝ_eq_zero_iff]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨Or.inr hN, n, by linear_combination hn⟩
      · rintro ⟨_, n, hn⟩
        exact ⟨n, by linear_combination hn⟩

/-- Complete classification on the closed left half-plane, including the exceptional origin. -/
theorem dirichletOrder_eq_trivialZero_indicator {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) {z : ℂ} (hz : z.re ≤ 0) :
    dirichletOrder χ z = if ∃ n : ℕ, z = dirichletTrivialZero χ n then 1 else 0 := by
  simp only [exists_dirichletTrivialZero_iff]
  by_cases h₀ : z ≠ 0 ∨ N ≠ 1
  · rw [dirichletOrder_of_re_nonpos hχ hz h₀]
    simp [h₀]
  · push Not at h₀
    obtain ⟨rfl, rfl⟩ := h₀
    simp [dirichletOrder_modOne_zero]

theorem dirichletOrder_nonneg_of_in_criticalStrip {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z : ℂ} (hz : z.re < 1) : 0 ≤ dirichletOrder χ z := by
  have h₁ : z ≠ 1 := by intro h; norm_num [h] at hz
  have ha := analyticAt_dirichletL_of_regular_parameter (χ := χ) (Or.inl h₁)
  exact WithTop.coe_le_coe.mp (by simpa only [dirichletOrder_spec, WithTop.coe_zero] using
    ha.meromorphicOrderAt_nonneg)

theorem dirichletTrivialZero_re_nonpos {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) :
    (dirichletTrivialZero χ n).re ≤ 0 := by
  have hn : 0 ≤ (n : ℝ) := by positivity
  unfold dirichletTrivialZero
  split_ifs <;> simp [Complex.mul_re] <;> linarith

theorem dirichletTrivialZero_injective {N : ℕ} (χ : DirichletCharacter ℂ N) :
    Function.Injective (dirichletTrivialZero χ) := by
  intro m n h
  unfold dirichletTrivialZero at h
  split_ifs at h <;> exact_mod_cast (by linear_combination -(1 / 2 : ℂ) * h : (m : ℂ) = n)

/-- The signed divisor splits into the conductor-one pole, the simple trivial zeros,
and the multiplicities in the open critical strip. -/
theorem dirichletOrder_eq_pole_add_trivial_add_critical {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (z : ℂ) :
    dirichletOrder χ z = -(if N = 1 ∧ z = 1 then (1 : ℤ) else 0) +
      (if ∃ n : ℕ, z = dirichletTrivialZero χ n then 1 else 0) +
      (if 0 < z.re ∧ z.re < 1 then dirichletOrder χ z else 0) := by
  by_cases hz : z.re ≤ 0
  · have h₁ : z ≠ 1 := by intro he; norm_num [he] at hz
    rw [dirichletOrder_eq_trivialZero_indicator hχ hz]
    simp [h₁, not_lt_of_ge hz]
  · have hp : 0 < z.re := lt_of_not_ge hz
    have ht : ¬∃ n : ℕ, z = dirichletTrivialZero χ n := by
      rintro ⟨n, rfl⟩
      exact (not_lt_of_ge (dirichletTrivialZero_re_nonpos χ n)) hp
    by_cases hR : z.re < 1
    · have h₁ : z ≠ 1 := by intro he; norm_num [he] at hR
      simp [h₁, ht, hp, hR]
    · by_cases hP : N = 1 ∧ z = 1
      · obtain ⟨rfl, rfl⟩ := hP
        have hχ₁ : χ = 1 := level_one' χ rfl
        rw [hχ₁] at ht
        simpa [hχ₁, ht] using dirichletOrder_trivial_one 1
      · have hreg : z ≠ 1 ∨ χ ≠ 1 := by
          by_contra! hh
          exact hP ⟨by simpa [hh.2, conductor_one] using hχ.symm, hh.1⟩
        rw [dirichletOrder_eq_zero_of_one_le_re χ (le_of_not_gt hR) hreg]
        simp [hP, ht, hR]

theorem dirichletOrder_ne_zero_imp_mem_critical_of_im_ne_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {z : ℂ} (him : z.im ≠ 0)
    (ho : dirichletOrder χ z ≠ 0) : z.re ∈ Set.Ioo (0 : ℝ) 1 := by
  have h₁ : z ≠ 1 := by intro he; exact him (by simp [he])
  have ht : ¬ ∃ n : ℕ, z = dirichletTrivialZero χ n := by
    rintro ⟨n, rfl⟩
    apply him
    unfold dirichletTrivialZero
    split_ifs <;> simp [Complex.mul_im]
  by_contra h
  exact ho (by
    rw [dirichletOrder_eq_pole_add_trivial_add_critical hχ z]
    simp [h₁, ht, show ¬ (0 < z.re ∧ z.re < 1) from h])

private theorem exists_int_re_dirichletTrivialZero {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) :
    ∃ k : ℤ, (dirichletTrivialZero χ n).re = k := by
  classical
  by_cases hN : N = 1
  · refine ⟨-(2 * ((n : ℤ) + 1)), ?_⟩
    simp [dirichletTrivialZero, hN, Complex.mul_re]
  · rcases χ.even_or_odd with he | ho
    · refine ⟨-(2 * (n : ℤ)), ?_⟩
      simp [dirichletTrivialZero, hN, he, Complex.mul_re]
    · refine ⟨-(2 * (n : ℤ) + 1), ?_⟩
      simp [dirichletTrivialZero, hN, ho.not_even, Complex.mul_re]

/-- Each negative half-integer line is free of singularities for a primitive L-function. -/
theorem dirichletOrder_eq_zero_on_left_halfInteger {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (m : ℕ) {z : ℂ} (hz : z.re = -((m : ℝ) + 1 / 2)) :
    dirichletOrder χ z = 0 := by
  classical
  rw [dirichletOrder_eq_trivialZero_indicator hχ (by rw [hz]; exact neg_nonpos.mpr (by positivity))]
  apply ite_eq_right
  rintro ⟨n, rfl⟩
  obtain ⟨k, hk⟩ := exists_int_re_dirichletTrivialZero χ n
  rw [hk] at hz
  have h : (2 : ℝ) * (k : ℝ) = - (2 * (m : ℝ) + 1) := by linarith
  have h' : (2 : ℤ) * k = -(2 * (m : ℤ) + 1) := by exact_mod_cast h
  omega

/-- The actual trivial-zero sum of R581 is absolutely convergent for a weight supported
strictly to the right of zero. -/
theorem summable_norm_laplace_dirichletTrivialZero {N : ℕ} (χ : DirichletCharacter ℂ N)
    {h : ℝ → ℝ} (hh : MeasureTheory.Integrable h) {a : ℝ}
    (hs : Function.support h ⊆ Set.Ici a) (ha : 0 < a) :
    Summable (fun n : ℕ => ‖laplaceTransform h (dirichletTrivialZero χ n)‖) := by
  classical
  by_cases hN : N = 1
  · refine (summable_laplaceTransform_re_progression hh hs ha (-2) (by norm_num)).congr fun n => ?_
    congr 2
    simp only [dirichletTrivialZero, hN, ite_true, ofReal_sub, ofReal_neg, ofReal_ofNat,
      ofReal_mul, ofReal_natCast]
    ring
  · rcases χ.even_or_odd with he | ho
    · refine (summable_laplaceTransform_re_progression hh hs ha 0 (by norm_num)).congr fun n => ?_
      simp [dirichletTrivialZero, hN, he]
    · refine (summable_laplaceTransform_re_progression hh hs ha (-1) (by norm_num)).congr fun n => ?_
      congr 2
      simp only [dirichletTrivialZero, hN, ho.not_even, ite_false, ofReal_sub, ofReal_neg,
        ofReal_one, ofReal_mul, ofReal_ofNat, ofReal_natCast]
      ring

end GoldbachR581
end

-- R581 PeriodicDirichletSeries
section
open Asymptotics Complex Filter MeasureTheory Set
open scoped Topology

namespace GoldbachR581

private def coefficientSum (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 n, f k

private theorem coefficientSum_eq_range (f : ℕ → ℂ) (n : ℕ) :
    coefficientSum f n = ∑ k ∈ Finset.range n, f (k + 1) := by
  rw [coefficientSum, ← Finset.Ico_succ_right_eq_Icc,
    Order.succ_eq_add_one, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  simp only [add_comm 1]

private theorem coefficientSum_add_period {f : ℕ → ℂ} {p : ℕ}
    (hf : Function.Periodic f p) (n : ℕ) :
    coefficientSum f (n + p) = coefficientSum f p + coefficientSum f n := by
  simp_rw [coefficientSum_eq_range]
  rw [add_comm n p, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [show p + k + 1 = k + 1 + p by omega]
  exact hf (k + 1)

private theorem norm_coefficientSum_le {f : ℕ → ℂ} {C : ℝ} (hf : ∀ n, ‖f n‖ ≤ C)
    (n : ℕ) : ‖coefficientSum f n‖ ≤ n * C := by
  rw [coefficientSum_eq_range]
  calc
    _ ≤ ∑ k ∈ Finset.range n, ‖f (k + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range n, C := Finset.sum_le_sum (fun k _ => hf (k + 1))
    _ = _ := by simp

private noncomputable def centeredCoeffSum (f : ℕ → ℂ) (p : ℕ) (x : ℝ) : ℂ :=
  coefficientSum f ⌊x⌋₊ - (coefficientSum f p / p) * x

private theorem centeredCoeffSum_add_period {f : ℕ → ℂ} {p : ℕ}
    (hp : 0 < p) (hf : Function.Periodic f p) {x : ℝ} (hx : 0 ≤ x) :
    centeredCoeffSum f p (x + p) = centeredCoeffSum f p x := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [centeredCoeffSum, centeredCoeffSum, Nat.floor_add_natCast hx,
    coefficientSum_add_period hf, ofReal_add, ofReal_natCast, mul_add, div_mul_cancel₀ _ hp']
  ring

private theorem measurable_centeredCoeffSum (f : ℕ → ℂ) (p : ℕ) :
    Measurable (centeredCoeffSum f p) := by
  apply Measurable.sub ((measurable_of_countable (coefficientSum f)).comp Nat.measurable_floor)
  exact measurable_const.mul continuous_ofReal.measurable

private theorem continuousWithinAt_centeredCoeffSum_right (f : ℕ → ℂ) (p : ℕ) {x : ℝ}
    (hx : 0 ≤ x) : ContinuousWithinAt (centeredCoeffSum f p) (Ioi x) x := by
  have hmem : ∀ᶠ y in 𝓝[>] x, y ∈ Ioi x := self_mem_nhdsWithin
  have hnear : ∀ᶠ y in 𝓝[>] x, y ∈ Iio ((⌊x⌋₊ : ℝ) + 1) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (Nat.lt_floor_add_one x))
  have hEq : centeredCoeffSum f p =ᶠ[𝓝[>] x]
      (fun y : ℝ => coefficientSum f ⌊x⌋₊ - (coefficientSum f p / p) * y) := by
    filter_upwards [hmem, hnear] with y hy h'
    have hyx : x < y := hy
    have hfl : ⌊y⌋₊ = ⌊x⌋₊ :=
      (Nat.floor_eq_iff (hx.trans hyx.le)).2 ⟨(Nat.floor_le hx).trans hyx.le, h'⟩
    simp only [centeredCoeffSum, hfl]
  have hcont : Continuous (fun y : ℝ => coefficientSum f ⌊x⌋₊ - (coefficientSum f p / p) * y) :=
    continuous_const.sub (continuous_const.mul continuous_ofReal)
  exact hcont.continuousWithinAt.congr_of_eventuallyEq hEq rfl

private theorem intervalIntegrable_centeredCoeffSum {f : ℕ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) (p : ℕ) (a b : ℝ) :
    IntervalIntegrable (centeredCoeffSum f p) volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (by rw [uIoc]; exact measure_Ioc_lt_top.ne)
    (measurable_centeredCoeffSum f p).aestronglyMeasurable
    (M := (max |a| |b|) * (C + ‖coefficientSum f p / p‖)) ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  have hx₀ : x ∈ uIcc a b := uIoc_subset_uIcc hx
  have hx' : |x| ≤ max |a| |b| := by
    rw [abs_le]
    have hA := le_max_left |a| |b|
    have hB := le_max_right |a| |b|
    have ha := abs_le.mp hA
    have hb := abs_le.mp hB
    exact ⟨(le_min ha.1 hb.1).trans hx₀.1, hx₀.2.trans (max_le ha.2 hb.2)⟩
  have hf' : (⌊x⌋₊ : ℝ) ≤ |x| := by
    rcases le_or_gt 0 x with hh | hh
    · exact (Nat.floor_le hh).trans (le_abs_self x)
    · simp [Nat.floor_of_nonpos hh.le]
  calc
    _ ≤ ‖coefficientSum f ⌊x⌋₊‖ + ‖(coefficientSum f p / p) * (x : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ (max |a| |b|) * C + ‖coefficientSum f p / p‖ * (max |a| |b|) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add ((norm_coefficientSum_le hf _).trans
        (mul_le_mul_of_nonneg_right (hf'.trans hx') hC))
        (mul_le_mul_of_nonneg_left hx' (norm_nonneg _))
    _ = _ := by ring

private theorem bounded_on_right_of_period {g : ℝ → ℂ} {p : ℝ} (hp : 0 < p)
    (hperiod : ∀ x ≥ 1, g (x + p) = g x) {C : ℝ}
    (hcompact : ∀ x ∈ Icc 1 (1 + p), ‖g x‖ ≤ C) :
    ∀ x ≥ 1, ‖g x‖ ≤ C := by
  have hstep : ∀ n : ℕ, ∀ x ∈ Icc 1 (1 + n * p), ‖g x‖ ≤ C := by
    intro n
    induction n with
    | zero =>
      intro x hx
      exact hcompact x ⟨hx.1, by simpa using hx.2.trans (by simpa using hp.le)⟩
    | succ n ih =>
      intro x hx
      rcases le_or_gt x (1 + p) with h | h
      · exact hcompact x ⟨hx.1, h⟩
      · have hx' : x - p ∈ Icc 1 (1 + n * p) := by
          refine ⟨by linarith, ?_⟩
          have hupper := hx.2
          push_cast at hupper
          linarith
        have he := hperiod (x - p) hx'.1
        rw [sub_add_cancel] at he
        rw [he]
        exact ih _ hx'
  intro x hx
  obtain ⟨n, hn⟩ := exists_nat_ge ((x - 1) / p)
  exact hstep n x ⟨hx, by linarith [(div_le_iff₀ hp).mp hn]⟩

private noncomputable def centeredCoeffMean (f : ℕ → ℂ) (p : ℕ) : ℂ :=
  (∫ x in (1 : ℝ)..(1 + p), centeredCoeffSum f p x) / p

private noncomputable def coeffPrimitive (f : ℕ → ℂ) (p : ℕ) (x : ℝ) : ℂ :=
  ∫ t in (1 : ℝ)..x, centeredCoeffSum f p t - centeredCoeffMean f p

private theorem continuous_coeffPrimitive {f : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, ‖f n‖ ≤ C) (p : ℕ) : Continuous (coeffPrimitive f p) :=
  intervalIntegral.continuous_primitive
    (fun a b => (intervalIntegrable_centeredCoeffSum hC hf p a b).sub intervalIntegrable_const) 1

private theorem coeffPrimitive_hasDerivWithinAt_right {f : ℕ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) (p : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt (coeffPrimitive f p) (centeredCoeffSum f p x - centeredCoeffMean f p)
      (Ioi x) x := by
  apply HasDerivWithinAt.mono (t := Ici x) _ Ioi_subset_Ici_self
  refine intervalIntegral.integral_hasDerivWithinAt_right (t := Ioi x)
    ((intervalIntegrable_centeredCoeffSum hC hf p 1 x).sub intervalIntegrable_const) ?_
    ((continuousWithinAt_centeredCoeffSum_right f p hx).sub continuousWithinAt_const)
  exact ((measurable_centeredCoeffSum f p).sub measurable_const).stronglyMeasurable.stronglyMeasurableAtFilter

private theorem coeffPrimitive_add_period {f : ℕ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) {p : ℕ} (hp : 0 < p) (hper : Function.Periodic f p)
    {x : ℝ} (hx : 1 ≤ x) : coeffPrimitive f p (x + p) = coeffPrimitive f p x := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  let g := fun t : ℝ => centeredCoeffSum f p t - centeredCoeffMean f p
  have hg (a b : ℝ) : IntervalIntegrable g volume a b :=
    (intervalIntegrable_centeredCoeffSum hC hf p a b).sub intervalIntegrable_const
  have hzero : ∫ t in (1 : ℝ)..(1 + p), g t = 0 := by
    dsimp only [g]
    rw [intervalIntegral.integral_sub (intervalIntegrable_centeredCoeffSum hC hf p _ _)
      intervalIntegrable_const, intervalIntegral.integral_const, add_sub_cancel_left,
      Complex.real_smul, ofReal_natCast, centeredCoeffMean, ← mul_div_assoc,
      mul_div_cancel_left₀ _ hp', sub_self]
  change (∫ t in (1 : ℝ)..(x + p), g t) = ∫ t in (1 : ℝ)..x, g t
  rw [← intervalIntegral.integral_add_adjacent_intervals (hg 1 (1 + p)) (hg (1 + p) (x + p)),
    hzero, zero_add, ← intervalIntegral.integral_comp_add_right]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hx] at ht
  simp only [g, centeredCoeffSum_add_period hp hper (zero_le_one.trans ht.1)]

private theorem exists_bound_coeffPrimitive {f : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, ‖f n‖ ≤ C) {p : ℕ} (hp : 0 < p) (hper : Function.Periodic f p) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ≥ 1, ‖coeffPrimitive f p x‖ ≤ B := by
  have hcf := continuous_coeffPrimitive hC hf p
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image
    (hcf.norm.continuousOn : ContinuousOn (fun x => ‖coeffPrimitive f p x‖) (Icc 1 (1 + (p : ℝ))))
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hb (x : ℝ) (hx : x ∈ Icc 1 (1 + (p : ℝ))) : ‖coeffPrimitive f p x‖ ≤ B :=
    hB (mem_image_of_mem _ hx)
  exact ⟨B, (norm_nonneg _).trans (hb 1 ⟨le_rfl, by linarith⟩),
    bounded_on_right_of_period hp' (fun _ hx => coeffPrimitive_add_period hC hf hp hper hx) hb⟩

private theorem exists_bound_centeredCoeffSum {f : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, ‖f n‖ ≤ C) {p : ℕ} (hp : 0 < p) (hper : Function.Periodic f p) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ≥ 1, ‖centeredCoeffSum f p x‖ ≤ B := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  refine ⟨(1 + (p : ℝ)) * (C + ‖coefficientSum f p / p‖), by positivity,
    bounded_on_right_of_period hp'
      (fun x hx => centeredCoeffSum_add_period hp hper (zero_le_one.trans hx)) ?_⟩
  intro x hx
  have hx₀ : 0 ≤ x := zero_le_one.trans hx.1
  calc
    _ ≤ ‖coefficientSum f ⌊x⌋₊‖ + ‖(coefficientSum f p / p) * (x : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ (1 + (p : ℝ)) * C + ‖coefficientSum f p / p‖ * (1 + (p : ℝ)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx₀]
      exact add_le_add ((norm_coefficientSum_le hf _).trans
        (mul_le_mul_of_nonneg_right ((Nat.floor_le hx₀).trans hx.2) hC))
        (mul_le_mul_of_nonneg_left hx.2 (norm_nonneg _))
    _ = _ := by ring

private theorem integrableOn_mul_cpow_of_bounded {g : ℝ → ℂ} (hg : Measurable g)
    {B : ℝ} (hB : ∀ x ≥ 1, ‖g x‖ ≤ B) {r : ℂ} (hr : r.re < -1) :
    IntegrableOn (fun x : ℝ => g x * (x : ℂ) ^ r) (Ioi 1) := by
  have hcont : ContinuousOn (fun x : ℝ => (x : ℂ) ^ r) (Ioi 1) := fun x hx =>
    (continuousAt_ofReal_cpow_const x r (Or.inr (zero_lt_one.trans hx).ne')).continuousWithinAt
  refine ((integrableOn_Ioi_rpow_of_lt hr zero_lt_one).const_mul B).mono'
    (hg.aestronglyMeasurable.mul (hcont.aestronglyMeasurable measurableSet_Ioi)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : 1 < x := hx
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx')]
  exact mul_le_mul_of_nonneg_right (hB x hx'.le) (Real.rpow_nonneg (zero_le_one.trans hx'.le) _)

private noncomputable def tailPowerIntegral (g : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 1, g x * (x : ℂ) ^ (-(s + 2))

private theorem differentiableAt_tailPowerIntegral {g : ℝ → ℂ} (hg : Continuous g)
    {B : ℝ} (hB : ∀ x ≥ 1, ‖g x‖ ≤ B) {s : ℂ} (hs : -1 < s.re) :
    DifferentiableAt ℂ (tailPowerIntegral g) s := by
  let G := (Ioi (1 : ℝ)).indicator g
  have hG : LocallyIntegrableOn G (Ioi 0) :=
    (hg.locallyIntegrable.indicator measurableSet_Ioi).locallyIntegrableOn _
  have htop : G =O[atTop] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
    refine isBigO_iff.mpr ⟨B, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx' : x ∈ Ioi (1 : ℝ) := hx
    rw [show G x = g x from indicator_of_mem hx' _]
    simpa using hB x hx.le
  have hbot : G =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-((-s - 1).re - 1))) := by
    refine isBigO_iff.mpr ⟨0, ?_⟩
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with x hx
    have hx' : x < 1 := hx
    have hx'' : x ∉ Ioi (1 : ℝ) := not_lt.mpr hx'.le
    rw [show G x = 0 from indicator_of_notMem hx'' _]
    simp
  have hmel := mellin_differentiableAt_of_isBigO_rpow hG htop
    (show (-s - 1).re < 0 by simp only [sub_re, neg_re, one_re]; linarith) hbot (sub_lt_self _ zero_lt_one)
  have hcomp := hmel.comp s (((differentiableAt_id (𝕜 := ℂ) (x := s)).neg).sub_const 1)
  convert hcomp using 1
  ext z
  have he : (fun x : ℝ => (x : ℂ) ^ (-z - 1 - 1) • G x) =
      (Ioi (1 : ℝ)).indicator (fun x : ℝ => g x * (x : ℂ) ^ (-(z + 2))) := by
    funext x
    have hpow : -z - 1 - 1 = -(z + 2) := by ring
    by_cases hx : x ∈ Ioi (1 : ℝ) <;> simp [G, hpow, hx, smul_eq_mul, mul_comm]
  change tailPowerIntegral g z = mellin G (-z - 1)
  rw [mellin, he, setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr
    (Ioi_subset_Ioi_iff.mpr (zero_le_one : (0 : ℝ) ≤ 1))]
  rfl

private theorem norm_tailPowerIntegral_le {g : ℝ → ℂ} {B : ℝ}
    (hB : ∀ x ≥ 1, ‖g x‖ ≤ B) {a : ℝ} (ha : -1 < a) {s : ℂ} (hs : a ≤ s.re) :
    ‖tailPowerIntegral g s‖ ≤ B / (a + 1) := by
  have h : -a - 2 < -1 := by linarith
  have hBi := (integrableOn_Ioi_rpow_of_lt h zero_lt_one).const_mul B
  change ‖∫ x : ℝ in Ioi 1, g x * (x : ℂ) ^ (-(s + 2))‖ ≤ _
  calc
    _ ≤ ∫ x : ℝ in Ioi 1, B * x ^ (-a - 2) := by
      refine norm_integral_le_of_norm_le hBi ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx' : 1 < x := hx
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx')]
      exact mul_le_mul (hB x hx'.le)
        (Real.rpow_le_rpow_of_exponent_le hx'.le (by simp only [neg_re, add_re]; norm_num; linarith))
        (Real.rpow_nonneg (zero_le_one.trans hx'.le) _) ((norm_nonneg _).trans (hB 1 le_rfl))
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt h zero_lt_one, Real.one_rpow]
      rw [show -a - 2 + 1 = -(a + 1) by ring, neg_div_neg_eq, mul_one_div]

private theorem integral_centeredCoeffSum_sub_mean {f : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, ‖f n‖ ≤ C) {p : ℕ} (hp : 0 < p) (hper : Function.Periodic f p)
    {s : ℂ} (hs : 0 < s.re) :
    (∫ x : ℝ in Ioi 1, (centeredCoeffSum f p x - centeredCoeffMean f p) *
      (x : ℂ) ^ (-(s + 1))) = (s + 1) * tailPowerIntegral (coeffPrimitive f p) s := by
  let P := coeffPrimitive f p
  let Q := fun x : ℝ => centeredCoeffSum f p x - centeredCoeffMean f p
  let K := fun x : ℝ => (x : ℂ) ^ (-(s + 1))
  let J := fun x : ℝ => (x : ℂ) ^ (-(s + 2))
  have hpcont : Continuous P := continuous_coeffPrimitive hC hf p
  have hqm : Measurable Q := (measurable_centeredCoeffSum f p).sub measurable_const
  obtain ⟨B, _, hb⟩ := exists_bound_coeffPrimitive hC hf hp hper
  obtain ⟨D, _, hd⟩ := exists_bound_centeredCoeffSum hC hf hp hper
  have hq (x : ℝ) (hx : 1 ≤ x) : ‖Q x‖ ≤ D + ‖centeredCoeffMean f p‖ :=
    (norm_sub_le _ _).trans (add_le_add_left (hd x hx) _)
  have hk : (-(s + 1)).re < -1 := by simp only [neg_re, add_re, one_re]; linarith
  have hj : (-(s + 2)).re < -1 := by simp only [neg_re, add_re]; norm_num; linarith
  have hIntQ : IntegrableOn (fun x => Q x * K x) (Ioi 1) :=
    integrableOn_mul_cpow_of_bounded hqm hq hk
  have hIntP : IntegrableOn (fun x => P x * J x) (Ioi 1) :=
    integrableOn_mul_cpow_of_bounded hpcont.measurable hb hj
  have hfinite (b : ℝ) (hb₁ : 1 ≤ b) :
      (∫ x in (1 : ℝ)..b, Q x * K x) =
        K b * P b + (s + 1) * (∫ x in (1 : ℝ)..b, P x * J x) := by
    have hK : ContinuousOn K (uIcc 1 b) := by
      rw [uIcc_of_le hb₁]
      exact fun x hx => (continuousAt_ofReal_cpow_const x _ (Or.inr
        (zero_lt_one.trans_le hx.1).ne')).continuousWithinAt
    have hKd {x : ℝ} (hx : 1 ≤ x) : HasDerivAt K (-(s + 1) * J x) x := by
      have hn : -(s + 1) ≠ 0 := fun e => by rw [e, zero_re] at hk; linarith
      convert hasDerivAt_ofReal_cpow_const (zero_lt_one.trans_le hx).ne' hn using 1
      dsimp only [J]
      congr 2
      ring
    have hKi : IntervalIntegrable (fun x => -(s + 1) * J x) volume 1 b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hb₁).2
        (((integrableOn_Ioi_cpow_of_lt hj zero_lt_one).mono_set Ioc_subset_Ioi_self).const_mul _)
    have hQi : IntervalIntegrable Q volume 1 b :=
      (intervalIntegrable_centeredCoeffSum hC hf p 1 b).sub intervalIntegrable_const
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
      hK hpcont.continuousOn
      (fun x hx => (hKd ((min_eq_left hb₁ ▸ hx.1).le)).hasDerivWithinAt)
      (fun x hx => coeffPrimitive_hasDerivWithinAt_right hC hf p
        (zero_le_one.trans (min_eq_left hb₁ ▸ hx.1).le)) hKi hQi
    have hp1 : P 1 = 0 := intervalIntegral.integral_same
    simp only [hp1, mul_zero, sub_zero] at hibp
    simp_rw [mul_comm (K _), mul_assoc, mul_comm (J _),
      intervalIntegral.integral_const_mul, neg_mul, sub_neg_eq_add] at hibp
    simpa only [mul_comm (P b) (K b)] using hibp
  have hzero : Tendsto (fun b : ℝ => K b * P b) atTop (𝓝 0) := by
    have hlim : Tendsto (fun b : ℝ => b ^ (-s.re - 1) * B) atTop (𝓝 0) := by
      rw [show -s.re - 1 = -(s.re + 1) by ring]
      simpa only [zero_mul] using
        (tendsto_rpow_neg_atTop (show 0 < s.re + 1 by linarith)).mul_const B
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb₁
    rw [norm_mul, show ‖K b‖ = b ^ (-s.re - 1) by
      change ‖(b : ℂ) ^ (-(s + 1))‖ = _
      rw [norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hb₁), neg_re, add_re, one_re]
      congr 1
      ring]
    exact mul_le_mul_of_nonneg_left (hb b hb₁) (Real.rpow_nonneg (zero_le_one.trans hb₁) _)
  have hLeft := intervalIntegral_tendsto_integral_Ioi 1 hIntQ tendsto_id
  have hRight := hzero.add ((intervalIntegral_tendsto_integral_Ioi 1 hIntP tendsto_id).const_mul (s + 1))
  rw [zero_add] at hRight
  exact tendsto_nhds_unique hLeft (hRight.congr' (by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb₁ using (hfinite b hb₁).symm))

private theorem LSeries_eq_periodic_integral {f : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, ‖f n‖ ≤ C) {p : ℕ} (hp : 0 < p) (hper : Function.Periodic f p)
    {s : ℂ} (hs : 1 < s.re) :
    (s - 1) * LSeries f s = s * (coefficientSum f p / p) +
      (s - 1) * centeredCoeffMean f p +
      (s - 1) * s * (s + 1) * tailPowerIntegral (coeffPrimitive f p) s := by
  let c := coefficientSum f p / (p : ℂ)
  let d := centeredCoeffMean f p
  let Q := fun x : ℝ => centeredCoeffSum f p x - d
  let K := fun x : ℝ => (x : ℂ) ^ (-(s + 1))
  let T := tailPowerIntegral (coeffPrimitive f p) s
  have hS : LSeries f s = s * ∫ x : ℝ in Ioi 1, coefficientSum f ⌊x⌋₊ * K x := by
    apply LSeries_eq_mul_integral' f (r := 1) zero_le_one hs
    refine isBigO_iff.mpr ⟨C, Eventually.of_forall fun n => ?_⟩
    rw [Real.rpow_one, Real.norm_of_nonneg (Nat.cast_nonneg n)]
    rw [← Finset.Ico_succ_right_eq_Icc, Order.succ_eq_add_one, Finset.sum_Ico_eq_sum_range,
      Nat.add_sub_cancel, mul_comm]
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    calc
      _ ≤ ∑ _k ∈ Finset.range n, C := Finset.sum_le_sum (fun k _ => hf (1 + k))
      _ = _ := by simp
  have hpow1 : (-s).re < -1 := by simp only [neg_re]; linarith
  have hpow2 : (-(s + 1)).re < -1 := by simp only [neg_re, add_re, one_re]; linarith
  have hCInt : IntegrableOn (fun x : ℝ => c * (x : ℂ) ^ (-s)) (Ioi 1) :=
    (integrableOn_Ioi_cpow_of_lt hpow1 zero_lt_one).const_mul _
  have hDInt : IntegrableOn (fun x : ℝ => d * K x) (Ioi 1) :=
    (integrableOn_Ioi_cpow_of_lt hpow2 zero_lt_one).const_mul _
  obtain ⟨D, _, hD⟩ := exists_bound_centeredCoeffSum hC hf hp hper
  have hQInt : IntegrableOn (fun x : ℝ => Q x * K x) (Ioi 1) :=
    integrableOn_mul_cpow_of_bounded ((measurable_centeredCoeffSum f p).sub measurable_const)
      (fun x hx => (norm_sub_le _ _).trans (add_le_add_left (hD x hx) _)) hpow2
  have hsplit :
      (∫ x : ℝ in Ioi 1, coefficientSum f ⌊x⌋₊ * K x) =
        (∫ x : ℝ in Ioi 1, c * (x : ℂ) ^ (-s)) +
        (∫ x : ℝ in Ioi 1, d * K x) +
        ∫ x : ℝ in Ioi 1, Q x * K x := by
    have hCD : IntegrableOn (fun x : ℝ => c * (x : ℂ) ^ (-s) + d * K x) (Ioi 1) :=
      hCInt.add hDInt
    calc
      _ = ∫ x : ℝ in Ioi 1, (c * (x : ℂ) ^ (-s) + d * K x) + Q x * K x := by
        refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
        have hx' : 1 < x := hx
        have hx₀ : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans hx').ne'
        have he : (x : ℂ) * K x = (x : ℂ) ^ (-s) := by
          change (x : ℂ) * (x : ℂ) ^ (-(s + 1)) = _
          conv_lhs => arg 1; rw [← cpow_one (x : ℂ)]
          rw [← cpow_add _ _ hx₀]
          congr 1
          ring
        rw [← he]
        simp only [Q, centeredCoeffSum, c]
        ring
      _ = _ := by
        rw [integral_add hCD hQInt, integral_add hCInt hDInt]
  have hCval : (∫ x : ℝ in Ioi 1, c * (x : ℂ) ^ (-s)) = c / (s - 1) := by
    rw [integral_const_mul, integral_Ioi_cpow_of_lt hpow1 zero_lt_one, ofReal_one, one_cpow,
      show -s + 1 = -(s - 1) by ring, neg_div_neg_eq, mul_one_div]
  have hDval : (∫ x : ℝ in Ioi 1, d * K x) = d / s := by
    change (∫ x : ℝ in Ioi 1, d * (x : ℂ) ^ (-(s + 1))) = _
    rw [integral_const_mul, integral_Ioi_cpow_of_lt hpow2 zero_lt_one, ofReal_one, one_cpow,
      show -(s + 1) + 1 = -s by ring, neg_div_neg_eq, mul_one_div]
  have hQval : (∫ x : ℝ in Ioi 1, Q x * K x) = (s + 1) * T :=
    integral_centeredCoeffSum_sub_mean hC hf hp hper (zero_lt_one.trans hs)
  have hs₀ : s ≠ 0 := ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hs₁ : s - 1 ≠ 0 := ne_zero_of_re_pos (by simpa only [sub_re, one_re, sub_pos] using hs)
  rw [hS, hsplit, hCval, hDval, hQval]
  change (s - 1) * (s * (c / (s - 1) + d / s + (s + 1) * T)) = _
  field_simp [hs₀, hs₁]
  ring

/-- For bounded periodic coefficients, the pole-removed Dirichlet series continues to
`Re s > -1` and is bounded by a cubic on every smaller closed right half-plane. -/
theorem exists_regularized_periodicLSeries {f : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, ‖f n‖ ≤ C) {p : ℕ} (hp : 0 < p) (hper : Function.Periodic f p) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s | -1 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → G s = (s - 1) * LSeries f s) ∧
      ∀ a : ℝ, -1 < a → ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, a ≤ s.re →
        ‖G s‖ ≤ A * (1 + ‖s‖) ^ 3 := by
  let c := coefficientSum f p / (p : ℂ)
  let d := centeredCoeffMean f p
  let P := coeffPrimitive f p
  let G := fun s : ℂ => s * c + (s - 1) * d + (s - 1) * s * (s + 1) * tailPowerIntegral P s
  obtain ⟨B, hB, hb⟩ := exists_bound_coeffPrimitive hC hf hp hper
  refine ⟨G, ?_, fun s hs => (LSeries_eq_periodic_integral hC hf hp hper hs).symm, ?_⟩
  · intro s hs
    have hM := differentiableAt_tailPowerIntegral (continuous_coeffPrimitive hC hf p) hb hs
    have hG : DifferentiableAt ℂ G s := by unfold G; fun_prop
    exact hG.differentiableWithinAt
  · intro a ha
    let M := B / (a + 1)
    have hM : 0 ≤ M := div_nonneg hB (by linarith)
    refine ⟨‖c‖ + ‖d‖ + M, by positivity, fun s hs => ?_⟩
    let u := 1 + ‖s‖
    have hu : 1 ≤ u := le_add_of_nonneg_right (norm_nonneg _)
    have hu₀ : 0 ≤ u := zero_le_one.trans hu
    have hs₀ : ‖s‖ ≤ u := by dsimp [u]; linarith
    have hm : ‖s - 1‖ ≤ u := (norm_sub_le _ _).trans (by simp [u, add_comm])
    have hp₁ : ‖s + 1‖ ≤ u := (norm_add_le _ _).trans (by simp [u, add_comm])
    have hu₃ : u ≤ u ^ 3 := by
      calc
        u = u * 1 := (mul_one _).symm
        _ ≤ u * u ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hu) hu₀
        _ = _ := by ring
    have hrest : ‖tailPowerIntegral P s‖ ≤ M := norm_tailPowerIntegral_le hb ha hs
    have hprod : ‖(s - 1) * s * (s + 1) * tailPowerIntegral P s‖ ≤ u ^ 3 * M := by
      simp only [norm_mul]
      rw [show u ^ 3 = u * u * u by ring]
      gcongr
    calc
      ‖G s‖ ≤ ‖s * c‖ + ‖(s - 1) * d‖ + ‖(s - 1) * s * (s + 1) * tailPowerIntegral P s‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
      _ ≤ u ^ 3 * ‖c‖ + u ^ 3 * ‖d‖ + u ^ 3 * M := by
        rw [norm_mul s, norm_mul (s - 1)]
        exact add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right (hs₀.trans hu₃) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hm.trans hu₃) (norm_nonneg _))) hprod
      _ = _ := by ring

end GoldbachR581
end

-- R581 UnitZeroCount
section
open Complex Filter Set Metric DirichletCharacter
open scoped Topology Classical BigOperators

namespace GoldbachR581

/-- Remove the principal pole before using Jensen's inequality. -/
noncomputable def entireDirichletL {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℂ → ℂ :=
  if χ = 1 then LFunctionTrivChar₁ N else χ.LFunction

theorem analyticAt_entireDirichletL {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (z : ℂ) :
    AnalyticAt ℂ (entireDirichletL χ) z := by
  unfold entireDirichletL
  split_ifs with h
  · exact (differentiable_LFunctionTrivChar₁ N).analyticAt z
  · exact (differentiable_LFunction h).analyticAt z

/-- A cubic bound for the actual L-function after removing the principal pole.
The constant may depend on the character and the left edge of the half-plane. -/
theorem exists_polynomial_bound_entireDirichletL {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {a : ℝ} (ha : -1 < a) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ z : ℂ, a ≤ z.re → ‖entireDirichletL χ z‖ ≤ A * (1 + ‖z‖) ^ 3 := by
  let f := fun n : ℕ => χ (n : ZMod N)
  have hf : Function.Periodic f N := by
    intro n
    simp [f, Nat.cast_add]
  obtain ⟨G, hGa, hGe, hGb⟩ := exists_regularized_periodicLSeries zero_le_one
    (fun n => χ.norm_le_one (n : ZMod N)) (NeZero.pos N) hf
  let F := fun z : ℂ => if χ = 1 then entireDirichletL χ z else (z - 1) * entireDirichletL χ z
  have hF (z : ℂ) : AnalyticAt ℂ F z := by
    dsimp only [F]
    split_ifs
    · exact analyticAt_entireDirichletL χ z
    · exact (analyticAt_id.sub analyticAt_const).mul (analyticAt_entireDirichletL χ z)
  have hFG : EqOn F G {z | -1 < z.re} := by
    have hz : (2 : ℂ) ∈ {z : ℂ | -1 < z.re} := by norm_num [Set.mem_ofPred_eq]
    apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (z₀ := (2 : ℂ))
      (fun z _ => hF z) ((analyticOnNhd_iff_differentiableOn (isOpen_re_gt (-1))).2 hGa)
      (convex_halfSpace_re_gt (r := -1)).isPreconnected hz
    have hmem : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), z ∈ {z : ℂ | 1 < z.re} :=
      (isOpen_re_gt 1).mem_nhds (by norm_num [Set.mem_ofPred_eq])
    filter_upwards [hmem] with z hz'
    have hzre : 1 < z.re := hz'
    have hz₁ : z ≠ 1 := fun e => by rw [e, one_re] at hzre; exact lt_irrefl _ hzre
    rw [hGe z hzre, ← χ.LFunction_eq_LSeries hzre]
    by_cases hχ : χ = 1
    · simp [F, entireDirichletL, hχ, LFunctionTrivChar₁, Function.update_of_ne hz₁]
    · simp [F, entireDirichletL, hχ]
  obtain ⟨A, _, hAb⟩ := hGb a ha
  have hC : Continuous (fun z => ‖entireDirichletL χ z‖) :=
    (continuous_iff_continuousAt.mpr fun z => (analyticAt_entireDirichletL χ z).continuousAt).norm
  obtain ⟨B, hB⟩ := (isCompact_closedBall (1 : ℂ) 1).bddAbove_image hC.continuousOn
  let M := max 1 (max A B)
  have hM : 1 ≤ M := le_max_left _ _
  refine ⟨M, hM, fun z hz => ?_⟩
  have hFA : ‖F z‖ ≤ M * (1 + ‖z‖) ^ 3 := by
    rw [hFG (show z ∈ {z : ℂ | -1 < z.re} from ha.trans_le hz)]
    exact (hAb z hz).trans (mul_le_mul_of_nonneg_right
      ((le_max_left A B).trans (le_max_right 1 _)) (by positivity))
  have h1 : 1 ≤ (1 + ‖z‖) ^ 3 := one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _))
  by_cases hχ : χ = 1
  · simpa only [F, ite_eq_left hχ] using hFA
  by_cases hb : z ∈ closedBall (1 : ℂ) 1
  · exact (hB (mem_image_of_mem _ hb)).trans ((le_max_right A B).trans
      ((le_max_right 1 _).trans (le_mul_of_one_le_right (zero_le_one.trans hM) h1)))
  · have hz₁ : 1 ≤ ‖z - 1‖ := by
      rw [mem_closedBall, Complex.dist_eq, not_le] at hb
      exact hb.le
    refine (le_mul_of_one_le_left (norm_nonneg _) hz₁).trans ?_
    simpa only [F, ite_eq_right hχ, norm_mul] using hFA

theorem meromorphicOrderAt_entireDirichletL {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z : ℂ} (hz : z ≠ 1) : meromorphicOrderAt (entireDirichletL χ) z = (dirichletOrder χ z : WithTop ℤ) := by
  rw [dirichletOrder_spec]
  by_cases hχ : χ = 1
  · subst χ
    have he : entireDirichletL (1 : DirichletCharacter ℂ N) =ᶠ[𝓝[≠] z]
        (fun w => (w - 1) * LFunctionTrivChar N w) := by
      filter_upwards [eventually_ne_nhdsWithin hz] with w hw
      simp only [entireDirichletL, ite_true, LFunctionTrivChar₁, Function.update_of_ne hw]
    rw [meromorphicOrderAt_congr he]
    exact meromorphicOrderAt_mul_of_ne_zero (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hz)
  · simp [entireDirichletL, hχ]

theorem exists_pos_le_norm_entireDirichletL_on_two {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, c ≤ ‖entireDirichletL χ (verticalPoint 2 t)‖ := by
  obtain ⟨c, hc, hb⟩ := exists_pos_le_norm_dirichletL_of_re_ge χ (σ := 2) (by norm_num)
  refine ⟨c, hc, fun t => ?_⟩
  let z := verticalPoint 2 t
  have hz : z.re = 2 := verticalPoint_re _ _
  have hz₁ : z ≠ 1 := by intro he; norm_num [he] at hz
  have h := hb z hz.ge
  change c ≤ ‖entireDirichletL χ z‖
  by_cases hχ : χ = 1
  · have hfactor : 1 ≤ ‖z - 1‖ :=
      (by rw [sub_re, one_re, hz]; norm_num : 1 ≤ (z - 1).re).trans (Complex.re_le_norm _)
    have h' : c ≤ ‖LFunctionTrivChar N z‖ := by simpa only [hχ] using h
    rw [entireDirichletL, ite_eq_left hχ, LFunctionTrivChar₁, Function.update_of_ne hz₁, norm_mul]
    exact h'.trans (le_mul_of_one_le_left (norm_nonneg _) hfactor)
  · simpa only [entireDirichletL, ite_eq_right hχ] using h

/-- Distinct nontrivial zero locations with imaginary part at most one from `t`. -/
noncomputable def dirichletUnitZeros {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) : Finset ℂ :=
  (dirichletRectangleSingularities χ 0 1 (t - 1) (t + 1)).filter (fun z => z.re ∈ Ioo (0 : ℝ) 1)

theorem mem_dirichletUnitZeros {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {t : ℝ} {z : ℂ} :
    z ∈ dirichletUnitZeros χ t ↔ z.re ∈ Ioo (0 : ℝ) 1 ∧ |z.im - t| ≤ 1 ∧ dirichletOrder χ z ≠ 0 := by
  rw [dirichletUnitZeros, Finset.mem_filter, mem_dirichletRectangleSingularities, mem_reProdIm, abs_le]
  constructor
  · rintro ⟨⟨⟨_, him⟩, ho⟩, hstrip⟩
    exact ⟨hstrip, ⟨by linarith [him.1], by linarith [him.2]⟩, ho⟩
  · rintro ⟨hstrip, ⟨hl, hu⟩, ho⟩
    exact ⟨⟨⟨⟨hstrip.1.le, hstrip.2.le⟩, ⟨by linarith, by linarith⟩⟩, ho⟩, hstrip⟩

private theorem dirichletUnitZero_mem_closedBall {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {t : ℝ} {z : ℂ} (hz : z ∈ dirichletUnitZeros χ t) : z ∈ closedBall (verticalPoint 2 t) (5 / 2) := by
  obtain ⟨hm, _⟩ := Finset.mem_filter.mp hz
  have ⟨hr, hi⟩ := mem_reProdIm.mp ((mem_dirichletRectangleSingularities χ).mp hm).1
  have hr' : |z.re - 2| ≤ 2 := abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hi' : |z.im - t| ≤ 1 := abs_le.mpr ⟨by linarith [hi.1], by linarith [hi.2]⟩
  have hr₂ := pow_le_pow_left₀ (abs_nonneg _) hr' 2
  have hi₂ := pow_le_pow_left₀ (abs_nonneg _) hi' 2
  rw [sq_abs] at hr₂ hi₂
  have hsq : ‖z - verticalPoint 2 t‖ ^ 2 ≤ 5 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, sub_im, verticalPoint_re, verticalPoint_im]
    nlinarith
  rw [mem_closedBall, Complex.dist_eq]
  nlinarith [norm_nonneg (z - verticalPoint 2 t)]

/-- Jensen's inequality gives the unit-height count with multiplicity from a bound on a
circle about `2 + it` of radius greater than `5 / 2`. -/
theorem dirichletUnitZero_count_le_jensen {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (t : ℝ) {R M : ℝ} (hR : 5 / 2 < R) (hM : 1 ≤ M)
    (hbound : ∀ z ∈ sphere (verticalPoint 2 t) R, ‖entireDirichletL χ z‖ ≤ M) :
    ((∑ z ∈ dirichletUnitZeros χ t, dirichletOrder χ z : ℤ) : ℝ) ≤
      Real.log (M / ‖entireDirichletL χ (verticalPoint 2 t)‖) / Real.log (R / (5 / 2)) := by
  let c := verticalPoint 2 t
  let U := closedBall c (5 / 2)
  let D := MeromorphicOn.divisor (entireDirichletL χ) U
  let S := (D.finiteSupport (isCompact_closedBall _ _)).toFinset
  have hA : AnalyticOnNhd ℂ (entireDirichletL χ) U := fun z _ => analyticAt_entireDirichletL χ z
  have hcore : entireDirichletL χ c ≠ 0 := by
    obtain ⟨q, hq, hb⟩ := exists_pos_le_norm_entireDirichletL_on_two χ
    exact norm_pos_iff.mp (hq.trans_le (hb t))
  have hR₀ : 0 ≤ R := by linarith
  have hj := AnalyticOnNhd.sum_divisor_le (c := c) (r := (5 / 2 : ℝ)) (R := R)
    (by norm_num) (by rwa [abs_of_nonneg (by norm_num : 0 ≤ (5 / 2 : ℝ)), abs_of_nonneg hR₀])
    hM (fun z _ => analyticAt_entireDirichletL χ z) hcore
    (by simpa only [abs_of_nonneg hR₀] using hbound)
  rw [abs_of_nonneg (by norm_num : 0 ≤ (5 / 2 : ℝ))] at hj
  have hj' : ((∑ᶠ z, D z : ℤ) : ℝ) ≤ _ := hj
  have hsum : (∑ᶠ z, D z) = ∑ z ∈ S, D z :=
    finsum_eq_sum_of_support_subset _ (by
      intro z hz
      simpa only [S, Finset.mem_coe, Set.Finite.mem_toFinset] using hz)
  rw [hsum] at hj'
  have hval {z : ℂ} (hz : z ∈ dirichletUnitZeros χ t) : D z = dirichletOrder χ z := by
    have hb : z ∈ U := dirichletUnitZero_mem_closedBall hz
    have hre := (Finset.mem_filter.mp hz).2.2
    have h₁ : z ≠ 1 := by intro he; norm_num [he] at hre
    dsimp only [D]
    rw [MeromorphicOn.divisor_apply hA.meromorphicOn hb, meromorphicOrderAt_entireDirichletL χ h₁,
      WithTop.untop₀_coe]
  have hsub : dirichletUnitZeros χ t ⊆ S := by
    intro z hz
    simpa only [S, Set.Finite.mem_toFinset, Function.mem_support, hval hz] using
      ((mem_dirichletRectangleSingularities χ).mp (Finset.mem_filter.mp hz).1).2
  have hDn : ∀ z : ℂ, 0 ≤ D z := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hA
  refine le_trans (Int.cast_le.mpr ?_) hj'
  rw [Finset.sum_congr rfl (fun z hz => (hval hz).symm)]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => hDn z)

/-- A polynomial growth bound on the Jensen circles suffices for a logarithmic unit-height
zero count. The lower bound at the centers follows from the inverse Dirichlet series. -/
theorem dirichletUnitZero_count_log_of_circle_polynomial {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {R A : ℝ} (hR : 5 / 2 < R) (hA : 1 ≤ A) (k : ℕ)
    (hbound : ∀ (t : ℝ) z, z ∈ sphere (verticalPoint 2 t) R →
      ‖entireDirichletL χ z‖ ≤ A * (2 + |t|) ^ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ((∑ z ∈ dirichletUnitZeros χ t, dirichletOrder χ z : ℤ) : ℝ) ≤ C * Real.log (2 + |t|) := by
  obtain ⟨c, hc, hcent⟩ := exists_pos_le_norm_entireDirichletL_on_two χ
  let d := Real.log (R / (5 / 2 : ℝ))
  have hd : 0 < d := Real.log_pos ((one_lt_div (by norm_num)).2 hR)
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA₀ : 0 < A := zero_lt_one.trans_le hA
  let B := |Real.log (A / c)| / Real.log 2
  have hB : 0 ≤ B := div_nonneg (abs_nonneg _) h₂.le
  refine ⟨(B + (k : ℝ)) / d, by positivity, fun t => ?_⟩
  let u := 2 + |t|
  have hu : 2 ≤ u := le_add_of_nonneg_right (abs_nonneg _)
  have hu₀ : 0 < u := (by norm_num : 0 < (2 : ℝ)).trans_le hu
  have hM : 1 ≤ A * u ^ k := by
    exact hA.trans (le_mul_of_one_le_right hA₀.le (one_le_pow₀ ((by norm_num : (1 : ℝ) ≤ 2).trans hu)))
  let L := ‖entireDirichletL χ (verticalPoint 2 t)‖
  have hLc : c ≤ L := hcent t
  have hL : 0 < L := hc.trans_le hLc
  have hJ := dirichletUnitZero_count_le_jensen χ t hR hM (hbound t)
  have hlog : Real.log (A * u ^ k / L) ≤ Real.log (A * u ^ k / c) :=
    Real.log_le_log (div_pos (mul_pos hA₀ (pow_pos hu₀ _)) hL)
      (div_le_div_of_nonneg_left (by positivity) hc hLc)
  have hbase : Real.log 2 ≤ Real.log u := Real.log_le_log (by norm_num) hu
  have hBu : Real.log (A / c) ≤ B * Real.log u := by
    calc
      _ ≤ |Real.log (A / c)| := le_abs_self _
      _ = B * Real.log 2 := by dsimp only [B]; rw [div_mul_cancel₀ _ h₂.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hbase hB
  apply hJ.trans
  change Real.log (A * u ^ k / L) / d ≤ (B + (k : ℝ)) / d * Real.log u
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hd.le
  apply hlog.trans
  rw [mul_comm A, mul_div_assoc, Real.log_mul (pow_ne_zero _ hu₀.ne') (div_ne_zero hA₀.ne' hc.ne'),
    Real.log_pow]
  linarith

/-- Cubic growth on the circles used both for Jensen counting and for the local
logarithmic derivative estimate. -/
theorem exists_polynomial_bound_entireDirichletL_on_jensen_circles {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (t : ℝ) z, z ∈ sphere (verticalPoint 2 t) (29 / 10) →
      ‖entireDirichletL χ z‖ ≤ A * (2 + |t|) ^ 3 := by
  obtain ⟨A, hA, hbound⟩ := exists_polynomial_bound_entireDirichletL χ (a := -9 / 10) (by norm_num)
  refine ⟨27 * A, by linarith, ?_⟩
  intro t z hz
  rw [mem_sphere, Complex.dist_eq] at hz
  have hre := Complex.abs_re_le_norm (z - verticalPoint 2 t)
  rw [sub_re, verticalPoint_re, hz] at hre
  have hzre : -9 / 10 ≤ z.re := by linarith [(abs_le.mp hre).1]
  have hc : ‖verticalPoint 2 t‖ ≤ 2 + |t| := by
    unfold verticalPoint
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_I, mul_one, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    norm_num
  have hnorm : ‖z‖ ≤ 29 / 10 + (2 + |t|) := by
    calc
      ‖z‖ = ‖(z - verticalPoint 2 t) + verticalPoint 2 t‖ := by rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (by rw [hz]; exact add_le_add_right hc _)
  have hu : 1 + ‖z‖ ≤ 3 * (2 + |t|) := by linarith [abs_nonneg t]
  calc
    _ ≤ A * (1 + ‖z‖) ^ 3 := hbound z hzre
    _ ≤ A * (3 * (2 + |t|)) ^ 3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hu _) (zero_le_one.trans hA)
    _ = _ := by ring

/-- The unit-height zero count of the actual Dirichlet L-function, with multiplicity. -/
theorem dirichletUnitZero_count_log {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ((∑ z ∈ dirichletUnitZeros χ t, dirichletOrder χ z : ℤ) : ℝ) ≤ C * Real.log (2 + |t|) := by
  obtain ⟨A, hA, hbound⟩ := exists_polynomial_bound_entireDirichletL_on_jensen_circles χ
  exact dirichletUnitZero_count_log_of_circle_polynomial χ (R := 29 / 10) (by norm_num) hA 3 hbound

/-- The distinct zero locations satisfy the same bound as the count with multiplicities. -/
theorem dirichletUnitZeros_card_log {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ((dirichletUnitZeros χ t).card : ℝ) ≤ C * Real.log (2 + |t|) := by
  obtain ⟨C, hC, hcount⟩ := dirichletUnitZero_count_log χ
  refine ⟨C, hC, fun t => ?_⟩
  apply le_trans _ (hcount t)
  have hcard : ((dirichletUnitZeros χ t).card : ℤ) ≤ ∑ z ∈ dirichletUnitZeros χ t, dirichletOrder χ z := by
    calc
      _ = ∑ _z ∈ dirichletUnitZeros χ t, (1 : ℤ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro z hz
        obtain ⟨hre, _, ho⟩ := (mem_dirichletUnitZeros χ).1 hz
        have hn := dirichletOrder_nonneg_of_in_criticalStrip χ hre.2
        omega
  exact_mod_cast hcard

end GoldbachR581
end

-- R581 Counting
section
open scoped BigOperators

namespace GoldbachR581

/-- The smaller primes in the unequal, unordered prime representations of `N`. -/
def smallerPrimes (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun p => p.Prime ∧ (N - p).Prime ∧ p < N - p

/-- The larger primes in the unequal, unordered prime representations of `N`. -/
def largerPrimes (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun p => p.Prime ∧ (N - p).Prime ∧ N - p < p

/-- The number of unequal, unordered prime representations of `N`. -/
def pairCount (N : ℕ) : ℕ := (smallerPrimes N).card

theorem pairCount_ne_zero_iff (N : ℕ) :
    pairCount N ≠ 0 ↔ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ p + q = N := by
  rw [pairCount, Finset.card_ne_zero]
  constructor
  · rintro ⟨p, hp⟩
    simp only [smallerPrimes, Finset.mem_filter, Finset.mem_range] at hp
    exact ⟨p, N - p, hp.2.1, hp.2.2.1, hp.2.2.2, by omega⟩
  · rintro ⟨p, q, hp, hq, hpq, hsum⟩
    refine ⟨p, ?_⟩
    have hsub : N - p = q := by omega
    simp [smallerPrimes, hsub, hp, hq, hpq, show p < N by omega]

theorem no_prime_pair_iff (N : ℕ) (heven : Even N) :
    (¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N) ↔
      pairCount N = 0 ∧ ¬ (N / 2).Prime := by
  constructor
  · intro h
    constructor
    · by_contra! hcount
      obtain ⟨p, q, hp, hq, _, hsum⟩ := (pairCount_ne_zero_iff N).mp hcount
      exact h ⟨p, q, hp, hq, hsum⟩
    · intro hp
      obtain ⟨m, hm⟩ := heven
      exact h ⟨N / 2, N / 2, hp, hp, by omega⟩
  · rintro ⟨hcount, hhalf⟩ ⟨p, q, hp, hq, hsum⟩
    rcases lt_trichotomy p q with hlt | heq | hgt
    · exact (pairCount_ne_zero_iff N).mpr ⟨p, q, hp, hq, hlt, hsum⟩ hcount
    · exact hhalf (show (N / 2).Prime by rwa [show N / 2 = p by omega])
    · exact (pairCount_ne_zero_iff N).mpr ⟨q, p, hq, hp, hgt, by omega⟩ hcount

private theorem sum_largerPrimes_eq {N : ℕ} (A : ℕ → ℂ) :
    ∑ q ∈ largerPrimes N, A q = ∑ p ∈ smallerPrimes N, A (N - p) := by
  refine Finset.sum_bij (fun q _ => N - q) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [largerPrimes, Finset.mem_filter, Finset.mem_range] at hq
    have hpos := hq.2.1.pos
    have hsub : N - (N - q) = q := by omega
    simp [smallerPrimes, hsub, hq.2.1, hq.2.2.1, hq.2.2.2,
      show N - q < N by omega]
  · intro q₁ hq₁ q₂ hq₂ h
    simp only [largerPrimes, Finset.mem_filter, Finset.mem_range] at hq₁ hq₂
    omega
  · intro p hp
    simp only [smallerPrimes, Finset.mem_filter, Finset.mem_range] at hp
    have hpos := hp.2.1.pos
    have hsub : N - (N - p) = p := by omega
    exact ⟨N - p, by simp [largerPrimes, hsub, hp.2.1, hp.2.2.1, hp.2.2.2,
      show N - p < N by omega], hsub⟩
  · intro q hq
    simp only [largerPrimes, Finset.mem_filter, Finset.mem_range] at hq
    rw [show N - (N - q) = q by omega]

theorem sum_primeOrientations {N : ℕ} (A : ℕ → ℂ)
    (hA : ∀ p < N, A p + A (N - p) = 1) :
    (∑ p ∈ smallerPrimes N, A p) + (∑ q ∈ largerPrimes N, A q) = (pairCount N : ℂ) := by
  rw [sum_largerPrimes_eq, ← Finset.sum_add_distrib, pairCount]
  calc
    _ = ∑ _ ∈ smallerPrimes N, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hA p (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
    _ = _ := by simp

private theorem prime_coprime_sum {p q N : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hsum : p + q = N) : p.Coprime N := by
  rw [hp.coprime_iff_not_dvd]
  intro hd
  have hdq : p ∣ q := by
    have h := Nat.dvd_sub hd (dvd_refl p)
    rwa [← hsum, Nat.add_sub_cancel_left] at h
  exact (hq.eq_one_or_self_of_dvd p hdq).elim hp.ne_one hne

private theorem prime_pair_units_iff {p q N : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hsum : p + q = N) : IsUnit (p : ZMod N) ∧ IsUnit (q : ZMod N) ↔ p ≠ q := by
  constructor
  · rintro ⟨hunit, _⟩ rfl
    exact (hp.coprime_iff_not_dvd.mp ((ZMod.isUnit_iff_coprime p N).mp hunit))
      (hsum ▸ dvd_add (dvd_refl p) (dvd_refl p))
  · intro hne
    exact ⟨(ZMod.isUnit_iff_coprime p N).mpr (prime_coprime_sum hp hq hne hsum),
      (ZMod.isUnit_iff_coprime q N).mpr (prime_coprime_sum hq hp hne.symm (by omega))⟩

private theorem sum_pairCharacters {N : ℕ} [NeZero N] (p q : ℕ) :
    (∑ χ : DirichletCharacter ℂ N, χ (-(p : ZMod N)) * star (χ (q : ZMod N))) =
      if N ∣ p + q ∧ IsUnit (p : ZMod N) ∧ IsUnit (q : ZMod N) then
        (N.totient : ℂ) else 0 := by
  by_cases hp : IsUnit (p : ZMod N)
  · by_cases hq : IsUnit (q : ZMod N)
    · have hcast : (q : ZMod N) = -(p : ZMod N) ↔ N ∣ p + q := by
        rw [eq_neg_iff_add_eq_zero, add_comm, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
      have hinv : Ring.inverse (q : ZMod N) = (q : ZMod N)⁻¹ := by
        rw [Ring.inverse_of_isUnit hq, ← ZMod.inv_coe_unit, hq.unit_spec]
      simp only [hp, hq, and_true, MulChar.star_apply', MulChar.inv_apply, hinv]
      calc
        _ = ∑ χ : DirichletCharacter ℂ N, χ ((q : ZMod N)⁻¹) * χ (-(p : ZMod N)) :=
          Finset.sum_congr rfl fun _ _ => mul_comm _ _
        _ = _ := by
          simpa only [hcast] using
            DirichletCharacter.sum_char_inv_mul_char_eq ℂ hq (-(p : ZMod N))
    · simp [hq, MulChar.map_nonunit]
  · have hpneg : ¬ IsUnit (-(p : ZMod N)) := fun h => hp (by simpa using h.neg)
    simp [hp, MulChar.map_nonunit _ hpneg]

private theorem eq_of_dvd_of_lt_twice {N m : ℕ} (hd : N ∣ m)
    (hpos : 0 < m) (hlt : m < 2 * N) : m = N := by
  obtain ⟨k, rfl⟩ := hd
  rcases k with _ | _ | k
  · simp at hpos
  · simp
  · have h := Nat.mul_le_mul_left N (show 2 ≤ k.succ.succ by omega)
    exact (not_lt_of_ge (by simpa [Nat.mul_comm] using h) hlt).elim

/-- The finite prime sum supported by either window in the R581 proof. -/
noncomputable def primeSum (N : ℕ) (χ : DirichletCharacter ℂ N) (A : ℕ → ℝ) : ℂ :=
  ∑ p ∈ (Finset.range (2 * N)).filter Nat.Prime, χ (p : ZMod N) * (A p : ℂ)

private theorem sum_window_indicator (N : ℕ) (A : ℕ → ℂ)
    (hA : ∀ p < N, A p + A (N - p) = 1) :
    (∑ p ∈ Finset.range (2 * N),
      if p < N ∧ p.Prime ∧ (N - p).Prime ∧ p ≠ N - p then A p else 0) =
      (pairCount N : ℂ) := by
  calc
    _ = (∑ p ∈ Finset.range (2 * N),
        ((if p ∈ smallerPrimes N then A p else 0) +
        (if p ∈ largerPrimes N then A p else 0))) := by
      apply Finset.sum_congr rfl
      intro p _
      simp only [smallerPrimes, largerPrimes, Finset.mem_filter, Finset.mem_range]
      rcases lt_trichotomy p (N - p) with hlt | heq | hgt
      · simp [hlt, hlt.ne, hlt.not_gt]
      · simp [show ¬ p ≠ N - p from fun h => h heq,
          show ¬ p < N - p by omega, show ¬ N - p < p by omega]
      · simp [hgt, hgt.ne', hgt.not_gt]
    _ = (∑ p ∈ smallerPrimes N, A p) + ∑ p ∈ largerPrimes N, A p := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
      have hsub₁ : ((Finset.range (2 * N)).filter fun p => p ∈ smallerPrimes N) =
          smallerPrimes N := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_range]
        exact and_iff_right_of_imp (fun h => by
          have := Finset.mem_range.mp (Finset.mem_filter.mp h).1
          omega)
      have hsub₂ : ((Finset.range (2 * N)).filter fun p => p ∈ largerPrimes N) =
          largerPrimes N := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_range]
        exact and_iff_right_of_imp (fun h => by
          have := Finset.mem_range.mp (Finset.mem_filter.mp h).1
          omega)
      rw [hsub₁, hsub₂]
    _ = _ := sum_primeOrientations A hA

private theorem weighted_pairCharacter_sum {N p q : ℕ} [NeZero N]
    (A B : ℕ → ℝ) (hp : p.Prime) (hq : q.Prime)
    (hA : ∀ t, 3 * N ≤ 5 * t → A t = 0)
    (hB : ∀ t, 13 * N ≤ 10 * t → B t = 0)
    (hB_one : ∀ t < N, B t = 1) :
    (∑ χ : DirichletCharacter ℂ N, χ (-(p : ZMod N)) * star (χ (q : ZMod N))) *
        ((A p : ℂ) * (B q : ℂ)) =
      (N.totient : ℂ) * if p + q = N ∧ p ≠ q then (A p : ℂ) else 0 := by
  rw [sum_pairCharacters]
  by_cases hsum : p + q = N
  · have hqN : q < N := by have := hp.pos; omega
    simp [hsum, prime_pair_units_iff hp hq hsum, hB_one q hqN, ite_mul]
  · simp only [hsum, false_and, ite_false, mul_zero]
    split_ifs with hd
    · by_cases hpbound : 3 * N ≤ 5 * p
      · simp [hA p hpbound]
      · have hqbound : 13 * N ≤ 10 * q := by
          by_contra! hqbound
          exact hsum (eq_of_dvd_of_lt_twice hd.1 (by have := hp.pos; omega) (by omega))
        simp [hB q hqbound]
    · exact zero_mul _

private theorem sum_prime_pair_indicator (N : ℕ) (A : ℕ → ℂ)
    (hA : ∀ p < N, A p + A (N - p) = 1) :
    (∑ p ∈ (Finset.range (2 * N)).filter Nat.Prime,
      ∑ q ∈ (Finset.range (2 * N)).filter Nat.Prime,
        if p + q = N ∧ p ≠ q then A p else 0) = (pairCount N : ℂ) := by
  rw [← sum_window_indicator N A hA, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.Prime
  · simp only [hp, ite_true, true_and]
    by_cases h : p < N ∧ (N - p).Prime
    · have hq_lt : N - p < 2 * N := by omega
      rw [Finset.sum_eq_single_of_mem (N - p) (by simp [hq_lt, h.2])]
      · simp [h.1, h.2, show p + (N - p) = N by omega]
      · intro q _ hq
        simp [show p + q ≠ N by omega]
    · have h' : ¬ (p < N ∧ (N - p).Prime ∧ p ≠ N - p) := fun hyes => h ⟨hyes.1, hyes.2.1⟩
      simp only [h', ite_false]
      apply Finset.sum_eq_zero
      intro q hq
      have hprime := (Finset.mem_filter.mp hq).2
      have hqpos := hprime.pos
      have hsum : p + q ≠ N := fun hsum => h ⟨by omega, (show N - p = q by omega) ▸ hprime⟩
      simp [hsum]
  · simp [hp]

/-- Equation (1) of R581, for any real weights satisfying the two window conditions. -/
theorem pairCount_eq_character_average {N : ℕ} [NeZero N] (A B : ℕ → ℝ)
    (hA : ∀ t, 3 * N ≤ 5 * t → A t = 0)
    (hB : ∀ t, 13 * N ≤ 10 * t → B t = 0)
    (hB_one : ∀ t < N, B t = 1)
    (hA_add : ∀ t < N, A t + A (N - t) = 1) :
    (pairCount N : ℂ) = (∑ χ : DirichletCharacter ℂ N,
      χ (-1) * primeSum N χ A * star (primeSum N χ B)) / (N.totient : ℂ) := by
  let primes := (Finset.range (2 * N)).filter Nat.Prime
  have hφ : (N.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos N)).ne'
  apply (eq_div_iff hφ).2
  symm
  calc
    _ = ∑ χ : DirichletCharacter ℂ N, ∑ p ∈ primes, ∑ q ∈ primes,
        (χ (-(p : ZMod N)) * star (χ (q : ZMod N))) * ((A p : ℂ) * (B q : ℂ)) := by
      apply Finset.sum_congr rfl
      intro χ _
      simp only [primeSum, star_sum, star_mul, Complex.star_def, Complex.conj_ofReal,
        Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      rw [← neg_one_mul (p : ZMod N), map_mul]
      ring
    _ = ∑ p ∈ primes, ∑ q ∈ primes,
        (N.totient : ℂ) * if p + q = N ∧ p ≠ q then (A p : ℂ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      rw [← Finset.sum_mul]
      exact weighted_pairCharacter_sum A B (Finset.mem_filter.mp hp).2
        (Finset.mem_filter.mp hq).2 hA hB hB_one
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [sum_prime_pair_indicator, mul_comm]
      intro p hp
      exact_mod_cast hA_add p hp

end GoldbachR581
end

-- R581 Windows
section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace GoldbachR581

/-- The symmetric bump used in R581, extended by zero outside `(0, 1)`. -/
noncomputable def windowBump (x : ℝ) : ℝ := expNegInvGlue x * expNegInvGlue (1 - x)

theorem windowBump_eq_exp {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    windowBump x = Real.exp (-1 / (x * (1 - x))) := by
  have hy : 0 < 1 - x := sub_pos.mpr hx.2
  rw [windowBump, expNegInvGlue, expNegInvGlue, ite_eq_right hx.1.not_ge, ite_eq_right hy.not_ge,
    ← Real.exp_add]
  congr 1
  field_simp [hx.1.ne', hy.ne']
  ring

private theorem windowBump_contDiff : ContDiff ℝ ∞ windowBump :=
  expNegInvGlue.contDiff.mul (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

private theorem windowBump_reflect (x : ℝ) : windowBump (1 - x) = windowBump x := by
  simp [windowBump, mul_comm]

private theorem windowBump_zero_left {x : ℝ} (hx : x ≤ 0) : windowBump x = 0 := by
  simp [windowBump, expNegInvGlue.zero_of_nonpos hx]

theorem windowBump_zero_right {x : ℝ} (hx : 1 ≤ x) : windowBump x = 0 := by
  rw [← windowBump_reflect]
  exact windowBump_zero_left (sub_nonpos.mpr hx)

private theorem windowBump_nonneg (x : ℝ) : 0 ≤ windowBump x :=
  mul_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _)

private theorem windowBump_mass_pos : 0 < ∫ x in (0 : ℝ)..1, windowBump x := by
  apply intervalIntegral.integral_pos zero_lt_one windowBump_contDiff.continuous.continuousOn
    (fun x _ => windowBump_nonneg x)
  refine ⟨1 / 2, by norm_num, ?_⟩
  exact mul_pos (expNegInvGlue.pos_of_pos (by norm_num)) (expNegInvGlue.pos_of_pos (by norm_num))

/-- The normalized primitive of the bump. The bump vanishes to the left of the lower limit. -/
noncomputable def windowStep (x : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..x, windowBump t) / (∫ t in (0 : ℝ)..1, windowBump t)

private theorem integral_windowBump_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y => ∫ t in (0 : ℝ)..y, windowBump t) (windowBump x) x := by
  have hc := windowBump_contDiff.continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem windowStep_contDiff : ContDiff ℝ ∞ windowStep := by
  unfold windowStep
  apply ContDiff.div_const
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (integral_windowBump_hasDerivAt x).differentiableAt, ?_⟩
  have h : deriv (fun y => ∫ t in (0 : ℝ)..y, windowBump t) = windowBump :=
    funext fun x => (integral_windowBump_hasDerivAt x).deriv
  rw [h]
  exact windowBump_contDiff

theorem windowStep_zero {x : ℝ} (hx : x ≤ 0) : windowStep x = 0 := by
  rw [windowStep, intervalIntegral.integral_symm x 0]
  have h : (∫ t in x..(0 : ℝ), windowBump t) = 0 := by
    calc
      _ = ∫ _ in x..(0 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hx]
        exact fun t ht => windowBump_zero_left ht.2
      _ = _ := intervalIntegral.integral_zero
  rw [h, neg_zero, zero_div]

theorem windowStep_reflect (x : ℝ) : windowStep x + windowStep (1 - x) = 1 := by
  have hreflect : (∫ t in (0 : ℝ)..x, windowBump t) = ∫ t in 1 - x..1, windowBump t := by
    simpa only [windowBump_reflect, sub_zero] using
      (intervalIntegral.integral_comp_sub_left (a := 0) (b := x) windowBump 1)
  have hc := windowBump_contDiff.continuous
  rw [windowStep, windowStep, hreflect, ← add_div, add_comm,
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (1 - x))
      (hc.intervalIntegrable (1 - x) 1), div_self windowBump_mass_pos.ne']

theorem windowStep_one {x : ℝ} (hx : 1 ≤ x) : windowStep x = 1 := by
  simpa [windowStep_zero (sub_nonpos.mpr hx)] using windowStep_reflect x

/-- The first prime window, with complementary weights at `u` and `1 - u`. -/
noncomputable def firstWindow (u : ℝ) : ℝ := 1 - windowStep (5 * u - 2)

/-- The second prime window, identically one below `1`. -/
noncomputable def secondWindow (u : ℝ) : ℝ := 1 - windowStep ((u - 1) / (3 / 10))

/-- The log-coordinate cutoff removes the apparent singularity at zero. -/
noncomputable def logWindow (s : ℝ) : ℝ :=
  windowStep ((s - Real.log (3 / 2)) / Real.log (4 / 3))

theorem firstWindow_contDiff : ContDiff ℝ ∞ firstWindow := by
  unfold firstWindow
  exact contDiff_const.sub (windowStep_contDiff.comp (by fun_prop))

theorem secondWindow_contDiff : ContDiff ℝ ∞ secondWindow := by
  unfold secondWindow
  exact contDiff_const.sub (windowStep_contDiff.comp (by fun_prop))

theorem logWindow_contDiff : ContDiff ℝ ∞ logWindow :=
  windowStep_contDiff.comp (by fun_prop)

theorem firstWindow_reflect (u : ℝ) : firstWindow u + firstWindow (1 - u) = 1 := by
  unfold firstWindow
  rw [show 5 * (1 - u) - 2 = 1 - (5 * u - 2) by ring]
  linarith [windowStep_reflect (5 * u - 2)]

theorem firstWindow_one {u : ℝ} (hu : u ≤ 2 / 5) : firstWindow u = 1 := by
  simp [firstWindow, windowStep_zero (show 5 * u - 2 ≤ 0 by linarith)]

theorem firstWindow_zero {u : ℝ} (hu : 3 / 5 ≤ u) : firstWindow u = 0 := by
  simp [firstWindow, windowStep_one (show 1 ≤ 5 * u - 2 by linarith)]

theorem secondWindow_one {u : ℝ} (hu : u ≤ 1) : secondWindow u = 1 := by
  have h : (u - 1) / (3 / 10) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu) (by norm_num)
  simp [secondWindow, windowStep_zero h]

theorem secondWindow_zero {u : ℝ} (hu : 13 / 10 ≤ u) : secondWindow u = 0 := by
  simp [secondWindow, windowStep_one (show 1 ≤ (u - 1) / (3 / 10) by linarith)]

theorem logWindow_zero {s : ℝ} (hs : s ≤ Real.log (3 / 2)) : logWindow s = 0 :=
  windowStep_zero (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) (Real.log_nonneg (by norm_num)))

theorem logWindow_one {s : ℝ} (hs : Real.log 2 ≤ s) : logWindow s = 1 := by
  apply windowStep_one
  rw [le_div_iff₀ (Real.log_pos (by norm_num)), one_mul]
  have hsum : Real.log (3 / 2) + Real.log (4 / 3) = Real.log 2 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  linarith

/-- The `hᵢⱼ` test function. At zero the division agrees with the prescribed zero extension. -/
noncomputable def mangoldtWeight (N j : ℕ) (A : ℝ → ℝ) (s : ℝ) : ℝ :=
  logWindow s * A (Real.exp ((j : ℝ) * s) / N) / ((j : ℝ) * s)

theorem mangoldtWeight_contDiff {N j : ℕ} {A : ℝ → ℝ} (hj : j ≠ 0) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (mangoldtWeight N j A) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : s = 0
  · subst s
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hlog : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
    filter_upwards [Iio_mem_nhds hlog] with s hs
    simp [mangoldtWeight, logWindow_zero hs.le]
  · exact (logWindow_contDiff.contDiffAt.mul (hA.contDiffAt.comp _ (by fun_prop))).div
      (by fun_prop) (mul_ne_zero (by exact_mod_cast hj) hs)

theorem mangoldtWeight_tsupport {N j : ℕ} {A : ℝ → ℝ} (hN : 0 < N) (hj : 0 < j)
    (hA : ∀ u, 13 / 10 ≤ u → A u = 0) :
    tsupport (mangoldtWeight N j A) ⊆
      Icc (Real.log (3 / 2)) (Real.log ((13 / 10 : ℝ) * N) / j) := by
  apply closure_minimal _ isClosed_Icc
  intro s hs
  have hs_ne := Function.mem_support.mp hs
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hjr : 0 < (j : ℝ) := by exact_mod_cast hj
  refine ⟨le_of_not_ge fun h => hs_ne ?_, le_of_not_ge fun h => hs_ne ?_⟩
  · simp [mangoldtWeight, logWindow_zero h]
  · have hlog : Real.log ((13 / 10 : ℝ) * N) ≤ (j : ℝ) * s := by
      rw [mul_comm (j : ℝ) s]
      exact (div_le_iff₀ hjr).mp h
    have hexp := (Real.log_le_iff_le_exp (mul_pos (by norm_num) hNr)).mp hlog
    simp [mangoldtWeight, hA _ ((le_div_iff₀ hNr).mpr hexp)]

theorem mangoldtWeight_hasCompactSupport {N j : ℕ} {A : ℝ → ℝ} (hN : 0 < N) (hj : 0 < j)
    (hA : ∀ u, 13 / 10 ≤ u → A u = 0) : HasCompactSupport (mangoldtWeight N j A) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (mangoldtWeight_tsupport hN hj hA)

theorem pairCount_eq_R581_prime_average {N : ℕ} [NeZero N] :
    (pairCount N : ℂ) = (∑ χ : DirichletCharacter ℂ N, χ (-1) *
      primeSum N χ (fun p => firstWindow ((p : ℝ) / N)) *
      star (primeSum N χ (fun p => secondWindow ((p : ℝ) / N)))) / (N.totient : ℂ) := by
  have hN : 0 < (N : ℝ) := by exact_mod_cast NeZero.pos N
  apply pairCount_eq_character_average
  · intro t ht
    apply firstWindow_zero
    rw [le_div_iff₀ hN]
    have h : (3 : ℝ) * N ≤ 5 * (t : ℝ) := by exact_mod_cast ht
    linarith
  · intro t ht
    apply secondWindow_zero
    rw [le_div_iff₀ hN]
    have h : (13 : ℝ) * N ≤ 10 * (t : ℝ) := by exact_mod_cast ht
    linarith
  · intro t ht
    exact secondWindow_one ((div_le_one hN).mpr (by exact_mod_cast ht.le))
  · intro t ht
    rw [Nat.cast_sub ht.le, sub_div, div_self hN.ne']
    exact firstWindow_reflect _

end GoldbachR581
end

-- R581 CriticalZeroSum
section
open Complex Filter MeasureTheory Set DirichletCharacter
open scoped Classical ContDiff Topology

namespace GoldbachR581

/-- The contribution of a critical-strip zero with its multiplicity, extended by zero
outside the strip. Regular points within the strip have order zero. -/
noncomputable def dirichletCriticalZeroTerm {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (W : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z.re ∈ Ioo (0 : ℝ) 1 then (dirichletOrder χ z : ℂ) * W z else 0

private theorem mem_unitZeros_at_floor_abs {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z : ℂ} (hz : z.re ∈ Ioo (0 : ℝ) 1) (hm : dirichletOrder χ z ≠ 0) :
    z ∈ dirichletUnitZeros χ (⌊|z.im|⌋₊ : ℝ) ∪
      dirichletUnitZeros χ (-(⌊|z.im|⌋₊ : ℝ)) := by
  classical
  have h₁ := Nat.floor_le (abs_nonneg z.im)
  have h₂ := Nat.lt_floor_add_one |z.im|
  rcases le_or_gt 0 z.im with hi | hi
  · rw [abs_of_nonneg hi] at h₁ h₂ ⊢
    exact Finset.mem_union_left _ ((mem_dirichletUnitZeros χ).2 ⟨hz,
      abs_le.mpr ⟨by linarith, by linarith⟩, hm⟩)
  · rw [abs_of_neg hi] at h₁ h₂ ⊢
    exact Finset.mem_union_right _ ((mem_dirichletUnitZeros χ).2 ⟨hz,
      abs_le.mpr ⟨by linarith, by linarith⟩, hm⟩)

/-- Cubic vertical decay suffices for the full critical-strip zero sum to converge
absolutely. The sum ranges over actual complex coordinates and counts multiplicity. -/
theorem summable_norm_dirichletCriticalZeroTerm {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {W : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hW : ∀ z : ℂ, z.re ∈ Ioo (0 : ℝ) 1 → ‖W z‖ ≤ A / (2 + |z.im|) ^ 3) :
    Summable (fun z : ℂ => ‖dirichletCriticalZeroTerm χ W z‖) := by
  classical
  let F := fun z : ℂ => ‖dirichletCriticalZeroTerm χ W z‖
  let m := fun z : ℂ => if z.re ∈ Ioo (0 : ℝ) 1 then (dirichletOrder χ z : ℝ) else 0
  let k := fun z : ℂ => ⌊|z.im|⌋₊
  let U := dirichletUnitZeros χ
  let B := fun n : ℕ => U (n : ℝ) ∪ U (-(n : ℝ))
  have hm₀ (z : ℂ) : 0 ≤ m z := by
    dsimp only [m]
    split_ifs with hz
    · exact_mod_cast dirichletOrder_nonneg_of_in_criticalStrip χ hz.2
    · exact le_rfl
  have hF (z : ℂ) : F z = m z * ‖W z‖ := by
    by_cases hz : z.re ∈ Ioo (0 : ℝ) 1
    · have hp : 0 ≤ (dirichletOrder χ z : ℝ) := by simpa only [m, ite_eq_left hz] using hm₀ z
      simp only [F, dirichletCriticalZeroTerm, m, ite_eq_left hz, norm_mul, norm_intCast, abs_of_nonneg hp]
    · simp only [F, dirichletCriticalZeroTerm, m, ite_eq_right hz, norm_zero, zero_mul]
  obtain ⟨C, hC, hcount⟩ := dirichletUnitZero_count_log χ
  have hU (t : ℝ) : ∑ z ∈ U t, m z ≤ C * (2 + |t|) := by
    have hEq : (∑ z ∈ U t, m z) = ((∑ z ∈ U t, dirichletOrder χ z : ℤ) : ℝ) := by
      rw [Int.cast_sum]
      apply Finset.sum_congr rfl
      intro z hz
      simp only [m, ite_eq_left ((mem_dirichletUnitZeros χ).1 hz).1]
    rw [hEq]
    exact (hcount t).trans (mul_le_mul_of_nonneg_left
      ((Real.log_le_sub_one_of_pos (by positivity : 0 < (2 : ℝ) + |t|)).trans (by linarith)) hC)
  have hB (n : ℕ) : ∑ z ∈ B n, m z ≤ 2 * C * (2 + (n : ℝ)) := by
    have hi : 0 ≤ ∑ z ∈ U (n : ℝ) ∩ U (-(n : ℝ)), m z := Finset.sum_nonneg (fun z _ => hm₀ z)
    calc
      _ ≤ (∑ z ∈ U (n : ℝ), m z) + ∑ z ∈ U (-(n : ℝ)), m z := by
        rw [← Finset.sum_union_inter]
        exact le_add_of_nonneg_right hi
      _ ≤ 2 * C * (2 + (n : ℝ)) := by
        have hp := hU (n : ℝ)
        have hn := hU (-(n : ℝ))
        rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg n)] at hn
        rw [abs_of_nonneg (Nat.cast_nonneg n)] at hp
        linarith
  have hBin {n : ℕ} {z : ℂ} (hz : F z ≠ 0) (hk : k z = n) : z ∈ B n := by
    have hstrip : z.re ∈ Ioo (0 : ℝ) 1 := by
      by_contra hn
      exact hz (by simp only [F, dirichletCriticalZeroTerm, ite_eq_right hn, norm_zero])
    have ho : dirichletOrder χ z ≠ 0 := by
      intro he
      exact hz (by simp [F, dirichletCriticalZeroTerm, he])
    exact hk ▸ mem_unitZeros_at_floor_abs χ hstrip ho
  let b := fun n : ℕ => (2 * C * A) / ((n : ℝ) + 2) ^ 2
  have hb (n : ℕ) : 0 ≤ b n := by dsimp [b]; positivity
  have hbs : Summable b := by
    have hs := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 2).2
      (Real.summable_one_div_nat_pow.mpr (by norm_num))
    simpa only [b, Nat.cast_add, Nat.cast_ofNat, mul_one_div] using hs.mul_left (2 * C * A)
  refine summable_of_sum_le (fun z => norm_nonneg _) (c := ∑' n, b n) fun s => ?_
  let S := s.filter (fun z => F z ≠ 0)
  have hS₀ : ∑ z ∈ S, F z = ∑ z ∈ s, F z :=
    Finset.sum_subset (Finset.filter_subset _ _) (by
      intro z hz hn
      by_contra he
      exact hn (Finset.mem_filter.mpr ⟨hz, he⟩))
  have hS (n : ℕ) : ∑ z ∈ S.filter (fun z => k z = n), F z ≤ b n := by
    let T := S.filter (fun z => k z = n)
    have hsub : T ⊆ B n := by
      intro z hz
      obtain ⟨hs, he⟩ := Finset.mem_filter.mp hz
      exact hBin (Finset.mem_filter.mp hs).2 he
    have hbase : 0 < (2 : ℝ) + n := by positivity
    have hfactor : 0 ≤ A / (2 + (n : ℝ)) ^ 3 := by positivity
    calc
      _ ≤ ∑ z ∈ T, m z * (A / (2 + (n : ℝ)) ^ 3) := by
        apply Finset.sum_le_sum
        intro z hz
        have hK : k z = n := (Finset.mem_filter.mp hz).2
        have hN : (n : ℝ) ≤ |z.im| := hK ▸ Nat.floor_le (abs_nonneg z.im)
        have hstrip : z.re ∈ Ioo (0 : ℝ) 1 := by
          rcases Finset.mem_union.mp (hsub hz) with he | he
          · exact ((mem_dirichletUnitZeros χ).1 he).1
          · exact ((mem_dirichletUnitZeros χ).1 he).1
        rw [hF]
        exact mul_le_mul_of_nonneg_left ((hW z hstrip).trans
          (div_le_div_of_nonneg_left hA (pow_pos hbase _) (by gcongr))) (hm₀ z)
      _ = (∑ z ∈ T, m z) * (A / (2 + (n : ℝ)) ^ 3) := by rw [Finset.sum_mul]
      _ ≤ (2 * C * (2 + (n : ℝ))) * (A / (2 + (n : ℝ)) ^ 3) :=
        mul_le_mul_of_nonneg_right ((Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun z _ _ => hm₀ z)).trans (hB n)) hfactor
      _ = b n := by
        unfold b
        rw [add_comm (n : ℝ) 2]
        field_simp [ne_of_gt hbase]
  change ∑ z ∈ s, F z ≤ _
  rw [← hS₀, ← Finset.sum_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem k hz) F]
  exact (Finset.sum_le_sum (fun n _ => hS n)).trans
    (hbs.sum_le_tsum (S.image k) (fun n _ => hb n))

/-- The actual critical zeros give an absolutely convergent Laplace sum for a smooth
weight of compact support. -/
theorem summable_norm_laplace_dirichletCriticalZero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {h : ℝ → ℝ} (hs : ContDiff ℝ ∞ h)
    {a b : ℝ} (hab : tsupport h ⊆ Icc a b) :
    Summable (fun z : ℂ => ‖dirichletCriticalZeroTerm χ (laplaceTransform h) z‖) := by
  let M := ((∫ x : ℝ, ‖h x‖) + (∫ x : ℝ, ‖iteratedDeriv 3 h x‖)) *
    Real.exp (max |a| |b|)
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg (add_nonneg (integral_nonneg (fun _ => norm_nonneg _))
      (integral_nonneg (fun _ => norm_nonneg _))) (Real.exp_nonneg _)
  refine summable_norm_dirichletCriticalZeroTerm χ (A := 27 * M) (by positivity) fun z hz => ?_
  have he (c : ℝ) : z.re * c ≤ |c| := by
    calc
      _ ≤ |z.re * c| := le_abs_self _
      _ = z.re * |c| := by rw [abs_mul, abs_of_nonneg hz.1.le]
      _ ≤ _ := mul_le_of_le_one_left (abs_nonneg _) hz.2.le
  have hh := (laplaceTransform_contour_bound hs hab 3 z).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (max_le ((he a).trans (le_max_left _ _)) ((he b).trans (le_max_right _ _))))
      (add_nonneg (integral_nonneg (fun _ => norm_nonneg _)) (integral_nonneg (fun _ => norm_nonneg _))))
  have ht : (2 + |z.im|) ^ 3 ≤ 27 * (1 + |z.im| ^ 3) := by
    rcases le_or_gt |z.im| 1 with h | h
    · have hc : (2 + |z.im|) ^ 3 ≤ (3 : ℝ) ^ 3 :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      nlinarith [pow_nonneg (abs_nonneg z.im) 3]
    · have hc : (2 + |z.im|) ^ 3 ≤ (3 * |z.im|) ^ 3 :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      nlinarith
  apply (le_div_iff₀ (by positivity)).2
  rw [mul_comm]
  calc
    _ ≤ (27 * (1 + |z.im| ^ 3)) * ‖laplaceTransform h z‖ :=
      mul_le_mul_of_nonneg_right ht (norm_nonneg _)
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hh (by norm_num)

/-- Finite critical-zero sums in expanding rectangles tend to the full zero sum.
The two heights may tend to infinity independently, without monotonicity. -/
theorem tendsto_dirichletCriticalZero_sum_rectangles {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {W : ℂ → ℂ}
    (hW : Summable (dirichletCriticalZeroTerm χ W))
    {a b : ℝ} (ha : a ≤ 0) (hb : 1 ≤ b) {ι : Type*} {l : Filter ι}
    {c d : ι → ℝ} (hc : Tendsto c l atBot) (hd : Tendsto d l atTop) :
    Tendsto (fun i => ∑ z ∈ dirichletRectangleSingularities χ a b (c i) (d i),
      dirichletCriticalZeroTerm χ W z) l (𝓝 (∑' z, dirichletCriticalZeroTerm χ W z)) := by
  classical
  let F := dirichletCriticalZeroTerm χ W
  let R := fun i => dirichletRectangleSingularities χ a b (c i) (d i)
  let S := fun i => (R i).subtype (· ∈ Function.support F)
  have hS : Tendsto S l atTop := by
    simp only [atTop_finset_eq_iInf, tendsto_iInf, tendsto_principal]
    intro z
    have hz : F z.val ≠ 0 := z.property
    have hre : z.val.re ∈ Ioo (0 : ℝ) 1 := by
      by_contra hn
      exact hz (by simp only [F, dirichletCriticalZeroTerm, ite_eq_right hn])
    have ho : dirichletOrder χ z.val ≠ 0 := by
      intro he
      exact hz (by simp [F, dirichletCriticalZeroTerm, he])
    filter_upwards [hc.eventually_le_atBot z.val.im, hd.eventually_ge_atTop z.val.im] with i hl hu
    refine Finset.singleton_subset_iff.2 (Finset.mem_subtype.2 ((mem_dirichletRectangleSingularities χ).2 ?_))
    exact ⟨mem_reProdIm.mpr ⟨⟨ha.trans hre.1.le, hre.2.le.trans hb⟩, ⟨hl, hu⟩⟩, ho⟩
  have hlim : HasSum (fun z : Function.support F => F z.val) (∑' z, F z) :=
    hasSum_subtype_support.2 hW.hasSum
  refine (hlim.comp hS).congr (fun i => ?_)
  change (∑ z ∈ S i, F z.val) = ∑ z ∈ R i, F z
  rw [Finset.sum_subtype_eq_sum_filter]
  exact Finset.sum_subset (Finset.filter_subset _ _) fun z _ hz => by
    by_contra hf
    exact hz (Finset.mem_filter.mpr ⟨by assumption, hf⟩)

/-- Absolute convergence for the primitive critical-zero sum in each R581 window. -/
theorem summable_norm_windowedMangoldt_primitive_criticalZero {N j : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hj : 0 < j) {A : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ A) (hc : ∀ u, 13 / 10 ≤ u → A u = 0) :
    let _ : NeZero (χ ^ j).conductor := ⟨(χ ^ j).conductor_ne_zero⟩
    Summable (fun z : ℂ => ‖dirichletCriticalZeroTerm (χ ^ j).primitiveCharacter
      (laplaceTransform (mangoldtWeight N j A)) z‖) := by
  have : NeZero (χ ^ j).conductor := ⟨(χ ^ j).conductor_ne_zero⟩
  exact summable_norm_laplace_dirichletCriticalZero (χ ^ j).primitiveCharacter
    (mangoldtWeight_contDiff hj.ne' hs) (mangoldtWeight_tsupport (NeZero.pos N) hj hc)

end GoldbachR581
end

-- R581 ContourResidueSum
section
open Complex DirichletCharacter Filter Set
open scoped Classical Topology

namespace GoldbachR581

private theorem dirichletTrivialZero_im {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) :
    (dirichletTrivialZero χ n).im = 0 := by
  unfold dirichletTrivialZero
  split_ifs <;> simp [Complex.mul_im]

private theorem dirichletOrder_at_trivialZero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (n : ℕ) :
    dirichletOrder χ (dirichletTrivialZero χ n) = 1 := by
  rw [dirichletOrder_eq_trivialZero_indicator hχ (dirichletTrivialZero_re_nonpos χ n),
    ite_eq_left (show ∃ m, dirichletTrivialZero χ n = dirichletTrivialZero χ m from ⟨n, rfl⟩)]

/-- Indices of the trivial zeros at or to the right of the left endpoint. -/
noncomputable def dirichletTrivialIndices {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (a : ℝ) : Finset ℕ :=
  (dirichletRectangleSingularities χ a 2 (-1) 1).preimage
    (dirichletTrivialZero χ) (dirichletTrivialZero_injective χ).injOn

theorem mem_dirichletTrivialIndices {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) {a : ℝ} {n : ℕ} :
    n ∈ dirichletTrivialIndices χ a ↔ a ≤ (dirichletTrivialZero χ n).re := by
  rw [dirichletTrivialIndices, Finset.mem_preimage, mem_dirichletRectangleSingularities, mem_reProdIm,
    dirichletTrivialZero_im, dirichletOrder_at_trivialZero hχ]
  exact ⟨fun h => h.1.1.1, fun h =>
    ⟨⟨⟨h, (dirichletTrivialZero_re_nonpos χ n).trans (by norm_num)⟩, by norm_num⟩, by norm_num⟩⟩

/-- The residue sum splits exactly into the conductor-one pole, the left-truncated trivial
zeros, and the critical zeros in the given rectangle. -/
theorem dirichletRectangle_residueSum_eq {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (W : ℂ → ℂ) {a c d : ℝ} (ha : a ≤ 0) (hc : c ≤ 0) (hd : 0 ≤ d) :
    (∑ z ∈ dirichletRectangleSingularities χ a 2 c d, (-(dirichletOrder χ z : ℂ) * W z)) =
      (if N = 1 then W 1 else 0) -
      (∑ n ∈ dirichletTrivialIndices χ a, W (dirichletTrivialZero χ n)) -
      ∑ z ∈ dirichletRectangleSingularities χ a 2 c d, dirichletCriticalZeroTerm χ W z := by
  let R := dirichletRectangleSingularities χ a 2 c d
  let S := dirichletTrivialIndices χ a
  let V := dirichletTrivialZero χ
  have hP : ∑ z ∈ R, (if N = 1 ∧ z = 1 then W z else 0) = if N = 1 then W 1 else 0 := by
    by_cases hN : N = 1
    · have hχ₁ : χ = 1 := level_one' χ hN
      have ho : dirichletOrder χ 1 ≠ 0 := by
        rw [hχ₁, dirichletOrder_trivial_one]
        norm_num
      have h1 : (1 : ℂ) ∈ R := (mem_dirichletRectangleSingularities χ).2
        ⟨mem_reProdIm.mpr ⟨⟨ha.trans zero_le_one, by norm_num⟩, ⟨hc, hd⟩⟩, ho⟩
      simp only [hN, true_and, ite_true]
      rw [Finset.sum_eq_single (1 : ℂ) (fun z _ hz => by simp [hz]) (fun hn => (hn h1).elim)]
      simp
    · simp [hN]
  have hV : ∑ z ∈ R, (if ∃ n, z = V n then W z else 0) = ∑ n ∈ S, W (V n) := by
    have hImage : S.image V = R.filter (fun z => ∃ n, z = V n) := by
      ext z
      rw [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨n, hn, rfl⟩
        have hr := (mem_dirichletTrivialIndices hχ).1 hn
        refine ⟨(mem_dirichletRectangleSingularities χ).2 ⟨?_, ?_⟩, ⟨n, rfl⟩⟩
        · apply mem_reProdIm.mpr
          refine ⟨⟨hr, (dirichletTrivialZero_re_nonpos χ n).trans (by norm_num)⟩, ?_⟩
          simpa only [V, dirichletTrivialZero_im] using (show (0 : ℝ) ∈ Icc c d from ⟨hc, hd⟩)
        · change dirichletOrder χ (dirichletTrivialZero χ n) ≠ 0
          rw [dirichletOrder_at_trivialZero hχ]
          norm_num
      · rintro ⟨hz, n, rfl⟩
        have hr := (mem_reProdIm.mp ((mem_dirichletRectangleSingularities χ).1 hz).1).1.1
        exact ⟨n, (mem_dirichletTrivialIndices hχ).2 hr, rfl⟩
    rw [← Finset.sum_filter, ← hImage, Finset.sum_image (dirichletTrivialZero_injective χ).injOn]
  change (∑ z ∈ R, (-(dirichletOrder χ z : ℂ) * W z)) = _
  calc
    _ = ∑ z ∈ R, ((if N = 1 ∧ z = 1 then W z else 0) -
        (if ∃ n, z = V n then W z else 0) - dirichletCriticalZeroTerm χ W z) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [dirichletOrder_eq_pole_add_trivial_add_critical hχ z]
      simp only [dirichletCriticalZeroTerm, Set.mem_Ioo, V]
      split_ifs <;> push_cast <;> ring
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hP, hV]

/-- The trivial-zero truncations exhaust every zero as the left half-integer lines recede. -/
theorem tendsto_dirichletTrivialIndices_atTop {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) :
    Tendsto (fun m : ℕ => dirichletTrivialIndices χ (-((m : ℝ) + 1 / 2))) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone
  · intro m n hmn j
    simp only [mem_dirichletTrivialIndices hχ]
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    intro hj
    linarith
  · intro j
    obtain ⟨m, hm⟩ := exists_nat_ge (-(dirichletTrivialZero χ j).re)
    exact ⟨m, (mem_dirichletTrivialIndices hχ).2 (by linarith)⟩

end GoldbachR581
end

-- R581 ContourHeights
section
public section

open Set MeasureTheory Complex

namespace GoldbachR581

private theorem exists_height_avoiding_intervals {ι : Type*} (s : Finset ι) (height : ι → ℝ)
    {a b r : ℝ} (hr : 0 ≤ r) (hlen : 2 * r * (s.card : ℝ) < b - a) :
    ∃ t ∈ Icc a b, ∀ i ∈ s, r ≤ |t - height i| := by
  classical
  by_contra! hn
  let U (i : ι) := Ioo (height i - r) (height i + r)
  have hsub : Icc a b ⊆ ⋃ i ∈ s, U i := by
    intro t ht
    obtain ⟨j, hj, hclose⟩ := hn t ht
    have hc := abs_lt.mp hclose
    exact mem_iUnion₂.mpr ⟨j, hj, by exact ⟨by linarith [hc.1], by linarith [hc.2]⟩⟩
  have hsum : ∑ i ∈ s, volume (U i) = ENNReal.ofReal (2 * r * (s.card : ℝ)) := by
    simp only [U, Real.volume_Ioo, show ∀ x : ℝ, x + r - (x - r) = 2 * r by intro; ring,
      Finset.sum_const, nsmul_eq_mul]
    rw [mul_comm (2 * r), ENNReal.ofReal_mul (Nat.cast_nonneg s.card), ENNReal.ofReal_natCast]
  have hvol := (measure_mono hsub).trans (measure_biUnion_finset_le (μ := volume) s U)
  rw [Real.volume_Icc, hsum] at hvol
  have hlen₀ : 0 < b - a := lt_of_le_of_lt (by positivity : 0 ≤ 2 * r * (s.card : ℝ)) hlen
  exact (not_lt_of_ge hvol) ((ENNReal.ofReal_lt_ofReal_iff hlen₀).mpr hlen)

/-- Avoid all singularities in a fixed horizontal strip at a height in `[k,k+1]`.
Only the singularities in `[k-1,k+2]` enter the bound on the forbidden length. -/
theorem exists_dirichlet_height_separated_of_card_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (a b k : ℝ) {r : ℝ} (hr : 0 ≤ r) (hr₁ : r ≤ 1)
    (hlen : 2 * r * ((dirichletRectangleSingularities χ a b (k - 1) (k + 2)).card : ℝ) < 1) :
    ∃ t ∈ Icc k (k + 1), ∀ z : ℂ, z.re ∈ Icc a b → dirichletOrder χ z ≠ 0 → r ≤ |t - z.im| := by
  let S := dirichletRectangleSingularities χ a b (k - 1) (k + 2)
  obtain ⟨t, ht, hsep⟩ := exists_height_avoiding_intervals S Complex.im hr
    (b := k + 1) (a := k) (by simpa [S] using hlen)
  refine ⟨t, ht, fun z hz ho => ?_⟩
  by_cases h : z.im ∈ Icc (k - 1) (k + 2)
  · exact hsep z ((mem_dirichletRectangleSingularities χ).mpr ⟨mem_reProdIm.mpr ⟨hz, h⟩, ho⟩)
  · have h' : z.im < k - 1 ∨ k + 2 < z.im := by
      by_contra! hn
      exact h ⟨hn.1, hn.2⟩
    apply hr₁.trans
    rcases h' with hlow | hhigh
    · exact (le_abs_self _).trans' (by linarith [ht.1])
    · exact (neg_le_abs _).trans' (by linarith [ht.2])

/-- An admissible horizontal edge exists in every unit height interval. The separation is
explicit in the number of singularities in the surrounding rectangle. -/
theorem exists_dirichlet_height_separated {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (a b k : ℝ) :
    ∃ t ∈ Icc k (k + 1), ∀ z : ℂ, z.re ∈ Icc a b → dirichletOrder χ z ≠ 0 →
      1 / (2 * (((dirichletRectangleSingularities χ a b (k - 1) (k + 2)).card : ℝ) + 1)) ≤ |t - z.im| := by
  let C : ℝ := (dirichletRectangleSingularities χ a b (k - 1) (k + 2)).card
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hden : 0 < 2 * (C + 1) := by positivity
  apply exists_dirichlet_height_separated_of_card_bound χ a b k
  · positivity
  · exact (div_le_one hden).mpr (by linarith)
  · change 2 * (1 / (2 * (C + 1))) * C < 1
    have hCp : 0 < C + 1 := by positivity
    rw [show 2 * (1 / (2 * (C + 1))) * C = C / (C + 1) by field_simp]
    exact (div_lt_one (by positivity : 0 < C + 1)).mpr (by linarith)

/-- At heights away from the real axis, the count in the enlarged selection rectangle
is logarithmic, uniformly in both of its real edges. -/
theorem dirichletRectangleSingularities_card_log {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b k : ℝ, (k < -2 ∨ 1 < k) →
      ((dirichletRectangleSingularities χ a b (k - 1) (k + 2)).card : ℝ) ≤
        C * Real.log (2 + |k|) := by
  classical
  obtain ⟨C, hC, hcount⟩ := dirichletUnitZeros_card_log χ
  refine ⟨3 * C, by positivity, fun a b k hk => ?_⟩
  let U := dirichletUnitZeros χ k
  let V := dirichletUnitZeros χ (k + 1)
  have hsub : dirichletRectangleSingularities χ a b (k - 1) (k + 2) ⊆ U ∪ V := by
    intro z hz
    obtain ⟨hzR, ho⟩ := (mem_dirichletRectangleSingularities χ).1 hz
    have him := (mem_reProdIm.mp hzR).2
    have h₀ : z.im ≠ 0 := by
      intro h
      rcases hk with hlow | hhigh <;> linarith [him.1, him.2]
    have hstrip := dirichletOrder_ne_zero_imp_mem_critical_of_im_ne_zero hχ h₀ ho
    rcases le_or_gt z.im (k + 1) with hl | hu
    · exact Finset.mem_union_left _ ((mem_dirichletUnitZeros χ).2
        ⟨hstrip, abs_le.mpr ⟨by linarith [him.1], by linarith⟩, ho⟩)
    · exact Finset.mem_union_right _ ((mem_dirichletUnitZeros χ).2
        ⟨hstrip, abs_le.mpr ⟨by linarith, by linarith [him.2]⟩, ho⟩)
  have hlog : Real.log (2 + |k + 1|) ≤ 2 * Real.log (2 + |k|) := by
    have habs := abs_add_le k (1 : ℝ)
    rw [abs_one] at habs
    have harg : 2 + |k + 1| ≤ 2 * (2 + |k|) := by linarith [abs_nonneg k]
    have h := Real.log_le_log (by positivity) harg
    rw [Real.log_mul (by norm_num) (by positivity)] at h
    have h₂ := Real.log_le_log (by norm_num : 0 < (2 : ℝ))
      (le_add_of_nonneg_right (abs_nonneg k))
    linarith
  have hcast : ((dirichletRectangleSingularities χ a b (k - 1) (k + 2)).card : ℝ) ≤
      (U.card : ℝ) + (V.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le U V)
  exact hcast.trans ((add_le_add (hcount k) ((hcount (k + 1)).trans
    (mul_le_mul_of_nonneg_left hlog hC))).trans_eq (by ring))

/-- A good height in each sufficiently high positive or negative unit interval, with
explicit inverse logarithmic separation from every singularity in the strip. -/
theorem exists_dirichlet_height_inverse_log_separated {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a b k : ℝ, 2 < |k| → ∃ t ∈ Icc k (k + 1),
      ∀ z : ℂ, z.re ∈ Icc a b → dirichletOrder χ z ≠ 0 →
        ε / Real.log (2 + |k|) ≤ |t - z.im| := by
  obtain ⟨C, hC, hcount⟩ := dirichletRectangleSingularities_card_log hχ
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let D := C + 1 / Real.log 2
  have hD : 0 < D := add_pos_of_nonneg_of_pos hC (by positivity)
  refine ⟨1 / (2 * D), by positivity, fun a b k hk => ?_⟩
  let L := Real.log (2 + |k|)
  have hL₂ : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (le_add_of_nonneg_right (abs_nonneg _))
  have hL : 0 < L := h₂.trans_le hL₂
  let Q : ℝ := (dirichletRectangleSingularities χ a b (k - 1) (k + 2)).card
  have hk' : k < -2 ∨ 1 < k := by
    rcases le_or_gt 0 k with h | h
    · right
      rw [abs_of_nonneg h] at hk
      linarith
    · left
      rw [abs_of_neg h] at hk
      linarith
  have hQ : Q ≤ C * L := hcount a b k hk'
  have hdL : Q + 1 ≤ D * L := by
    have h1 : 1 ≤ L / Real.log 2 := (one_le_div h₂).2 hL₂
    dsimp only [D]
    rw [add_mul, one_div_mul_eq_div]
    exact add_le_add hQ h1
  obtain ⟨t, ht, hsep⟩ := exists_dirichlet_height_separated χ a b k
  refine ⟨t, ht, fun z hz ho => le_trans ?_ (hsep z hz ho)⟩
  change 1 / (2 * D) / L ≤ 1 / (2 * (Q + 1))
  rw [div_div]
  exact one_div_le_one_div_of_le (by dsimp [Q]; positivity) (by linarith)

/-- The contours for the finite residue formula can be chosen with any negative half-integer
left edge and with lower and upper heights in any two separated unit intervals. -/
theorem exists_admissible_dirichlet_rectangle {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (m : ℕ) {k₁ k₂ : ℝ} (hk : k₁ + 1 < k₂) :
    let a : ℝ := -((m : ℝ) + 1 / 2)
    ∃ c ∈ Icc k₁ (k₁ + 1), ∃ d ∈ Icc k₂ (k₂ + 1), c < d ∧
      ∀ z ∈ Icc a 2 ×ℂ Icc c d, dirichletOrder χ z ≠ 0 → z ∈ Ioo a 2 ×ℂ Ioo c d := by
  dsimp only
  let a : ℝ := -((m : ℝ) + 1 / 2)
  obtain ⟨c, hc, hcsep⟩ := exists_dirichlet_height_separated χ a 2 k₁
  obtain ⟨d, hd, hdsep⟩ := exists_dirichlet_height_separated χ a 2 k₂
  refine ⟨c, hc, d, hd, hc.2.trans_lt (hk.trans_le hd.1), fun z hz ho => ?_⟩
  obtain ⟨hx, hy⟩ := mem_reProdIm.mp hz
  have hza : z.re ≠ a := fun h => ho (dirichletOrder_eq_zero_on_left_halfInteger hχ m h)
  have hz₂ : z.re ≠ 2 := by
    intro he
    apply ho (dirichletOrder_eq_zero_of_one_le_re χ (by rw [he]; norm_num) (Or.inl ?_))
    intro hze
    norm_num [hze] at he
  have hzc : z.im ≠ c := by
    intro he
    have h := hcsep z hx ho
    rw [he, sub_self, abs_zero] at h
    exact (not_le_of_gt (by positivity)) h
  have hzd : z.im ≠ d := by
    intro he
    have h := hdsep z hx ho
    rw [he, sub_self, abs_zero] at h
    exact (not_le_of_gt (by positivity)) h
  exact mem_reProdIm.mpr ⟨⟨lt_of_le_of_ne hx.1 hza.symm, lt_of_le_of_ne hx.2 hz₂⟩,
    ⟨lt_of_le_of_ne hy.1 hzc.symm, lt_of_le_of_ne hy.2 hzd⟩⟩

end GoldbachR581
end

-- R581 DigammaBounds
section
public section

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

namespace GoldbachR581

private noncomputable def gammaEulerKernel (n : ℕ) (x : ℝ) : ℝ :=
  (Ioc (0 : ℝ) (n : ℝ)).indicator (fun t => (1 - t / n) ^ n) x

private theorem gammaEulerKernel_measurable (n : ℕ) : Measurable (gammaEulerKernel n) := by
  unfold gammaEulerKernel
  exact (by fun_prop : Measurable (fun t : ℝ => (1 - t / n) ^ n)).indicator measurableSet_Ioc

private theorem gammaEulerKernel_nonneg_le (n : ℕ) {x : ℝ} (hx : 0 < x) :
    0 ≤ gammaEulerKernel n x ∧ gammaEulerKernel n x ≤ Real.exp (-x) := by
  by_cases hxn : x ≤ (n : ℝ)
  · rw [gammaEulerKernel, indicator_of_mem (mem_Ioc.mpr ⟨hx, hxn⟩)]
    exact ⟨pow_nonneg (sub_nonneg.mpr (div_le_one_of_le₀ hxn (by positivity))) _,
      Real.one_sub_div_pow_le_exp_neg hxn⟩
  · rw [gammaEulerKernel, indicator_of_notMem (notMem_Ioc_of_gt (lt_of_not_ge hxn))]
    exact ⟨le_rfl, (Real.exp_pos _).le⟩

private theorem tendsto_gammaEulerKernel {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n => gammaEulerKernel n x) atTop (𝓝 (Real.exp (-x))) := by
  apply (Real.tendsto_one_add_div_pow_exp (-x)).congr'
  filter_upwards [eventually_ge_atTop ⌈x⌉₊] with n hn
  rw [Nat.ceil_le] at hn
  rw [gammaEulerKernel, indicator_of_mem (mem_Ioc.mpr ⟨hx, hn⟩), neg_div, sub_eq_add_neg]

private theorem integrable_gammaEuler_integrand {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    IntegrableOn (fun x : ℝ => (gammaEulerKernel n x : ℂ) * (x : ℂ) ^ (z - 1)) (Ioi 0) := by
  have hcont : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (z - 1)) (Ioi 0) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    exact (continuousAt_cpow_const (ofReal_mem_slitPlane.mpr hx)).comp continuous_ofReal.continuousAt
  refine (Real.GammaIntegral_convergent hz).mono' ?_ ?_
  · exact (continuous_ofReal.measurable.comp (gammaEulerKernel_measurable n)).aestronglyMeasurable.mul
      (hcont.aestronglyMeasurable measurableSet_Ioi)
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    have hk := gammaEulerKernel_nonneg_le n hx
    rw [norm_mul, Complex.norm_of_nonneg hk.1, norm_cpow_eq_rpow_re_of_pos hx, sub_re, one_re]
    exact mul_le_mul_of_nonneg_right hk.2 (Real.rpow_nonneg hx.le _)

private theorem gammaSeq_eq_kernelIntegral {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : n ≠ 0) :
    GammaSeq z n = ∫ x in Ioi (0 : ℝ), (gammaEulerKernel n x : ℂ) * (x : ℂ) ^ (z - 1) := by
  rw [GammaSeq_eq_approx_Gamma_integral hz hn, intervalIntegral.integral_of_le (Nat.cast_nonneg _)]
  have he : (fun x : ℝ => (gammaEulerKernel n x : ℂ) * (x : ℂ) ^ (z - 1)) =
      (Ioc (0 : ℝ) (n : ℝ)).indicator (fun x => (((1 - x / n) ^ n : ℝ) : ℂ) * (x : ℂ) ^ (z - 1)) := by
    funext x
    by_cases hx : x ∈ Ioc (0 : ℝ) (n : ℝ) <;> simp [gammaEulerKernel, hx]
  rw [he, integral_indicator measurableSet_Ioc, Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]

/-- Uniform convergence of Euler's Gamma approximants on every strip with positive lower
real part and bounded upper real part. The proof dominates the kernel error before integrating. -/
theorem tendstoUniformlyOn_gammaSeq_re_band {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    TendstoUniformlyOn (fun n z => GammaSeq z n) Gamma atTop {z | a ≤ z.re ∧ z.re ≤ b} := by
  let W (x : ℝ) := x ^ (a - 1) + x ^ (b - 1)
  let D (n : ℕ) (x : ℝ) := |Real.exp (-x) - gammaEulerKernel n x| * W x
  let B (x : ℝ) := Real.exp (-x) * W x
  let ν := volume.restrict (Ioi (0 : ℝ))
  have hB : Integrable B ν := by
    have he : B = (fun x : ℝ => Real.exp (-x) * x ^ (a - 1)) +
        (fun x : ℝ => Real.exp (-x) * x ^ (b - 1)) := by
      funext x
      simp only [B, W, Pi.add_apply, mul_add]
    rw [he]
    exact (Real.GammaIntegral_convergent ha).add (Real.GammaIntegral_convergent hb)
  have hW : Measurable W := by unfold W; fun_prop
  have hDm (n : ℕ) : AEStronglyMeasurable (D n) ν := by
    have hE : Measurable (fun x : ℝ => Real.exp (-x) - gammaEulerKernel n x) :=
      (by fun_prop : Measurable (fun x : ℝ => Real.exp (-x))).sub (gammaEulerKernel_measurable n)
    exact ((continuous_abs.measurable.comp hE).mul hW).aestronglyMeasurable
  have hDb (n : ℕ) : ∀ᵐ x ∂ν, ‖D n x‖ ≤ B x := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    have hk := gammaEulerKernel_nonneg_le n hx
    have hW₀ : 0 ≤ W x := add_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hx.le _)
    dsimp only [D]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hW₀),
      abs_of_nonneg (sub_nonneg.mpr hk.2)]
    exact mul_le_mul_of_nonneg_right (sub_le_self _ hk.1) hW₀
  have hD (n : ℕ) : Integrable (D n) ν := hB.mono' (hDm n) (hDb n)
  have hlim : Tendsto (fun n => ∫ x, D n x ∂ν) atTop (𝓝 (0 : ℝ)) := by
    have ht : ∀ᵐ x ∂ν, Tendsto (fun n => D n x) atTop (𝓝 ((0 : ℝ → ℝ) x)) := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with x hx
      have hc : Tendsto (fun _ : ℕ => Real.exp (-x)) atTop (𝓝 (Real.exp (-x))) := tendsto_const_nhds
      simpa only [D, Pi.zero_apply, sub_self, abs_zero, zero_mul] using
        ((hc.sub (tendsto_gammaEulerKernel hx)).abs).mul_const (W x)
    simpa only [Pi.zero_apply, integral_zero] using
      tendsto_integral_of_dominated_convergence B hDm hB hDb ht
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp hlim).2 _ hε, eventually_ne_atTop 0] with n hlt hn z hz
  obtain ⟨haz, hzb⟩ := hz
  have hz₀ : 0 < z.re := ha.trans_le haz
  rw [dist_eq_norm, Gamma_eq_integral hz₀, GammaIntegral, gammaSeq_eq_kernelIntegral hz₀ hn,
    ← integral_sub (GammaIntegral_convergent hz₀) (integrable_gammaEuler_integrand hz₀ n)]
  apply lt_of_le_of_lt (norm_integral_le_of_norm_le (hD n) ?_) hlt
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with x hx
  have hpow : x ^ (z.re - 1) ≤ W x := by
    rcases le_total x 1 with hx₁ | hx₁
    · exact (Real.rpow_le_rpow_of_exponent_ge hx hx₁ (by linarith)).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg hx.le _))
    · exact (Real.rpow_le_rpow_of_exponent_le hx₁ (by linarith)).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg hx.le _))
  simp only [← sub_mul, ← ofReal_sub, norm_mul, norm_real, Real.norm_eq_abs,
    norm_cpow_eq_rpow_re_of_pos hx, sub_re, one_re, D]
  exact mul_le_mul_of_nonneg_left hpow (abs_nonneg _)

theorem tendstoLocallyUniformlyOn_gammaSeq_right :
    TendstoLocallyUniformlyOn (fun n z => GammaSeq z n) Gamma atTop {z | 0 < z.re} := by
  apply Metric.tendstoLocallyUniformlyOn_iff.mpr
  intro ε hε z hz
  have hz₀ : 0 < z.re := hz
  let t : Set ℂ := {w | z.re / 2 ≤ w.re ∧ w.re ≤ z.re + 1}
  have ht₁ : ∀ᶠ w in 𝓝 z, z.re / 2 < w.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by dsimp; linarith)
  have ht₂ : ∀ᶠ w in 𝓝 z, w.re < z.re + 1 :=
    (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by dsimp; linarith)
  have ht : t ∈ 𝓝 z := by
    filter_upwards [ht₁, ht₂] with w h₁ h₂
    exact ⟨h₁.le, h₂.le⟩
  exact ⟨t, nhdsWithin_le_nhds ht,
    Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_gammaSeq_re_band
      (by positivity : 0 < z.re / 2) (by positivity : 0 < z.re + 1)) ε hε⟩

private theorem gammaEulerDenom_term_ne_zero {z : ℂ} (hz : 0 < z.re) (j : ℕ) :
    z + (j : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [add_re, natCast_re, zero_re] at hre
  linarith [Nat.cast_nonneg (α := ℝ) j]

private theorem differentiableAt_gammaSeq {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : n ≠ 0) :
    DifferentiableAt ℂ (fun w => GammaSeq w n) z := by
  unfold GammaSeq
  have hn₀ : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  refine ((differentiableAt_id.const_cpow (.inl hn₀)).mul_const _).div ?_ ?_
  · exact .fun_finsetProd fun j _ => differentiableAt_id.add_const (j : ℂ)
  · exact Finset.prod_ne_zero_iff.mpr fun j _ => gammaEulerDenom_term_ne_zero hz j

/-- Euler's product approximants give the logarithmic derivative of Gamma as an explicit
limit of finite reciprocal sums on the right half-plane. -/
theorem tendsto_euler_digamma {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => Complex.log (n : ℂ) -
      ∑ j ∈ Finset.range (n + 1), (z + (j : ℂ))⁻¹) atTop (𝓝 (digamma z)) := by
  have hd : ∀ᶠ n : ℕ in atTop, DifferentiableOn ℂ (fun w => GammaSeq w n) {w | 0 < w.re} := by
    filter_upwards [eventually_ne_atTop 0] with n hn w hw
    exact (differentiableAt_gammaSeq hw hn).differentiableWithinAt
  have ht := Complex.logDeriv_tendsto (isOpen_lt continuous_const Complex.continuous_re) hz
    tendstoLocallyUniformlyOn_gammaSeq_right hd (Gamma_ne_zero_of_re_pos hz)
  apply ht.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  let p (w : ℂ) := (n : ℂ) ^ w
  let q (w : ℂ) := ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ))
  have hn₀ : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hpn : p z ≠ 0 := cpow_ne_zero_iff.mpr (.inl hn₀)
  have hpd : HasDerivAt p (p z * Complex.log (n : ℂ)) z := by
    simpa only [p, id_eq, mul_one] using (hasDerivAt_id z).const_cpow (.inl hn₀)
  have hqn : q z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => gammaEulerDenom_term_ne_zero hz j
  have hqd : DifferentiableAt ℂ q z := .fun_finsetProd fun j _ => differentiableAt_id.add_const (j : ℂ)
  have hpl : logDeriv p z = Complex.log (n : ℂ) := by
    rw [logDeriv_apply, hpd.deriv, mul_div_cancel_left₀ _ hpn]
  have hql : logDeriv q z = ∑ j ∈ Finset.range (n + 1), (z + (j : ℂ))⁻¹ := by
    unfold q
    rw [logDeriv_fun_prod (f := fun (j : ℕ) (w : ℂ) => w + (j : ℂ))
      (fun j _ => gammaEulerDenom_term_ne_zero hz j)
      (fun j _ => differentiableAt_id.add_const (j : ℂ))]
    apply Finset.sum_congr rfl
    intro j _
    simp [logDeriv_apply, one_div]
  change logDeriv (fun w => (p w * (n.factorial : ℂ)) / q w) z = _
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [logDeriv_fun_div (f := fun w => p w * (n.factorial : ℂ)) (g := q) z
    (mul_ne_zero hpn hf) hqn (hpd.differentiableAt.mul_const _) hqd,
    logDeriv_mul_const z _ hf, hpl, hql]

private theorem norm_euler_digamma_diff_term_le {z : ℂ} (hz : 1 / 2 ≤ z.re) (j : ℕ) :
    ‖(1 + (j : ℂ))⁻¹ - (z + (j : ℂ))⁻¹‖ ≤
      2 * ‖z - 1‖ * (((j : ℝ) + 1) ^ 2)⁻¹ := by
  have hj₀ : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  have h₁ : (1 : ℂ) + (j : ℂ) ≠ 0 := gammaEulerDenom_term_ne_zero (by norm_num) j
  have hz₀ : z + (j : ℂ) ≠ 0 := gammaEulerDenom_term_ne_zero (by linarith) j
  have he : (1 + (j : ℂ))⁻¹ - (z + (j : ℂ))⁻¹ =
      (z - 1) / ((1 + (j : ℂ)) * (z + (j : ℂ))) := by
    field_simp
    ring
  have h₁n : ‖(1 : ℂ) + (j : ℂ)‖ = (j : ℝ) + 1 := by
    rw [← ofReal_natCast, ← ofReal_one, ← ofReal_add, norm_real, Real.norm_of_nonneg (by positivity), add_comm]
  have hzn : ((j : ℝ) + 1) / 2 ≤ ‖z + (j : ℂ)‖ := by
    have h := Complex.re_le_norm (z + (j : ℂ))
    simp only [add_re, natCast_re] at h
    linarith
  have hden : ((j : ℝ) + 1) ^ 2 / 2 ≤ ((j : ℝ) + 1) * ‖z + (j : ℂ)‖ := by
    calc
      _ = ((j : ℝ) + 1) * (((j : ℝ) + 1) / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hzn (by positivity)
  rw [he, norm_div, norm_mul, h₁n]
  refine (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hden).trans_eq ?_
  rw [div_div_eq_mul_div, div_eq_mul_inv, mul_comm ‖z - 1‖]

/-- A linear growth bound for digamma on `Re z ≥ 1/2`, proved by subtracting the Euler
approximants at `1` and using the summable inverse-square bound on the differences. -/
theorem norm_digamma_le_linear_of_half_le_re :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 1 / 2 ≤ z.re → ‖digamma z‖ ≤ C * (1 + ‖z‖) := by
  let A (j : ℕ) : ℝ := (((j : ℝ) + 1) ^ 2)⁻¹
  have hA : Summable A := by
    have h := (summable_nat_add_iff (f := fun j : ℕ => ((j : ℝ) ^ 2)⁻¹) 1).mpr
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ)))
    simpa only [A, Nat.cast_add, Nat.cast_one] using h
  let B := ∑' j : ℕ, A j
  have hB : 0 ≤ B := tsum_nonneg (fun j => by dsimp [A]; positivity)
  refine ⟨‖digamma 1‖ + 2 * B, by positivity, fun z hz => ?_⟩
  have hlim := ((tendsto_euler_digamma (by linarith : 0 < z.re)).sub
    (tendsto_euler_digamma (z := 1) (by norm_num))).norm
  have hdiff : ‖digamma z - digamma 1‖ ≤ 2 * ‖z - 1‖ * B := by
    apply le_of_tendsto' hlim
    intro n
    have he : (Complex.log (n : ℂ) - ∑ j ∈ Finset.range (n + 1), (z + (j : ℂ))⁻¹) -
        (Complex.log (n : ℂ) - ∑ j ∈ Finset.range (n + 1), (1 + (j : ℂ))⁻¹) =
        ∑ j ∈ Finset.range (n + 1), ((1 + (j : ℂ))⁻¹ - (z + (j : ℂ))⁻¹) := by
      rw [Finset.sum_sub_distrib]
      ring
    change ‖_ - _‖ ≤ _
    rw [he]
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1), ‖(1 + (j : ℂ))⁻¹ - (z + (j : ℂ))⁻¹‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (n + 1), 2 * ‖z - 1‖ * A j :=
        Finset.sum_le_sum (fun j _ => norm_euler_digamma_diff_term_le hz j)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hA.sum_le_tsum _ (fun j _ => by dsimp [A]; positivity))
          (by positivity)
  have hz₁ : ‖z - 1‖ ≤ 1 + ‖z‖ := by simpa [add_comm] using norm_sub_le z 1
  calc
    ‖digamma z‖ = ‖(digamma z - digamma 1) + digamma 1‖ := by rw [sub_add_cancel]
    _ ≤ ‖digamma z - digamma 1‖ + ‖digamma 1‖ := norm_add_le _ _
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hz₁ hB, norm_nonneg (digamma (1 : ℂ)), norm_nonneg z]

end GoldbachR581
end

-- R581 ReflectedLogDeriv
section
open Complex Filter DirichletCharacter
open scoped Topology Classical ComplexConjugate

namespace GoldbachR581

private theorem differentiableAt_gammaFactor_of_ne_zero {N : ℕ} {χ : DirichletCharacter ℂ N}
    {z : ℂ} (hΓ : χ.gammaFactor z ≠ 0) : DifferentiableAt ℂ χ.gammaFactor z := by
  have hi : Differentiable ℂ (fun w => (χ.gammaFactor w)⁻¹) := by
    rcases χ.even_or_odd with he | ho
    · simp_rw [he.gammaFactor_def]
      exact differentiable_Gammaℝ_inv
    · simp_rw [ho.gammaFactor_def]
      exact differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)
  have h := (hi z).inv (inv_ne_zero hΓ)
  change DifferentiableAt ℂ (fun w => ((χ.gammaFactor w)⁻¹)⁻¹) z at h
  simpa only [inv_inv] using h

private theorem logDeriv_completed_dirichletL {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z : ℂ} (h₀ : z ≠ 0 ∨ N ≠ 1) (h₁ : z ≠ 1 ∨ χ ≠ 1)
    (hL : χ.LFunction z ≠ 0) (hΓ : χ.gammaFactor z ≠ 0) :
    logDeriv (completedLFunction χ) z = logDeriv χ.LFunction z + logDeriv χ.gammaFactor z := by
  have hΓd := differentiableAt_gammaFactor_of_ne_zero hΓ
  have hne : ∀ᶠ w in 𝓝 z, χ.gammaFactor w ≠ 0 := hΓd.continuousAt.eventually_ne hΓ
  have hz : ∀ᶠ w in 𝓝 z, w ≠ 0 ∨ N ≠ 1 := by
    rcases h₀ with h | h
    · exact (eventually_ne_nhds h).mono fun _ hw => Or.inl hw
    · exact Eventually.of_forall fun _ => Or.inr h
  have he : completedLFunction χ =ᶠ[𝓝 z] fun w => χ.LFunction w * χ.gammaFactor w := by
    filter_upwards [hne, hz] with w hn hw
    rw [χ.LFunction_eq_completed_div_gammaFactor w hw, div_mul_cancel₀ _ hn]
  rw [(logDeriv_congr_nhds he).eq_of_nhds,
    logDeriv_fun_mul z hL hΓ (χ.differentiableAt_LFunction z h₁) hΓd]

/-- The left-line logarithmic derivative reduced by the functional equation to a right-half-plane
logarithmic derivative and the two archimedean factors. The identity holds at all regular points
with negative real part, including the negative half-integer lines used in R581. -/
theorem neg_logDeriv_dirichletL_eq_reflected {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) {z : ℂ} (hz : z.re < 0) (hΓ : χ.gammaFactor z ≠ 0) :
    -logDeriv χ.LFunction z = Complex.log (N : ℂ) + logDeriv χ⁻¹.LFunction (1 - z) +
      logDeriv χ⁻¹.gammaFactor (1 - z) + logDeriv χ.gammaFactor z := by
  have h₀ : z ≠ 0 := by intro h; norm_num [h] at hz
  have h₁ : z ≠ 1 := by intro h; norm_num [h] at hz
  have hR : 1 < ((1 : ℂ) - z).re := by rw [sub_re, one_re]; linarith
  have hR₀ : (1 : ℂ) - z ≠ 0 := by intro h; norm_num [h] at hR
  have hR₁ : (1 : ℂ) - z ≠ 1 := by intro h; norm_num [h] at hR
  have hL : χ.LFunction z ≠ 0 := by
    have horder : dirichletOrder χ z = 0 := by
      rw [dirichletOrder_of_re_nonpos hχ hz.le (.inl h₀), ite_eq_right hΓ]
    intro hzero
    have ha := analyticAt_dirichletL_of_regular_parameter (χ := χ) (.inl h₁)
    have hp : 0 < meromorphicOrderAt χ.LFunction z :=
      (tendsto_zero_iff_meromorphicOrderAt_pos ha.meromorphicAt).mp
        (hzero ▸ ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    rw [← dirichletOrder_spec χ z, horder, WithTop.coe_zero] at hp
    exact lt_irrefl _ hp
  have hL' := (χ⁻¹).LFunction_ne_zero_of_one_le_re (.inr hR₁) hR.le
  have hΓ' := gammaFactor_ne_zero_of_re_pos χ⁻¹ (zero_lt_one.trans hR)
  have hld := logDeriv_completed_dirichletL χ (.inl h₀) (.inl h₁) hL hΓ
  have hld' := logDeriv_completed_dirichletL χ⁻¹ (.inl hR₀) (.inl hR₁) hL' hΓ'
  let P (w : ℂ) := (N : ℂ) ^ (1 - w - 1 / 2)
  let Q (w : ℂ) := completedLFunction χ⁻¹ (1 - w)
  have hfe : completedLFunction χ = fun w => P w * (rootNumber χ * Q w) := by
    ext w
    have he := hχ.completedLFunction_one_sub (1 - w)
    rw [sub_sub_cancel] at he
    simpa only [P, Q, mul_assoc] using he
  have hN₀ : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hdP : HasDerivAt P (-Complex.log (N : ℂ) * P z) z := by
    have hd := (((hasDerivAt_id z).const_sub 1).sub_const (1 / 2 : ℂ)).const_cpow (.inl hN₀)
    convert hd using 1 <;> simp only [P, id_eq, neg_mul, one_mul, mul_comm]
  have hnP : P z ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl hN₀)
  have hdQ := (χ⁻¹).differentiableAt_completedLFunction _ (.inl hR₀) (.inl hR₁)
  have hdreflect : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := (hasDerivAt_id z).const_sub 1
  have hQ : DifferentiableAt ℂ Q z := hdQ.comp z hdreflect.differentiableAt
  have hnQ : Q z ≠ 0 := completed_dirichletL_ne_zero_of_one_le_re _ hR.le (.inl hR₁)
  have hnroot := primitive_rootNumber_ne_zero hχ
  have hlogP : logDeriv P z = -Complex.log (N : ℂ) := by
    rw [logDeriv_apply, hdP.deriv, mul_div_cancel_right₀ _ hnP]
  have hlogQ : logDeriv Q z = -logDeriv (completedLFunction χ⁻¹) (1 - z) := by
    change logDeriv (fun w : ℂ => completedLFunction χ⁻¹ (1 - w)) z = _
    rw [logDeriv_fun_comp hdQ hdreflect.differentiableAt, hdreflect.deriv, mul_neg, mul_one]
  have hlogfe : logDeriv (completedLFunction χ) z =
      -Complex.log (N : ℂ) - logDeriv (completedLFunction χ⁻¹) (1 - z) := by
    rw [hfe, logDeriv_fun_mul (f := P) (g := fun w => rootNumber χ * Q w) z hnP
      (mul_ne_zero hnroot hnQ) hdP.differentiableAt (hQ.const_mul _),
      logDeriv_const_mul z _ hnroot, hlogP, hlogQ]
    rfl
  rw [hld, hld'] at hlogfe
  linear_combination -hlogfe

private theorem logDeriv_gammaR_eq_digamma {z : ℂ} (hΓ : Gammaℝ z ≠ 0) :
    logDeriv Gammaℝ z = (-Complex.log (Real.pi : ℂ) + digamma (z / 2)) / 2 := by
  let p (w : ℂ) := (Real.pi : ℂ) ^ (-w / 2)
  let G (w : ℂ) := Gamma (w / 2)
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpn : p z ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl hπ)
  have hGn : G z ≠ 0 := by
    intro h
    change Gamma (z / 2) = 0 at h
    exact hΓ (by simp [Gammaℝ_def, h])
  have hn (n : ℕ) : z / 2 ≠ -(n : ℂ) := fun h => hGn ((Gamma_eq_zero_iff _).mpr ⟨n, h⟩)
  have hpd : HasDerivAt p (-(1 / 2) * Complex.log (Real.pi : ℂ) * p z) z := by
    have hd : HasDerivAt (fun w : ℂ => -w / 2) (-(1 / 2)) z := by
      simpa only [neg_div, Pi.neg_apply, id_eq] using! ((hasDerivAt_id z).neg).div_const (2 : ℂ)
    convert hd.const_cpow (.inl hπ) using 1
    simp only [p]
    ring
  have hGd : DifferentiableAt ℂ G z :=
    (differentiableAt_Gamma _ hn).comp z ((hasDerivAt_id z).div_const (2 : ℂ)).differentiableAt
  have hlp : logDeriv p z = -(1 / 2) * Complex.log (Real.pi : ℂ) := by
    rw [logDeriv_apply, hpd.deriv, mul_div_cancel_right₀ _ hpn]
  have hlG : logDeriv G z = (1 / 2) * digamma (z / 2) :=
    ((hasDerivAt_id z).div_const (2 : ℂ)).logDeriv_Gamma hn
  rw [show Gammaℝ = (fun w => p w * G w) from rfl,
    logDeriv_fun_mul (f := p) (g := G) z hpn hGn hpd.differentiableAt hGd, hlp, hlG]
  ring

/-- The archimedean part of the reflected logarithmic derivative is a digamma value at the
parity-shifted argument. -/
theorem logDeriv_gammaFactor_eq_digamma {N : ℕ} {χ : DirichletCharacter ℂ N}
    {z : ℂ} (hΓ : χ.gammaFactor z ≠ 0) :
    logDeriv χ.gammaFactor z =
      (-Complex.log (Real.pi : ℂ) + digamma ((z + if χ.Even then (0 : ℂ) else 1) / 2)) / 2 := by
  rcases χ.even_or_odd with he | ho
  · rw [funext he.gammaFactor_def] at hΓ ⊢
    simpa only [ite_eq_left he, add_zero] using logDeriv_gammaR_eq_digamma hΓ
  · rw [funext ho.gammaFactor_def] at hΓ ⊢
    have hG := (differentiable_Gammaℝ_inv (z + 1)).inv (inv_ne_zero hΓ)
    change DifferentiableAt ℂ (fun w => ((Gammaℝ w)⁻¹)⁻¹) (z + 1) at hG
    rw [logDeriv_fun_comp (f := Gammaℝ) (g := fun w : ℂ => w + 1)
      (by simpa only [inv_inv] using hG)
      (differentiableAt_id.add_const 1)]
    simp only [deriv_add_const, deriv_id'', mul_one, ite_eq_right ho.not_even]
    exact logDeriv_gammaR_eq_digamma hΓ

private theorem norm_cot_le_one_of_twice_re {w : ℂ} (n : ℤ)
    (hw : 2 * w.re = Real.pi / 2 + (n : ℝ) * Real.pi) : ‖Complex.cot w‖ ≤ 1 := by
  have hθ : (Real.pi : ℂ) / 2 - conj w = w - (n : ℂ) * (Real.pi : ℂ) := by
    apply Complex.ext
    · simp [sub_re, mul_re, div_ofNat_re]
      linarith
    · simp [sub_im, mul_im, div_ofNat_im]
  have hn : ‖Complex.cos w‖ = ‖Complex.sin w‖ := by
    have hsin : Complex.sin ((n : ℂ) * (Real.pi : ℂ)) = 0 := by
      exact_mod_cast Real.sin_int_mul_pi n
    have hcos : ‖Complex.cos ((n : ℂ) * (Real.pi : ℂ))‖ = 1 := by
      have hcoe : (n : ℂ) * (Real.pi : ℂ) = (((n : ℝ) * Real.pi : ℝ) : ℂ) := by push_cast; rfl
      rw [hcoe, ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_cos_int_mul_pi n
    rw [← Complex.norm_conj (Complex.cos w), ← Complex.cos_conj, ← Complex.sin_pi_div_two_sub,
      hθ, Complex.sin_sub, hsin, mul_zero, sub_zero, norm_mul, hcos, mul_one]
  rw [Complex.cot_eq_cos_div_sin, norm_div, hn]
  by_cases h : ‖Complex.sin w‖ = 0 <;> simp [h]

/-- On the half-integer contours the reflection term in the digamma identity is uniformly
bounded. This reduces the remaining Gamma estimate to a right-half-plane digamma estimate. -/
theorem norm_digamma_le_reflect_add_pi_on_left_halfInteger (m a : ℕ) {z : ℂ}
    (hz : z.re = -((m : ℝ) + 1 / 2)) :
    ‖digamma ((z + (a : ℂ)) / 2)‖ ≤ ‖digamma (1 - (z + (a : ℂ)) / 2)‖ + Real.pi := by
  let u : ℂ := (z + (a : ℂ)) / 2
  have hu : 2 * u.re = -((m : ℝ) + 1 / 2) + (a : ℝ) := by
    dsimp only [u]
    rw [Complex.div_ofNat_re, add_re, Complex.natCast_re, hz]
    ring
  have huint (k : ℤ) : u ≠ k := by
    intro he
    rw [he, Complex.intCast_re] at hu
    have h : (4 : ℝ) * (k : ℝ) = -(2 * (m : ℝ) + 1) + 2 * (a : ℝ) := by linarith
    have h' : (4 : ℤ) * k = -(2 * (m : ℤ) + 1) + 2 * (a : ℤ) := by exact_mod_cast h
    omega
  have hcot : ‖Complex.cot ((Real.pi : ℂ) * u)‖ ≤ 1 := by
    apply norm_cot_le_one_of_twice_re ((a : ℤ) - (m : ℤ) - 1)
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, Int.cast_sub, Int.cast_natCast,
      Int.cast_one]
    linear_combination Real.pi * hu
  have he := Complex.digamma_one_sub huint
  have hdecomp : digamma u = digamma (1 - u) - (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * u) := by
    linear_combination -he
  calc
    ‖digamma u‖ ≤ ‖digamma (1 - u)‖ + ‖(Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * u)‖ := by
      rw [hdecomp]
      exact norm_sub_le _ _
    _ ≤ _ := by
      rw [norm_mul, norm_real, Real.norm_of_nonneg Real.pi_nonneg]
      linarith [mul_le_mul_of_nonneg_left hcot Real.pi_nonneg]

/-- A constant plus two right-half-plane digamma norms bounds the logarithmic derivative on
every left contour used in R581. Both digamma arguments have real part at least `3/4`. -/
theorem norm_logDeriv_dirichletL_left_le_right_digamma {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (z : ℂ), z.re = -((m : ℝ) + 1 / 2) →
      let u := (z + if χ.Even then (0 : ℂ) else 1) / 2
      let v := (1 - z + if χ⁻¹.Even then (0 : ℂ) else 1) / 2
      3 / 4 ≤ (1 - u).re ∧ 3 / 4 ≤ v.re ∧
        ‖logDeriv χ.LFunction z‖ ≤ C + (‖digamma (1 - u)‖ + ‖digamma v‖) / 2 := by
  obtain ⟨D, hD, hright⟩ := norm_logDeriv_dirichletL_le_of_re_ge χ⁻¹ (σ := 3 / 2) (by norm_num)
  use ‖Complex.log (N : ℂ)‖ + D + ‖Complex.log (Real.pi : ℂ)‖ + Real.pi / 2
  refine ⟨by positivity, fun m z hz => ?_⟩
  dsimp only
  let u : ℂ := (z + if χ.Even then (0 : ℂ) else 1) / 2
  let v : ℂ := (1 - z + if χ⁻¹.Even then (0 : ℂ) else 1) / 2
  have h₀ : z.re < 0 := by rw [hz]; exact neg_lt_zero.mpr (by positivity)
  have hR : 3 / 2 ≤ ((1 : ℂ) - z).re := by
    rw [sub_re, one_re, hz]
    have hm : 0 ≤ (m : ℝ) := by positivity
    linarith
  have hLΓ : χ.gammaFactor z ≠ 0 := by
    intro hh
    have horder := dirichletOrder_eq_zero_on_left_halfInteger hχ m hz
    have hn : z ≠ 0 := by intro he; norm_num [he] at h₀
    rw [dirichletOrder_of_re_nonpos hχ h₀.le (.inl hn), ite_eq_left hh] at horder
    norm_num at horder
  have hRΓ := gammaFactor_ne_zero_of_re_pos χ⁻¹ (z := 1 - z) (by linarith)
  have hψ : ‖digamma u‖ ≤ ‖digamma (1 - u)‖ + Real.pi := by
    by_cases he : χ.Even
    · simpa only [u, ite_eq_left he, Nat.cast_zero] using
        norm_digamma_le_reflect_add_pi_on_left_halfInteger m 0 hz
    · simpa only [u, ite_eq_right he, Nat.cast_one] using
        norm_digamma_le_reflect_add_pi_on_left_halfInteger m 1 hz
  have gamma_bound (s : ℂ) : ‖-Complex.log (Real.pi : ℂ) + digamma s‖ / 2 ≤
      (‖Complex.log (Real.pi : ℂ)‖ + ‖digamma s‖) / 2 := by
    rw [← norm_neg (Complex.log (Real.pi : ℂ))]
    exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
  have hγL : ‖logDeriv χ.gammaFactor z‖ ≤ (‖Complex.log (Real.pi : ℂ)‖ + ‖digamma u‖) / 2 := by
    rw [logDeriv_gammaFactor_eq_digamma hLΓ, norm_div, norm_ofNat]
    exact gamma_bound u
  have hγR : ‖logDeriv χ⁻¹.gammaFactor (1 - z)‖ ≤
      (‖Complex.log (Real.pi : ℂ)‖ + ‖digamma v‖) / 2 := by
    rw [logDeriv_gammaFactor_eq_digamma hRΓ, norm_div, norm_ofNat]
    exact gamma_bound v
  refine ⟨?_, ?_, ?_⟩
  · split_ifs <;> simp [sub_re, div_ofNat_re, hz] <;> linarith [Nat.cast_nonneg (α := ℝ) m]
  · split_ifs <;> simp [sub_re, div_ofNat_re, hz] <;> linarith [Nat.cast_nonneg (α := ℝ) m]
  · have he := neg_logDeriv_dirichletL_eq_reflected hχ h₀ hLΓ
    rw [← norm_neg (logDeriv χ.LFunction z), he]
    have ht (x y z w : ℂ) : ‖x + y + z + w‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ + ‖w‖ := by
      calc
        ‖x + y + z + w‖ ≤ ‖x + y + z‖ + ‖w‖ := norm_add_le _ _
        _ ≤ ‖x + y‖ + ‖z‖ + ‖w‖ := add_le_add (norm_add_le _ _) le_rfl
        _ ≤ _ := add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    apply (ht _ _ _ _).trans
    linarith [hright (1 - z) hR]

end GoldbachR581
end

-- R581 HorizontalLeft
section
open Complex DirichletCharacter
open scoped Classical

namespace GoldbachR581

private theorem norm_digamma_le_linear_high (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → 1 / 2 ≤ |z.im| →
      ‖digamma z‖ ≤ C * (1 + ‖z‖) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (1 / 2 - a)
  obtain ⟨B, hB, hb⟩ := norm_digamma_le_linear_of_half_le_re
  refine ⟨B * (1 + n) + 2 * n, by positivity, fun z hz hi => ?_⟩
  have hnot (k : ℕ) : z ≠ -(k : ℂ) := by
    intro he
    norm_num [he] at hi
  have hs : ‖∑ k ∈ Finset.range n, (z + (k : ℂ))⁻¹‖ ≤ 2 * (n : ℝ) := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, ‖(z + (k : ℂ))⁻¹‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range n, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        have hk := Complex.abs_im_le_norm (z + (k : ℂ))
        simp only [add_im, natCast_im, add_zero] at hk
        rw [norm_inv, ← one_div]
        apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hi.trans hk))).mpr
        linarith
      _ = _ := by simp [mul_comm]
  have hre : 1 / 2 ≤ (z + (n : ℂ)).re := by simp only [add_re, natCast_re]; linarith
  have ht : ‖z + (n : ℂ)‖ ≤ ‖z‖ + (n : ℝ) := by simpa using norm_add_le z (n : ℂ)
  have he := digamma_apply_add_nat hnot n
  have he' : digamma z = digamma (z + (n : ℂ)) - ∑ k ∈ Finset.range n, (z + (k : ℂ))⁻¹ := by
    rw [he, add_sub_cancel_right]
  calc
    ‖digamma z‖ ≤ ‖digamma (z + (n : ℂ))‖ + ‖∑ k ∈ Finset.range n, (z + (k : ℂ))⁻¹‖ := by
      rw [he']
      exact norm_sub_le _ _
    _ ≤ B * (1 + (‖z‖ + n)) + 2 * n := add_le_add
      ((hb _ hre).trans (mul_le_mul_of_nonneg_left (add_le_add_right ht 1) hB)) hs
    _ ≤ _ := by nlinarith [mul_nonneg hB (Nat.cast_nonneg n : (0 : ℝ) ≤ n), norm_nonneg z]

private theorem gammaFactor_ne_zero_of_im_ne_zero {N : ℕ} (χ : DirichletCharacter ℂ N)
    {z : ℂ} (hz : z.im ≠ 0) : χ.gammaFactor z ≠ 0 := by
  have hh {w : ℂ} (hw : w.im ≠ 0) : Gammaℝ w ≠ 0 := by
    intro he
    obtain ⟨k, hk⟩ := Gammaℝ_eq_zero_iff.mp he
    exact hw (by rw [hk]; simp [mul_im])
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def]
    exact hh hz
  · rw [ho.gammaFactor_def]
    exact hh (by simpa only [add_im, one_im, add_zero] using hz)

/-- A uniform linear logarithmic derivative bound on the reflected portion of a horizontal
contour. The left real endpoint is fixed while the height tends to infinity. -/
theorem exists_norm_logDeriv_left_horizontal {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ -1 / 4 → 1 ≤ |z.im| →
      ‖logDeriv χ.LFunction z‖ ≤ C * (1 + ‖z‖) := by
  obtain ⟨D, hD, hright⟩ := norm_logDeriv_dirichletL_le_of_re_ge χ⁻¹ (σ := 5 / 4) (by norm_num)
  obtain ⟨B, hB, hψ⟩ := norm_digamma_le_linear_high (a / 2)
  obtain ⟨E, hE, hψR⟩ := norm_digamma_le_linear_of_half_le_re
  let K := ‖Complex.log (N : ℂ)‖ + D + ‖Complex.log (Real.pi : ℂ)‖
  refine ⟨K + 2 * B + 2 * E, by dsimp [K]; positivity, fun z hza hz hi => ?_⟩
  have hRe : 5 / 4 ≤ (1 - z).re := by rw [sub_re, one_re]; linarith
  have hz' : z.re < 0 := hz.trans_lt (by norm_num)
  have h₀ : z.im ≠ 0 := fun he => by rw [he, abs_zero] at hi; linarith
  have hΓ₁ := gammaFactor_ne_zero_of_im_ne_zero χ h₀
  have hΓ₂ := gammaFactor_ne_zero_of_re_pos χ⁻¹ (z := 1 - z) (by linarith)
  let e : ℂ := if χ.Even then 0 else 1
  let e' : ℂ := if χ⁻¹.Even then 0 else 1
  let u : ℂ := (z + e) / 2
  let v : ℂ := (1 - z + e') / 2
  have he : ‖e‖ ≤ 1 := by dsimp only [e]; split_ifs <;> simp
  have he' : ‖e'‖ ≤ 1 := by dsimp only [e']; split_ifs <;> simp
  have hu : a / 2 ≤ u.re := by
    dsimp only [u, e]
    split_ifs <;> simp only [div_ofNat_re, add_re, zero_re, one_re] <;> linarith
  have huim : 1 / 2 ≤ |u.im| := by
    have hei : e.im = 0 := by dsimp only [e]; split_ifs <;> simp
    dsimp only [u]
    rw [div_ofNat_im, add_im, hei, add_zero, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have hv : 1 / 2 ≤ v.re := by
    dsimp only [v, e']
    split_ifs <;> simp only [div_ofNat_re, add_re, zero_re, one_re] <;> linarith
  have hnu : ‖u‖ ≤ (‖z‖ + 1) / 2 := by
    dsimp only [u]
    rw [norm_div, norm_ofNat]
    linarith [norm_add_le z e]
  have hnv : ‖v‖ ≤ (2 + ‖z‖) / 2 := by
    dsimp only [v]
    rw [norm_div, norm_ofNat]
    linarith [norm_add_le (1 - z) e', norm_sub_le (1 : ℂ) z, norm_one (α := ℂ)]
  have hγ (w : ℂ) : ‖(-Complex.log (Real.pi : ℂ) + digamma w) / 2‖ ≤
      (‖Complex.log (Real.pi : ℂ)‖ + ‖digamma w‖) / 2 := by
    rw [norm_div, norm_ofNat, ← norm_neg (Complex.log (Real.pi : ℂ))]
    exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
  rw [← norm_neg (logDeriv χ.LFunction z), neg_logDeriv_dirichletL_eq_reflected hχ hz' hΓ₁,
    logDeriv_gammaFactor_eq_digamma hΓ₁, logDeriv_gammaFactor_eq_digamma hΓ₂]
  change ‖Complex.log (N : ℂ) + logDeriv χ⁻¹.LFunction (1 - z) +
    (-Complex.log (Real.pi : ℂ) + digamma v) / 2 + (-Complex.log (Real.pi : ℂ) + digamma u) / 2‖ ≤ _
  have hb₁ := (hψ u hu huim).trans
    (mul_le_mul_of_nonneg_left (add_le_add_right hnu 1) hB)
  have hb₂ := (hψR v hv).trans
    (mul_le_mul_of_nonneg_left (add_le_add_right hnv 1) hE)
  refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (hγ u)) |>.trans ?_
  refine (add_le_add (add_le_add (norm_add_le _ _) (hγ v)) le_rfl).trans ?_
  dsimp only [K]
  nlinarith [hright (1 - z) hRe, hb₁, hb₂, norm_nonneg z,
    mul_nonneg (norm_nonneg (Complex.log (N : ℂ))) (norm_nonneg z),
    mul_nonneg (norm_nonneg (Complex.log (Real.pi : ℂ))) (norm_nonneg z),
    mul_nonneg hD (norm_nonneg z), mul_nonneg hB (norm_nonneg z), mul_nonneg hE (norm_nonneg z)]

end GoldbachR581
end

-- R581 LocalLogDeriv
section
open Complex Filter Metric Set
open scoped Classical Topology

namespace GoldbachR581

private theorem exists_normalized_logarithm {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball c R)) (h₀ : ∀ z ∈ ball c R, f z ≠ 0) :
    ∃ h : ℂ → ℂ, (∀ z ∈ ball c R, HasDerivAt h (logDeriv f z) z) ∧
      h c = 0 ∧ ∀ z ∈ ball c R, Complex.exp (h z) = f z / f c := by
  have hD : DifferentiableOn ℂ (logDeriv f) (ball c R) := by
    exact hf.deriv.differentiableOn.div hf.differentiableOn h₀
  obtain ⟨h, hc, hh⟩ := hD.isExactOn_ball.with_val_at c 0
  let p := fun z => f z * Complex.exp (-h z)
  have hp (z : ℂ) (hz : z ∈ ball c R) : HasDerivAt p 0 z := by
    have he := (hf z hz).differentiableAt.hasDerivAt.mul ((hh z hz).neg.cexp)
    convert he using 1
    rw [logDeriv_apply]
    field_simp [h₀ z hz]
    ring
  refine ⟨h, hh, hc, fun z hz => ?_⟩
  have heq := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected
    (fun w hw => (hp w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hp w hw).deriv) hz (mem_ball_self hR)
  have he : f z * (Complex.exp (h z))⁻¹ = f c := by
    simpa only [p, hc, neg_zero, exp_neg, exp_zero, inv_one, mul_one] using heq
  field_simp [h₀ c (mem_ball_self hR), Complex.exp_ne_zero (h z)] at he ⊢
  linear_combination -he

/-- Bound the logarithmic derivative on an inner disk by the logarithm of the growth of a
zero-free holomorphic function on the outer disk. -/
theorem norm_logDeriv_le_of_zero_free_disk {f : ℂ → ℂ} {c : ℂ} {r R M : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hf : AnalyticOnNhd ℂ f (ball c R))
    (h₀ : ∀ z ∈ ball c R, f z ≠ 0) (hfM : ∀ z ∈ ball c R, ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖logDeriv f z‖ ≤
      (2 * R / ((R - r) / 2) ^ 2) * (1 + Real.log (M / ‖f c‖)) := by
  have hR := hr.trans_lt hrR
  have hcpos : 0 < ‖f c‖ := norm_pos_iff.mpr (h₀ c (mem_ball_self hR))
  have hM : 0 < M := hcpos.trans_le (hfM c (mem_ball_self hR))
  obtain ⟨h, hh, hc, he⟩ := exists_normalized_logarithm hR hf h₀
  let B := 1 + Real.log (M / ‖f c‖)
  have hB : 0 < B := by
    have hlog := Real.log_nonneg ((one_le_div hcpos).mpr (hfM c (mem_ball_self hR)))
    dsimp only [B]
    linarith
  have hp (w : ℂ) (hw : w ∈ ball c R) : (h w).re ≤ B := by
    have hx : Real.exp (h w).re = ‖f w‖ / ‖f c‖ := by rw [← norm_exp, he w hw, norm_div]
    rw [← Real.log_exp (h w).re, hx]
    exact (Real.log_le_log (div_pos (norm_pos_iff.mpr (h₀ w hw)) hcpos)
      (div_le_div_of_nonneg_right (hfM w hw) hcpos.le)).trans (le_add_of_nonneg_left zero_le_one)
  let h' := fun w : ℂ => h (w + c)
  have hmem {w : ℂ} (hw : w ∈ ball (0 : ℂ) R) : w + c ∈ ball c R := by
    simpa only [mem_ball, Complex.dist_eq, add_sub_cancel_right, sub_zero] using hw
  have hd : DifferentiableOn ℂ h' (ball 0 R) :=
    fun w hw => (((hh _ (hmem hw)).differentiableAt.comp w
      (differentiableAt_id.add_const c)).differentiableWithinAt)
  let δ := (R - r) / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hsum : r + δ < R := by dsimp only [δ]; linarith
  have hs (w : ℂ) (hw : w ∈ closedBall z δ) : dist w c ≤ r + δ := by
    linarith [dist_triangle w z c, mem_closedBall.mp hw, mem_closedBall.mp hz]
  have hsb : closedBall z δ ⊆ ball c R := fun w hw => (hs w hw).trans_lt hsum
  have hbound (w : ℂ) (hw : w ∈ sphere z δ) : ‖h w‖ ≤ 2 * B * R / δ := by
    have hwc := hs w (sphere_subset_closedBall hw)
    have hsub : ‖w - c‖ ≤ r + δ := by simpa only [Complex.dist_eq] using hwc
    have hw' : w - c ∈ ball (0 : ℂ) R := by
      simpa only [mem_ball, dist_zero_right] using hsub.trans_lt hsum
    have hBc := borelCaratheodory_zero hB hd (fun a ha => hp _ (hmem ha)) hR hw'
      (by simpa only [h', zero_add] using hc)
    have hBc' : ‖h w‖ ≤ 2 * B * ‖w - c‖ / (R - ‖w - c‖) := by
      simpa only [h', sub_add_cancel] using hBc
    apply hBc'.trans
    have hgap : δ ≤ R - ‖w - c‖ := by dsimp only [δ] at *; linarith
    gcongr
    exact hsub.trans hsum.le
  have hdiff : DiffContOnCl ℂ h (ball z δ) := by
    have hh₀ : DifferentiableOn ℂ h (ball c R) :=
      fun a ha => (hh a ha).differentiableAt.differentiableWithinAt
    exact hh₀.diffContOnCl_ball hsb
  have hb := norm_deriv_le_of_forall_mem_sphere_norm_le hδ hdiff hbound
  rw [(hh z ((mem_closedBall.mp hz).trans_lt hrR)).deriv] at hb
  rw [div_div, ← pow_two] at hb
  convert hb using 1
  change 2 * R / δ ^ 2 * B = 2 * B * R / δ ^ 2
  ring

private theorem analyticAt_power_product (S : Finset ℂ) (D : ℂ → ℤ)
    (hD : ∀ u, 0 ≤ D u) (w : ℂ) :
    AnalyticAt ℂ (fun q : ℂ => ∏ u ∈ S, (q - u) ^ D u) w := by
  induction S using Finset.cons_induction with
  | empty => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) w)
  | cons u S hu ih =>
    simp only [Finset.prod_cons]
    have hp : AnalyticAt ℂ (fun q : ℂ => (q - u) ^ D u) w := by
      rw [← Int.toNat_of_nonneg (hD u)]
      simp only [zpow_natCast]
      exact (analyticAt_id.sub analyticAt_const).pow _
    exact hp.mul ih

private theorem exists_analytic_divisor_quotient {f : ℂ → ℂ} {c : ℂ} {s : ℝ}
    (hf : ∀ w, AnalyticAt ℂ f w) (hc : f c ≠ 0) :
    let D := MeromorphicOn.divisor f (closedBall c s)
    let S := (D.finiteSupport (isCompact_closedBall c s)).toFinset
    let P := fun w : ℂ => ∏ u ∈ S, (w - u) ^ D u
    ∃ g : ℂ → ℂ, (∀ w, AnalyticAt ℂ g w) ∧ (∀ w ∈ closedBall c s, g w ≠ 0) ∧
      ∀ w, P w ≠ 0 → f w = P w * g w := by
  let U := closedBall c s
  let D := MeromorphicOn.divisor f U
  have hfU : AnalyticOnNhd ℂ f U := fun w _ => hf w
  have hfM : MeromorphicOn f univ := fun w _ => (hf w).meromorphicAt
  have hD : (Function.support (D : ℂ → ℤ)).Finite := D.finiteSupport (isCompact_closedBall c s)
  let S := hD.toFinset
  let P := fun w : ℂ => ∏ u ∈ S, (w - u) ^ D u
  let Q := fun w : ℂ => (P w)⁻¹ * f w
  let g := toMeromorphicNFOn Q univ
  have hD₀ (w : ℂ) : 0 ≤ D w := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfU w
  have hPn (w : ℂ) : AnalyticAt ℂ P w := analyticAt_power_product S D hD₀ w
  have hP_eq : P = ∏ᶠ u, (· - u) ^ D u := by
    have hsub : Function.mulSupport (fun u ↦ (· - u : ℂ → ℂ) ^ D u) ⊆ S := by
      intro u hu
      change u ∈ hD.toFinset
      rw [Set.Finite.mem_toFinset]
      by_contra h
      have hzero : D u = 0 := not_not.mp h
      exact hu (by simp [hzero])
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
    ext w
    simp only [P, Finset.prod_apply, Pi.pow_apply]
  have hQm : MeromorphicOn Q univ := fun w _ => (hPn w).meromorphicAt.inv.mul (hf w).meromorphicAt
  have hnf : MeromorphicNFOn g univ := meromorphicNFOn_toMeromorphicNFOn Q univ
  have htop (w : ℂ) : meromorphicOrderAt f w ≠ ⊤ := by
    apply hfM.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ c) (mem_univ w)
    rw [(hf c).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hc]
    exact WithTop.coe_ne_top
  have hQord (w : ℂ) : meromorphicOrderAt g w = -(D w : WithTop ℤ) + meromorphicOrderAt f w := by
    rw [meromorphicOrderAt_toMeromorphicNFOn hQm (mem_univ w),
      show Q = P⁻¹ * f from rfl, meromorphicOrderAt_mul (hPn w).meromorphicAt.inv (hf w).meromorphicAt,
      meromorphicOrderAt_inv, hP_eq, Function.FactorizedRational.meromorphicOrderAt_eq D hD]
  have hgord (w : ℂ) (hw : w ∈ U) : meromorphicOrderAt g w = 0 := by
    rw [hQord, MeromorphicOn.divisor_apply hfU.meromorphicOn hw, WithTop.coe_untop₀_of_ne_top (htop w)]
    lift meromorphicOrderAt f w to ℤ using htop w with n hn
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero]
  have hgA : AnalyticOnNhd ℂ g univ := by
    apply hnf.divisor_nonneg_iff_analyticOnNhd.mp
    intro w
    rw [MeromorphicOn.divisor_apply hnf.meromorphicOn (mem_univ w)]
    by_cases hw : w ∈ U
    · simp [hgord w hw]
    · have hDzero : D w = 0 := by
        by_contra h
        exact hw (D.supportWithinDomain h)
      simp only [hQord, hDzero, WithTop.coe_zero, neg_zero, zero_add]
      exact WithTop.untop₀_nonneg.mpr (hf w).meromorphicOrderAt_nonneg
  refine ⟨g, fun w => hgA w (mem_univ w), fun w hw => ?_, fun w hw => ?_⟩
  · exact (hnf (mem_univ w)).meromorphicOrderAt_eq_zero_iff.mp (hgord w hw)
  · have hqA : AnalyticAt ℂ Q w := ((hPn w).inv hw).mul (hf w)
    change P w ≠ 0 at hw
    change f w = P w * g w
    rw [show g w = Q w by
      change toMeromorphicNFOn Q univ w = _
      rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hQm (mem_univ w),
        toMeromorphicNFAt_eq_self.mpr hqA.meromorphicNFAt]]
    simp only [Q, ← mul_assoc, mul_inv_cancel₀ hw, one_mul]

/-- A fixed-radius disk estimate for the logarithmic derivative of an entire function.
The separation hypothesis only concerns zeros in the intermediate closed disk. -/
theorem exists_norm_logDeriv_le_of_separated_disk :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : ℂ → ℂ} {c z : ℂ} {M δ : ℝ},
      (∀ w, AnalyticAt ℂ f w) → f c ≠ 0 → 1 ≤ M →
      (∀ w ∈ sphere c (29 / 10), ‖f w‖ ≤ M) →
      z ∈ closedBall c (9 / 4) → 0 < δ →
      (∀ u ∈ closedBall c (5 / 2), meromorphicOrderAt f u ≠ 0 → δ ≤ ‖z - u‖) →
      ‖logDeriv f z‖ ≤ C * (1 + Real.log (M / ‖f c‖)) * (1 + 1 / δ) := by
  let ell := Real.log ((29 / 10 : ℝ) / (5 / 2))
  let E := Real.log (25 / 4 : ℝ)
  have hell : 0 < ell := Real.log_pos (by norm_num)
  have hE : 0 ≤ E := Real.log_nonneg (by norm_num)
  let C := 320 * (1 + E / ell) + 1 / ell
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro f c z M δ hf hc hM hbound hz hδ hsep
  let D := MeromorphicOn.divisor f (closedBall c (5 / 2))
  let S := (D.finiteSupport (isCompact_closedBall c (5 / 2))).toFinset
  let P := fun w : ℂ => ∏ u ∈ S, (w - u) ^ D u
  let m := ∑ u ∈ S, (D u).toNat
  let L := Real.log (M / ‖f c‖)
  obtain ⟨g, hg, hg₀, hEq⟩ := exists_analytic_divisor_quotient (s := (5 / 2 : ℝ)) hf hc
  change ∀ w, P w ≠ 0 → f w = P w * g w at hEq
  have hfA : AnalyticOnNhd ℂ f (closedBall c (5 / 2)) := fun w _ => hf w
  have hD₀ (u : ℂ) : 0 ≤ D u := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfA u
  have hinfo {u : ℂ} (hu : u ∈ S) :
      u ∈ closedBall c (5 / 2) ∧ meromorphicOrderAt f u ≠ 0 := by
    have hn : D u ≠ 0 := by simpa only [S, Set.Finite.mem_toFinset, Function.mem_support] using hu
    have hu' := D.supportWithinDomain hn
    refine ⟨hu', fun he => hn ?_⟩
    simp [D, MeromorphicOn.divisor_apply hfA.meromorphicOn hu', he]
  have hPnz {w : ℂ} (hw : ∀ u ∈ S, w ≠ u) : P w ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun u hu => zpow_ne_zero _ (sub_ne_zero.mpr (hw u hu))
  have hPa (w : ℂ) : AnalyticAt ℂ P w := analyticAt_power_product S D hD₀ w
  have hcenter : P c ≠ 0 := by
    apply hPnz
    intro u hu he
    subst u
    exact (hinfo hu).2 ((hf c).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hc)
  have hcP : ‖P c‖ ≤ (5 / 2 : ℝ) ^ m := by
    change ‖∏ u ∈ S, (c - u) ^ D u‖ ≤ _
    rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod₀ (fun u _ => norm_nonneg _)
    intro u hu
    rw [norm_zpow, ← zpow_natCast, Int.toNat_of_nonneg (hD₀ u)]
    exact zpow_le_zpow_left₀ (hD₀ u) (norm_nonneg _)
      (by simpa only [mem_closedBall, Complex.dist_eq, norm_sub_rev u c] using (hinfo hu).1)
  have hcoef₁ : 0 < (5 / 2 : ℝ) ^ m := by positivity
  have hcoef₂ : 0 < (2 / 5 : ℝ) ^ m := by positivity
  have hgcenter : ‖f c‖ / ((5 / 2 : ℝ) ^ m) ≤ ‖g c‖ := by
    rw [div_le_iff₀ hcoef₁, hEq c hcenter, norm_mul, mul_comm (‖g c‖)]
    exact mul_le_mul_of_nonneg_right hcP (norm_nonneg _)
  have hgr {w : ℂ} (hw : w ∈ sphere c (29 / 10)) : ‖g w‖ ≤ M / ((2 / 5 : ℝ) ^ m) := by
    have hd (u : ℂ) (hu : u ∈ S) : (2 / 5 : ℝ) ≤ ‖w - u‖ := by
      have he := dist_triangle w u c
      rw [mem_sphere] at hw
      rw [hw, Complex.dist_eq w u] at he
      linarith [mem_closedBall.mp (hinfo hu).1]
    have hPn : P w ≠ 0 := by
      apply hPnz
      intro u hu he
      have hh := hd u hu
      norm_num [he] at hh
    have hb : (2 / 5 : ℝ) ^ m ≤ ‖P w‖ := by
      change _ ≤ ‖∏ u ∈ S, (w - u) ^ D u‖
      rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod₀ (fun u _ => by positivity) fun u hu => ?_
      rw [norm_zpow, ← zpow_natCast, Int.toNat_of_nonneg (hD₀ u)]
      exact zpow_le_zpow_left₀ (hD₀ u) (by norm_num) (hd u hu)
    apply (le_div_iff₀ hcoef₂).mpr
    calc
      ‖g w‖ * (2 / 5 : ℝ) ^ m ≤ ‖P w‖ * ‖g w‖ := by
        rw [mul_comm ‖g w‖]
        exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = ‖f w‖ := by rw [hEq w hPn, norm_mul]
      _ ≤ M := hbound w hw
  have hgmax (w : ℂ) (hw : w ∈ ball c (5 / 2)) : ‖g w‖ ≤ M / ((2 / 5 : ℝ) ^ m) := by
    have hgd : Differentiable ℂ g := fun u => (hg u).differentiableAt
    apply norm_le_of_forall_mem_frontier_norm_le (U := ball c (29 / 10)) isBounded_ball
      hgd.diffContOnCl
    · exact fun u hu => hgr (frontier_ball_subset_sphere hu)
    · exact subset_closure (ball_subset_ball (by norm_num) hw)
  have hlog : Real.log (M / ((2 / 5 : ℝ) ^ m) / ‖g c‖) ≤ L + (m : ℝ) * E := by
    have hfcn : 0 < ‖f c‖ := norm_pos_iff.mpr hc
    have hgcn : 0 < ‖g c‖ := (div_pos hfcn hcoef₁).trans_le hgcenter
    have hMn : 0 < M / ((2 / 5 : ℝ) ^ m) := div_pos (zero_lt_one.trans_le hM) hcoef₂
    calc
      _ ≤ Real.log (M / ((2 / 5 : ℝ) ^ m) / (‖f c‖ / ((5 / 2 : ℝ) ^ m))) :=
        Real.log_le_log (div_pos hMn hgcn) (div_le_div_of_nonneg_left hMn.le
          (div_pos hfcn hcoef₁) hgcenter)
      _ = Real.log (M / ‖f c‖ * (25 / 4 : ℝ) ^ m) := by
        congr 1
        rw [div_div_div_comm, ← div_pow, show (2 / 5 : ℝ) / (5 / 2) = (25 / 4)⁻¹ by norm_num,
          inv_pow, div_inv_eq_mul]
      _ = _ := by
        rw [Real.log_mul (div_ne_zero (zero_lt_one.trans_le hM).ne' hfcn.ne')
          (pow_ne_zero _ (by norm_num)), Real.log_pow]
  have hN : (m : ℝ) ≤ L / ell := by
    have hJ := AnalyticOnNhd.sum_divisor_le (c := c) (r := (5 / 2 : ℝ)) (R := (29 / 10 : ℝ))
      (by norm_num) (by norm_num) hM (fun w _ => hf w) hc
      (by simpa only [abs_of_nonneg (by norm_num : 0 ≤ (29 / 10 : ℝ))] using hbound)
    have hsum : (m : ℤ) = ∑ᶠ u, D u := by
      rw [finsum_eq_sum_of_support_subset (s := S) _ (by simpa only [S, Set.Finite.coe_toFinset] using
        (Set.Subset.rfl : Function.support D ⊆ Function.support D))]
      simp only [m, Nat.cast_sum, Int.toNat_of_nonneg (hD₀ _)]
    rw [← Int.cast_natCast, hsum]
    have hball : closedBall c |(5 / 2 : ℝ)| = closedBall c (5 / 2) := by
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 2)]
    rw [hball] at hJ
    exact hJ
  have hL₀ : 0 ≤ L := by
    linarith [(le_div_iff₀ hell).mp ((Nat.cast_nonneg m).trans hN)]
  have hPn : P z ≠ 0 := by
    apply hPnz
    intro u hu he
    have hh := hsep u (hinfo hu).1 (hinfo hu).2
    simp [he, not_le.mpr hδ] at hh
  have hze : z ∈ closedBall c (5 / 2) := closedBall_subset_closedBall (by norm_num) hz
  have hder : logDeriv f z = logDeriv P z + logDeriv g z := by
    have hEv : f =ᶠ[𝓝 z] fun w => P w * g w :=
      ((hPa z).continuousAt.eventually_ne hPn).mono fun w hw => hEq w hw
    rw [(logDeriv_congr_nhds hEv).eq_of_nhds,
      logDeriv_fun_mul z hPn (hg₀ z hze) (hPa z).differentiableAt (hg z).differentiableAt]
  have hPl : ‖logDeriv P z‖ ≤ (m : ℝ) / δ := by
    change ‖logDeriv (fun w : ℂ => ∏ u ∈ S, (w - u) ^ D u) z‖ ≤ _
    rw [logDeriv_fun_prod]
    · calc
        _ ≤ ∑ u ∈ S, ‖logDeriv (fun w : ℂ => (w - u) ^ D u) z‖ := norm_sum_le _ _
        _ ≤ ∑ u ∈ S, (D u : ℝ) / δ := by
          apply Finset.sum_le_sum
          intro u hu
          have hd : HasDerivAt (fun w : ℂ => w - u) 1 z := (hasDerivAt_id z).sub_const u
          rw [logDeriv_fun_zpow (by fun_prop),
            show logDeriv (fun w : ℂ => w - u) z = 1 / (z - u) by
              rw [logDeriv_apply, hd.deriv],
            norm_mul, Complex.norm_intCast, abs_of_nonneg (by exact_mod_cast hD₀ u), norm_div, norm_one]
          rw [mul_one_div]
          exact div_le_div_of_nonneg_left (by exact_mod_cast hD₀ u) hδ (hsep u (hinfo hu).1 (hinfo hu).2)
        _ = _ := by
          rw [← Finset.sum_div]
          congr 1
          simp only [m, Nat.cast_sum]
          exact Finset.sum_congr rfl fun u _ => by
            exact_mod_cast (Int.toNat_of_nonneg (hD₀ u)).symm
    · intro u hu
      apply zpow_ne_zero
      exact norm_pos_iff.mp (hδ.trans_le (hsep u (hinfo hu).1 (hinfo hu).2))
    · intro u _
      rw [← Int.toNat_of_nonneg (hD₀ u)]
      simp only [zpow_natCast]
      fun_prop
  have hGl := norm_logDeriv_le_of_zero_free_disk (r := (9 / 4 : ℝ)) (R := (5 / 2 : ℝ))
    (by norm_num) (by norm_num) (fun w _ => hg w)
    (fun w hw => hg₀ w (ball_subset_closedBall hw)) hgmax hz
  norm_num at hGl
  rw [hder]
  calc
    _ ≤ 320 * (1 + L + (m : ℝ) * E) + (m : ℝ) / δ := by
      have hg' := hGl.trans (mul_le_mul_of_nonneg_left (add_le_add_right hlog 1) (by norm_num))
      linarith [norm_add_le (logDeriv P z) (logDeriv g z)]
    _ ≤ 320 * (1 + L + (L / ell) * E) + (L / ell) / δ := by
      gcongr
    _ ≤ C * (1 + L) * (1 + 1 / δ) := by
      have h₁ : 320 * (1 + L + L / ell * E) ≤ (320 * (1 + E / ell)) * (1 + L) := by
        calc
          _ = (320 * (1 + E / ell)) * (1 + L) - 320 * (E / ell) := by ring
          _ ≤ _ := sub_le_self _ (by positivity)
      have h₂ : L / ell / δ ≤ (1 / ell) * (1 + L) * (1 / δ) := by
        calc
          _ = (1 / ell) * L * (1 / δ) := by ring
          _ ≤ _ := by gcongr; linarith
      have h₃ := add_le_add h₁ h₂
      dsimp only [C]
      have hx : 0 ≤ 320 * (1 + E / ell) * (1 + L) * (1 / δ) := by positivity
      have hy : 0 ≤ (1 / ell) * (1 + L) := by positivity
      nlinarith only [h₃, hx, hy]

end GoldbachR581
end

-- R581 HorizontalBounds
section
open Complex DirichletCharacter Filter MeasureTheory Metric Set
open scoped Classical ContDiff Topology

namespace GoldbachR581

private theorem norm_logDeriv_le_entire_add_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z : ℂ} (hi : 1 ≤ |z.im|) (hn : entireDirichletL χ z ≠ 0) :
    ‖logDeriv χ.LFunction z‖ ≤ ‖logDeriv (entireDirichletL χ) z‖ + 1 := by
  by_cases hχ : χ = 1
  · have hz : z ≠ 1 := by
      intro he
      norm_num [he] at hi
    have he : entireDirichletL χ =ᶠ[𝓝 z] fun w => (w - 1) * χ.LFunction w := by
      filter_upwards [eventually_ne_nhds hz] with w hw
      simp [entireDirichletL, hχ, LFunctionTrivChar₁, Function.update_of_ne hw]
    have hnL : χ.LFunction z ≠ 0 := by
      intro h
      exact hn (by rw [he.eq_of_nhds, h, mul_zero])
    have hl : logDeriv (entireDirichletL χ) z =
        1 / (z - 1) + logDeriv χ.LFunction z := by
      have hd : HasDerivAt (fun w : ℂ => w - 1) 1 z := (hasDerivAt_id z).sub_const 1
      rw [(logDeriv_congr_nhds he).eq_of_nhds,
        logDeriv_fun_mul (f := fun w : ℂ => w - 1) (g := χ.LFunction) z
          (sub_ne_zero.mpr hz) hnL hd.differentiableAt
          (χ.differentiableAt_LFunction z (Or.inl hz)), logDeriv_apply (fun w : ℂ => w - 1),
        hd.deriv]
    have hinv : ‖1 / (z - 1)‖ ≤ 1 := by
      have hh := Complex.abs_im_le_norm (z - 1)
      simp only [sub_im, one_im, sub_zero] at hh
      rw [norm_div, norm_one]
      exact (div_le_one (zero_lt_one.trans_le (hi.trans hh))).mpr (hi.trans hh)
    have hs : logDeriv χ.LFunction z = logDeriv (entireDirichletL χ) z - 1 / (z - 1) := by
      rw [hl, add_sub_cancel_left]
    rw [hs]
    exact (norm_sub_le _ _).trans (add_le_add_right hinv _)
  · rw [entireDirichletL, ite_eq_right hχ]
    exact le_add_of_nonneg_right zero_le_one

private theorem verticalPoint_sub_same_height (x y t : ℝ) :
    verticalPoint x t - verticalPoint y t = ((x - y : ℝ) : ℂ) := by
  simp only [verticalPoint, ofReal_sub]
  ring

private theorem norm_verticalPoint_le_abs (x t : ℝ) :
    ‖verticalPoint x t‖ ≤ |x| + |t| := by
  unfold verticalPoint
  simpa only [norm_real, Real.norm_eq_abs, norm_mul, norm_I, mul_one] using
    (norm_add_le (x : ℂ) ((t : ℂ) * I))

private theorem exists_norm_logDeriv_near_critical {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t x δ : ℝ}, 3 ≤ |t| → x ∈ Icc (-1 / 4 : ℝ) 2 → 0 < δ →
      (∀ u : ℂ, u.re ∈ Ioo (0 : ℝ) 1 → dirichletOrder χ u ≠ 0 → δ ≤ |t - u.im|) →
      ‖logDeriv χ.LFunction (verticalPoint x t)‖ ≤ C * (2 + |t|) * (1 + 1 / δ) := by
  obtain ⟨A, hA, hA'⟩ := exists_polynomial_bound_entireDirichletL_on_jensen_circles χ
  obtain ⟨l, hl, hl'⟩ := exists_pos_le_norm_entireDirichletL_on_two χ
  obtain ⟨D, hD, hD'⟩ := exists_norm_logDeriv_le_of_separated_disk
  let B := |Real.log (A / l)| + 4
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨D * B + 1, by positivity, ?_⟩
  intro t x δ ht hx hδ hsep
  let c := verticalPoint 2 t
  let z := verticalPoint x t
  let q := 2 + |t|
  let M := A * q ^ 3
  have hq : 1 ≤ q := by dsimp only [q]; linarith [abs_nonneg t]
  have hq₀ : 0 < q := zero_lt_one.trans_le hq
  have hM : 1 ≤ M := hA.trans (le_mul_of_one_le_right (zero_le_one.trans hA) (one_le_pow₀ hq))
  have hcn : 0 < ‖entireDirichletL χ c‖ := hl.trans_le (hl' t)
  have hclose : z ∈ closedBall c (9 / 4) := by
    rw [mem_closedBall, Complex.dist_eq]
    change ‖verticalPoint x t - verticalPoint 2 t‖ ≤ _
    rw [verticalPoint_sub_same_height, norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have him (v : ℂ) (hv : v ∈ closedBall c (5 / 2)) : v.im ≠ 0 := by
    have hs := Complex.abs_im_le_norm (v - c)
    have hcim : c.im = t := verticalPoint_im _ _
    intro he
    rw [sub_im, hcim, he, zero_sub, abs_neg] at hs
    rw [mem_closedBall, Complex.dist_eq] at hv
    linarith
  have hsep' (u : ℂ) (hu : u ∈ closedBall c (5 / 2))
      (ho : meromorphicOrderAt (entireDirichletL χ) u ≠ 0) : δ ≤ ‖z - u‖ := by
    have huim := him u hu
    have hu₁ : u ≠ 1 := by intro e; exact huim (by simp [e])
    rw [meromorphicOrderAt_entireDirichletL χ hu₁] at ho
    have ho' : dirichletOrder χ u ≠ 0 := by
      intro he
      exact ho (by rw [he]; rfl)
    have hs := Complex.abs_im_le_norm (z - u)
    rw [sub_im, show z.im = t from verticalPoint_im _ _] at hs
    exact (hsep u (dirichletOrder_ne_zero_imp_mem_critical_of_im_ne_zero hχ huim ho') ho').trans hs
  have hlz := hD' (analyticAt_entireDirichletL χ) (norm_pos_iff.mp hcn) hM (hA' t) hclose hδ hsep'
  have hlog : 1 + Real.log (M / ‖entireDirichletL χ c‖) ≤ B * q := by
    have hA₀ : 0 < A := zero_lt_one.trans_le hA
    have hLe : Real.log (M / ‖entireDirichletL χ c‖) ≤ Real.log (M / l) :=
      Real.log_le_log (div_pos (zero_lt_one.trans_le hM) hcn)
        (div_le_div_of_nonneg_left (zero_le_one.trans hM) hl (hl' t))
    have hcomp : Real.log (M / l) = Real.log (A / l) + 3 * Real.log q := by
      dsimp only [M]
      rw [mul_comm A, mul_div_assoc, Real.log_mul (pow_ne_zero _ hq₀.ne')
        (div_ne_zero hA₀.ne' hl.ne'), Real.log_pow]
      ring
    rw [hcomp] at hLe
    dsimp only [B]
    nlinarith [Real.log_le_sub_one_of_pos hq₀, le_abs_self (Real.log (A / l)),
      mul_nonneg (abs_nonneg (Real.log (A / l))) (sub_nonneg.mpr hq)]
  have hzin := closedBall_subset_closedBall (by norm_num : (9 / 4 : ℝ) ≤ 5 / 2) hclose
  have hnz : entireDirichletL χ z ≠ 0 := by
    apply ((analyticAt_entireDirichletL χ z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).mp
    by_contra h
    have he := hsep' z hzin h
    simp [not_le.mpr hδ] at he
  have h₀ := norm_logDeriv_le_entire_add_one χ (z := z)
    (by rw [show z.im = t from verticalPoint_im _ _]; linarith) hnz
  have hd₀ : 0 ≤ 1 / δ := by positivity
  have hqδ : 1 ≤ q * (1 + 1 / δ) := hq.trans
    (le_mul_of_one_le_right (zero_le_one.trans hq) (le_add_of_nonneg_right hd₀))
  calc
    _ ≤ ‖logDeriv (entireDirichletL χ) z‖ + 1 := h₀
    _ ≤ D * (B * q) * (1 + 1 / δ) + 1 :=
      by exact add_le_add_left (hlz.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog hD) (by positivity))) 1
    _ ≤ (D * B + 1) * q * (1 + 1 / δ) := by linarith

/-- There are arbitrarily high and low horizontal contours free of singularities, with
uniform quadratic growth of the logarithmic derivative on each such segment. -/
theorem exists_good_horizontal_edges {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℝ, 4 ≤ |k| → ∃ t ∈ Icc k (k + 1),
      ∀ x ∈ Icc a 2, dirichletOrder χ (verticalPoint x t) = 0 ∧
        ‖logDeriv χ.LFunction (verticalPoint x t)‖ ≤ C * (2 + |t|) ^ 2 := by
  obtain ⟨ε, hε, hchoose⟩ := exists_dirichlet_height_inverse_log_separated hχ
  obtain ⟨B, hB, hb⟩ := exists_norm_logDeriv_left_horizontal hχ a
  obtain ⟨D, hD, hd⟩ := exists_norm_logDeriv_near_critical hχ
  let C := B * (3 + |a|) + D * (1 + 2 / ε)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun k hk => ?_⟩
  obtain ⟨t, ht, hsep⟩ := hchoose (min a 0) 2 k (by linarith)
  have hkt : |k - t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hkk : |k| ≤ |t| + 1 := by
    have hl := abs_add_le (k - t) t
    rw [sub_add_cancel] at hl
    linarith
  have ht₀ : 3 ≤ |t| := by linarith
  let δ := ε / Real.log (2 + |k|)
  have hlog₀ : 0 < Real.log (2 + |k|) := Real.log_pos (by linarith)
  have hδ : 0 < δ := div_pos hε hlog₀
  let q := 2 + |t|
  have hq : 1 ≤ q := by dsimp only [q]; linarith
  have hqa : 0 ≤ q := zero_le_one.trans hq
  refine ⟨t, ht, fun x hx => ⟨?_, ?_⟩⟩
  · by_contra h
    have h' := hsep (verticalPoint x t) (by
      rw [verticalPoint_re]
      exact ⟨(min_le_left a 0).trans hx.1, hx.2⟩) h
    rw [verticalPoint_im, sub_self, abs_zero] at h'
    exact hδ.not_ge h'
  · rcases le_or_gt x (-1 / 4) with hxl | hxr
    · have h := hb (verticalPoint x t) (by simpa only [verticalPoint_re] using hx.1)
        (by simpa only [verticalPoint_re] using hxl) (by rw [verticalPoint_im]; linarith)
      have hxabs : |x| ≤ |a| + 2 :=
        abs_le.mpr ⟨by linarith [hx.1, neg_abs_le a], by linarith [hx.2, abs_nonneg a]⟩
      have hzabs := norm_verticalPoint_le_abs x t
      have hh : 1 + ‖verticalPoint x t‖ ≤ (3 + |a|) * q ^ 2 := by
        have h₁ : 1 + ‖verticalPoint x t‖ ≤ (3 + |a|) + |t| := by linarith
        have h₂ : (3 + |a|) + |t| ≤ (3 + |a|) * q := by
          dsimp only [q]
          nlinarith [mul_nonneg (abs_nonneg a) (abs_nonneg t)]
        exact h₁.trans (h₂.trans (by gcongr; nlinarith))
      exact h.trans ((mul_le_mul_of_nonneg_left hh hB).trans (by
        rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg q)
        dsimp only [C]
        exact le_add_of_nonneg_right (by positivity)))
    · have hb₁ : 1 + 1 / δ ≤ (1 + 2 / ε) * q := by
        have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 + |k|)
        have h' : Real.log (2 + |k|) ≤ 2 * q := by dsimp only [q]; linarith
        have h'' := div_le_div_of_nonneg_right h' hε.le
        change 1 + 1 / (ε / Real.log (2 + |k|)) ≤ _
        rw [one_div_div]
        rw [mul_comm (1 + 2 / ε) q, mul_add, mul_one]
        exact add_le_add hq (by rwa [show q * (2 / ε) = (2 * q) / ε by ring])
      have he := hd ht₀ ⟨hxr.le, hx.2⟩ hδ (fun u hu ho =>
        hsep u ⟨(min_le_right a 0).trans hu.1.le, hu.2.le.trans (by norm_num)⟩ ho)
      apply he.trans
      change D * q * (1 + 1 / δ) ≤ _
      calc
        _ ≤ D * q * ((1 + 2 / ε) * q) := mul_le_mul_of_nonneg_left hb₁ (mul_nonneg hD hqa)
        _ = D * (1 + 2 / ε) * q ^ 2 := by ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg q)
          dsimp only [C]
          exact le_add_of_nonneg_left (by positivity)

/-- The contribution of a horizontal contour, with the real coordinate traversed from
left to right. -/
noncomputable def horizontalContourIntegral {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : ℝ → ℝ) (a t : ℝ) : ℂ :=
  ∫ x in a..2, (-logDeriv χ.LFunction (verticalPoint x t)) * laplaceTransform h (verticalPoint x t)

private theorem tendsto_horizontalContourIntegral_zero_of_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {h : ℝ → ℝ} (hs : ContDiff ℝ ∞ h)
    {b₁ b₂ a : ℝ} (hab : tsupport h ⊆ Icc b₁ b₂) (ha : a ≤ 2)
    {ι : Type*} {l : Filter ι} {t : ι → ℝ} (ht : Tendsto (fun n => |t n|) l atTop)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n, ∀ x ∈ Icc a 2,
      ‖logDeriv χ.LFunction (verticalPoint x (t n))‖ ≤ C * (2 + |t n|) ^ 2) :
    Tendsto (fun i => horizontalContourIntegral χ h a (t i)) l (𝓝 0) := by
  let A := (∫ x : ℝ, ‖h x‖) + (∫ x : ℝ, ‖iteratedDeriv 4 h x‖)
  have hA : 0 ≤ A :=
    by exact add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  let M := A * Real.exp ((|a| + 2) * (|b₁| + |b₂|))
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hLap (s x : ℝ) (hx : x ∈ Icc a 2) :
      ‖laplaceTransform h (verticalPoint x s)‖ ≤ M / (1 + |s| ^ 4) := by
    have hxabs : |x| ≤ |a| + 2 :=
      abs_le.mpr ⟨by linarith [hx.1, neg_abs_le a], by linarith [hx.2, abs_nonneg a]⟩
    have he (b : ℝ) (habs : |b| ≤ |b₁| + |b₂|) : x * b ≤ (|a| + 2) * (|b₁| + |b₂|) :=
      (le_abs_self _).trans (by
        rw [abs_mul]
        exact mul_le_mul hxabs habs (abs_nonneg b) (by positivity))
    have hmain := laplaceTransform_contour_bound hs hab 4 (verticalPoint x s)
    rw [verticalPoint_im, verticalPoint_re] at hmain
    apply (le_div_iff₀ (by positivity)).mpr
    rw [mul_comm]
    exact hmain.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (max_le (he b₁ (le_add_of_nonneg_right (abs_nonneg _)))
        (he b₂ (le_add_of_nonneg_left (abs_nonneg _))))) hA)
  let D := (2 - a) * C * M
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (sub_nonneg.mpr ha) hC) hM
  have hInt (n : ι) : ‖horizontalContourIntegral χ h a (t n)‖ ≤
      D * ((2 + |t n|) ^ 2 / (1 + |t n| ^ 4)) := by
    unfold horizontalContourIntegral
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := 2) (C := (C * (2 + |t n|) ^ 2) * (M / (1 + |t n| ^ 4)))
      (f := fun x => (-logDeriv χ.LFunction (verticalPoint x (t n))) *
        laplaceTransform h (verticalPoint x (t n))) (by
      intro x hx
      rw [uIoc_of_le ha] at hx
      have hx' := Ioc_subset_Icc_self hx
      rw [norm_mul, norm_neg]
      exact mul_le_mul (hb n x hx') (hLap _ x hx') (norm_nonneg _) (by positivity))
    refine h.trans_eq ?_
    rw [abs_of_nonneg (sub_nonneg.mpr ha)]
    dsimp only [D]
    ring
  have hdec (y : ℝ) (hy : 2 ≤ y) : (2 + y) ^ 2 / (1 + y ^ 4) ≤ 4 / y ^ 2 := by
    have hy₀ : 0 < y := (by norm_num : (0 : ℝ) < 2).trans_le hy
    calc
      _ ≤ (2 * y) ^ 2 / (1 + y ^ 4) := by gcongr; linarith
      _ ≤ (2 * y) ^ 2 / y ^ 4 := div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hy₀ _) (by linarith)
      _ = _ := by field_simp [hy₀.ne']; ring
  have hlim : Tendsto (fun n => (D * 4) / |t n| ^ 2) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp ht)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [ht.eventually_ge_atTop 2] with n hn
  exact (hInt n).trans (by rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left (hdec _ hn) hD)

/-- The horizontal integrals vanish as the two selected heights go to opposite infinities,
with every point of both segments regular. -/
theorem exists_horizontalContour_vanishing {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) {a : ℝ} (ha : a ≤ 2) :
    ∃ c d : ℕ → ℝ, Tendsto c atTop atBot ∧ Tendsto d atTop atTop ∧
      (∀ n, c n < 0 ∧ 0 < d n) ∧
      (∀ n, ∀ x ∈ Icc a 2, dirichletOrder χ (verticalPoint x (c n)) = 0 ∧
        dirichletOrder χ (verticalPoint x (d n)) = 0) ∧
      ∀ {h : ℝ → ℝ}, ContDiff ℝ ∞ h → ∀ {b₁ b₂ : ℝ}, tsupport h ⊆ Icc b₁ b₂ →
        Tendsto (fun n => horizontalContourIntegral χ h a (c n)) atTop (𝓝 0) ∧
        Tendsto (fun n => horizontalContourIntegral χ h a (d n)) atTop (𝓝 0) := by
  obtain ⟨C, hC, h⟩ := exists_good_horizontal_edges hχ a
  choose c hc hc' using fun n : ℕ => h (-(n : ℝ) - 5) (by
    rw [abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) n] : -(n : ℝ) - 5 ≤ 0)]
    linarith [Nat.cast_nonneg (α := ℝ) n])
  choose d hd hd' using fun n : ℕ => h ((n : ℝ) + 4) (by
    rw [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 4)]
    linarith [Nat.cast_nonneg (α := ℝ) n])
  have hc₀ : Tendsto c atTop atBot := by
    refine tendsto_atBot.2 fun b => ?_
    obtain ⟨j, hj⟩ := exists_nat_ge (-b)
    filter_upwards [eventually_ge_atTop j] with n hn
    linarith [(hc n).2, show (j : ℝ) ≤ n by exact_mod_cast hn]
  have hd₀ : Tendsto d atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    obtain ⟨j, hj⟩ := exists_nat_ge b
    filter_upwards [eventually_ge_atTop j] with n hn
    linarith [(hd n).1, show (j : ℝ) ≤ n by exact_mod_cast hn]
  refine ⟨c, d, hc₀, hd₀, fun n => ⟨?_, ?_⟩, fun n x hx => ⟨(hc' n x hx).1, (hd' n x hx).1⟩, ?_⟩
  · linarith [(hc n).2, Nat.cast_nonneg (α := ℝ) n]
  · linarith [(hd n).1, Nat.cast_nonneg (α := ℝ) n]
  · intro h hs b₁ b₂ hab
    exact ⟨tendsto_horizontalContourIntegral_zero_of_bound χ hs hab ha
      (tendsto_abs_atBot_atTop.comp hc₀) hC (fun n x hx => (hc' n x hx).2),
      tendsto_horizontalContourIntegral_zero_of_bound χ hs hab ha
      (tendsto_abs_atTop_atTop.comp hd₀) hC (fun n x hx => (hd' n x hx).2)⟩

end GoldbachR581
end

-- R581 LeftContour
section
public section

open Complex Filter Set MeasureTheory
open scoped ContDiff Topology Classical

namespace GoldbachR581

/-- A linear bound in the complex coordinate for the logarithmic derivative on all the negative
half-integer vertical lines. Polynomial growth of this size suffices for the contour shift. -/
theorem norm_logDeriv_dirichletL_le_linear_on_left_lines {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (z : ℂ), z.re = -((m : ℝ) + 1 / 2) →
      ‖logDeriv χ.LFunction z‖ ≤ C * (1 + ‖z‖) := by
  obtain ⟨A, hA, hχb⟩ := norm_logDeriv_dirichletL_left_le_right_digamma hχ
  obtain ⟨B, hB, hψ⟩ := norm_digamma_le_linear_of_half_le_re
  refine ⟨A + 3 * B, by positivity, fun m z hz => ?_⟩
  have h := hχb m z hz
  let e : ℂ := if χ.Even then 0 else 1
  let e' : ℂ := if χ⁻¹.Even then 0 else 1
  let u : ℂ := (z + e) / 2
  let v : ℂ := (1 - z + e') / 2
  change 3 / 4 ≤ (1 - u).re ∧ 3 / 4 ≤ v.re ∧
    ‖logDeriv χ.LFunction z‖ ≤ A + (‖digamma (1 - u)‖ + ‖digamma v‖) / 2 at h
  have he : ‖e‖ ≤ 1 := by dsimp only [e]; split_ifs <;> simp
  have he' : ‖e'‖ ≤ 1 := by dsimp only [e']; split_ifs <;> simp
  have hu : ‖1 - u‖ ≤ 2 + ‖z‖ / 2 := by
    have h := norm_sub_le (1 : ℂ) u
    have hu₀ : ‖u‖ ≤ (‖z‖ + ‖e‖) / 2 := by
      dsimp only [u]
      rw [norm_div, norm_ofNat]
      exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    simp only [norm_one] at h
    linarith
  have hv : ‖v‖ ≤ 2 + ‖z‖ / 2 := by
    have h := norm_sub_le (1 : ℂ) z
    have hv₀ : ‖v‖ ≤ (‖1 - z‖ + ‖e'‖) / 2 := by
      dsimp only [v]
      rw [norm_div, norm_ofNat]
      exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    simp only [norm_one] at h
    linarith
  have hψ₁ := hψ (1 - u) (by linarith [h.1])
  have hψ₂ := hψ v (by linarith [h.2.1])
  nlinarith [h.2.2, mul_le_mul_of_nonneg_left hu hB, mul_le_mul_of_nonneg_left hv hB, norm_nonneg z]

/-- The integrand on `Re z = -(m+1/2)`, parametrized by its imaginary part. -/
noncomputable def leftContourIntegrand {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : ℝ → ℝ) (m : ℕ) (t : ℝ) : ℂ :=
  let z := verticalPoint (-((m : ℝ) + 1 / 2)) t
  (-logDeriv χ.LFunction z) * laplaceTransform h z

private theorem quartic_left_domination (t : ℝ) :
    (1 + |t|) / (1 + |t| ^ 4) ≤ 4 * (1 + t ^ 2)⁻¹ := by
  let x := |t|
  have hx : 0 ≤ x := abs_nonneg _
  have he : t ^ 2 = x ^ 2 := (sq_abs _).symm
  rw [he, ← div_eq_mul_inv]
  change (1 + x) / (1 + x ^ 4) ≤ 4 / (1 + x ^ 2)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rcases le_total x 1 with h | h
  · have h₂ : x ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hx h 2
    have hb : (1 + x) * (1 + x ^ 2) ≤ 2 * 2 := by gcongr <;> linarith
    nlinarith [pow_nonneg hx 4]
  · have h₂ : 1 ≤ x ^ 2 := one_le_pow₀ h
    have hb : (1 + x) * (1 + x ^ 2) ≤ (2 * x) * (2 * x ^ 2) := by gcongr <;> linarith
    have hp : x ^ 3 ≤ x ^ 4 := pow_le_pow_right₀ h (by norm_num : 3 ≤ 4)
    nlinarith

private theorem continuous_leftContourIntegrand {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) {h : ℝ → ℝ} (hh : Continuous h) (hc : HasCompactSupport h) (m : ℕ) :
    Continuous (leftContourIntegrand χ h m) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  let z := verticalPoint (-((m : ℝ) + 1 / 2)) t
  have hz : z.re = -((m : ℝ) + 1 / 2) := verticalPoint_re _ _
  have ho := dirichletOrder_eq_zero_on_left_halfInteger hχ m hz
  have horder : meromorphicOrderAt χ.LFunction z = 0 := by
    simpa only [ho, WithTop.coe_zero] using (dirichletOrder_spec χ z).symm
  obtain ⟨ha, hn⟩ := analytic_ne_zero_of_dirichlet_order_zero horder
  have hl : AnalyticAt ℂ (logDeriv χ.LFunction) z := ha.deriv.div ha hn
  have hcont : ContinuousAt (fun w => (-logDeriv χ.LFunction w) * laplaceTransform h w) z :=
    hl.continuousAt.neg.mul (analyticAt_laplaceTransform hh hc z).continuousAt
  have hline : Continuous (fun t : ℝ => verticalPoint (-((m : ℝ) + 1 / 2)) t) := by
    unfold verticalPoint
    fun_prop
  exact hcont.comp' (f := fun t : ℝ => verticalPoint (-((m : ℝ) + 1 / 2)) t) hline.continuousAt

/-- The left integrals are absolutely integrable, with a bound of a linear factor times the
exponential dictated by the lower edge of the support of the window. -/
theorem leftContourIntegral_exponential_bound {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) {h : ℝ → ℝ} (hs : ContDiff ℝ ∞ h) {a b : ℝ} (hab : tsupport h ⊆ Icc a b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ,
      Integrable (leftContourIntegrand χ h m) ∧
        ‖∫ t : ℝ, leftContourIntegrand χ h m t‖ ≤
          C * (1 + (m : ℝ)) * Real.exp (-(a * ((m : ℝ) + 1 / 2))) := by
  obtain ⟨C, hC, hχb⟩ := norm_logDeriv_dirichletL_le_linear_on_left_lines hχ
  let B : ℝ := (∫ t : ℝ, ‖h t‖) + (∫ t : ℝ, ‖iteratedDeriv 4 h t‖)
  have hB : 0 ≤ B := add_nonneg (integral_nonneg fun _ => norm_nonneg _)
    (integral_nonneg fun _ => norm_nonneg _)
  let K : ℝ := ∫ t : ℝ, (1 + t ^ 2)⁻¹
  have hK : 0 ≤ K := integral_nonneg fun _ => by positivity
  have hc : HasCompactSupport h := isCompact_Icc.of_isClosed_subset isClosed_closure hab
  refine ⟨8 * C * B * K, by positivity, fun m => ?_⟩
  let R : ℝ := (m : ℝ) + 1 / 2
  let Q : ℝ := 8 * C * B * (1 + (m : ℝ)) * Real.exp (-(a * R))
  have hR : 0 < R := by dsimp [R]; positivity
  have hm : 0 ≤ (m : ℝ) := by positivity
  have hdom : Integrable (fun t : ℝ => Q * (1 + t ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul Q
  have hpoint (t : ℝ) : ‖leftContourIntegrand χ h m t‖ ≤ Q * (1 + t ^ 2)⁻¹ := by
    let z := verticalPoint (-R) t
    have hre : z.re = -R := verticalPoint_re _ _
    have him : z.im = t := verticalPoint_im _ _
    have hnorm : ‖z‖ ≤ R + |t| := by
      simpa only [hre, him, abs_neg, abs_of_pos hR] using Complex.norm_le_abs_re_add_abs_im z
    have hsize : 1 + ‖z‖ ≤ 2 * (1 + (m : ℝ)) * (1 + |t|) := by
      have hx := abs_nonneg t
      dsimp [R] at hnorm
      nlinarith [mul_nonneg hm hx]
    have hL := (hχb m z hre).trans (mul_le_mul_of_nonneg_left hsize hC)
    have hab' : tsupport h ⊆ Icc a (max a b) :=
      fun t ht => ⟨(hab ht).1, (hab ht).2.trans (le_max_right _ _)⟩
    have hH := laplaceTransform_contour_bound hs hab' 4 z
    have hmax : max (z.re * a) (z.re * max a b) = -(a * R) := by
      rw [max_eq_left (mul_le_mul_of_nonpos_left (le_max_left _ _) (by rw [hre]; exact neg_nonpos.mpr hR.le)), hre]
      ring
    change ‖(-logDeriv χ.LFunction z) * laplaceTransform h z‖ ≤ _
    rw [norm_mul, norm_neg]
    rw [him, hmax] at hH
    have hH' : ‖laplaceTransform h z‖ ≤ B * Real.exp (-(a * R)) / (1 + |t| ^ 4) := by
      apply (le_div_iff₀ (by positivity : 0 < 1 + |t| ^ 4)).mpr
      simpa only [mul_comm (‖laplaceTransform h z‖)] using hH
    calc
      _ ≤ (C * (2 * (1 + (m : ℝ)) * (1 + |t|))) *
          (B * Real.exp (-(a * R)) / (1 + |t| ^ 4)) :=
        mul_le_mul hL hH' (norm_nonneg _) (by positivity)
      _ = (2 * C * B * (1 + (m : ℝ)) * Real.exp (-(a * R))) * ((1 + |t|) / (1 + |t| ^ 4)) := by ring
      _ ≤ (2 * C * B * (1 + (m : ℝ)) * Real.exp (-(a * R))) * (4 * (1 + t ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (quartic_left_domination t) (by positivity)
      _ = _ := by unfold Q; ring
  refine ⟨hdom.mono' (continuous_leftContourIntegrand hχ hs.continuous hc m).aestronglyMeasurable
    (Eventually.of_forall hpoint), ?_⟩
  refine (norm_integral_le_of_norm_le hdom (Eventually.of_forall hpoint)).trans_eq ?_
  rw [integral_const_mul]
  change Q * K = _
  dsimp only [Q, R]
  ring

/-- The entire vertical integral on the left edge tends to zero along the negative
half-integer contours of R581. -/
theorem tendsto_leftContourIntegral_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) {h : ℝ → ℝ} (hs : ContDiff ℝ ∞ h) {a b : ℝ} (hab : tsupport h ⊆ Icc a b)
    (ha : 0 < a) : Tendsto (fun m : ℕ => ∫ t : ℝ, leftContourIntegrand χ h m t) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := leftContourIntegral_exponential_bound hχ hs hab
  apply squeeze_zero_norm (fun m => (hb m).2)
  have h₀ := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 a ha
  have h₁ := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha
  have hsum : Tendsto (fun x : ℝ => Real.exp (-a * x) + x * Real.exp (-a * x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, Real.rpow_one, one_mul, add_zero] using h₀.add h₁
  have ht := ((hsum.comp tendsto_natCast_atTop_atTop).const_mul (C * Real.exp (-(a / 2))))
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards with m
  rw [show -(a * ((m : ℝ) + 1 / 2)) = -(a / 2) + -a * (m : ℝ) by ring, Real.exp_add]
  simp only [Function.comp_apply]
  ring

/-- Left-edge vanishing for the precise primitive Mangoldt integral used in R581. -/
theorem tendsto_windowedMangoldt_primitive_leftContourIntegral_zero {N j : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hj : 0 < j) {A : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ A) (hc : ∀ u, 13 / 10 ≤ u → A u = 0) :
    let _ : NeZero (χ ^ j).conductor := ⟨(χ ^ j).conductor_ne_zero⟩
    Tendsto (fun m : ℕ => ∫ t : ℝ,
      leftContourIntegrand (χ ^ j).primitiveCharacter (mangoldtWeight N j A) m t) atTop (𝓝 0) := by
  have : NeZero (χ ^ j).conductor := ⟨(χ ^ j).conductor_ne_zero⟩
  exact tendsto_leftContourIntegral_zero (χ ^ j).primitiveCharacter_isPrimitive
    (mangoldtWeight_contDiff hj.ne' hs) (mangoldtWeight_tsupport (NeZero.pos N) hj hc)
    (Real.log_pos (by norm_num))

end GoldbachR581
end

-- R581 ExplicitFormula
section
open Complex DirichletCharacter Filter MeasureTheory Set
open scoped ArithmeticFunction ArithmeticFunction.Moebius Classical ContDiff Topology

namespace GoldbachR581

private theorem dirichletOrder_right_edge {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z : ℂ} (hz : z.re = 2) : dirichletOrder χ z = 0 := by
  apply dirichletOrder_eq_zero_of_one_le_re χ (by rw [hz]; norm_num)
  exact Or.inl fun he => by simp [he] at hz

private theorem integrable_right_edge {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {h : ℝ → ℝ} (hs : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    Integrable (fun t : ℝ =>
      (-logDeriv χ.LFunction (verticalPoint 2 t)) * laplaceTransform h (verticalPoint 2 t)) := by
  obtain ⟨C, hC, hb⟩ := norm_logDeriv_dirichletL_le_of_re_ge χ (σ := 2) (by norm_num)
  refine ((integrable_laplace_vertical hs hc 2).norm.const_mul C).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro t
    let z := verticalPoint 2 t
    have ho : dirichletOrder χ z = 0 := dirichletOrder_right_edge χ (verticalPoint_re 2 t)
    have ho' : meromorphicOrderAt χ.LFunction z = 0 := by
      simpa only [ho, WithTop.coe_zero] using (dirichletOrder_spec χ z).symm
    obtain ⟨hA, hn⟩ := analytic_ne_zero_of_dirichlet_order_zero ho'
    have hA' : AnalyticAt ℂ (logDeriv χ.LFunction) z := hA.deriv.div hA hn
    have hcont := hA'.continuousAt.neg.mul (analyticAt_laplaceTransform hs.continuous hc z).continuousAt
    have hv : Continuous (verticalPoint 2) := by unfold verticalPoint; fun_prop
    exact hcont.comp' (f := verticalPoint 2) hv.continuousAt
  · filter_upwards with t
    rw [norm_mul, norm_neg]
    exact mul_le_mul_of_nonneg_right (hb _ (verticalPoint_re 2 t).ge) (norm_nonneg _)

private theorem mangoldtSum_sub_left_eq_zero_sums {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {h : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ h) {a b : ℝ} (hab : tsupport h ⊆ Icc a b) (m : ℕ) :
    mangoldtSum χ h - (↑(2 * Real.pi) : ℂ)⁻¹ * ∫ t : ℝ, leftContourIntegrand χ h m t =
      (if N = 1 then laplaceTransform h 1 else 0) -
      (∑ n ∈ dirichletTrivialIndices χ (-((m : ℝ) + 1 / 2)),
        laplaceTransform h (dirichletTrivialZero χ n)) -
      ∑' z, dirichletCriticalZeroTerm χ (laplaceTransform h) z := by
  let x₀ := -((m : ℝ) + 1 / 2)
  have hx : x₀ ≤ 0 := by dsimp only [x₀]; exact neg_nonpos.mpr (by positivity)
  have hx₂ : x₀ < 2 := hx.trans_lt (by norm_num)
  have hcs : HasCompactSupport h := isCompact_Icc.of_isClosed_subset isClosed_closure hab
  obtain ⟨c, d, hc, hd, hsign, hregular, hvan⟩ := exists_horizontalContour_vanishing hχ hx₂.le
  obtain ⟨_, _, hleft⟩ := leftContourIntegral_exponential_bound hχ hs hab
  let W := laplaceTransform h
  let F := fun z => (-logDeriv χ.LFunction z) * W z
  let U := ∫ t : ℝ, F (verticalPoint 2 t)
  let V := ∫ t : ℝ, leftContourIntegrand χ h m t
  let P := (↑(2 * Real.pi) : ℂ)
  let K := (if N = 1 then W 1 else 0) -
    ∑ n ∈ dirichletTrivialIndices χ x₀, W (dirichletTrivialZero χ n)
  let Z := ∑' z, dirichletCriticalZeroTerm χ W z
  have hbd (n : ℕ) (z : ℂ) (hz : z ∈ Icc x₀ 2 ×ℂ Icc (c n) (d n)) (ho : dirichletOrder χ z ≠ 0) :
      z ∈ Ioo x₀ 2 ×ℂ Ioo (c n) (d n) := by
    obtain ⟨hre, him⟩ := mem_reProdIm.mp hz
    have e₀ : verticalPoint z.re z.im = z := Complex.ext (verticalPoint_re _ _) (verticalPoint_im _ _)
    have hzl : z.re ≠ x₀ := fun e => ho (dirichletOrder_eq_zero_on_left_halfInteger hχ m e)
    have hzr : z.re ≠ 2 := fun e => ho (dirichletOrder_right_edge χ e)
    have hzb : z.im ≠ c n := by
      intro e
      have h := (hregular n z.re hre).1
      rw [← e, e₀] at h
      exact ho h
    have hzt : z.im ≠ d n := by
      intro e
      have h := (hregular n z.re hre).2
      rw [← e, e₀] at h
      exact ho h
    exact mem_reProdIm.mpr
      ⟨⟨lt_of_le_of_ne hre.1 hzl.symm, lt_of_le_of_ne hre.2 hzr⟩,
        ⟨lt_of_le_of_ne him.1 hzb.symm, lt_of_le_of_ne him.2 hzt⟩⟩
  have hRect (n : ℕ) : rectangleIntegral F x₀ 2 (c n) (d n) =
      P * I * (K - ∑ z ∈ dirichletRectangleSingularities χ x₀ 2 (c n) (d n),
        dirichletCriticalZeroTerm χ W z) := by
    have h := rectangleIntegral_dirichletL_laplace χ hs.continuous hcs hx₂
      ((hsign n).1.trans (hsign n).2) (hbd n)
    exact h.trans (congrArg (fun r => P * I * r)
      (dirichletRectangle_residueSum_eq hχ W hx (hsign n).1.le (hsign n).2.le))
  have hCrit := tendsto_dirichletCriticalZero_sum_rectangles χ
    (summable_norm_laplace_dirichletCriticalZero χ hs hab).of_norm hx (by norm_num : (1 : ℝ) ≤ 2) hc hd
  have hres : Tendsto (fun n => rectangleIntegral F x₀ 2 (c n) (d n)) atTop (𝓝 (P * I * (K - Z))) :=
    ((tendsto_const_nhds.sub hCrit).const_mul (P * I)).congr fun n => (hRect n).symm
  have hR := intervalIntegral_tendsto_integral (integrable_right_edge χ hs hcs) hc hd
  have hL := intervalIntegral_tendsto_integral (hleft m).1 hc hd
  have hhor := hvan hs hab
  have hcont : Tendsto (fun n => rectangleIntegral F x₀ 2 (c n) (d n)) atTop (𝓝 (I * U - I * V)) := by
    dsimp only [U, V]
    simpa only [rectangleIntegral, horizontalContourIntegral, F, W, x₀, leftContourIntegrand,
      zero_sub, sub_zero, zero_add] using
      (((hhor.1.sub hhor.2).add (hR.const_mul I)).sub (hL.const_mul I))
  have hUV : U - V = P * (K - Z) := by
    apply mul_left_cancel₀ I_ne_zero
    calc
      I * (U - V) = I * U - I * V := mul_sub _ _ _
      _ = P * I * (K - Z) := tendsto_nhds_unique hcont hres
      _ = _ := by ring
  have hP : P ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  rw [mangoldtSum_eq_rightLine χ hs hcs (by norm_num : (1 : ℝ) < 2)]
  simp_rw [mul_comm (laplaceTransform h _)]
  change P⁻¹ * U - P⁻¹ * V = K - Z
  rw [← mul_sub, hUV, ← mul_assoc, inv_mul_cancel₀ hP, one_mul]

/-- The exact explicit formula for a primitive Dirichlet character and a smooth weight
with compact logarithmic support bounded away from zero. Both zero sums are absolute. -/
theorem mangoldtSum_eq_full_zero_sums {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {h : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ h) {a b : ℝ} (hab : tsupport h ⊆ Icc a b) (ha : 0 < a) :
    mangoldtSum χ h = (if N = 1 then laplaceTransform h 1 else 0) -
      (∑' n, laplaceTransform h (dirichletTrivialZero χ n)) -
      ∑' z, dirichletCriticalZeroTerm χ (laplaceTransform h) z := by
  have hcs : HasCompactSupport h := isCompact_Icc.of_isClosed_subset isClosed_closure hab
  have hT := (summable_norm_laplace_dirichletTrivialZero χ
    (hs.continuous.integrable_of_hasCompactSupport hcs)
    (subset_closure.trans (hab.trans Icc_subset_Ici_self)) ha).of_norm.hasSum.comp
      (tendsto_dirichletTrivialIndices_atTop hχ)
  have hL := tendsto_leftContourIntegral_zero hχ hs hab ha
  have h₁ := (tendsto_const_nhds (x := mangoldtSum χ h)).sub (hL.const_mul (↑(2 * Real.pi) : ℂ)⁻¹)
  rw [mul_zero, sub_zero] at h₁
  have h₂ := ((tendsto_const_nhds (x := if N = 1 then laplaceTransform h 1 else 0)).sub hT).sub
    (tendsto_const_nhds (x := ∑' z, dirichletCriticalZeroTerm χ (laplaceTransform h) z))
  exact tendsto_nhds_unique h₁ (h₂.congr fun m => (mangoldtSum_sub_left_eq_zero_sums hχ hs hab m).symm)

end GoldbachR581
end

section
open Complex DirichletCharacter Filter MeasureTheory Set
open scoped FourierTransform InnerProductSpace ArithmeticFunction Classical Topology

namespace GoldbachR581

def HasLaplaceCubicDecay (h : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
    ‖laplaceTransform h z‖ ≤
      C * Real.exp (max (z.re * a) (z.re * b)) / (1 + |z.im| ^ 3)

private theorem cubic_left_domination (t : ℝ) :
    (1 + |t|) / (1 + |t| ^ 3) ≤ 4 * (1 + t ^ 2)⁻¹ := by
  let x := |t|
  have hx : 0 ≤ x := abs_nonneg _
  rw [show t ^ 2 = x ^ 2 from (sq_abs _).symm, ← div_eq_mul_inv]
  change (1 + x) / (1 + x ^ 3) ≤ 4 / (1 + x ^ 2)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  by_cases h : x ≤ 1
  · have h₂ : x ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hx h 2
    have hb : (1 + x) * (1 + x ^ 2) ≤ 2 * 2 := by gcongr <;> linarith
    nlinarith [pow_nonneg hx 3]
  · have h₁ : 1 ≤ x := le_of_not_ge h
    have h₂ : 1 ≤ x ^ 2 := one_le_pow₀ h₁
    have hb : (1 + x) * (1 + x ^ 2) ≤ (2 * x) * (2 * x ^ 2) := by gcongr <;> linarith
    nlinarith

private theorem integrable_laplace_vertical_of_cubic {h : ℝ → ℝ} {a b : ℝ}
    (hh : Continuous h) (hc : HasCompactSupport h) (σ : ℝ)
    (hdecay : HasLaplaceCubicDecay h a b) :
    Integrable (fun t : ℝ => laplaceTransform h (verticalPoint σ t)) := by
  obtain ⟨C, hC, hbound⟩ := hdecay
  let A := C * Real.exp (max (σ * a) (σ * b))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine (integrable_inv_one_add_sq.const_mul (4 * A)).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    exact (continuous_iff_continuousAt.mpr fun z =>
      (analyticAt_laplaceTransform hh hc z).continuousAt).comp (by unfold verticalPoint; fun_prop)
  · filter_upwards with t
    refine (hbound _).trans ?_
    rw [verticalPoint_re, verticalPoint_im]
    change A / (1 + |t| ^ 3) ≤ 4 * A * (1 + t ^ 2)⁻¹
    rw [mul_comm (4 : ℝ), mul_assoc, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ hA
    rw [inv_eq_one_div (1 + |t| ^ 3)]
    exact (div_le_div_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg t)) (by positivity)).trans
      (cubic_left_domination t)

theorem laplace_inversion_of_integrable {h : ℝ → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    (σ : ℝ) (hVertical : Integrable (fun t : ℝ => laplaceTransform h (verticalPoint σ t)))
    (s : ℝ) : (h s : ℂ) = (↑(2 * Real.pi) : ℂ)⁻¹ *
      ∫ t : ℝ, laplaceTransform h (verticalPoint σ t) *
        Complex.exp (-(verticalPoint σ t) * (s : ℂ)) := by
  let f := tiltedWeight h σ
  let F : ℝ → ℂ := fun t => laplaceTransform h (verticalPoint σ t) *
    Complex.exp (-(verticalPoint σ t) * (s : ℂ))
  have hπ : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hval : f s = (h s : ℂ) * Complex.exp ((σ : ℂ) * (s : ℂ)) := rfl
  have hcont : Continuous f := by
    unfold f tiltedWeight
    fun_prop
  have hsupport : HasCompactSupport f := by
    have hc' : HasCompactSupport (fun s : ℝ => (h s : ℂ)) := by
      apply hc.mono
      intro t ht
      simpa [Function.mem_support] using ht
    exact hc'.mul_right
  have hπne : 2 * Real.pi ≠ 0 := hπ.ne'
  have hinvint : Integrable (𝓕⁻ f) := by
    have hscaled := (integrable_comp_mul_left_iff
      (fun t => laplaceTransform h (verticalPoint σ t)) hπne).mpr hVertical
    simpa only [laplace_fourierInv, f] using hscaled
  have hforward : Integrable (𝓕 f) := by
    apply (integrable_comp_mul_left_iff (𝓕 f) (show (-1 : ℝ) ≠ 0 by norm_num)).mp
    simpa only [neg_one_mul, ← Real.fourierInv_eq_fourier_neg] using hinvint
  have hinv : 𝓕 (𝓕⁻ f) s = f s :=
    (hcont.integrable_of_hasCompactSupport hsupport).fourier_fourierInv_eq hforward hcont.continuousAt
  calc
    (h s : ℂ) = Complex.exp (-(σ : ℂ) * (s : ℂ)) * f s := by
      rw [hval, neg_mul, Complex.exp_neg]
      have hne := Complex.exp_ne_zero ((σ : ℂ) * (s : ℂ))
      field_simp
    _ = ∫ t : ℝ, F (2 * Real.pi * t) := by
      rw [← hinv, Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      simp only [F, laplace_fourierInv, smul_eq_mul]
      rw [show -(verticalPoint σ (2 * Real.pi * t)) * (s : ℂ) =
          -(σ : ℂ) * (s : ℂ) + (↑(-2 * Real.pi * t * s) : ℂ) * Complex.I by
        simp only [verticalPoint, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
        ring, Complex.exp_add]
      ring
    _ = (↑(2 * Real.pi) : ℂ)⁻¹ * ∫ t : ℝ, F t := by
      rw [Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hπ), Complex.real_smul, Complex.ofReal_inv]

theorem mangoldtSum_eq_rightLine_of_integrable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {h : ℝ → ℝ}
    (hh : Continuous h) (hc : HasCompactSupport h) {σ : ℝ} (hσ : 1 < σ)
    (hVertical : Integrable (fun t : ℝ => laplaceTransform h (verticalPoint σ t))) :
    mangoldtSum χ h = (↑(2 * Real.pi) : ℂ)⁻¹ *
      ∫ t : ℝ, laplaceTransform h (verticalPoint σ t) * (-logDeriv χ.LFunction (verticalPoint σ t)) := by
  let a : ℕ → ℂ := fun n => χ (n : ZMod N) * (Λ n : ℂ)
  let H : ℝ → ℂ := fun t => laplaceTransform h (verticalPoint σ t)
  let F : ℕ → ℝ → ℂ := fun n t => H t * LSeries.term a (verticalPoint σ t) n
  have ha0 : a 0 = 0 := by simp [a]
  have hintegrable : Integrable H := hVertical
  have hnorm (n : ℕ) (t : ℝ) : ‖F n t‖ = ‖H t‖ * ‖LSeries.term a (σ : ℂ) n‖ := by
    simp only [F, norm_mul, LSeries.norm_term_eq, verticalPoint_re, Complex.ofReal_re]
  have hF (n : ℕ) : Integrable (F n) := by
    apply (hintegrable.norm.mul_const ‖LSeries.term a (σ : ℂ) n‖).mono'
    · apply hintegrable.aestronglyMeasurable.mul
      apply Continuous.aestronglyMeasurable
      simp_rw [dirichlet_term_exp ha0]
      unfold verticalPoint
      fun_prop
    · exact Filter.Eventually.of_forall fun t => (hnorm n t).le
  have hDirichlet : Summable fun n => ‖LSeries.term a (σ : ℂ) n‖ :=
    (show LSeriesSummable a (σ : ℂ) from χ.LSeriesSummable_twist_vonMangoldt (by simpa using hσ)).norm
  have hS : Summable fun n => ∫ t : ℝ, ‖F n t‖ := by
    simp_rw [hnorm, integral_mul_const]
    exact hDirichlet.mul_left _
  unfold mangoldtSum
  calc
    _ = ∑' n : ℕ, (↑(2 * Real.pi) : ℂ)⁻¹ * ∫ t : ℝ, F n t := by
      apply tsum_congr
      intro n
      change a n * (h (Real.log (n : ℝ)) : ℂ) = _
      rw [laplace_inversion_of_integrable hh hc σ hVertical (Real.log (n : ℝ)), ← mul_assoc, mul_comm (a n), mul_assoc,
        ← integral_const_mul]
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      simp only [F, H, dirichlet_term_exp ha0]
      ring
    _ = (↑(2 * Real.pi) : ℂ)⁻¹ * ∫ t : ℝ, ∑' n : ℕ, F n t := by
      rw [tsum_mul_left, integral_tsum_of_summable_integral_norm hF hS]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      simp only [F, tsum_mul_left, H]
      change _ * LSeries a (verticalPoint σ t) = _
      rw [twistedMangoldtLSeries_eq_neg_logDeriv χ (by simpa using hσ)]

theorem leftContourIntegral_exponential_bound_of_cubic {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) {h : ℝ → ℝ} (hh : Continuous h) {a b : ℝ} (hab : tsupport h ⊆ Icc a b) (hab₀ : a ≤ b)
    (hdecay : HasLaplaceCubicDecay h a b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ,
      Integrable (leftContourIntegrand χ h m) ∧
        ‖∫ t : ℝ, leftContourIntegrand χ h m t‖ ≤
          C * (1 + (m : ℝ)) * Real.exp (-(a * ((m : ℝ) + 1 / 2))) := by
  obtain ⟨C, hC, hχb⟩ := norm_logDeriv_dirichletL_le_linear_on_left_lines hχ
  obtain ⟨B, hB, hTransform⟩ := hdecay
  let K : ℝ := ∫ t : ℝ, (1 + t ^ 2)⁻¹
  have hK : 0 ≤ K := integral_nonneg fun _ => by positivity
  have hc : HasCompactSupport h := isCompact_Icc.of_isClosed_subset isClosed_closure hab
  refine ⟨8 * C * B * K, by positivity, fun m => ?_⟩
  let R : ℝ := (m : ℝ) + 1 / 2
  let Q : ℝ := 8 * C * B * (1 + (m : ℝ)) * Real.exp (-(a * R))
  have hR : 0 < R := by dsimp [R]; positivity
  have hm : 0 ≤ (m : ℝ) := by positivity
  have hdom : Integrable (fun t : ℝ => Q * (1 + t ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul Q
  have hpoint (t : ℝ) : ‖leftContourIntegrand χ h m t‖ ≤ Q * (1 + t ^ 2)⁻¹ := by
    let z := verticalPoint (-R) t
    have hre : z.re = -R := verticalPoint_re _ _
    have him : z.im = t := verticalPoint_im _ _
    have hnorm : ‖z‖ ≤ R + |t| := by
      simpa only [hre, him, abs_neg, abs_of_pos hR] using Complex.norm_le_abs_re_add_abs_im z
    have hsize : 1 + ‖z‖ ≤ 2 * (1 + (m : ℝ)) * (1 + |t|) := by
      have hx := abs_nonneg t
      dsimp [R] at hnorm
      nlinarith [mul_nonneg hm hx]
    have hL := (hχb m z hre).trans (mul_le_mul_of_nonneg_left hsize hC)
    have hH' : ‖laplaceTransform h z‖ ≤ B * Real.exp (-(a * R)) / (1 + |t| ^ 3) := by
      have hmax : max (z.re * a) (z.re * b) = -(a * R) := by
        rw [max_eq_left (mul_le_mul_of_nonpos_left hab₀ (by rw [hre]; exact neg_nonpos.mpr hR.le)), hre]
        ring
      simpa only [him, hmax] using hTransform z
    change ‖(-logDeriv χ.LFunction z) * laplaceTransform h z‖ ≤ _
    rw [norm_mul, norm_neg]
    calc
      _ ≤ (C * (2 * (1 + (m : ℝ)) * (1 + |t|))) *
          (B * Real.exp (-(a * R)) / (1 + |t| ^ 3)) :=
        mul_le_mul hL hH' (norm_nonneg _) (by positivity)
      _ = (2 * C * B * (1 + (m : ℝ)) * Real.exp (-(a * R))) * ((1 + |t|) / (1 + |t| ^ 3)) := by ring
      _ ≤ (2 * C * B * (1 + (m : ℝ)) * Real.exp (-(a * R))) * (4 * (1 + t ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (cubic_left_domination t) (by positivity)
      _ = _ := by unfold Q; ring
  refine ⟨hdom.mono' (continuous_leftContourIntegrand hχ hh hc m).aestronglyMeasurable
    (Eventually.of_forall hpoint), ?_⟩
  refine (norm_integral_le_of_norm_le hdom (Eventually.of_forall hpoint)).trans_eq ?_
  rw [integral_const_mul]
  change Q * K = _
  dsimp only [Q, R]
  ring

/-- The entire vertical integral on the left edge tends to zero along the negative
half-integer contours of R581. -/
theorem tendsto_leftContourIntegral_zero_of_cubic {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) {h : ℝ → ℝ} (hh : Continuous h) {a b : ℝ} (hab : tsupport h ⊆ Icc a b)
    (hab₀ : a ≤ b) (hdecay : HasLaplaceCubicDecay h a b) (ha : 0 < a) : Tendsto (fun m : ℕ => ∫ t : ℝ, leftContourIntegrand χ h m t) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := leftContourIntegral_exponential_bound_of_cubic hχ hh hab hab₀ hdecay
  apply squeeze_zero_norm (fun m => (hb m).2)
  have h₀ := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 a ha
  have h₁ := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha
  have hsum : Tendsto (fun x : ℝ => Real.exp (-a * x) + x * Real.exp (-a * x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, Real.rpow_one, one_mul, add_zero] using h₀.add h₁
  have ht := ((hsum.comp tendsto_natCast_atTop_atTop).const_mul (C * Real.exp (-(a / 2))))
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards with m
  rw [show -(a * ((m : ℝ) + 1 / 2)) = -(a / 2) + -a * (m : ℝ) by ring, Real.exp_add]
  simp only [Function.comp_apply]
  ring

private theorem tendsto_horizontalContourIntegral_zero_of_cubic {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {h : ℝ → ℝ}
    {b₁ b₂ a : ℝ} (hdecay : HasLaplaceCubicDecay h b₁ b₂) (ha : a ≤ 2)
    {ι : Type*} {l : Filter ι} {t : ι → ℝ} (ht : Tendsto (fun n => |t n|) l atTop)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n, ∀ x ∈ Icc a 2,
      ‖logDeriv χ.LFunction (verticalPoint x (t n))‖ ≤ C * (2 + |t n|) ^ 2) :
    Tendsto (fun i => horizontalContourIntegral χ h a (t i)) l (𝓝 0) := by
  obtain ⟨A, hA, hTransform⟩ := hdecay
  let M := A * Real.exp ((|a| + 2) * (|b₁| + |b₂|))
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hLap (s x : ℝ) (hx : x ∈ Icc a 2) :
      ‖laplaceTransform h (verticalPoint x s)‖ ≤ M / (1 + |s| ^ 3) := by
    have hxabs : |x| ≤ |a| + 2 :=
      abs_le.mpr ⟨by linarith [hx.1, neg_abs_le a], by linarith [hx.2, abs_nonneg a]⟩
    have he (b : ℝ) (habs : |b| ≤ |b₁| + |b₂|) : x * b ≤ (|a| + 2) * (|b₁| + |b₂|) :=
      (le_abs_self _).trans (by
        rw [abs_mul]
        exact mul_le_mul hxabs habs (abs_nonneg b) (by positivity))
    refine (hTransform _).trans ?_
    rw [verticalPoint_im, verticalPoint_re]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (max_le (he b₁ (le_add_of_nonneg_right (abs_nonneg _)))
        (he b₂ (le_add_of_nonneg_left (abs_nonneg _))))) hA) (by positivity)
  let D := (2 - a) * C * M
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (sub_nonneg.mpr ha) hC) hM
  have hInt (n : ι) : ‖horizontalContourIntegral χ h a (t n)‖ ≤
      D * ((2 + |t n|) ^ 2 / (1 + |t n| ^ 3)) := by
    unfold horizontalContourIntegral
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := 2) (C := (C * (2 + |t n|) ^ 2) * (M / (1 + |t n| ^ 3)))
      (f := fun x => (-logDeriv χ.LFunction (verticalPoint x (t n))) *
        laplaceTransform h (verticalPoint x (t n))) (by
      intro x hx
      rw [uIoc_of_le ha] at hx
      have hx' := Ioc_subset_Icc_self hx
      rw [norm_mul, norm_neg]
      exact mul_le_mul (hb n x hx') (hLap _ x hx') (norm_nonneg _) (by positivity))
    refine h.trans_eq ?_
    rw [abs_of_nonneg (sub_nonneg.mpr ha)]
    dsimp only [D]
    ring
  have hdec (y : ℝ) (hy : 2 ≤ y) : (2 + y) ^ 2 / (1 + y ^ 3) ≤ 4 / y := by
    have hy₀ : 0 < y := (by norm_num : (0 : ℝ) < 2).trans_le hy
    calc
      _ ≤ (2 * y) ^ 2 / (1 + y ^ 3) := by gcongr; linarith
      _ ≤ (2 * y) ^ 2 / y ^ 3 := div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hy₀ _) (by linarith)
      _ = _ := by field_simp [hy₀.ne']; ring
  have hlim : Tendsto (fun n => (D * 4) / |t n|) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop ht
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [ht.eventually_ge_atTop 2] with n hn
  exact (hInt n).trans (by rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left (hdec _ hn) hD)

/-- The horizontal integrals vanish as the two selected heights go to opposite infinities,
with every point of both segments regular. -/
theorem exists_horizontalContour_vanishing_of_cubic {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) {a : ℝ} (ha : a ≤ 2) :
    ∃ c d : ℕ → ℝ, Tendsto c atTop atBot ∧ Tendsto d atTop atTop ∧
      (∀ n, c n < 0 ∧ 0 < d n) ∧
      (∀ n, ∀ x ∈ Icc a 2, dirichletOrder χ (verticalPoint x (c n)) = 0 ∧
        dirichletOrder χ (verticalPoint x (d n)) = 0) ∧
      ∀ {h : ℝ → ℝ}, ∀ {b₁ b₂ : ℝ}, HasLaplaceCubicDecay h b₁ b₂ →
        Tendsto (fun n => horizontalContourIntegral χ h a (c n)) atTop (𝓝 0) ∧
        Tendsto (fun n => horizontalContourIntegral χ h a (d n)) atTop (𝓝 0) := by
  obtain ⟨C, hC, h⟩ := exists_good_horizontal_edges hχ a
  choose c hc hc' using fun n : ℕ => h (-(n : ℝ) - 5) (by
    rw [abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) n] : -(n : ℝ) - 5 ≤ 0)]
    linarith [Nat.cast_nonneg (α := ℝ) n])
  choose d hd hd' using fun n : ℕ => h ((n : ℝ) + 4) (by
    rw [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 4)]
    linarith [Nat.cast_nonneg (α := ℝ) n])
  have hc₀ : Tendsto c atTop atBot := by
    refine tendsto_atBot.2 fun b => ?_
    obtain ⟨j, hj⟩ := exists_nat_ge (-b)
    filter_upwards [eventually_ge_atTop j] with n hn
    linarith [(hc n).2, show (j : ℝ) ≤ n by exact_mod_cast hn]
  have hd₀ : Tendsto d atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    obtain ⟨j, hj⟩ := exists_nat_ge b
    filter_upwards [eventually_ge_atTop j] with n hn
    linarith [(hd n).1, show (j : ℝ) ≤ n by exact_mod_cast hn]
  refine ⟨c, d, hc₀, hd₀, fun n => ⟨?_, ?_⟩, fun n x hx => ⟨(hc' n x hx).1, (hd' n x hx).1⟩, ?_⟩
  · linarith [(hc n).2, Nat.cast_nonneg (α := ℝ) n]
  · linarith [(hd n).1, Nat.cast_nonneg (α := ℝ) n]
  · intro h b₁ b₂ hdecay
    exact ⟨tendsto_horizontalContourIntegral_zero_of_cubic χ hdecay ha
      (tendsto_abs_atBot_atTop.comp hc₀) hC (fun n x hx => (hc' n x hx).2),
      tendsto_horizontalContourIntegral_zero_of_cubic χ hdecay ha
      (tendsto_abs_atTop_atTop.comp hd₀) hC (fun n x hx => (hd' n x hx).2)⟩

theorem summable_norm_laplace_dirichletCriticalZero_of_cubic {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {h : ℝ → ℝ} {a b : ℝ} (hdecay : HasLaplaceCubicDecay h a b) :
    Summable (fun z : ℂ => ‖dirichletCriticalZeroTerm χ (laplaceTransform h) z‖) := by
  obtain ⟨C, hC, hTransform⟩ := hdecay
  let M := C * Real.exp (max |a| |b|)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine summable_norm_dirichletCriticalZeroTerm χ (A := 27 * M) (by positivity) fun z hz => ?_
  have he (c : ℝ) : z.re * c ≤ |c| := by
    calc
      _ ≤ |z.re * c| := le_abs_self _
      _ = z.re * |c| := by rw [abs_mul, abs_of_nonneg hz.1.le]
      _ ≤ _ := mul_le_of_le_one_left (abs_nonneg _) hz.2.le
  have hh : ‖laplaceTransform h z‖ ≤ M / (1 + |z.im| ^ 3) :=
    (hTransform z).trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (max_le ((he a).trans (le_max_left _ _))
        ((he b).trans (le_max_right _ _)))) hC) (by positivity))
  have ht : (2 + |z.im|) ^ 3 ≤ 27 * (1 + |z.im| ^ 3) := by
    rcases le_or_gt |z.im| 1 with h | h
    · have hc : (2 + |z.im|) ^ 3 ≤ (3 : ℝ) ^ 3 :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      nlinarith [pow_nonneg (abs_nonneg z.im) 3]
    · have hc : (2 + |z.im|) ^ 3 ≤ (3 * |z.im|) ^ 3 :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      nlinarith
  exact hh.trans ((div_le_div_iff₀ (by positivity) (by positivity)).mpr (by
    change M * (2 + |z.im|) ^ 3 ≤ _
    calc
      _ ≤ M * (27 * (1 + |z.im| ^ 3)) := mul_le_mul_of_nonneg_left ht hM
      _ = _ := by ring))

private theorem dirichletOrder_right_edge_for_cubic {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z : ℂ} (hz : z.re = 2) : dirichletOrder χ z = 0 := by
  apply dirichletOrder_eq_zero_of_one_le_re χ (by rw [hz]; norm_num)
  exact Or.inl fun he => by simp [he] at hz

private theorem integrable_right_edge_of_cubic {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {h : ℝ → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    {a b : ℝ} (hdecay : HasLaplaceCubicDecay h a b) :
    Integrable (fun t : ℝ =>
      (-logDeriv χ.LFunction (verticalPoint 2 t)) * laplaceTransform h (verticalPoint 2 t)) := by
  obtain ⟨C, hC, hb⟩ := norm_logDeriv_dirichletL_le_of_re_ge χ (σ := 2) (by norm_num)
  refine ((integrable_laplace_vertical_of_cubic hh hc 2 hdecay).norm.const_mul C).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro t
    let z := verticalPoint 2 t
    have ho : dirichletOrder χ z = 0 := dirichletOrder_right_edge_for_cubic χ (verticalPoint_re 2 t)
    have ho' : meromorphicOrderAt χ.LFunction z = 0 := by
      simpa only [ho, WithTop.coe_zero] using (dirichletOrder_spec χ z).symm
    obtain ⟨hA, hn⟩ := analytic_ne_zero_of_dirichlet_order_zero ho'
    have hA' : AnalyticAt ℂ (logDeriv χ.LFunction) z := hA.deriv.div hA hn
    have hcont := hA'.continuousAt.neg.mul (analyticAt_laplaceTransform hh hc z).continuousAt
    have hv : Continuous (verticalPoint 2) := by unfold verticalPoint; fun_prop
    exact hcont.comp' (f := verticalPoint 2) hv.continuousAt
  · filter_upwards with t
    rw [norm_mul, norm_neg]
    exact mul_le_mul_of_nonneg_right (hb _ (verticalPoint_re 2 t).ge) (norm_nonneg _)

private theorem mangoldtSum_sub_left_eq_zero_sums_of_cubic {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {h : ℝ → ℝ}
    (hh : Continuous h) {a b : ℝ} (hab : tsupport h ⊆ Icc a b)
    (hab₀ : a ≤ b) (hdecay : HasLaplaceCubicDecay h a b) (m : ℕ) :
    mangoldtSum χ h - (↑(2 * Real.pi) : ℂ)⁻¹ * ∫ t : ℝ, leftContourIntegrand χ h m t =
      (if N = 1 then laplaceTransform h 1 else 0) -
      (∑ n ∈ dirichletTrivialIndices χ (-((m : ℝ) + 1 / 2)),
        laplaceTransform h (dirichletTrivialZero χ n)) -
      ∑' z, dirichletCriticalZeroTerm χ (laplaceTransform h) z := by
  let x₀ := -((m : ℝ) + 1 / 2)
  have hx : x₀ ≤ 0 := by dsimp only [x₀]; exact neg_nonpos.mpr (by positivity)
  have hx₂ : x₀ < 2 := hx.trans_lt (by norm_num)
  have hcs : HasCompactSupport h := isCompact_Icc.of_isClosed_subset isClosed_closure hab
  obtain ⟨c, d, hc, hd, hsign, hregular, hvan⟩ := exists_horizontalContour_vanishing_of_cubic hχ hx₂.le
  obtain ⟨_, _, hleft⟩ := leftContourIntegral_exponential_bound_of_cubic hχ hh hab hab₀ hdecay
  let W := laplaceTransform h
  let F := fun z => (-logDeriv χ.LFunction z) * W z
  let U := ∫ t : ℝ, F (verticalPoint 2 t)
  let V := ∫ t : ℝ, leftContourIntegrand χ h m t
  let P := (↑(2 * Real.pi) : ℂ)
  let K := (if N = 1 then W 1 else 0) -
    ∑ n ∈ dirichletTrivialIndices χ x₀, W (dirichletTrivialZero χ n)
  let Z := ∑' z, dirichletCriticalZeroTerm χ W z
  have hbd (n : ℕ) (z : ℂ) (hz : z ∈ Icc x₀ 2 ×ℂ Icc (c n) (d n)) (ho : dirichletOrder χ z ≠ 0) :
      z ∈ Ioo x₀ 2 ×ℂ Ioo (c n) (d n) := by
    obtain ⟨hre, him⟩ := mem_reProdIm.mp hz
    have e₀ : verticalPoint z.re z.im = z := Complex.ext (verticalPoint_re _ _) (verticalPoint_im _ _)
    have hzl : z.re ≠ x₀ := fun e => ho (dirichletOrder_eq_zero_on_left_halfInteger hχ m e)
    have hzr : z.re ≠ 2 := fun e => ho (dirichletOrder_right_edge_for_cubic χ e)
    have hzb : z.im ≠ c n := by
      intro e
      have h := (hregular n z.re hre).1
      rw [← e, e₀] at h
      exact ho h
    have hzt : z.im ≠ d n := by
      intro e
      have h := (hregular n z.re hre).2
      rw [← e, e₀] at h
      exact ho h
    exact mem_reProdIm.mpr
      ⟨⟨lt_of_le_of_ne hre.1 hzl.symm, lt_of_le_of_ne hre.2 hzr⟩,
        ⟨lt_of_le_of_ne him.1 hzb.symm, lt_of_le_of_ne him.2 hzt⟩⟩
  have hRect (n : ℕ) : rectangleIntegral F x₀ 2 (c n) (d n) =
      P * I * (K - ∑ z ∈ dirichletRectangleSingularities χ x₀ 2 (c n) (d n),
        dirichletCriticalZeroTerm χ W z) := by
    have h := rectangleIntegral_dirichletL_laplace χ hh hcs hx₂
      ((hsign n).1.trans (hsign n).2) (hbd n)
    exact h.trans (congrArg (fun r => P * I * r)
      (dirichletRectangle_residueSum_eq hχ W hx (hsign n).1.le (hsign n).2.le))
  have hCrit := tendsto_dirichletCriticalZero_sum_rectangles χ
    (summable_norm_laplace_dirichletCriticalZero_of_cubic χ hdecay).of_norm hx (by norm_num : (1 : ℝ) ≤ 2) hc hd
  have hres : Tendsto (fun n => rectangleIntegral F x₀ 2 (c n) (d n)) atTop (𝓝 (P * I * (K - Z))) :=
    ((tendsto_const_nhds.sub hCrit).const_mul (P * I)).congr fun n => (hRect n).symm
  have hR := intervalIntegral_tendsto_integral (integrable_right_edge_of_cubic χ hh hcs hdecay) hc hd
  have hL := intervalIntegral_tendsto_integral (hleft m).1 hc hd
  have hhor := hvan hdecay
  have hcont : Tendsto (fun n => rectangleIntegral F x₀ 2 (c n) (d n)) atTop (𝓝 (I * U - I * V)) := by
    dsimp only [U, V]
    simpa only [rectangleIntegral, horizontalContourIntegral, F, W, x₀, leftContourIntegrand,
      zero_sub, sub_zero, zero_add] using
      (((hhor.1.sub hhor.2).add (hR.const_mul I)).sub (hL.const_mul I))
  have hUV : U - V = P * (K - Z) := by
    apply mul_left_cancel₀ I_ne_zero
    calc
      I * (U - V) = I * U - I * V := mul_sub _ _ _
      _ = P * I * (K - Z) := tendsto_nhds_unique hcont hres
      _ = _ := by ring
  have hP : P ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  rw [mangoldtSum_eq_rightLine_of_integrable χ hh hcs (by norm_num : (1 : ℝ) < 2)
    (integrable_laplace_vertical_of_cubic hh hcs 2 hdecay)]
  simp_rw [mul_comm (laplaceTransform h _)]
  change P⁻¹ * U - P⁻¹ * V = K - Z
  rw [← mul_sub, hUV, ← mul_assoc, inv_mul_cancel₀ hP, one_mul]

/-- The exact explicit formula for a primitive Dirichlet character and a smooth weight
with compact logarithmic support bounded away from zero. Both zero sums are absolute. -/
theorem mangoldtSum_eq_full_zero_sums_of_cubic {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {h : ℝ → ℝ}
    (hh : Continuous h) {a b : ℝ} (hab : tsupport h ⊆ Icc a b)
    (hab₀ : a ≤ b) (hdecay : HasLaplaceCubicDecay h a b) (ha : 0 < a) :
    mangoldtSum χ h = (if N = 1 then laplaceTransform h 1 else 0) -
      (∑' n, laplaceTransform h (dirichletTrivialZero χ n)) -
      ∑' z, dirichletCriticalZeroTerm χ (laplaceTransform h) z := by
  have hcs : HasCompactSupport h := isCompact_Icc.of_isClosed_subset isClosed_closure hab
  have hT := (summable_norm_laplace_dirichletTrivialZero χ
    (hh.integrable_of_hasCompactSupport hcs)
    (subset_closure.trans (hab.trans Icc_subset_Ici_self)) ha).of_norm.hasSum.comp
      (tendsto_dirichletTrivialIndices_atTop hχ)
  have hL := tendsto_leftContourIntegral_zero_of_cubic hχ hh hab hab₀ hdecay ha
  have h₁ := (tendsto_const_nhds (x := mangoldtSum χ h)).sub (hL.const_mul (↑(2 * Real.pi) : ℂ)⁻¹)
  rw [mul_zero, sub_zero] at h₁
  have h₂ := ((tendsto_const_nhds (x := if N = 1 then laplaceTransform h 1 else 0)).sub hT).sub
    (tendsto_const_nhds (x := ∑' z, dirichletCriticalZeroTerm χ (laplaceTransform h) z))
  exact tendsto_nhds_unique h₁ (h₂.congr fun m => (mangoldtSum_sub_left_eq_zero_sums_of_cubic hχ hh hab hab₀ hdecay m).symm)

end GoldbachR581
end
end

section
open MeasureTheory Set

namespace GoldbachR581.Triangular

noncomputable def kernel (δ v : ℝ) : ℝ := (1 / δ) * (1 - |v| / δ)

noncomputable def window (δ w : ℝ) : ℝ :=
  if w ≤ -δ then 1
  else if w ≤ 0 then 1 - (w + δ) ^ 2 / (2 * δ ^ 2)
  else if w < δ then (δ - w) ^ 2 / (2 * δ ^ 2)
  else 0

open Conjectures.Goldbach.GmSmoothingKernelMellin_aux (integral_lin integral_ker)

lemma kernel_continuous (δ : ℝ) : Continuous (kernel δ) := by
  unfold kernel
  fun_prop

private theorem integral_kernel_of_nonneg {δ lo hi : ℝ}
    (hδ : 0 < δ) (hlo : 0 ≤ lo) (hhi : lo ≤ hi) :
    (∫ v in lo..hi, kernel δ v) =
      (1 / δ * hi - hi ^ 2 / (2 * δ ^ 2)) -
        (1 / δ * lo - lo ^ 2 / (2 * δ ^ 2)) := by
  have hlin : (∫ v in lo..hi, kernel δ v) =
      ∫ v in lo..hi, 1 / δ + (-(1 / δ ^ 2)) * v := by
    refine intervalIntegral.integral_congr ?_
    intro v hv
    rw [uIcc_of_le hhi] at hv
    rw [kernel, abs_of_nonneg (hlo.trans hv.1)]
    field_simp [hδ.ne']
    ring
  rw [hlin, integral_lin]
  ring

private theorem integral_kernel_of_nonpos {δ lo hi : ℝ}
    (hδ : 0 < δ) (hlo : lo ≤ hi) (hhi : hi ≤ 0) :
    (∫ v in lo..hi, kernel δ v) =
      (1 / δ * hi + hi ^ 2 / (2 * δ ^ 2)) -
        (1 / δ * lo + lo ^ 2 / (2 * δ ^ 2)) := by
  have hlin : (∫ v in lo..hi, kernel δ v) =
      ∫ v in lo..hi, 1 / δ + (1 / δ ^ 2) * v := by
    refine intervalIntegral.integral_congr ?_
    intro v hv
    rw [uIcc_of_le hlo] at hv
    rw [kernel, abs_of_nonpos (hv.2.trans hhi)]
    field_simp [hδ.ne']
    ring
  rw [hlin, integral_lin]
  ring

/-- The frozen quadratic window is the cumulative mass of the triangular kernel. -/
theorem window_eq_integral (δ w : ℝ) (hδ : 0 < δ) :
    window δ w = ∫ v in (max (-δ) (min δ w))..δ, kernel δ v := by
  by_cases hwL : w ≤ -δ
  · have hwD : w ≤ δ := by linarith
    simpa [window, hwL, min_eq_right hwD, max_eq_left hwL, kernel] using
      (integral_ker δ hδ).symm
  by_cases hwD : w < δ
  · rw [min_eq_right hwD.le, max_eq_right (lt_of_not_ge hwL).le]
    by_cases hw0 : w ≤ 0
    · rw [window, ite_eq_right hwL, ite_eq_left hw0, ← intervalIntegral.integral_add_adjacent_intervals
        ((kernel_continuous δ).intervalIntegrable w 0)
        ((kernel_continuous δ).intervalIntegrable 0 δ),
        integral_kernel_of_nonpos hδ hw0 le_rfl,
        integral_kernel_of_nonneg hδ le_rfl hδ.le]
      field_simp [hδ.ne']
      <;> ring
    · rw [window, ite_eq_right hwL, ite_eq_right hw0, ite_eq_left hwD,
        integral_kernel_of_nonneg hδ (lt_of_not_ge hw0).le hwD.le]
      field_simp [hδ.ne']
      ring
  · have hn0 : ¬ w ≤ 0 := fun hw => hwD (hw.trans_lt hδ)
    have hnδ : -δ ≤ δ := by linarith
    rw [window, ite_eq_right hwL, ite_eq_right hn0, ite_eq_right hwD, min_eq_left (le_of_not_gt hwD),
      max_eq_right hnδ, intervalIntegral.integral_same]

end GoldbachR581.Triangular
end

section
open MeasureTheory Set Filter
open scoped Topology

namespace GoldbachR581.Triangular

noncomputable def supportedKernel (δ v : ℝ) : ℝ := max 0 (kernel δ v)

theorem supportedKernel_eq_kernel {δ v : ℝ} (hδ : 0 < δ) (hv : |v| ≤ δ) :
    supportedKernel δ v = kernel δ v := by
  exact max_eq_right (Conjectures.Goldbach.GmSmoothingKernelMellin_aux.ker_nonneg hδ hv)

theorem supportedKernel_eq_zero {δ v : ℝ} (hδ : 0 < δ) (hv : δ ≤ |v|) :
    supportedKernel δ v = 0 := by
  refine max_eq_left (mul_nonpos_of_nonneg_of_nonpos (by positivity) ?_)
  exact sub_nonpos.mpr ((le_div_iff₀ hδ).mpr (by simpa using hv))

theorem continuous_supportedKernel (δ : ℝ) : Continuous (supportedKernel δ) :=
  continuous_const.max (kernel_continuous δ)

theorem window_eq_integral_unclamped (δ w : ℝ) (hδ : 0 < δ) :
    window δ w = ∫ v in w..δ, supportedKernel δ v := by
  rw [window_eq_integral δ w hδ]
  let u := max (-δ) (min δ w)
  have hu : -δ ≤ u ∧ u ≤ δ := ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hint (a b : ℝ) : IntervalIntegrable (supportedKernel δ) volume a b :=
    (continuous_supportedKernel δ).intervalIntegrable _ _
  have hmain : (∫ v in u..δ, supportedKernel δ v) = ∫ v in u..δ, kernel δ v := by
    refine intervalIntegral.integral_congr fun v hv => supportedKernel_eq_kernel hδ (abs_le.mpr ?_)
    rw [uIcc_of_le hu.2] at hv
    exact ⟨hu.1.trans hv.1, hv.2⟩
  have hout : (∫ v in w..u, supportedKernel δ v) = 0 := by
    by_cases hw₁ : w ≤ -δ
    · have he : u = -δ := by dsimp [u]; rw [min_eq_right (by linarith), max_eq_left hw₁]
      rw [he]
      calc
        _ = ∫ v in w..(-δ), (0 : ℝ) := by
          refine intervalIntegral.integral_congr fun v hv => ?_
          rw [uIcc_of_le hw₁] at hv
          exact supportedKernel_eq_zero hδ ((show δ ≤ -v by linarith [hv.2]).trans (neg_le_abs v))
        _ = 0 := by simp
    by_cases hw₂ : w ≤ δ
    · have he : u = w := by dsimp [u]; rw [min_eq_right hw₂, max_eq_right (le_of_not_ge hw₁)]
      rw [he, intervalIntegral.integral_same]
    · have he : u = δ := by dsimp [u]; rw [min_eq_left (le_of_not_ge hw₂), max_eq_right (by linarith)]
      rw [he]
      calc
        _ = ∫ v in w..δ, (0 : ℝ) := by
          refine intervalIntegral.integral_congr fun v hv => ?_
          rw [uIcc_comm, uIcc_of_le (le_of_not_ge hw₂)] at hv
          exact supportedKernel_eq_zero hδ (hv.1.trans (le_abs_self v))
        _ = 0 := by simp
  exact hmain.symm.trans (by rw [← intervalIntegral.integral_add_adjacent_intervals (hint w u) (hint u δ),
    hout, zero_add])

theorem hasDerivAt_window (δ w : ℝ) (hδ : 0 < δ) :
    HasDerivAt (window δ) (-supportedKernel δ w) w := by
  have he : window δ = (fun u => ∫ v in u..δ, supportedKernel δ v) :=
    funext fun u => window_eq_integral_unclamped δ u hδ
  rw [he]
  have hcont := continuous_supportedKernel δ
  exact intervalIntegral.integral_hasDerivAt_left (hcont.intervalIntegrable w δ)
    (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt

theorem window_eq_one {δ w : ℝ} (hw : w ≤ -δ) : window δ w = 1 := by
  rw [window, if_pos hw]

theorem window_eq_zero {δ w : ℝ} (hδ : 0 < δ) (hw : δ ≤ w) : window δ w = 0 := by
  rw [window, if_neg (by linarith), if_neg (by linarith), if_neg (not_lt.mpr hw)]

noncomputable def difference (c d c₀ d₀ t : ℝ) : ℝ := window d (t - c) - window d₀ (t - c₀)

theorem difference_tsupport {c d c₀ d₀ a b : ℝ} (hd : 0 < d) (hd₀ : 0 < d₀)
    (ha : a ≤ min (c - d) (c₀ - d₀)) (hb : max (c + d) (c₀ + d₀) ≤ b) :
    tsupport (difference c d c₀ d₀) ⊆ Icc a b := by
  refine closure_minimal (fun t ht => ?_) isClosed_Icc
  have hn : difference c d c₀ d₀ t ≠ 0 := Function.mem_support.mp ht
  have ha' := ha.trans (min_le_left (c-d) (c₀-d₀))
  have ha₀ := ha.trans (min_le_right (c-d) (c₀-d₀))
  have hb' := (le_max_left (c+d) (c₀+d₀)).trans hb
  have hb₀ := (le_max_right (c+d) (c₀+d₀)).trans hb
  refine ⟨le_of_not_gt fun h => hn ?_, le_of_not_gt fun h => hn ?_⟩
  · rw [difference, window_eq_one (by linarith : t - c ≤ -d),
      window_eq_one (by linarith : t - c₀ ≤ -d₀), sub_self]
  · rw [difference, window_eq_zero hd (by linarith : d ≤ t - c),
      window_eq_zero hd₀ (by linarith : d₀ ≤ t - c₀), sub_self]

theorem difference_hasDerivAt {c d c₀ d₀ : ℝ} (hd : 0 < d) (hd₀ : 0 < d₀) (t : ℝ) :
    HasDerivAt (difference c d c₀ d₀)
      (supportedKernel d₀ (t - c₀) - supportedKernel d (t - c)) t := by
  have h₁ := (hasDerivAt_window d (t - c) hd).comp t ((hasDerivAt_id' t).sub_const c)
  have h₂ := (hasDerivAt_window d₀ (t - c₀) hd₀).comp t ((hasDerivAt_id' t).sub_const c₀)
  have he : ((window d ∘ fun x => x - c) - (window d₀ ∘ fun x => x - c₀)) =
      difference c d c₀ d₀ := by ext x; rfl
  simpa only [he, id_eq, mul_one, neg_sub_neg] using h₁.sub h₂

noncomputable def laplace (h : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (h t : ℂ) * Complex.exp (z * (t : ℂ))

noncomputable def mellin (d : ℝ) (z : ℂ) : ℂ :=
  ((Complex.exp (((d / 2 : ℝ) : ℂ) * z) - Complex.exp (((-(d / 2) : ℝ) : ℂ) * z)) /
    ((d : ℂ) * z)) ^ 2

private theorem shiftedKernel_support (c : ℝ) {d : ℝ} (hd : 0 < d) :
    Function.support (fun t => supportedKernel d (t - c)) ⊆ Ioc (c - d) (c + d) := by
  intro t ht
  have hn : supportedKernel d (t - c) ≠ 0 := Function.mem_support.mp ht
  have hl : -d < t - c := lt_of_not_ge fun h => hn
    (supportedKernel_eq_zero hd ((show d ≤ -(t-c) by linarith).trans (neg_le_abs _)))
  have hr : t - c < d := lt_of_not_ge fun h => hn
    (supportedKernel_eq_zero hd (h.trans (le_abs_self _)))
  exact ⟨by linarith, by linarith⟩

private theorem shiftedKernel_compactSupport (c : ℝ) {d : ℝ} (hd : 0 < d) :
    HasCompactSupport (fun t => supportedKernel d (t - c)) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal ((shiftedKernel_support c hd).trans Ioc_subset_Icc_self) isClosed_Icc)

private theorem cast_integrable_mul_continuous {h : ℝ → ℝ} (hh : Continuous h)
    (hc : HasCompactSupport h) {v : ℝ → ℂ} (hv : Continuous v) :
    Integrable (fun x => (h x : ℂ) * v x) := by
  have hcast : HasCompactSupport (fun x => (h x : ℂ)) := by
    apply hc.mono
    intro x hx
    simpa [Function.mem_support] using hx
  exact (Complex.continuous_ofReal.comp hh |>.mul hv).integrable_of_hasCompactSupport hcast.mul_right

theorem laplace_shiftedKernel {c d : ℝ} {z : ℂ} (hd : 0 < d) (hz : z ≠ 0) :
    laplace (fun t => supportedKernel d (t - c)) z =
      Complex.exp ((c : ℂ) * z) * mellin d z := by
  let f (t : ℝ) := ((supportedKernel d (t - c) : ℝ) : ℂ) * Complex.exp (z * (t : ℂ))
  have hf : Function.support f ⊆ Ioc (c - d) (c + d) := by
    intro t ht
    apply shiftedKernel_support c hd
    refine Function.mem_support.mpr fun h => (Function.mem_support.mp ht) ?_
    simp [f, h]
  change (∫ t : ℝ, f t) = _
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hf]
  let g (v : ℝ) := (supportedKernel d v : ℂ) * Complex.exp (z * (v : ℂ))
  have he : ∀ t, f t = Complex.exp ((c : ℂ) * z) * g (t - c) := by
    intro t
    dsimp [f, g]
    rw [← mul_assoc, mul_comm (Complex.exp ((c : ℂ) * z)), mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right]
  have hL : c - d - c = -d := by ring
  have hR : c + d - c = d := by ring
  rw [hL, hR]
  congr 1
  rw [mellin, ← Conjectures.Goldbach.GmSmoothingKernelMellin_aux.main_id d z hd hz]
  refine intervalIntegral.integral_congr fun v hv => ?_
  rw [uIcc_of_le (by linarith : -d ≤ d)] at hv
  simp [g, supportedKernel_eq_kernel hd (abs_le.mpr hv), kernel]

theorem laplace_difference {c d c₀ d₀ : ℝ} {z : ℂ} (hd : 0 < d) (hd₀ : 0 < d₀) (hz : z ≠ 0) :
    laplace (difference c d c₀ d₀) z =
      (Complex.exp ((c : ℂ) * z) * mellin d z - Complex.exp ((c₀ : ℂ) * z) * mellin d₀ z) / z := by
  let h := difference c d c₀ d₀
  let k (t : ℝ) := supportedKernel d₀ (t - c₀) - supportedKernel d (t - c)
  let U (t : ℝ) := Complex.exp (z * (t : ℂ))
  let U' (t : ℝ) := z * U t
  have hH (t : ℝ) : HasDerivAt h (k t) t := difference_hasDerivAt hd hd₀ t
  have hU (t : ℝ) : HasDerivAt U (U' t) t :=
    Conjectures.Goldbach.GmSmoothingKernelMellin_aux.hasDerivAt_exp_mul z t
  have hcont : Continuous h := continuous_iff_continuousAt.mpr fun t => (hH t).continuousAt
  have hsupp : HasCompactSupport h := isCompact_Icc.of_isClosed_subset isClosed_closure
    (difference_tsupport hd hd₀ le_rfl le_rfl)
  have hK₁ : Continuous (fun t : ℝ => supportedKernel d (t - c)) :=
    (continuous_supportedKernel d).comp (continuous_id.sub continuous_const)
  have hK₀ : Continuous (fun t : ℝ => supportedKernel d₀ (t - c₀)) :=
    (continuous_supportedKernel d₀).comp (continuous_id.sub continuous_const)
  have hUcont : Continuous U := by unfold U; fun_prop
  have hU'cont : Continuous U' := continuous_const.mul hUcont
  have hKint : Integrable (fun t => U t * (k t : ℂ)) := by
    simpa only [mul_comm, Pi.sub_apply, k] using cast_integrable_mul_continuous (hK₀.sub hK₁)
      ((shiftedKernel_compactSupport c₀ hd₀).sub (shiftedKernel_compactSupport c hd)) hUcont
  have hH'Int : Integrable (fun t => U' t * (h t : ℂ)) := by
    simpa only [mul_comm] using cast_integrable_mul_continuous hcont hsupp hU'cont
  have hHInt : Integrable (fun t => U t * (h t : ℂ)) := by
    simpa only [mul_comm] using cast_integrable_mul_continuous hcont hsupp hUcont
  have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hU t)
    (fun t _ => (hH t).ofReal_comp) hKint hH'Int hHInt
  have hparts' : laplace k z = -z * laplace h z := by
    calc
      _ = ∫ t : ℝ, U t * (k t : ℂ) := by simp only [laplace, U, mul_comm]
      _ = -(∫ t : ℝ, U' t * (h t : ℂ)) := hparts
      _ = _ := by
        rw [neg_mul, laplace, ← integral_const_mul]
        simp only [U', U, mul_assoc, mul_left_comm, mul_comm]
  have hk : laplace k z = laplace (fun t => supportedKernel d₀ (t - c₀)) z -
      laplace (fun t => supportedKernel d (t - c)) z := by
    simp only [laplace, k, Complex.ofReal_sub, sub_mul]
    exact integral_sub (cast_integrable_mul_continuous hK₀ (shiftedKernel_compactSupport c₀ hd₀) hUcont)
      (cast_integrable_mul_continuous hK₁ (shiftedKernel_compactSupport c hd) hUcont)
  rw [hk, laplace_shiftedKernel hd hz, laplace_shiftedKernel hd₀ hz] at hparts'
  apply (eq_div_iff hz).2
  dsimp only [h] at hparts'
  linear_combination hparts'

private theorem norm_laplace_of_interval {h : ℝ → ℝ} (hh : Integrable h)
    {a b : ℝ} (hab : Function.support h ⊆ Icc a b) (z : ℂ) :
    ‖laplace h z‖ ≤ (∫ x : ℝ, ‖h x‖) * Real.exp (max (z.re * a) (z.re * b)) := by
  unfold laplace
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_mul_const]
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (hh.norm.mul_const _)
  filter_upwards with x
  by_cases hx : h x = 0
  · simp [hx]
  obtain ⟨hla, hhb⟩ := hab (Function.mem_support.mpr hx)
  have hprod : z.re * x ≤ max (z.re * a) (z.re * b) := by
    by_cases hz : 0 ≤ z.re
    · exact (mul_le_mul_of_nonneg_left hhb hz).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left hla (le_of_not_ge hz)).trans (le_max_left _ _)
  simp only [norm_mul, Complex.norm_real, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hprod) (norm_nonneg _)

private theorem norm_mellin_div_le {a b c d : ℝ} {z : ℂ} (hd : 0 < d)
    (ha : a ≤ c - d) (hb : c + d ≤ b) (hz : z ≠ 0) (hi : 0 < |z.im|) :
    ‖Complex.exp ((c : ℂ) * z) * mellin d z / z‖ ≤
      (4 / d ^ 2) * Real.exp (max (z.re * a) (z.re * b)) / |z.im| ^ 3 := by
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hM : ‖mellin d z‖ ≤ 4 * Real.exp (d * |z.re|) / (d ^ 2 * ‖z‖ ^ 2) :=
    Conjectures.Goldbach.GmSmoothingKernelMellin_aux.bound_closed d z hd hz
  have he : z.re * c + d * |z.re| ≤ max (z.re * a) (z.re * b) := by
    by_cases hr : 0 ≤ z.re
    · rw [abs_of_nonneg hr]
      calc
        _ = z.re * (c + d) := by ring
        _ ≤ z.re * b := mul_le_mul_of_nonneg_left hb hr
        _ ≤ _ := le_max_right _ _
    · have hr' := le_of_not_ge hr
      rw [abs_of_nonpos hr']
      calc
        _ = z.re * (c - d) := by ring
        _ ≤ z.re * a := mul_le_mul_of_nonpos_left ha hr'
        _ ≤ _ := le_max_left _ _
  rw [norm_div, norm_mul, Complex.norm_exp,
    show (((c : ℂ) * z)).re = z.re * c by simp [Complex.mul_re, mul_comm]]
  calc
    _ ≤ (Real.exp (z.re * c) * (4 * Real.exp (d * |z.re|) / (d ^ 2 * ‖z‖ ^ 2))) / ‖z‖ := by gcongr
    _ = (4 / d ^ 2) * Real.exp (z.re * c + d * |z.re|) / ‖z‖ ^ 3 := by
      rw [Real.exp_add]
      field_simp [hd.ne', hnorm.ne'] <;> ring
    _ ≤ _ := by
      refine (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)) (by positivity)).trans ?_
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos hi _)
        (pow_le_pow_left₀ hi.le (Complex.abs_im_le_norm z) 3)

theorem laplace_difference_cubic_decay {a b c d c₀ d₀ : ℝ} (hd : 0 < d) (hd₀ : 0 < d₀)
    (ha : a ≤ min (c - d) (c₀ - d₀)) (hb : max (c + d) (c₀ + d₀) ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖laplace (difference c d c₀ d₀) z‖ ≤
        C * Real.exp (max (z.re * a) (z.re * b)) / (1 + |z.im| ^ 3) := by
  let h := difference c d c₀ d₀
  let A := ∫ t, ‖h t‖
  let B := 4 / d ^ 2 + 4 / d₀ ^ 2
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsup : tsupport h ⊆ Icc a b := difference_tsupport hd hd₀ ha hb
  have hcontinuous : Continuous h := continuous_iff_continuousAt.mpr fun t =>
    (difference_hasDerivAt (c := c) (c₀ := c₀) hd hd₀ t).continuousAt
  have hcompact : HasCompactSupport h := isCompact_Icc.of_isClosed_subset isClosed_closure hsup
  have hint : Integrable h := hcontinuous.integrable_of_hasCompactSupport hcompact
  refine ⟨2 * (A + B), by positivity, fun z => ?_⟩
  let E := Real.exp (max (z.re * a) (z.re * b))
  have hE : 0 < E := Real.exp_pos _
  change ‖laplace h z‖ ≤ 2 * (A + B) * E / (1 + |z.im| ^ 3)
  rcases le_total |z.im| 1 with hz | hz
  · have him := pow_le_pow_left₀ (abs_nonneg z.im) hz 3
    simp only [one_pow] at him
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ (A * E) * (1 + |z.im| ^ 3) := mul_le_mul_of_nonneg_right
        (norm_laplace_of_interval hint (subset_closure.trans hsup) z) (by positivity)
      _ ≤ (A * E) * 2 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hE.le hB]
  · have him : 0 < |z.im| := (by norm_num : (0 : ℝ) < 1).trans_le hz
    have hne : z ≠ 0 := fun h' => by simp [h'] at him
    have hp := one_le_pow₀ (n := 3) hz
    have hterm₁ := norm_mellin_div_le hd (ha.trans (min_le_left _ _)) ((le_max_left _ _).trans hb) hne him
    have hterm₀ := norm_mellin_div_le hd₀ (ha.trans (min_le_right _ _)) ((le_max_right _ _).trans hb) hne him
    apply (le_div_iff₀ (by positivity)).mpr
    have hnorm : ‖laplace h z‖ ≤ B * E / |z.im| ^ 3 := by
      change ‖laplace (difference c d c₀ d₀) z‖ ≤ _
      rw [laplace_difference hd hd₀ hne, sub_div]
      calc
        _ ≤ _ := norm_sub_le _ _
        _ ≤ _ := add_le_add hterm₁ hterm₀
        _ = _ := by dsimp [B, E]; ring
    calc
      _ ≤ (B * E / |z.im| ^ 3) * (1 + |z.im| ^ 3) := mul_le_mul_of_nonneg_right hnorm (by positivity)
      _ ≤ (B * E / |z.im| ^ 3) * (2 * |z.im| ^ 3) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 * B * E := by field_simp [him.ne'] <;> ring
      _ ≤ _ := by nlinarith [mul_nonneg hE.le hA]

theorem window_mem_Icc {δ : ℝ} (hδ : 0 < δ) (w : ℝ) : window δ w ∈ Icc 0 1 := by
  let u := max (-δ) (min δ w)
  have hu : -δ ≤ u ∧ u ≤ δ := ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hpos : ∀ {a b : ℝ}, -δ ≤ a → b ≤ δ → a ≤ b → 0 ≤ ∫ v in a..b, kernel δ v := by
    intro a b ha hb hab
    exact intervalIntegral.integral_nonneg hab fun v hv =>
      Conjectures.Goldbach.GmSmoothingKernelMellin_aux.ker_nonneg hδ
        (abs_le.mpr ⟨ha.trans hv.1, hv.2.trans hb⟩)
  rw [window_eq_integral δ w hδ]
  change (∫ v in u..δ, kernel δ v) ∈ Icc 0 1
  refine ⟨hpos hu.1 le_rfl hu.2, ?_⟩
  have h1 : (∫ v in (-δ)..δ, kernel δ v) = 1 :=
    Conjectures.Goldbach.GmSmoothingKernelMellin_aux.integral_ker δ hδ
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((kernel_continuous δ).intervalIntegrable (-δ) u)
    ((kernel_continuous δ).intervalIntegrable u δ)] at h1
  linarith [hpos le_rfl hu.2 hu.1]

theorem norm_difference_le_one {c d c₀ d₀ : ℝ} (hd : 0 < d) (hd₀ : 0 < d₀) (t : ℝ) :
    ‖difference c d c₀ d₀ t‖ ≤ 1 := by
  have hu := window_mem_Icc hd (t-c)
  have hl := window_mem_Icc hd₀ (t-c₀)
  rw [Real.norm_eq_abs, abs_le, difference]
  exact ⟨by linarith [hu.1, hl.2], by linarith [hu.2, hl.1]⟩

noncomputable def goldbachWindow (x δ : ℝ) : ℝ → ℝ :=
  difference (Real.log x) δ (3 / 8) (1 / 4)

theorem goldbachWindow_endpoints {x δ : ℝ} (hx : 2 ≤ x) (hδ : 0 < δ) (hd : δ ≤ 1 / 2) :
    (1 / 8 : ℝ) ≤ min (Real.log x - δ) (3 / 8 - 1 / 4) ∧
      max (Real.log x + δ) (3 / 8 + 1 / 4) ≤ Real.log x + δ := by
  have hxlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
  exact ⟨le_min (by linarith [Real.log_two_gt_d9]) (by norm_num),
    max_le le_rfl (by linarith [Real.log_two_gt_d9])⟩

theorem goldbachWindow_eq_at_log_nat {x δ : ℝ} (hx : 2 ≤ x) {n : ℕ} (hn : 2 ≤ n) :
    goldbachWindow x δ (Real.log (n : ℝ)) = window δ (Real.log ((n : ℝ) / x)) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn'
  have hvan := window_eq_zero (show (0 : ℝ) < 1 / 4 by norm_num)
    (show (1 / 4 : ℝ) ≤ Real.log (n : ℝ) - 3 / 8 by linarith [Real.log_two_gt_d9])
  rw [goldbachWindow, difference, hvan, sub_zero, Real.log_div (by linarith : (n : ℝ) ≠ 0)
    (by linarith : x ≠ 0)]

theorem goldbachWindow_eq_zero_above_cutoff {x δ : ℝ} (hx : 2 ≤ x) (hδ : 0 < δ)
    {n : ℕ} (hn : 2 ≤ n) (hcut : ⌊Real.exp δ * x⌋₊ < n) :
    goldbachWindow x δ (Real.log (n : ℝ)) = 0 := by
  rw [goldbachWindow_eq_at_log_nat hx hn]
  apply window_eq_zero hδ
  have hx₀ : 0 < x := by linarith
  have hpos : 0 < Real.exp δ * x := mul_pos (Real.exp_pos _) hx₀
  have hn' := (Nat.floor_lt hpos.le).1 hcut
  rw [← Real.log_exp δ]
  exact Real.log_le_log (Real.exp_pos _) ((le_div_iff₀ hx₀).2 hn'.le)

theorem goldbachWindow_mangoldt_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x δ : ℝ} (hx : 2 ≤ x) (hδ : 0 < δ) :
    (∑' n : ℕ, (χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) *
        (goldbachWindow x δ (Real.log (n : ℝ)) : ℂ)) =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp δ * x⌋₊,
        ((ArithmeticFunction.vonMangoldt n * window δ (Real.log ((n : ℝ) / x)) : ℝ) : ℂ) *
          χ (n : ZMod q) := by
  classical
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊Real.exp δ * x⌋₊)]
  · apply Finset.sum_congr rfl
    intro n _
    by_cases hn : 2 ≤ n
    · rw [goldbachWindow_eq_at_log_nat hx hn, Complex.ofReal_mul]
      ring
    · interval_cases n <;> simp
  · intro n hn
    by_cases hn₂ : 2 ≤ n
    · have hcut : ⌊Real.exp δ * x⌋₊ < n := lt_of_not_ge fun h => hn (Finset.mem_Icc.mpr ⟨by omega, h⟩)
      rw [goldbachWindow_eq_zero_above_cutoff hx hδ hn₂ hcut, Complex.ofReal_zero, mul_zero]
    · interval_cases n <;> simp

theorem norm_laplace_tsum_of_negative_real_parts {h : ℝ → ℝ} {b : ℝ} (hb : 1 / 8 ≤ b)
    (hh : Continuous h) (hs : tsupport h ⊆ Icc (1 / 8 : ℝ) b) (hu : ∀ t, ‖h t‖ ≤ 1)
    (z : ℕ → ℂ) (hz : ∀ n, (z n).re ≤ -(2 * (n : ℝ))) :
    ‖∑' n : ℕ, laplace h (z n)‖ ≤ 5 * (b - 1 / 8) := by
  let a : ℝ := 1 / 8
  let L : ℝ := b - a
  have hL : 0 ≤ L := sub_nonneg.mpr hb
  have hcompact : HasCompactSupport h := isCompact_Icc.of_isClosed_subset isClosed_closure hs
  have hIsupp : Function.support h ⊆ Icc a b := subset_closure.trans hs
  have hmass : (∫ t, ‖h t‖) ≤ L := by
    have he : (∫ t, ‖h t‖) = ∫ t in Icc a b, ‖h t‖ := by
      rw [← integral_indicator measurableSet_Icc]
      congr 1
      symm
      apply indicator_eq_self.2
      intro t ht
      exact hIsupp (Function.mem_support.mpr fun he => (Function.mem_support.mp ht) (by simp [he]))
    rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb]
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hb (hh.norm.intervalIntegrable a b)
      (continuous_const.intervalIntegrable a b) (f := fun t => ‖h t‖) (g := fun _ => (1 : ℝ))
      (fun t _ => hu t)
    simpa [L, a] using hmono
  let r := Real.exp (-1 / 4)
  have hr : 0 ≤ r := Real.exp_nonneg _
  have hr₄ : r ≤ 4 / 5 := by
    have he : (-1 / 4 : ℝ) = -(1 / 4) := by norm_num
    dsimp [r]
    rw [he, Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
    nlinarith [Real.add_one_le_exp (1 / 4)]
  have hr₁ : r < 1 := hr₄.trans_lt (by norm_num)
  have hpt (n : ℕ) : ‖laplace h (z n)‖ ≤ L * r ^ n := by
    have hZ := hz n
    have hZ' : (z n).re ≤ 0 := hZ.trans (neg_nonpos.mpr (by positivity))
    have hb' : (z n).re * b ≤ (z n).re * a := mul_le_mul_of_nonpos_left hb hZ'
    have hExp : Real.exp ((z n).re * a) ≤ r ^ n := by
      rw [show r ^ n = Real.exp ((n : ℝ) * (-1 / 4)) from (Real.exp_nat_mul _ _).symm]
      apply Real.exp_le_exp.mpr
      dsimp only [a]
      linarith
    have hbound := norm_laplace_of_interval (hh.integrable_of_hasCompactSupport hcompact) hIsupp (z n)
    rw [max_eq_left hb'] at hbound
    exact hbound.trans (mul_le_mul hmass hExp (Real.exp_nonneg _) hL)
  have hsum : Summable (fun n : ℕ => L * r ^ n) := (summable_geometric_of_lt_one hr hr₁).mul_left L
  have hsum' := hsum.of_nonneg_of_le (fun n => norm_nonneg (laplace h (z n))) hpt
  refine (norm_tsum_le_tsum_norm hsum').trans ((hsum'.tsum_le_tsum hpt hsum).trans ?_)
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr hr₁]
  refine (mul_le_mul_of_nonneg_left ?_ hL).trans_eq (mul_comm _ _)
  rw [inv_eq_one_div, div_le_iff₀ (sub_pos.mpr hr₁)]
  linarith

noncomputable def lowerReference (z : ℂ) : ℂ :=
  Complex.exp (((3 / 8 : ℝ) : ℂ) * z) * mellin (1 / 4) z / z

private theorem exp_five_sixteenth_le : Real.exp (5 / 16) ≤ 3 / 2 := by
  exact (Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)).trans (by norm_num)

open Conjectures.Goldbach.GmSmoothingKernelMellin_aux (main_id bound_int)

private theorem norm_lowerReference_le_of_re_half {z : ℂ} (hz : z.re = 1 / 2) :
    ‖lowerReference z‖ ≤ (3 / 2) / ‖z‖ := by
  have hne : z ≠ 0 := fun h => by norm_num [h] at hz
  have hδ : (0 : ℝ) < 1 / 4 := by norm_num
  have hm : ‖mellin (1 / 4) z‖ ≤ Real.exp ((1 / 4) * |z.re|) := by
    rw [mellin, ← main_id _ _ hδ hne]
    exact bound_int _ _ hδ
  rw [lowerReference, norm_div, norm_mul, Complex.norm_exp,
    show ((((3 / 8 : ℝ) : ℂ) * z)).re = (3 / 8) * z.re by simp [Complex.mul_re]]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    _ ≤ Real.exp ((3 / 8) * z.re) * Real.exp ((1 / 4) * |z.re|) :=
      mul_le_mul_of_nonneg_left hm (Real.exp_nonneg _)
    _ = Real.exp (5 / 16) := by rw [← Real.exp_add, hz]; norm_num
    _ ≤ _ := exp_five_sixteenth_le

theorem norm_lowerReference_le_two {z : ℂ} (hz : z.re = 1 / 2) :
    ‖lowerReference z‖ ≤ (3 / 2) * 2 := by
  have hnorm := Complex.re_le_norm z
  rw [hz] at hnorm
  exact (norm_lowerReference_le_of_re_half hz).trans
    ((div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ) < 1 / 2) hnorm).trans (by norm_num))

theorem norm_lowerReference_le_inv {z : ℂ} (hz : z.re = 1 / 2) {y : ℝ}
    (hy : 0 < y) (hyi : y ≤ |z.im|) : ‖lowerReference z‖ ≤ (3 / 2) / y :=
  (norm_lowerReference_le_of_re_half hz).trans
    (div_le_div_of_nonneg_left (by norm_num) hy (hyi.trans (Complex.abs_im_le_norm z)))

theorem norm_lowerReference_le_cube {z : ℂ} (hz : z.re = 1 / 2) {y : ℝ}
    (hy : 0 < y) (hyi : y ≤ |z.im|) : ‖lowerReference z‖ ≤ (3 / 2) * 64 / y ^ 3 := by
  have hne : z ≠ 0 := fun h => by norm_num [h] at hz
  have hm := norm_mellin_div_le (a := 1 / 8) (b := 5 / 8) (c := 3 / 8) (d := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) hne (hy.trans_le hyi)
  rw [hz, show max ((1 / 2 : ℝ) * (1 / 8)) ((1 / 2) * (5 / 8)) = 5 / 16 by norm_num] at hm
  refine hm.trans ?_
  calc
    _ ≤ (4 / (1 / 4 : ℝ) ^ 2) * (3 / 2) / |z.im| ^ 3 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left exp_five_sixteenth_le (by positivity))
        (by positivity)
    _ ≤ _ := by
      norm_num
      exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hy _)
        (pow_le_pow_left₀ hy.le hyi 3)

theorem norm_upperReference_le_cube {x δ : ℝ} {z : ℂ} (hx : 0 < x) (hδ : 0 < δ)
    (hz : z.re = 1 / 2) (hi : 0 < |z.im|) :
    ‖(x : ℂ) ^ z * mellin δ z / z‖ ≤
      4 * Real.sqrt x * Real.exp (δ / 2) / (δ ^ 2 * |z.im| ^ 3) := by
  have hne : z ≠ 0 := fun h => by norm_num [h] at hz
  have hm := norm_mellin_div_le (a := Real.log x - δ) (b := Real.log x + δ)
    (c := Real.log x) hδ le_rfl le_rfl hne hi
  have hp : (x : ℂ) ^ z = Complex.exp ((Real.log x : ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le]
  have he : Real.exp (max (z.re * (Real.log x - δ)) (z.re * (Real.log x + δ))) =
      Real.sqrt x * Real.exp (δ / 2) := by
    rw [hz, max_eq_right (by linarith), Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, ← Real.exp_add]
    congr 1
    ring
  rw [hp]
  refine (hm.trans_eq ?_)
  rw [he]
  field_simp [hδ.ne', hi.ne'] <;> ring

end GoldbachR581.Triangular
end

section
namespace GoldbachR581.Triangular

open Complex DirichletCharacter

private theorem gammaFactor_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) : χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [hχ.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [hχ.gammaFactor_def]
    apply Gammaℝ_ne_zero_of_re_pos
    simp only [add_re, one_re]
    linarith

/-- The frozen right-half-plane nonvanishing assumption and the functional equation
put every primitive critical-strip zero on the critical line. -/
theorem re_eq_half_of_grh
    (hGRH : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → χ.LFunction s ≠ 0)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {s : ℂ}
    (h₀ : 0 < s.re) (h₁ : s.re < 1) (hs : χ.LFunction s = 0) : s.re = 1 / 2 := by
  have hs₀ : s ≠ 0 := by
    intro h
    simp [h] at h₀
  have hs₁ : s ≠ 1 := by
    intro h
    simp [h] at h₁
  have hupper : s.re ≤ 1 / 2 := by
    exact le_of_not_gt (fun h => hGRH q χ s h (Or.inr hs₁) hs)
  have hcompleted : χ.completedLFunction s = 0 := by
    rw [χ.LFunction_eq_completed_div_gammaFactor s (Or.inl hs₀),
      div_eq_zero_iff] at hs
    exact hs.resolve_right (gammaFactor_ne_zero χ h₀)
  have hreflect₀ : (1 - s).re > 0 := by
    simp only [sub_re, one_re]
    linarith
  have hreflect_ne_zero : (1 : ℂ) - s ≠ 0 := by
    intro h
    simp [h] at hreflect₀
  have hreflect_ne_one : (1 : ℂ) - s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [sub_re, one_re] at hre
    linarith
  have hreflect : (χ⁻¹).LFunction (1 - s) = 0 := by
    rw [(χ⁻¹).LFunction_eq_completed_div_gammaFactor (1 - s) (Or.inl hreflect_ne_zero),
      hχ.inv.completedLFunction_one_sub]
    simp [hcompleted]
  have hlower : 1 / 2 ≤ s.re := by
    apply le_of_not_gt
    intro h
    apply hGRH q χ⁻¹ (1 - s) _ (Or.inr hreflect_ne_one) hreflect
    simp only [sub_re, one_re]
    linarith
  exact le_antisymm hupper hlower

end GoldbachR581.Triangular
end

section
open Complex Metric Set MeromorphicOn
open scoped BigOperators

namespace GoldbachZeroCount

private theorem log_radius_ratio :
    (10 / 41 : ℝ) ≤ Real.log ((23 / 16 : ℝ) / (9 / 8 : ℝ)) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -(5 / 18 : ℝ)) (by norm_num) 9
  have h' := (abs_le.mp h).1
  norm_num [Finset.sum_range_succ] at h' ⊢
  linarith

/-- Quantitative R581 Jensen step for a height-one window on the critical line. -/
theorem criticalLine_window_order_le {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    (t M : ℝ) (hM : 1 ≤ M) (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, z.re = 1 / 2 ∧ |z.im - t| ≤ 1 / 2)
    (hcenter : f (⟨3 / 2, t⟩ : ℂ) ≠ 0)
    (hbound : ∀ z ∈ sphere (⟨3 / 2, t⟩ : ℂ) (23 / 16), ‖f z‖ ≤ M) :
    ((∑ z ∈ Z, analyticOrderNatAt f z) : ℝ) ≤
      Real.log (M / ‖f (⟨3 / 2, t⟩ : ℂ)‖) / Real.log (23 / 18) := by
  let c : ℂ := ⟨3 / 2, t⟩
  let r : ℝ := 9 / 8
  let R : ℝ := 23 / 16
  let U := closedBall c r
  let D := MeromorphicOn.divisor f U
  have hsupp := D.finiteSupport (isCompact_closedBall _ _)
  let S := hsupp.toFinset
  have hA : AnalyticOnNhd ℂ f U := fun z _ => hf z
  have hR : 0 ≤ R := by norm_num [R]
  have hJ := AnalyticOnNhd.sum_divisor_le (c := c) (r := r) (R := R)
    (by norm_num [r]) (by norm_num [r, R]) hM (fun z _ => hf z)
    hcenter (by simpa only [abs_of_nonneg hR, c, R] using hbound)
  rw [abs_of_nonneg (by norm_num [r] : 0 ≤ r)] at hJ
  have hpos : ∀ z, 0 ≤ D z := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hA
  have hmem {z : ℂ} (hz : z ∈ Z) : z ∈ U := by
    obtain ⟨hre, him⟩ := hZ z hz
    have himsq : (z.im - t) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) him 2
    have hn : ‖z - c‖ ^ 2 ≤ r ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      norm_num [c, r, hre]
      nlinarith
    change z ∈ closedBall c r
    rw [mem_closedBall, dist_eq_norm]
    exact (sq_le_sq₀ (norm_nonneg _) (by norm_num [r])).1 hn
  have hval (z : ℂ) (hz : z ∈ Z) : (analyticOrderNatAt f z : ℤ) = D z := by
    change _ = MeromorphicOn.divisor f U z
    rw [hA.divisor_apply (hmem hz)]
    unfold analyticOrderNatAt
    cases h : analyticOrderAt f z using ENat.recTopCoe <;> simp
  have hmono : (∑ z ∈ Z, (analyticOrderNatAt f z : ℤ)) ≤ ∑ᶠ z, D z := by
    classical
    have hu : Function.support D ⊆ ((Z ∪ S : Finset ℂ) : Set ℂ) := by
      intro z hz
      exact Finset.mem_union_right _ (hsupp.mem_toFinset.mpr hz)
    rw [finsum_eq_sum_of_support_subset _ hu]
    calc
      _ = ∑ z ∈ Z, D z := Finset.sum_congr rfl hval
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun z _ _ => hpos z)
  have hsum_le : ((∑ z ∈ Z, analyticOrderNatAt f z) : ℝ) ≤ ((∑ᶠ z, D z : ℤ) : ℝ) := by
    exact_mod_cast hmono
  rw [show R / r = 23 / 18 by norm_num [R, r]] at hJ
  exact hsum_le.trans hJ

private theorem inverse_rpow_le_sqrt_difference (x : ℝ) (hx : 0 < x) :
    1 / (x + 1) ^ (3 / 2 : ℝ) ≤ 2 / √x - 2 / √(x + 1) := by
  have hy : 0 < x + 1 := by positivity
  let A := √x
  let B := √(x + 1)
  have hA : 0 < A := Real.sqrt_pos.2 hx
  have hB : 0 < B := Real.sqrt_pos.2 hy
  have hAB : A ≤ B := Real.sqrt_le_sqrt (by linarith)
  have heA : A ^ 2 = x := Real.sq_sqrt hx.le
  have heB : B ^ 2 = x + 1 := Real.sq_sqrt hy.le
  have hrd : (x + 1) ^ (3 / 2 : ℝ) = B ^ 3 := by
    rw [show (3 / 2 : ℝ) = (1 / 2) * (3 : ℕ) by norm_num, Real.rpow_mul hy.le,
      ← Real.sqrt_eq_rpow, Real.rpow_natCast]
  rw [hrd]
  change 1 / B ^ 3 ≤ 2 / A - 2 / B
  have hdiff : 2 / A - 2 / B = 2 / (A * B * (A + B)) := by
    field_simp
    nlinarith
  rw [hdiff, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 := mul_le_mul hAB (show A + B ≤ 2 * B by linarith) (by positivity) hB.le
  have h2 := mul_le_mul_of_nonneg_left h1 hB.le
  nlinarith

/-- At real part three halves the inverse Möbius series has norm at most three. -/
theorem third_le_norm_dirichletL_at_three_halves {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s.re = 3 / 2) :
    (1 / 3 : ℝ) ≤ ‖χ.LFunction s‖ := by
  have hs₁ : 1 < s.re := by rw [hs]; norm_num
  let a (n : ℕ) := χ (n : ZMod q) * (ArithmeticFunction.moebius n : ℂ)
  let f := LSeries.term a s
  let u (n : ℕ) : ℝ := 2 / √((n : ℝ) + 1)
  have hf : Summable f := χ.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs₁)
  have hterm (n : ℕ) : ‖f (n + 2)‖ ≤ u n - u (n + 1) := by
    have hn : n + 2 ≠ 0 := by omega
    have hnorm : ‖f (n + 2)‖ = ‖a (n + 2)‖ / (((n : ℝ) + 2) ^ (3 / 2 : ℝ)) := by
      simp only [f, LSeries.norm_term_eq, ite_eq_right hn, hs, Nat.cast_add, Nat.cast_ofNat]
    have ha (k : ℕ) : ‖a k‖ ≤ 1 := by
      dsimp only [a]
      rw [norm_mul, Complex.norm_intCast]
      calc
        _ ≤ 1 * 1 := mul_le_mul (χ.norm_le_one _) (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k))
          (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    rw [hnorm]
    calc
      _ ≤ 1 / (((n : ℝ) + 2) ^ (3 / 2 : ℝ)) :=
        div_le_div_of_nonneg_right (ha _) (by positivity)
      _ ≤ _ := by
        simp only [u, Nat.cast_add_one]
        rw [← show (n : ℝ) + 1 + 1 = n + 2 by ring]
        exact inverse_rpow_le_sqrt_difference _ (by positivity)
  have htail : ‖∑' n : ℕ, f (n + 2)‖ ≤ 2 := by
    have hshift := (summable_nat_add_iff (f := f) 2).mpr hf
    apply le_of_tendsto hshift.hasSum.tendsto_sum_nat.norm
    apply Filter.Eventually.of_forall
    intro n
    calc
      _ ≤ ∑ k ∈ Finset.range n, (u k - u (k + 1)) :=
        norm_sum_le_of_le _ (fun k _ => hterm k)
      _ = u 0 - u n := Finset.sum_range_sub' u n
      _ ≤ 2 := by
        have hu : 0 ≤ u n := by dsimp [u]; positivity
        simpa [u] using sub_le_self (u 0) hu
  have hfirst : (∑ k ∈ Finset.range 2, f k) = 1 := by
    simp [Finset.sum_range_succ, f, a]
  have hsplit : (1 : ℂ) + (∑' k : ℕ, f (k + 2)) = LSeries a s := by
    rw [← hfirst]
    exact hf.sum_add_tsum_nat_add 2
  have hnorm : ‖LSeries a s‖ ≤ 3 := by
    rw [← hsplit]
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖∑' k : ℕ, f (k + 2)‖ := norm_add_le _ _
      _ ≤ _ := by simp only [norm_one]; linarith
  have hprod : ‖χ.LFunction s‖ * ‖LSeries a s‖ = 1 := by
    rw [← norm_mul, χ.LFunction_eq_LSeries hs₁]
    have hm : LSeries (fun n => χ (n : ZMod q)) s * LSeries a s = 1 :=
      DirichletCharacter.LSeries.mul_mu_eq_one χ hs₁
    rw [hm, norm_one]
  linarith [mul_le_mul_of_nonneg_left hnorm (norm_nonneg (χ.LFunction s))]

end GoldbachZeroCount

namespace GoldbachZeroCount

-- The Mellin integral identities below are from GrhGoldbachExceptionDensity.lean.
section

open Finset Filter Set MeasureTheory Complex Asymptotics
open scoped BigOperators Topology

private theorem complete_character_sum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) :
    ∑ k ∈ range q, χ (k : ZMod q) = 0 := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    rw [← Fin.sum_univ_eq_sum_range]
    convert χ.sum_eq_zero_of_ne_one hne using 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt i.isLt)

private theorem char_partial_norm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)‖ ≤ (q : ℝ) + 1 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hr (m : ℕ) : ‖∑ k ∈ range m, χ (k : ZMod q)‖ ≤ (q : ℝ) := by
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      by_cases hm : m < q
      · calc
          _ ≤ ∑ k ∈ range m, ‖χ (k : ZMod q)‖ := norm_sum_le _ _
          _ ≤ ∑ _k ∈ range m, (1 : ℝ) := Finset.sum_le_sum fun k _ => χ.norm_le_one _
          _ ≤ (q : ℝ) := by simpa using (Nat.cast_le.mpr hm.le : (m : ℝ) ≤ q)
      · have hmq : m = q + (m - q) := by omega
        conv_lhs => rw [hmq, sum_range_add, complete_character_sum χ hne, zero_add]
        simpa only [Nat.cast_add, ZMod.natCast_self, zero_add] using ih (m - q) (by omega)
  have htotal : ∑ k ∈ range (n+1), χ (k : ZMod q) =
      χ 0 + ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q) := by
    rw [Nat.range_succ_eq_Icc_zero,
      ← Finset.insert_Icc_add_one_left_eq_Icc n.zero_le, Finset.sum_insert (by simp)]
    simp
  have hdiff : (∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)) =
      (∑ k ∈ range (n+1), χ (k : ZMod q)) - χ 0 := by rw [htotal]; abel
  rw [hdiff]
  exact (norm_sub_le ..).trans (add_le_add (hr _) (χ.norm_le_one _))

private noncomputable def charSum {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q)

private theorem charSum_measurable {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Measurable (charSum χ) :=
  (measurable_of_countable (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q))).comp
    Nat.measurable_floor

private noncomputable def charMellin {q : ℕ} (χ : DirichletCharacter ℂ q) :=
  (Ioi (1 : ℝ)).indicator (charSum χ)

private theorem charMellin_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    mellin (charMellin χ) (-s) =
      ∫ t in Ioi (1 : ℝ), charSum χ t * (t : ℂ) ^ (-(s + 1)) := by
  have hf : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • charMellin χ t) =
      (Set.Ioi (1 : ℝ)).indicator (fun t : ℝ => charSum χ t * (t : ℂ) ^ (-(s+1))) := by
    funext t
    by_cases ht : t ∈ Ioi (1 : ℝ) <;>
      simp [charMellin, Set.indicator, ht, smul_eq_mul, show -s-1 = -(s+1) by ring, mul_comm]
  rw [mellin, hf, setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))]

theorem nonprincipal_LFunction_eq_partial_integral {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    χ.LFunction s = s * ∫ t in Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(s + 1)) := by
  let F := charMellin χ
  have hbound (t : ℝ) : ‖F t‖ ≤ (q : ℝ) + 1 := by
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · simpa [F, charMellin, Set.indicator_of_mem ht, charSum] using char_partial_norm χ hne ⌊t⌋₊
    · simp [F, charMellin, Set.indicator_of_notMem ht]
      positivity
  have hmeas : Measurable F := (charSum_measurable χ).indicator measurableSet_Ioi
  have hloc : LocallyIntegrableOn F (Ioi 0) := by
    apply (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2
    intro K _ hK
    exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne hmeas.aestronglyMeasurable
      (Eventually.of_forall hbound)
  have htop : F =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
    apply Asymptotics.IsBigO.of_bound ((q : ℝ) + 1)
    exact Eventually.of_forall (fun t => by simpa using hbound t)
  have hbot (b : ℝ) : F =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
    apply Asymptotics.IsBigO.of_bound 0
    have hsm : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hsm] with t ht
    simp [F, charMellin, not_lt.mpr ht.le]
  let U := {z : ℂ | 0 < z.re}
  have ho : IsOpen U := continuous_re.isOpen_preimage (Set.Ioi (0:ℝ)) isOpen_Ioi
  have hd : AnalyticOnNhd ℂ (fun z : ℂ => z * mellin F (-z)) U := by
    apply DifferentiableOn.analyticOnNhd _ ho
    intro z hz
    have hm := mellin_differentiableAt_of_isBigO_rpow (s := -z) hloc htop
      (show (-z).re < 0 by simpa using (show 0 < z.re from hz)) (hbot ((-z).re - 1)) (by linarith)
    exact (differentiableAt_id.mul (hm.comp z differentiableAt_id.neg)).differentiableWithinAt
  have hχ : AnalyticOnNhd ℂ χ.LFunction U := by
    exact (χ.differentiable_LFunction hne).differentiableOn.analyticOnNhd ho
  have hagree : χ.LFunction =ᶠ[𝓝 (2:ℂ)] fun z => z * mellin F (-z) := by
    filter_upwards [(continuous_re.isOpen_preimage (Set.Ioi (1:ℝ)) isOpen_Ioi).mem_nhds
      (show 1 < (2:ℂ).re by norm_num)] with z hz
    have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (0 : ℝ)) := by
      apply Asymptotics.IsBigO.of_bound ((q : ℝ) + 1)
      exact Eventually.of_forall (fun n => by simpa using char_partial_norm χ hne n)
    rw [show F = charMellin χ from rfl, charMellin_eq, χ.LFunction_eq_LSeries hz]
    exact LSeries_eq_mul_integral _ le_rfl (zero_lt_one.trans hz) (χ.LSeriesSummable_of_one_lt_re hz) hO
  have hh := hχ.eqOn_of_preconnected_of_eventuallyEq hd (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ U by change 0 < (2:ℂ).re; norm_num) hagree hs
  simpa only [F, charMellin_eq, charSum] using hh

/-- The elementary vertical-growth bound from the bounded sums of a
nonprincipal character, throughout the open right half-plane. -/
theorem nonprincipal_LFunction_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    ‖χ.LFunction s‖ ≤ ‖s‖ * ((q : ℝ) + 1) / s.re := by
  rw [nonprincipal_LFunction_eq_partial_integral χ hne s hs, norm_mul, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have he : -(s.re + 1) < -1 := by linarith
  calc
    _ ≤ ∫ t in Set.Ioi (1 : ℝ), ((q : ℝ) + 1) * t ^ (-(s.re + 1)) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt he zero_lt_one).const_mul ((q : ℝ) + 1))
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
      have ht' : (0 : ℝ) < t := zero_lt_one.trans ht
      simp only [norm_mul, norm_cpow_eq_rpow_re_of_pos ht', neg_re, add_re, one_re]
      exact mul_le_mul_of_nonneg_right (char_partial_norm χ hne _) (Real.rpow_nonneg ht'.le _)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt he zero_lt_one,
        Real.one_rpow, show -(s.re + 1) + 1 = -s.re by ring]
      simp [div_eq_mul_inv]
end

section

open Finset Filter Set MeasureTheory Complex Asymptotics
open scoped BigOperators Topology

private noncomputable def fracPart (t : ℝ) : ℂ := ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ)

private theorem measurable_fracPart : Measurable fracPart := by
  unfold fracPart
  fun_prop

private theorem frac_norm {t : ℝ} (ht : 0 ≤ t) : ‖fracPart t‖ ≤ 1 := by
  rw [fracPart, Complex.norm_of_nonneg (Nat.zero_le_self_sub_floor ht)]
  exact (Nat.self_sub_floor_lt_one t).le

private noncomputable def fracMellinFun := (Set.Ioi (1 : ℝ)).indicator fracPart

private theorem mellin_frac_eq (s : ℂ) :
    mellin fracMellinFun (-s) = ∫ t in Set.Ioi (1 : ℝ), fracPart t * (t : ℂ) ^ (-(s + 1)) := by
  have hf : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • fracMellinFun t) =
      (Set.Ioi (1 : ℝ)).indicator (fun t : ℝ => fracPart t * (t : ℂ) ^ (-(s+1))) := by
    funext t
    by_cases ht : t ∈ Set.Ioi (1 : ℝ) <;>
      simp [fracMellinFun, Set.indicator, ht, smul_eq_mul, show -s-1 = -(s+1) by ring, mul_comm]
  rw [mellin, hf, setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))]

private theorem frac_kernel_bound (s : ℂ) {t : ℝ} (ht : 1 < t) :
    ‖fracPart t * (t : ℂ) ^ (-(s+1))‖ ≤ t ^ (-(s.re+1)) := by
  have ht' := zero_lt_one.trans ht
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht', neg_re, add_re, one_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg ht'.le _) (frac_norm ht'.le)

private theorem frac_kernel_integrable (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => fracPart t * (t : ℂ) ^ (-(s+1))) (Set.Ioi 1) := by
  apply (integrableOn_Ioi_rpow_of_lt (show -(s.re+1) < -1 by linarith) zero_lt_one).mono'
  · exact (measurable_fracPart.mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    exact frac_kernel_bound s ht

private theorem zeta_mellin_right (s : ℂ) (hs : 1 < s.re) :
    riemannZeta₁ s = s - (s - 1) * s * mellin fracMellinFun (-s) := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have h0 : 0 < s.re := zero_lt_one.trans hs
  have hZ : riemannZeta s =
      s * ∫ t in Set.Ioi (1 : ℝ), (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s+1)) := by
    rw [← LSeries_one_eq_riemannZeta hs, LSeries_eq_mul_integral (1 : ℕ → ℂ) zero_le_one
      hs (LSeriesSummable_one_iff.mpr hs)]
    · simp [Nat.card_Icc]
    · apply Asymptotics.IsBigO.of_bound 1
      exact Eventually.of_forall (fun n => by simp [Nat.card_Icc])
  have he : (-s).re < -1 := by simpa using hs
  have hI := integral_Ioi_cpow_of_lt he zero_lt_one
  have hc : (s - 1) * (∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ (-s)) = 1 := by
    rw [hI, ofReal_one, one_cpow, show -s + 1 = -(s - 1) by ring, neg_div_neg_eq]
    field_simp [sub_ne_zero.mpr hs1]
  have hsplit : (∫ t in Set.Ioi (1:ℝ), (⌊t⌋₊ : ℂ) * (t:ℂ)^(-(s+1))) =
      (∫ t : ℝ in Set.Ioi 1, (t:ℂ)^(-s)) - mellin fracMellinFun (-s) := by
    rw [mellin_frac_eq, ← integral_sub (integrableOn_Ioi_cpow_of_lt he zero_lt_one)
      (frac_kernel_integrable s h0)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hz : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
    have hp : (t:ℂ) ^ (-s) = (t:ℂ) * (t:ℂ) ^ (-(s+1)) := by
      conv_lhs => rw [show -s = 1 + (-(s+1)) by ring, cpow_add _ _ hz, cpow_one]
    dsimp only
    rw [hp, fracPart, ofReal_sub, ofReal_natCast]
    ring
  have hreg : riemannZeta₁ s = (s-1) * riemannZeta s := by
    rw [riemannZeta_eq_inv_sub_mul hs1, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs1), one_mul]
  rw [hreg, hZ, hsplit]
  linear_combination s * hc

/-- Euler's integral representation of the zeta function after removal of its
simple pole. The entire function on the left takes the value one at one. -/
theorem zeta_pole_removed_eq_floor_integral (s : ℂ) (hs : 0 < s.re) :
    riemannZeta₁ s = s - (s - 1) * s * ∫ t in Set.Ioi (1 : ℝ),
      (((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
  have hbound (t : ℝ) : ‖fracMellinFun t‖ ≤ 1 := by
    by_cases ht : t ∈ Set.Ioi (1 : ℝ)
    · simpa only [fracMellinFun, Set.indicator_of_mem ht] using frac_norm (zero_lt_one.trans ht).le
    · simp [fracMellinFun, Set.indicator_of_notMem ht]
  have hloc : LocallyIntegrableOn fracMellinFun (Set.Ioi 0) := by
    apply (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2
    intro K _ hK
    exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne
      (measurable_fracPart.indicator measurableSet_Ioi).aestronglyMeasurable
      (Eventually.of_forall hbound)
  have htop : fracMellinFun =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
    apply Asymptotics.IsBigO.of_bound 1
    exact Eventually.of_forall (fun t => by simpa using hbound t)
  have hbot (b : ℝ) : fracMellinFun =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
    apply Asymptotics.IsBigO.of_bound 0
    have hsm : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hsm] with t ht
    simp [fracMellinFun, not_lt.mpr ht.le]
  let U := {z : ℂ | 0 < z.re}
  have ho : IsOpen U := continuous_re.isOpen_preimage (Set.Ioi (0:ℝ)) isOpen_Ioi
  have hd : AnalyticOnNhd ℂ (fun z : ℂ => z - (z - 1) * z * mellin fracMellinFun (-z)) U := by
    apply DifferentiableOn.analyticOnNhd _ ho
    intro z hz
    have hm := mellin_differentiableAt_of_isBigO_rpow (s := -z) hloc htop
      (show (-z).re < 0 by simpa using (show 0 < z.re from hz)) (hbot ((-z).re - 1)) (by linarith)
    exact (differentiableAt_id.sub (((differentiableAt_id.sub_const 1).mul differentiableAt_id).mul
      (hm.comp z differentiableAt_id.neg))).differentiableWithinAt
  have hZ := differentiable_riemannZeta₁.differentiableOn.analyticOnNhd ho
  have hagree : riemannZeta₁ =ᶠ[𝓝 (2:ℂ)] fun z => z - (z-1)*z*mellin fracMellinFun (-z) := by
    filter_upwards [(continuous_re.isOpen_preimage (Set.Ioi (1:ℝ)) isOpen_Ioi).mem_nhds
      (show 1 < (2:ℂ).re by norm_num)] with z hz
    exact zeta_mellin_right z hz
  have hh := hZ.eqOn_of_preconnected_of_eventuallyEq hd (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ U by change 0 < (2:ℂ).re; norm_num) hagree hs
  simpa only [mellin_frac_eq, fracPart] using hh

private theorem zeta_pole_removed_norm_bound (z : ℂ) (hz : 1 / 16 ≤ z.re) :
    ‖riemannZeta₁ z‖ ≤ ‖z‖ + ‖z - 1‖ * ‖z‖ * 16 := by
  have hz' : 0 < z.re := by linarith
  have he : -(z.re + 1) < -1 := by linarith
  have hI : ‖∫ t in Set.Ioi (1 : ℝ), fracPart t * (t : ℂ) ^ (-(z + 1))‖ ≤ 16 := by
    calc
      _ ≤ ∫ t in Set.Ioi (1 : ℝ), t ^ (-(z.re + 1)) := by
        apply norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt he zero_lt_one)
        filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
        exact frac_kernel_bound z ht
      _ ≤ 16 := by
        rw [integral_Ioi_rpow_of_lt he zero_lt_one, Real.one_rpow,
          show -(z.re + 1) + 1 = -z.re by ring, neg_div_neg_eq, div_le_iff₀ hz']
        linarith
  rw [zeta_pole_removed_eq_floor_integral z hz']
  apply (norm_sub_le ..).trans
  simpa only [norm_mul, fracPart] using add_le_add_right
    (mul_le_mul_of_nonneg_left hI (show 0 ≤ ‖z - 1‖ * ‖z‖ by positivity)) ‖z‖

private theorem regular_zeta_eq_mul {z : ℂ} (hz : z ≠ 1) :
    riemannZeta₁ z = (z - 1) * riemannZeta z := by
  rw [riemannZeta_eq_inv_sub_mul hz, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hz), one_mul]

private theorem regular_zeta_order {z : ℂ} (hz : z ≠ 1) :
    analyticOrderNatAt riemannZeta₁ z = analyticOrderNatAt riemannZeta z := by
  have he : riemannZeta₁ =ᶠ[𝓝 z] fun w => (w - 1) * riemannZeta w := by
    filter_upwards [compl_singleton_mem_nhds hz] with w hw using regular_zeta_eq_mul hw
  have hfactor : AnalyticAt ℂ (fun w : ℂ => w - 1) z := by fun_prop
  have hζ := analyticOn_riemannZeta z hz
  rw [analyticOrderNatAt, analyticOrderAt_congr he, analyticOrderAt_fun_mul hfactor hζ,
    hfactor.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hz), zero_add]
  rfl

end

private theorem jensen_bound_to_log {x B : ℝ} (hx : 0 < x) (hB : 1 ≤ B) (hxB : x ≤ B) :
    Real.log x / Real.log (23 / 18) ≤ (41 / 10 : ℝ) * Real.log B := by
  have hratio : (10 / 41 : ℝ) ≤ Real.log (23 / 18) := by
    convert log_radius_ratio using 2
    norm_num
  have hratio_pos : 0 < Real.log (23 / 18) := (by norm_num : (0 : ℝ) < 10 / 41).trans_le hratio
  have hlog := Real.log_le_log hx hxB
  apply (div_le_iff₀ hratio_pos).2
  have hmul := mul_le_mul_of_nonneg_right hratio (Real.log_nonneg hB)
  nlinarith

private theorem critical_window_circle_bounds (t : ℝ) (z : ℂ)
    (hz : z ∈ sphere (⟨3 / 2, t⟩ : ℂ) (23 / 16)) :
    (1 / 16 : ℝ) ≤ z.re ∧ ‖z‖ ≤ |t| + 3 := by
  let c : ℂ := ⟨3 / 2, t⟩
  have hd : ‖z - c‖ = 23 / 16 := by simpa only [mem_sphere, dist_eq_norm] using hz
  have hre : |z.re - 3 / 2| ≤ 23 / 16 := by
    simpa only [Complex.sub_re, hd, c] using Complex.abs_re_le_norm (z - c)
  have hc : ‖c‖ ≤ 3 / 2 + |t| := by
    simpa [c, abs_of_nonneg (show (0 : ℝ) ≤ 3 / 2 by norm_num)] using
      Complex.norm_le_abs_re_add_abs_im c
  refine ⟨by linarith [(abs_le.mp hre).1], ?_⟩
  have hin := norm_le_norm_sub_add z c
  rw [hd] at hin
  linarith

/-- The quantitative unit-height zero count for nonprincipal characters on GRH. -/
theorem nonprincipal_window_order_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, z.re = 1 / 2 ∧ |z.im - t| ≤ 1 / 2) :
    ((∑ z ∈ Z, analyticOrderNatAt χ.LFunction z) : ℝ) ≤
      (41 / 10 : ℝ) * Real.log (96 * (q : ℝ) * (|t| + 3)) := by
  let c : ℂ := ⟨3 / 2, t⟩
  let M : ℝ := 32 * (q : ℝ) * (|t| + 3)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hM : 1 ≤ M := by
    have h := mul_le_mul_of_nonneg_right hq (show 0 ≤ |t| + 3 by positivity)
    dsimp [M]
    linarith [abs_nonneg t]
  have hcen : (1 / 3 : ℝ) ≤ ‖χ.LFunction c‖ := third_le_norm_dirichletL_at_three_halves χ rfl
  have hcpos : 0 < ‖χ.LFunction c‖ := (by norm_num : (0 : ℝ) < 1 / 3).trans_le hcen
  have hbound (z : ℂ) (hz : z ∈ sphere c (23 / 16)) : ‖χ.LFunction z‖ ≤ M := by
    obtain ⟨hre, hnorm⟩ := critical_window_circle_bounds t z hz
    have hpos : 0 < z.re := by linarith
    apply (nonprincipal_LFunction_norm_le χ hχ z hpos).trans
    apply (div_le_iff₀ hpos).2
    have h₁ := mul_le_mul hnorm (show (q : ℝ) + 1 ≤ 2 * (q : ℝ) by linarith)
      (by positivity) (by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hre (show 0 ≤ M by linarith)
    dsimp only [M] at h₂ ⊢
    linarith
  have hrat : M / ‖χ.LFunction c‖ ≤ 96 * (q : ℝ) * (|t| + 3) := by
    apply (div_le_iff₀ hcpos).2
    have h := mul_le_mul_of_nonneg_left hcen (show 0 ≤ 96 * (q : ℝ) * (|t| + 3) by positivity)
    dsimp [M]
    linarith
  refine (criticalLine_window_order_le (fun z => (χ.differentiable_LFunction hχ).analyticAt z)
    t M hM Z hZ (norm_pos_iff.mp hcpos) hbound).trans ?_
  have h3M : 3 * M = 96 * (q : ℝ) * (|t| + 3) := by dsimp only [M]; ring
  exact jensen_bound_to_log (div_pos (by linarith) hcpos) (by rw [← h3M]; linarith) hrat

/-- The analogous quantitative unit-height zero count for the Riemann zeta function. -/
theorem zeta_window_order_le (t : ℝ) (ht : 5 / 2 ≤ |t|) (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, z.re = 1 / 2 ∧ |z.im - t| ≤ 1 / 2) :
    ((∑ z ∈ Z, analyticOrderNatAt riemannZeta z) : ℝ) ≤
      (41 / 10 : ℝ) * Real.log (96 * (|t| + 3)) := by
  let c : ℂ := ⟨3 / 2, t⟩
  let M : ℝ := 32 * (|t| + 3) * ‖c - 1‖
  have hden : (5 / 2 : ℝ) ≤ ‖c - 1‖ := ht.trans (by
    simpa [c] using Complex.abs_im_le_norm (c - 1))
  have hM : 1 ≤ M := by
    have h := mul_le_mul_of_nonneg_left hden (show 0 ≤ 32 * (|t| + 3) by positivity)
    dsimp only [M]
    linarith
  have hζ : (1 / 3 : ℝ) ≤ ‖riemannZeta c‖ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      third_le_norm_dirichletL_at_three_halves (1 : DirichletCharacter ℂ 1) (s := c) rfl
  have hcne : c ≠ 1 := by
    intro he
    have hh := congrArg Complex.re he
    norm_num [c] at hh
  have hcen : (1 / 3 : ℝ) * ‖c - 1‖ ≤ ‖riemannZeta₁ c‖ := by
    rw [regular_zeta_eq_mul hcne, norm_mul, mul_comm (1 / 3 : ℝ)]
    exact mul_le_mul_of_nonneg_left hζ (norm_nonneg _)
  have hcpos : 0 < ‖riemannZeta₁ c‖ :=
    (mul_pos (by norm_num) (show 0 < ‖c - 1‖ by linarith)).trans_le hcen
  have hbound (z : ℂ) (hz : z ∈ sphere c (23 / 16)) : ‖riemannZeta₁ z‖ ≤ M := by
    obtain ⟨hre, hnorm⟩ := critical_window_circle_bounds t z hz
    have hd : ‖z - c‖ = 23 / 16 := by simpa only [mem_sphere, dist_eq_norm] using hz
    have hs : ‖z - 1‖ ≤ (8 / 5 : ℝ) * ‖c - 1‖ := by
      have hi := norm_le_norm_sub_add (z - 1) (c - 1)
      rw [show (z - 1) - (c - 1) = z - c by ring, hd] at hi
      linarith
    have h₁ := mul_le_mul_of_nonneg_right hs (norm_nonneg z)
    have h₂ := mul_le_mul_of_nonneg_right hden (norm_nonneg z)
    have h₃ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg (c - 1))
    have h₄ := mul_nonneg (norm_nonneg z) (norm_nonneg (c - 1))
    apply (zeta_pole_removed_norm_bound z hre).trans
    dsimp only [M]
    linarith
  have hrat : M / ‖riemannZeta₁ c‖ ≤ 96 * (|t| + 3) := by
    apply (div_le_iff₀ hcpos).2
    have h := mul_le_mul_of_nonneg_left hcen (show 0 ≤ 96 * (|t| + 3) by positivity)
    dsimp only [M]
    linarith
  calc
    _ = ((∑ z ∈ Z, analyticOrderNatAt riemannZeta₁ z) : ℝ) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hz' : z ≠ 1 := by
        intro he
        have := (hZ z hz).1
        norm_num [he] at this
      rw [regular_zeta_order hz']
    _ ≤ Real.log (M / ‖riemannZeta₁ c‖) / Real.log (23 / 18) :=
      criticalLine_window_order_le (fun z => differentiable_riemannZeta₁.analyticAt z)
        t M hM Z hZ (norm_pos_iff.mp hcpos) hbound
    _ ≤ _ := jensen_bound_to_log (div_pos (by linarith) hcpos) (by linarith [abs_nonneg t]) hrat

/-- A unit-height bin bound for every primitive Dirichlet character, including conductor one. -/
theorem primitive_window_order_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 5 / 2 ≤ |t|) (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, z.re = 1 / 2 ∧ |z.im - t| ≤ 1 / 2) :
    ((∑ z ∈ Z, analyticOrderNatAt χ.LFunction z) : ℝ) ≤
      (41 / 10 : ℝ) * Real.log (96 * (q : ℝ) * (|t| + 3)) := by
  by_cases he : χ = 1
  · subst χ
    have hq : q = 1 := by simpa only [DirichletCharacter.conductor_one] using hχ.symm
    subst q
    simpa only [DirichletCharacter.LFunction_modOne_eq, Nat.cast_one, mul_one] using
      zeta_window_order_le t ht Z hZ
  · exact nonprincipal_window_order_le χ he t Z hZ

end GoldbachZeroCount


namespace GoldbachZeroCount

-- Compact finiteness is from GrhGoldbachExceptionDensity.lean.
section

open Set Filter Complex DirichletCharacter

private theorem finite_compact_zeros {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {b : ℂ} (hb : f b ≠ 0) {K : Set ℂ} (hK : IsCompact K) :
    {z ∈ K | f z = 0}.Finite := by
  have ha : AnalyticOnNhd ℂ f univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hd := ha.preimage_zero_mem_codiscreteWithin hb
    (show b ∈ (univ : Set ℂ) from mem_univ b) isConnected_univ
  exact (hK.finite_sdiff_of_mem_codiscreteWithin
    (Filter.codiscreteWithin_mono (subset_univ K) hd)).subset fun z hz => ⟨hz.1, by simp [hz.2]⟩

theorem finite_character_zeros_on_compact {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {K : Set ℂ} (hK : IsCompact K) :
    {z ∈ K | z ≠ 1 ∧ LFunction χ z = 0}.Finite := by
  by_cases hχ : χ = 1
  · subst χ
    refine (finite_compact_zeros (differentiable_LFunctionTrivChar₁ q)
      (LFunctionTrivChar₁_apply_one_ne_zero q) hK).subset ?_
    intro z hz
    refine ⟨hz.1, ?_⟩
    rw [LFunctionTrivChar₁, Function.update_of_ne hz.2.1]
    exact mul_eq_zero_of_right _ hz.2.2
  · have h₂ : LFunction χ 2 ≠ 0 := LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)
    exact (finite_compact_zeros (differentiable_LFunction hχ) h₂ hK).subset
      fun _ hz => ⟨hz.1, hz.2.2⟩

theorem finite_character_zeros_in_window {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t R : ℝ) :
    {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ R ∧ LFunction χ z = 0}.Finite := by
  let K := (Icc (0 : ℝ) 1) ×ℂ (Icc (t - R) (t + R))
  have hk : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  apply (finite_character_zeros_on_compact χ hk).subset
  intro z hz
  obtain ⟨h₀, h₁, him, hL⟩ := hz
  obtain ⟨hl, hr⟩ := abs_le.mp him
  refine ⟨⟨⟨h₀.le, h₁.le⟩, ⟨by linarith, by linarith⟩⟩, ?_, hL⟩
  intro he
  simp [he] at h₁

/-- The finite set underlying the requested unconditional zero-count theorem. -/
theorem exists_nontrivial_character_zero_finset {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    ∃ Z : Finset ℂ, ∀ z : ℂ,
      z ∈ Z ↔ 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T ∧ LFunction χ z = 0 := by
  have hfin := finite_character_zeros_in_window χ 0 T
  refine ⟨hfin.toFinset, fun z => ?_⟩
  simpa only [Set.mem_ofPred_eq, sub_zero] using (hfin.mem_toFinset (a := z))

end

end GoldbachZeroCount

open scoped BigOperators

namespace GoldbachZeroCount

/-- Transfer the Bennett–Martin–O'Bryant–Rechnitzer bound to the requested constants. -/
theorem dirichlet_constant_transfer {q T N M : ℝ} (hq : 1 ≤ q) (hT : 2 ≤ T)
    (hcount : |N - M| ≤ 0.298 * Real.log (q * T) + 4.358) :
    |N - M| ≤ 0.35 * Real.log (q * T) + 6.5 := by
  have hqT : 1 ≤ q * T := by nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hT)]
  linarith [Real.log_nonneg hqT]

private theorem log_optimum_bound : Real.log (443 / 38 : ℝ) ≤ 5 / 2 := by
  have h := Real.sum_le_exp_of_nonneg (x := (5 / 2 : ℝ)) (by norm_num) 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.log_le_iff_le_exp (by norm_num)]
  linarith

private theorem zeta_error_comparison {T : ℝ} (hT : 2 ≤ T) :
    7 / 4 + 2 * (0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588) ≤
      0.35 * Real.log T + 6.5 := by
  let x := Real.log T
  let a : ℝ := 443 / 38
  have hx : 0 < x := Real.log_pos (by linarith)
  have ha : 0 < a := by norm_num [a]
  have h := Real.log_le_sub_one_of_pos (div_pos hx ha)
  rw [Real.log_div hx.ne' ha.ne'] at h
  have hlog : Real.log a ≤ 5 / 2 := log_optimum_bound
  change 7 / 4 + 2 * (0.137 * x + 0.443 * Real.log x + 1.588) ≤ 0.35 * x + 6.5
  dsimp only [a] at h
  linarith

/-- Transfer Rosser's one-sided bound with the seven-eighths term to a two-sided count. -/
theorem zeta_constant_transfer {T N M : ℝ} (hT : 2 ≤ T)
    (hcount : |N - (M + 7 / 8)| ≤
      0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588) :
    |2 * N - 2 * M| ≤ 0.35 * Real.log T + 6.5 := by
  calc
    _ = |2 * (N - (M + 7 / 8)) + 7 / 4| := by congr 1; ring
    _ ≤ 2 * |N - (M + 7 / 8)| + 7 / 4 := by
      simpa only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
        abs_of_nonneg (show (0 : ℝ) ≤ 7 / 4 by norm_num)] using
        abs_add_le (2 * (N - (M + 7 / 8))) (7 / 4)
    _ ≤ _ := by linarith [zeta_error_comparison hT]

/-- Numerical bound for the normalized height logarithm in the Jensen tail. -/
theorem log_264_le : Real.log (264 : ℝ) ≤ 28 / 5 := by
  have h := Real.sum_le_exp_of_nonneg (x := (28 / 5 : ℝ)) (by norm_num) 15
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.log_le_iff_le_exp (by norm_num)]
  linarith

end GoldbachZeroCount

open scoped BigOperators

namespace GoldbachR581.Triangular

private theorem reciprocal_cube_step {s : ℝ} (hs : 1 / 2 < s) :
    1 / s ^ 3 ≤ (1 / (s - 1 / 2) ^ 2 - 1 / (s + 1 / 2) ^ 2) / 2 := by
  have hs₀ : 0 < s := by linarith
  have hleft : 0 < s - 1 / 2 := by linarith
  have hright : 0 < s + 1 / 2 := by linarith
  have he : (1 / (s - 1 / 2) ^ 2 - 1 / (s + 1 / 2) ^ 2) / 2 =
      s / ((s - 1 / 2) ^ 2 * (s + 1 / 2) ^ 2) := by
    rw [div_sub_div _ _ (pow_ne_zero _ hleft.ne') (pow_ne_zero _ hright.ne'), div_div]
    have hn : (1 : ℝ) * (s + 1 / 2) ^ 2 - (s - 1 / 2) ^ 2 * 1 = s * 2 := by ring
    rw [hn]
    exact mul_div_mul_right _ _ (by norm_num)
  rw [he]
  apply (div_le_div_iff₀ (pow_pos hs₀ _) (mul_pos (pow_pos hleft _) (pow_pos hright _))).2
  have hprod : (s - 1 / 2) * (s + 1 / 2) ≤ s * s := by nlinarith
  have hsq := pow_le_pow_left₀ (mul_nonneg hleft.le hright.le) hprod 2
  nlinarith only [hsq]

private theorem reciprocal_square_step {s : ℝ} (hs : 0 < s) :
    1 / (s + 1 / 2) ^ 2 ≤ 1 / s - 1 / (s + 1) := by
  have hx : 0 < s + 1 := by positivity
  have he : 1 / s - 1 / (s + 1) = 1 / (s * (s + 1)) := by
    field_simp [hs.ne', hx.ne']
    ring
  rw [he]
  apply one_div_le_one_div_of_le (mul_pos hs hx)
  nlinarith

/-- The reciprocal-cube tail can be bounded without introducing an infinite sum. -/
theorem sum_reciprocal_cubes_after_first (t : ℝ) (ht : 0 < t) (m : ℕ) :
    (∑ k ∈ Finset.range m, 1 / (t + (k : ℝ) + 1) ^ 3) ≤
      (1 / (t + 1 / 2) ^ 2 - 1 / (t + (m : ℝ) + 1 / 2) ^ 2) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm₀ : (1 / 2 : ℝ) < t + (m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
    have hm := reciprocal_cube_step hm₀
    rw [show t + (m : ℝ) + 1 - 1 / 2 = t + (m : ℝ) + 1 / 2 by ring] at hm
    rw [Finset.sum_range_succ, Nat.cast_succ]
    rw [show t + ((m : ℝ) + 1) + 1 / 2 = t + (m : ℝ) + 1 + 1 / 2 by ring]
    linarith

private theorem weighted_potential (t : ℝ) (ht : 0 < t) (m : ℕ) :
    (∑ k ∈ Finset.range m, ((k : ℝ) + 1) / (t + (k : ℝ) + 1) ^ 3) +
      (m : ℝ) / 2 * (1 / (t + (m : ℝ) + 1 / 2) ^ 2) ≤
      (1 / t - 1 / (t + (m : ℝ))) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm₀ : (1 / 2 : ℝ) < t + (m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
    have hm := reciprocal_cube_step hm₀
    rw [show t + (m : ℝ) + 1 - 1 / 2 = t + (m : ℝ) + 1 / 2 by ring] at hm
    have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ (m : ℝ) + 1)
    have hs := reciprocal_square_step (s := t + (m : ℝ)) (by positivity)
    rw [Finset.sum_range_succ, Nat.cast_succ]
    rw [show t + ((m : ℝ) + 1) + 1 / 2 = t + (m : ℝ) + 1 + 1 / 2 by ring,
      show t + ((m : ℝ) + 1) = t + (m : ℝ) + 1 by ring]
    simp only [div_eq_mul_inv, one_mul] at ih hm' hs ⊢
    linarith only [ih, hm', hs]

/-- The linear term arising from the logarithm in a zero-count bound. -/
theorem sum_weighted_reciprocal_cubes (t : ℝ) (ht : 0 < t) (m : ℕ) :
    (∑ k ∈ Finset.range m, ((k : ℝ) + 1) / (t + (k : ℝ) + 1) ^ 3) ≤ 1 / (2 * t) := by
  have h := weighted_potential t ht m
  have hp : 0 ≤ (m : ℝ) / 2 * (1 / (t + (m : ℝ) + 1 / 2) ^ 2) := by positivity
  have hq : 0 ≤ 1 / (t + (m : ℝ)) := by positivity
  rw [show (1 : ℝ) / (2 * t) = (1 / t) / 2 by ring]
  linarith

/-- A uniform bound on all finite sums of reciprocal cubes above height `t`. -/
theorem sum_reciprocal_cubes (t : ℝ) (ht : 2 ≤ t) (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), 1 / (t + (k : ℝ)) ^ 3) ≤ (41 / 50 : ℝ) / t ^ 2 := by
  rw [Finset.sum_range_succ']
  push_cast
  simp only [add_zero, ← add_assoc]
  have ht₀ : 0 < t := by linarith
  have htail := sum_reciprocal_cubes_after_first t ht₀ m
  have hp : 0 ≤ (1 : ℝ) / (t + (m : ℝ) + 1 / 2) ^ 2 := by positivity
  have hmaj : (1 : ℝ) / t ^ 3 + 1 / (2 * (t + 1 / 2) ^ 2) ≤ (41 / 50 : ℝ) / t ^ 2 := by
    apply sub_nonneg.mp
    have he : (41 / 50 : ℝ) / t ^ 2 - (1 / t ^ 3 + 1 / (2 * (t + 1 / 2) ^ 2)) =
        (t - 2) * (64 * t ^ 2 + 92 * t + 25) / (50 * t ^ 3 * (2 * t + 1) ^ 2) := by
      have h₁ : 0 < t + 1 / 2 := by positivity
      have h₂ : 0 < 2 * t + 1 := by positivity
      field_simp [ht₀.ne', h₁.ne', h₂.ne']
      ring
    rw [he]
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr ht) (by positivity)) (by positivity)
  rw [show (1 : ℝ) / (2 * (t + 1 / 2) ^ 2) = (1 / (t + 1 / 2) ^ 2) / 2 by
    rw [div_div, mul_comm ((t + 1 / 2) ^ 2) 2]] at hmaj
  linarith

end GoldbachR581.Triangular

open Complex
open scoped BigOperators

namespace GoldbachZeroCount

private noncomputable def tailBin (T : ℝ) (z : ℂ) : ℕ := ⌊|z.im| - T⌋₊

private theorem tailBin_bounds {T : ℝ} {z : ℂ} (hz : T ≤ |z.im|) :
    T + (tailBin T z : ℝ) ≤ |z.im| ∧ |z.im| < T + (tailBin T z : ℝ) + 1 := by
  constructor
  · have h := Nat.floor_le (sub_nonneg.mpr hz)
    dsimp only [tailBin]
    linarith
  · have h := Nat.lt_floor_add_one (|z.im| - T)
    dsimp only [tailBin]
    linarith

private theorem tail_bin_log_le {q T : ℝ} (hq : 1 ≤ q) (hT : 2 ≤ T) (k : ℕ)
    (h264 : Real.log (264 : ℝ) ≤ 28 / 5) :
    Real.log (96 * q * (T + k + 7 / 2)) ≤ Real.log (q * T) + 28 / 5 + k / T := by
  have ht : 0 < T := by linarith
  have hq' : 0 < q := by linarith
  have hK : 0 < 1 + (k : ℝ) / T := by positivity
  have hmul : 264 * (q * T) * (1 + (k : ℝ) / T) = 264 * q * (T + k) := by
    field_simp
  calc
    _ ≤ Real.log (264 * (q * T) * (1 + (k : ℝ) / T)) := by
      apply Real.log_le_log (by positivity)
      rw [hmul]
      have h := mul_le_mul_of_nonneg_left (show (336 : ℝ) ≤ 168 * (T + k) by
        linarith [Nat.cast_nonneg (α := ℝ) k]) hq'.le
      linarith
    _ = Real.log 264 + Real.log (q * T) + Real.log (1 + (k : ℝ) / T) := by
      rw [Real.log_mul (by positivity) hK.ne', Real.log_mul (by norm_num) (by positivity)]
    _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos hK]

/-- Partition a finite set of critical-line zeros into unit-height bins on both sides of the real axis. -/
theorem finite_tail_binned {q T : ℝ} (hq : 1 ≤ q) (hT : 2 ≤ T) (f : ℂ → ℂ) (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, z.re = 1 / 2 ∧ T ≤ |z.im|)
    (hcount : ∀ (t : ℝ), 5 / 2 ≤ |t| → ∀ (U : Finset ℂ),
      (∀ z ∈ U, z.re = 1 / 2 ∧ |z.im - t| ≤ 1 / 2) →
      (∑ z ∈ U, (analyticOrderNatAt f z : ℝ)) ≤ (41 / 10) * Real.log (96 * q * (|t| + 3)))
    (h264 : Real.log (264 : ℝ) ≤ 28 / 5) :
    ∃ m : ℕ, (∑ z ∈ Z, (analyticOrderNatAt f z : ℝ) / |z.im| ^ 3) ≤
      (41 / 5) * ∑ k ∈ Finset.range (m + 1), (Real.log (q * T) + 28 / 5 + k / T) / (T + k) ^ 3 := by
  classical
  let m := Z.sup (tailBin T)
  let C (k : ℕ) : ℝ := T + k + 1 / 2
  have hC (k : ℕ) : 5 / 2 ≤ C k := by dsimp [C]; linarith [Nat.cast_nonneg (α := ℝ) k]
  let B (k : ℕ) := Z.filter (fun z => tailBin T z = k)
  let w (z : ℂ) : ℝ := (analyticOrderNatAt f z : ℝ)
  have hbin {k : ℕ} {z : ℂ} (hz : z ∈ B k) :
      z.re = 1 / 2 ∧ T + (k : ℝ) ≤ |z.im| ∧ |z.im| < T + (k : ℝ) + 1 := by
    obtain ⟨hz, hk⟩ := Finset.mem_filter.mp hz
    refine ⟨(hZ z hz).1, ?_⟩
    simpa only [hk] using tailBin_bounds (hZ z hz).2
  have hbin_sum (k : ℕ) :
      (∑ z ∈ B k, w z) ≤ (41 / 5) * Real.log (96 * q * (T + k + 7 / 2)) := by
    let P := (B k).filter (fun z => 0 ≤ z.im)
    let N := (B k).filter (fun z => ¬0 ≤ z.im)
    have hP : ∀ z ∈ P, z.re = 1 / 2 ∧ |z.im - C k| ≤ 1 / 2 := by
      intro z hz
      obtain ⟨hz, hs⟩ := Finset.mem_filter.mp hz
      obtain ⟨hRe, hLo, hHi⟩ := hbin hz
      rw [abs_of_nonneg hs] at hLo hHi
      exact ⟨hRe, abs_le.mpr ⟨by dsimp [C]; linarith, by dsimp [C]; linarith⟩⟩
    have hN : ∀ z ∈ N, z.re = 1 / 2 ∧ |z.im - (-C k)| ≤ 1 / 2 := by
      intro z hz
      obtain ⟨hz, hs⟩ := Finset.mem_filter.mp hz
      obtain ⟨hRe, hLo, hHi⟩ := hbin hz
      rw [abs_of_neg (lt_of_not_ge hs)] at hLo hHi
      exact ⟨hRe, abs_le.mpr ⟨by dsimp [C]; linarith, by dsimp [C]; linarith⟩⟩
    have hC' : 0 ≤ C k := by linarith [hC k]
    have h₁ := hcount (C k) (by simpa only [abs_of_nonneg hC'] using hC k) P hP
    have h₂ := hcount (-C k) (by simpa only [abs_neg, abs_of_nonneg hC'] using hC k) N hN
    rw [abs_of_nonneg hC'] at h₁
    rw [abs_neg, abs_of_nonneg hC'] at h₂
    have hsum : (∑ z ∈ P, w z) + (∑ z ∈ N, w z) = ∑ z ∈ B k, w z :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    rw [← hsum, show T + (k : ℝ) + 7 / 2 = C k + 3 by dsimp only [C]; ring]
    dsimp only [w] at h₁ h₂ ⊢
    linarith
  have hmaps (z : ℂ) (hz : z ∈ Z) : tailBin T z ∈ Finset.range (m + 1) := by
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Finset.le_sup (f := tailBin T) hz)
  refine ⟨m, ?_⟩
  calc
    _ = ∑ k ∈ Finset.range (m + 1), ∑ z ∈ B k, w z / |z.im| ^ 3 :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ k ∈ Finset.range (m + 1), (41 / 5) *
        ((Real.log (q * T) + 28 / 5 + k / T) / (T + k) ^ 3) := by
      apply Finset.sum_le_sum
      intro k _
      have hk : 0 < T + (k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
      calc
        _ ≤ ∑ z ∈ B k, w z / (T + (k : ℝ)) ^ 3 := by
          apply Finset.sum_le_sum
          intro z hz
          exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
            (pow_le_pow_left₀ hk.le (hbin hz).2.1 3)
        _ = (∑ z ∈ B k, w z) / (T + (k : ℝ)) ^ 3 := by rw [Finset.sum_div]
        _ ≤ ((41 / 5) * Real.log (96 * q * (T + k + 7 / 2))) / (T + (k : ℝ)) ^ 3 :=
          div_le_div_of_nonneg_right (hbin_sum k) (by positivity)
        _ ≤ _ := by
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (tail_bin_log_le hq hT k h264) (by positivity)) (by norm_num)
    _ = _ := by rw [Finset.mul_sum]

/-- Evaluate the binned estimate using the two finite reciprocal-cube estimates. -/
theorem finite_tail_cubic_bound {q T : ℝ} (hq : 1 ≤ q) (hT : 2 ≤ T)
    (f : ℂ → ℂ) (Z : Finset ℂ) (hZ : ∀ z ∈ Z, z.re = 1 / 2 ∧ T ≤ |z.im|)
    (hcount : ∀ (t : ℝ), 5 / 2 ≤ |t| → ∀ (U : Finset ℂ),
      (∀ z ∈ U, z.re = 1 / 2 ∧ |z.im - t| ≤ 1 / 2) →
      (∑ z ∈ U, (analyticOrderNatAt f z : ℝ)) ≤ (41 / 10) * Real.log (96 * q * (|t| + 3)))
    (h264 : Real.log (264 : ℝ) ≤ 28 / 5)
    (hplain : ∀ m : ℕ, (∑ k ∈ Finset.range (m + 1), 1 / (T + (k : ℝ)) ^ 3) ≤ (41 / 50) / T ^ 2)
    (hweight : ∀ m : ℕ,
      (∑ k ∈ Finset.range m, ((k : ℝ) + 1) / (T + (k : ℝ) + 1) ^ 3) ≤ 1 / (2 * T)) :
    (∑ z ∈ Z, (analyticOrderNatAt f z : ℝ) / |z.im| ^ 3) ≤ 8 * (Real.log (q * T) + 6) / T ^ 2 := by
  obtain ⟨m, hm⟩ := finite_tail_binned hq hT f Z hZ hcount h264
  let L := Real.log (q * T)
  have hT' : 0 < T := by linarith
  have hqT : 1 ≤ q * T := by
    have h := mul_le_mul_of_nonneg_right hq hT'.le
    linarith
  have hL : 0 ≤ L := Real.log_nonneg hqT
  have hw : (∑ k ∈ Finset.range (m + 1), (k : ℝ) / (T + (k : ℝ)) ^ 3) ≤ 1 / (2 * T) := by
    rw [Finset.sum_range_succ']
    push_cast
    simpa [add_assoc] using hweight m
  have hsplit (k : ℕ) : (L + 28 / 5 + (k : ℝ) / T) / (T + (k : ℝ)) ^ 3 =
      (L + 28 / 5) * (1 / (T + (k : ℝ)) ^ 3) + (1 / T) * ((k : ℝ) / (T + (k : ℝ)) ^ 3) := by
    ring
  calc
    _ ≤ (41 / 5) * ∑ k ∈ Finset.range (m + 1), (L + 28 / 5 + k / T) / (T + k) ^ 3 := hm
    _ ≤ (41 / 5) * ((L + 28 / 5) * ((41 / 50) / T ^ 2) + (1 / T) * (1 / (2 * T))) := by
      simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
      · exact mul_le_mul_of_nonneg_left (hplain m) (by positivity)
      · exact mul_le_mul_of_nonneg_left hw (by positivity)
    _ = ((41 / 5) * ((L + 28 / 5) * (41 / 50) + 1 / 2)) / T ^ 2 := by
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (by dsimp only [L] at hL ⊢; linarith) (sq_nonneg T)

end GoldbachZeroCount

namespace GoldbachZeroCount

/-- Uniform cubic zero-tail bound for finite sets on GRH, also for the conductor-one character. -/
theorem primitive_finite_tail_cubic_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 2 ≤ T) (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, z.re = 1 / 2 ∧ T ≤ |z.im|) :
    (∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℝ) / |z.im| ^ 3) ≤
      8 * (Real.log ((q : ℝ) * T) + 6) / T ^ 2 := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  refine finite_tail_cubic_bound hq hT χ.LFunction Z hZ ?_ log_264_le
    (GoldbachR581.Triangular.sum_reciprocal_cubes T hT)
    (GoldbachR581.Triangular.sum_weighted_reciprocal_cubes T (by linarith))
  intro t ht U hU
  simpa only [Nat.cast_sum] using primitive_window_order_le χ hχ t ht U hU

/-- The cubic zero-tail majorant controls the absolute infinite tail of a weight. -/
theorem primitive_tsum_tail_norm_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T A : ℝ} (hT : 2 ≤ T) (hA : 0 ≤ A) (F : ℂ → ℝ)
    (hF₀ : ∀ z, 0 ≤ F z)
    (hF : ∀ z, F z ≠ 0 → z.re = 1 / 2 ∧ T ≤ |z.im| ∧
        F z ≤ A * ((analyticOrderNatAt χ.LFunction z : ℝ) / |z.im| ^ 3)) :
    Summable F ∧ (∑' z : ℂ, F z) ≤ A * (8 * (Real.log ((q : ℝ) * T) + 6) / T ^ 2) := by
  classical
  have hsum (Z : Finset ℂ) : ∑ z ∈ Z, F z ≤ A * (8 * (Real.log ((q : ℝ) * T) + 6) / T ^ 2) := by
    let U := Z.filter (fun z => F z ≠ 0)
    have hU (z : ℂ) (hz : z ∈ U) := hF z (Finset.mem_filter.mp hz).2
    calc
      _ = ∑ z ∈ U, F z := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro z hz hzu
        by_contra hnez
        exact hzu (Finset.mem_filter.mpr ⟨hz, hnez⟩)
      _ ≤ ∑ z ∈ U, A * ((analyticOrderNatAt χ.LFunction z : ℝ) / |z.im| ^ 3) :=
        Finset.sum_le_sum (fun z hz => (hU z hz).2.2)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (primitive_finite_tail_cubic_bound χ hχ hT U
          (fun z hz => ⟨(hU z hz).1, (hU z hz).2.1⟩)) hA
  exact ⟨summable_of_sum_le hF₀ hsum, Real.tsum_le_of_sum_le hF₀ hsum⟩

end GoldbachZeroCount
end

section
namespace GoldbachZeroCount

open scoped BigOperators

private noncomputable def shortHeightWeight (k : ℕ) : ℝ :=
  if k = 0 then 2 else 1 / (k : ℝ)

private theorem shortHeightWeight_nonneg (k : ℕ) : 0 ≤ shortHeightWeight k := by
  unfold shortHeightWeight
  split <;> positivity

private theorem shortHeightWeight_sum :
    (∑ k ∈ Finset.range 8, shortHeightWeight k) ≤ (23 / 5 : ℝ) := by
  norm_num [Finset.sum_range_succ, shortHeightWeight]

private theorem log_1008_le_seven : Real.log 1008 ≤ 7 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  rw [show (7 : ℝ) = (7 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
  exact (show (1008 : ℝ) ≤ (271 / 100 : ℝ) ^ 7 by norm_num).trans
    (pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 7)

private theorem short_bin_log_le {q : ℝ} (hq : 0 < q) {k : ℕ} (hk : k < 8) :
    Real.log (96 * q * ((k : ℝ) + 7 / 2)) ≤ Real.log q + 7 := by
  have hk' : (k : ℝ) ≤ 7 := by exact_mod_cast (Nat.le_of_lt_succ hk)
  rw [show 96 * q * ((k : ℝ) + 7 / 2) = q * (96 * ((k : ℝ) + 7 / 2)) by ring,
    Real.log_mul hq.ne' (by positivity)]
  have h : 96 * ((k : ℝ) + 7 / 2) ≤ 1008 := by linarith
  have hlog := (Real.log_le_log (by positivity) h).trans log_1008_le_seven
  linarith

private theorem short_reference_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (H : ℂ → ℂ) (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, z.re = 1 / 2 ∧ |z.im| < 8)
    (hH : ∀ z ∈ Z, ‖H z‖ ≤ (3 / 2) * shortHeightWeight (tailBin 0 z)) :
    (∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℝ) * ‖H z‖) ≤
      (567 / 10) * (Real.log q + 7) := by
  classical
  let w (z : ℂ) : ℝ := (analyticOrderNatAt χ.LFunction z : ℝ)
  let B (k : ℕ) := Z.filter (fun z => tailBin 0 z = k)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq
  have hmap {z : ℂ} (hz : z ∈ Z) : tailBin 0 z ∈ Finset.range 8 := by
    apply Finset.mem_range.mpr
    have hz' := (tailBin_bounds (T := 0) (abs_nonneg z.im)).1
    have : (tailBin 0 z : ℝ) < 8 := by linarith [(hZ z hz).2]
    exact_mod_cast this
  have hcount (k : ℕ) (hk : k < 8) :
      (∑ z ∈ B k, w z) ≤ (41 / 5) * (Real.log q + 7) := by
    let t : ℝ := (k : ℝ) + 1 / 2
    have ht : 0 ≤ t := by dsimp [t]; positivity
    let P := (B k).filter (fun z => 0 ≤ z.im)
    let N := (B k).filter (fun z => ¬ 0 ≤ z.im)
    have hb {z : ℂ} (hz : z ∈ B k) :
        z.re = 1 / 2 ∧ (k : ℝ) ≤ |z.im| ∧ |z.im| < (k : ℝ) + 1 := by
      obtain ⟨hz, hk⟩ := Finset.mem_filter.mp hz
      exact ⟨(hZ z hz).1, by simpa [hk] using tailBin_bounds (T := 0) (abs_nonneg z.im)⟩
    have hp : ∀ z ∈ P, z.re = 1 / 2 ∧ |z.im - t| ≤ 1 / 2 := by
      intro z hz
      obtain ⟨hz, hs⟩ := Finset.mem_filter.mp hz
      obtain ⟨hre, hlo, hhi⟩ := hb hz
      rw [abs_of_nonneg hs] at hlo hhi
      exact ⟨hre, abs_le.mpr ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩⟩
    have hn : ∀ z ∈ N, z.re = 1 / 2 ∧ |z.im - (-t)| ≤ 1 / 2 := by
      intro z hz
      obtain ⟨hz, hs⟩ := Finset.mem_filter.mp hz
      obtain ⟨hre, hlo, hhi⟩ := hb hz
      rw [abs_of_neg (lt_of_not_ge hs)] at hlo hhi
      exact ⟨hre, abs_le.mpr ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩⟩
    have h₁ := nonprincipal_window_order_le χ hχ t P hp
    have h₂ := nonprincipal_window_order_le χ hχ (-t) N hn
    rw [abs_of_nonneg ht] at h₁
    rw [abs_neg, abs_of_nonneg ht] at h₂
    rw [← Finset.sum_filter_add_sum_filter_not (B k) (fun z => 0 ≤ z.im) w]
    have hlog := short_bin_log_le (q := q) (by positivity : (0 : ℝ) < q) hk
    rw [show (k : ℝ) + 7 / 2 = t + 3 by dsimp [t]; ring] at hlog
    dsimp only [w]
    linarith
  calc
    _ = ∑ k ∈ Finset.range 8, ∑ z ∈ B k, w z * ‖H z‖ :=
      (Finset.sum_fiberwise_of_maps_to (fun z hz => hmap hz) _).symm
    _ ≤ ∑ k ∈ Finset.range 8, ((41 / 5) * (Real.log q + 7)) * ((3 / 2) * shortHeightWeight k) := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        _ ≤ ∑ z ∈ B k, w z * ((3 / 2) * shortHeightWeight k) := by
          apply Finset.sum_le_sum
          intro z hz
          obtain ⟨hz, hk⟩ := Finset.mem_filter.mp hz
          exact mul_le_mul_of_nonneg_left (by simpa only [hk] using hH z hz) (by dsimp [w]; positivity)
        _ = (∑ z ∈ B k, w z) * ((3 / 2) * shortHeightWeight k) := by rw [Finset.sum_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (hcount k (Finset.mem_range.mp hk))
          (mul_nonneg (by norm_num) (shortHeightWeight_nonneg k))
    _ = (123 / 10) * (Real.log q + 7) * ∑ k ∈ Finset.range 8, shortHeightWeight k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ _ := by
      have he := mul_le_mul_of_nonneg_left shortHeightWeight_sum
        (by positivity : 0 ≤ (123 / 10 : ℝ) * (Real.log q + 7))
      linarith

private theorem long_reference_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (H : ℂ → ℂ) (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, z.re = 1 / 2 ∧ 8 ≤ |z.im|)
    (hH : ∀ z ∈ Z, ‖H z‖ ≤ 96 / |z.im| ^ 3) :
    (∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℝ) * ‖H z‖) ≤
      (71 / 10) * Real.log q + 61 := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq
  obtain ⟨m, hm⟩ := finite_tail_binned hq (by norm_num : (2 : ℝ) ≤ 8)
    χ.LFunction Z hZ (fun t _ U hU => by
      simpa only [Nat.cast_sum] using nonprincipal_window_order_le χ hχ t U hU) log_264_le
  have hplain : (∑ k ∈ Finset.range (m + 1), 1 / (8 + (k : ℝ)) ^ 3) ≤ (4 / 7 : ℝ) / 64 := by
    have h := GoldbachR581.Triangular.sum_reciprocal_cubes_after_first 8 (by norm_num) m
    have hp : 0 ≤ ((8 + (m : ℝ) + 1 / 2) ^ 2)⁻¹ := by positivity
    rw [Finset.sum_range_succ']
    push_cast
    simp only [add_zero, ← add_assoc]
    norm_num at h ⊢
    linarith
  have hw : (∑ k ∈ Finset.range (m + 1), (k : ℝ) / (8 + (k : ℝ)) ^ 3) ≤ 1 / 16 := by
    rw [Finset.sum_range_succ']
    push_cast
    have h := GoldbachR581.Triangular.sum_weighted_reciprocal_cubes 8 (by norm_num) m
    norm_num at h ⊢
    simpa [add_assoc] using h
  have hL : 0 ≤ Real.log ((q : ℝ) * 8) := Real.log_nonneg (by nlinarith)
  have hlog8 : Real.log 8 ≤ (21 / 10 : ℝ) := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have hsum (k : ℕ) :
      (Real.log ((q : ℝ) * 8) + 28 / 5 + (k : ℝ) / 8) / (8 + (k : ℝ)) ^ 3 =
      (Real.log ((q : ℝ) * 8) + 28 / 5) * (1 / (8 + (k : ℝ)) ^ 3) +
        (1 / 8) * ((k : ℝ) / (8 + (k : ℝ)) ^ 3) := by ring
  calc
    _ ≤ ∑ z ∈ Z, 96 * ((analyticOrderNatAt χ.LFunction z : ℝ) / |z.im| ^ 3) := by
      apply Finset.sum_le_sum
      intro z hz
      rw [← mul_div_assoc, mul_comm (96 : ℝ), mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (hH z hz) (Nat.cast_nonneg _)
    _ ≤ 96 * ((41 / 5) * ∑ k ∈ Finset.range (m + 1),
        (Real.log ((q : ℝ) * 8) + 28 / 5 + (k : ℝ) / 8) / (8 + (k : ℝ)) ^ 3) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hm (by norm_num)
    _ ≤ 96 * ((41 / 5) * ((Real.log ((q : ℝ) * 8) + 28 / 5) * (4 / 7 / 64) +
        1 / 8 * (1 / 16))) := by
      simp only [hsum, Finset.sum_add_distrib, ← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add (mul_le_mul_of_nonneg_left hplain (by positivity))
        (mul_le_mul_of_nonneg_left hw (by norm_num))
    _ ≤ _ := by
      rw [Real.log_mul (by positivity) (by norm_num)]
      linarith

/-- Uniform bound for the contribution of the lower triangular transition on the critical line. -/
theorem finite_reference_zero_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (H : ℂ → ℂ) (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, z.re = 1 / 2)
    (hnear : ∀ z ∈ Z, ‖H z‖ ≤ 3)
    (hmiddle : ∀ z ∈ Z, 1 ≤ |z.im| → ‖H z‖ ≤ (3 / 2) / |z.im|)
    (hfar : ∀ z ∈ Z, 8 ≤ |z.im| → ‖H z‖ ≤ 96 / |z.im| ^ 3) :
    (∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℝ) * ‖H z‖) ≤
      64 * Real.log q + 465 := by
  classical
  let P := Z.filter (fun z => |z.im| < 8)
  let N := Z.filter (fun z => ¬ |z.im| < 8)
  have hp : ∀ z ∈ P, z.re = 1 / 2 ∧ |z.im| < 8 := by
    intro z hz
    obtain ⟨hz, ht⟩ := Finset.mem_filter.mp hz
    exact ⟨hZ z hz, ht⟩
  have hn : ∀ z ∈ N, z.re = 1 / 2 ∧ 8 ≤ |z.im| := by
    intro z hz
    obtain ⟨hz, ht⟩ := Finset.mem_filter.mp hz
    exact ⟨hZ z hz, le_of_not_gt ht⟩
  have hP := short_reference_sum χ hχ H P hp (by
    intro z hz
    have hz' := (Finset.mem_filter.mp hz).1
    have hbin : (tailBin 0 z : ℝ) ≤ |z.im| := by
      simpa using (tailBin_bounds (T := 0) (abs_nonneg z.im)).1
    unfold shortHeightWeight
    by_cases hk : tailBin 0 z = 0
    · simpa [hk] using hnear z hz'
    · simp only [hk, ite_false]
      rw [← mul_div_assoc, mul_one]
      have hk' : (1 : ℝ) ≤ tailBin 0 z := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      exact (hmiddle z hz' (hk'.trans hbin)).trans
        (div_le_div_of_nonneg_left (by norm_num) (by linarith) hbin))
  have hN := long_reference_sum χ hχ H N hn (by
    intro z hz
    exact hfar z (Finset.mem_filter.mp hz).1 (hn z hz).2)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq
  rw [← Finset.sum_filter_add_sum_filter_not Z (fun z => |z.im| < 8) (fun z =>
    (analyticOrderNatAt χ.LFunction z : ℝ) * ‖H z‖)]
  change (∑ z ∈ P, _) + (∑ z ∈ N, _) ≤ _
  linarith

/-- Version of the lower-transition estimate for its absolutely convergent zero sum. -/
theorem tsum_reference_zero_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (H : ℂ → ℂ) (F : ℂ → ℝ) (hF₀ : ∀ z, 0 ≤ F z)
    (hF : ∀ z, F z ≠ 0 → z.re = 1 / 2 ∧
      F z ≤ (analyticOrderNatAt χ.LFunction z : ℝ) * ‖H z‖ ∧ ‖H z‖ ≤ 3 ∧
      (1 ≤ |z.im| → ‖H z‖ ≤ (3 / 2) / |z.im|) ∧
      (8 ≤ |z.im| → ‖H z‖ ≤ 96 / |z.im| ^ 3)) :
    Summable F ∧ (∑' z : ℂ, F z) ≤ 64 * Real.log q + 465 := by
  classical
  have hsum (Z : Finset ℂ) : (∑ z ∈ Z, F z) ≤ 64 * Real.log q + 465 := by
    let U := Z.filter (fun z => F z ≠ 0)
    have hU (z : ℂ) (hz : z ∈ U) := hF z (Finset.mem_filter.mp hz).2
    calc
      _ = ∑ z ∈ U, F z := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro z hz hzu
        by_contra hnez
        exact hzu (Finset.mem_filter.mpr ⟨hz, hnez⟩)
      _ ≤ ∑ z ∈ U, (analyticOrderNatAt χ.LFunction z : ℝ) * ‖H z‖ :=
        Finset.sum_le_sum (fun z hz => (hU z hz).2.1)
      _ ≤ _ := finite_reference_zero_sum χ hχ H U
        (fun z hz => (hU z hz).1) (fun z hz => (hU z hz).2.2.1)
        (fun z hz => (hU z hz).2.2.2.1) (fun z hz => (hU z hz).2.2.2.2)
  exact ⟨summable_of_sum_le hF₀ hsum, Real.tsum_le_of_sum_le hF₀ hsum⟩

end GoldbachZeroCount

namespace GoldbachR581.Triangular

/-- Absorb the lower critical-line correction and the trivial zeros in the frozen quadratic budget. -/
theorem reference_and_trivial_budget {q x δ A B : ℝ} (hq : 2 ≤ q) (hx : 2 ≤ x)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (hA : A ≤ 64 * Real.log q + 465)
    (hB : B ≤ 5 * (Real.log x + δ - 1 / 8)) :
    A + B ≤ 16 * (Real.log (q * x / δ) + 4) ^ 2 := by
  have hlog2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogx : (2 / 3 : ℝ) ≤ Real.log x := hlog2.trans (Real.log_le_log (by norm_num) hx)
  have hlogq : (2 / 3 : ℝ) ≤ Real.log q := hlog2.trans (Real.log_le_log (by norm_num) hq)
  have hlogδ : Real.log δ ≤ -(2 / 3 : ℝ) := by
    have h := Real.log_le_log hδ hδ'
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv] at h
    linarith
  rw [Real.log_div (by positivity) hδ.ne', Real.log_mul (by positivity) (by positivity)]
  let L := Real.log q + Real.log x - Real.log δ + 4
  have hL : 6 ≤ L := by dsimp [L]; linarith
  have hsum : A + B ≤ 64 * L + 170 := by dsimp [L]; linarith
  change A + B ≤ 16 * L ^ 2
  nlinarith [mul_nonneg (sub_nonneg.mpr hL) (show 0 ≤ 16 * L + 32 by linarith)]

end GoldbachR581.Triangular
end

section
open MeasureTheory Set Filter Complex DirichletCharacter
open scoped BigOperators ArithmeticFunction

namespace GoldbachR581.Triangular

noncomputable def criticalWeighted {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (W : ℂ → ℂ) (z : ℂ) : ℂ := by
  classical
  exact if 0 < z.re ∧ z.re < 1 ∧ χ.LFunction z = 0 then
    ((analyticOrderNatAt χ.LFunction z : ℕ) : ℂ) * W z else 0

private theorem dirichletOrder_eq_natOrder {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {z : ℂ} (hz : z.re < 1) : dirichletOrder χ z = (analyticOrderNatAt χ.LFunction z : ℤ) := by
  have ha : AnalyticAt ℂ χ.LFunction z := analyticAt_dirichletL_of_regular_parameter (.inl (by
    intro he
    norm_num [he] at hz))
  have hm := meromorphicOrderAt_dirichletL_ne_top χ z
  rw [ha.meromorphicOrderAt_eq] at hm
  have hn : analyticOrderAt χ.LFunction z ≠ ⊤ := by
    intro ht
    simp [ht] at hm
  apply WithTop.coe_injective
  rw [dirichletOrder_spec, ha.meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt hn]
  simp

private theorem criticalWeighted_eq_order {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (W : ℂ → ℂ) (z : ℂ) : criticalWeighted χ W z = dirichletCriticalZeroTerm χ W z := by
  classical
  by_cases hz : z.re ∈ Ioo (0 : ℝ) 1
  · rcases eq_or_ne (χ.LFunction z) 0 with hzero | hzero
    · rw [criticalWeighted, if_pos ⟨hz.1, hz.2, hzero⟩, dirichletCriticalZeroTerm, if_pos hz,
        dirichletOrder_eq_natOrder χ hz.2, Int.cast_natCast]
    · have ha : AnalyticAt ℂ χ.LFunction z := analyticAt_dirichletL_of_regular_parameter (.inl (by
      intro he
      have h := hz.2
      norm_num [he] at h))
      have horder := (ha.analyticOrderAt_eq_zero).2 hzero
      simp [criticalWeighted, hzero, dirichletCriticalZeroTerm, hz, dirichletOrder_eq_natOrder χ hz.2,
        analyticOrderNatAt, horder]
  · rw [criticalWeighted, if_neg (fun h => hz ⟨h.1, h.2.1⟩), dirichletCriticalZeroTerm, if_neg hz]

private theorem norm_trivial_goldbachWindow {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 2 ≤ q) {x δ : ℝ} (hx : 2 ≤ x) (hδ : 0 < δ) (hd : δ ≤ 1 / 2) :
    ‖∑' n, laplaceTransform (goldbachWindow x δ) (dirichletTrivialZero χ n)‖ ≤
      5 * (Real.log x + δ - 1 / 8) := by
  have he := goldbachWindow_endpoints hx hδ hd
  have ha : (1 / 8 : ℝ) ≤ Real.log x + δ := by
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith [Real.log_two_gt_d9]
  change ‖∑' n, laplace (goldbachWindow x δ) (dirichletTrivialZero χ n)‖ ≤ _
  refine norm_laplace_tsum_of_negative_real_parts ha
    (continuous_iff_continuousAt.mpr fun t =>
      (difference_hasDerivAt (c := Real.log x) (c₀ := 3 / 8) (d₀ := 1 / 4) hδ (by norm_num) t).continuousAt)
    (difference_tsupport hδ (by norm_num) he.1 he.2)
    (norm_difference_le_one hδ (by norm_num)) (dirichletTrivialZero χ) ?_
  intro n
  classical
  rw [dirichletTrivialZero, if_neg (by omega : q ≠ 1)]
  split_ifs <;> simp [Complex.mul_re] <;> linarith

noncomputable def upperReference (x δ : ℝ) (z : ℂ) : ℂ :=
  (x : ℂ) ^ z * mellin δ z / z

private theorem laplace_goldbachWindow {x δ : ℝ} {z : ℂ}
    (hx : 2 ≤ x) (hδ : 0 < δ) (hz : z ≠ 0) :
    laplaceTransform (goldbachWindow x δ) z = upperReference x δ z - lowerReference z := by
  change laplace (difference (Real.log x) δ (3 / 8) (1 / 4)) z = _
  rw [laplace_difference hδ (by norm_num) hz, sub_div, upperReference, lowerReference,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (by linarith : x ≠ 0)),
    ← Complex.ofReal_log (by linarith : 0 ≤ x)]

theorem goldbach_explicit_formula_of_lower_budget
    (hgrh : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → χ.LFunction s ≠ 0)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive)
    {x δ T : ℝ} (hx : 2 ≤ x) (hδ : 0 < δ) (hd : δ ≤ 1 / 2) (hT : 2 ≤ T)
    (hLower : Summable (fun z : ℂ => ‖criticalWeighted χ lowerReference z‖))
    (hBudget : (∑' z : ℂ, ‖criticalWeighted χ lowerReference z‖) +
        5 * (Real.log x + δ - 1 / 8) ≤ 16 * (Real.log ((q : ℝ) * x / δ) + 4) ^ 2) :
    ∃ Z : Finset ℂ,
      (∀ z, z ∈ Z ↔ 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T ∧ χ.LFunction z = 0) ∧
      ‖(∑ n ∈ Finset.Icc 1 ⌊Real.exp δ * x⌋₊,
          ((ArithmeticFunction.vonMangoldt n * window δ (Real.log ((n : ℝ) / x)) : ℝ) : ℂ) *
            χ (n : ZMod q)) +
        ∑ z ∈ Z, ((analyticOrderNatAt χ.LFunction z : ℕ) : ℂ) * (x : ℂ) ^ z * mellin δ z / z‖ ≤
        32 * Real.sqrt x * Real.exp (δ / 2) * (Real.log ((q : ℝ) * T) + 6) / (δ ^ 2 * T ^ 2) +
          16 * (Real.log ((q : ℝ) * x / δ) + 4) ^ 2 := by
  classical
  obtain ⟨Z, hZ⟩ := GoldbachZeroCount.exists_nontrivial_character_zero_finset χ T
  refine ⟨Z, hZ, ?_⟩
  let H := goldbachWindow x δ
  let F := upperReference x δ
  let L := criticalWeighted χ lowerReference
  let U (z : ℂ) := if T < |z.im| then criticalWeighted χ F z else 0
  let V (z : ℂ) := if z ∈ Z then ((analyticOrderNatAt χ.LFunction z : ℕ) : ℂ) * F z else 0
  let A := 4 * Real.sqrt x * Real.exp (δ / 2) / δ ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hU (z : ℂ) (hz : ‖U z‖ ≠ 0) : z.re = 1 / 2 ∧ T ≤ |z.im| ∧
      ‖U z‖ ≤ A * ((analyticOrderNatAt χ.LFunction z : ℝ) / |z.im| ^ 3) := by
    have hTz : T < |z.im| := by by_contra h; exact hz (by simp [U, h])
    have hRoot : 0 < z.re ∧ z.re < 1 ∧ χ.LFunction z = 0 := by
      by_contra h
      exact hz (by simp [U, hTz, criticalWeighted, h])
    have hRe := re_eq_half_of_grh hgrh hχ hRoot.1 hRoot.2.1 hRoot.2.2
    refine ⟨hRe, hTz.le, ?_⟩
    have hi : 0 < |z.im| := by linarith
    have hF : ‖F z‖ ≤ A / |z.im| ^ 3 := by
      have h := norm_upperReference_le_cube (by linarith : 0 < x) hδ hRe hi
      simpa only [F, A, upperReference, div_div] using h
    dsimp only [U]
    rw [if_pos hTz, criticalWeighted, if_pos hRoot, norm_mul, Complex.norm_natCast]
    exact (mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg _)).trans_eq (by ring)
  obtain ⟨hUsum, hUbound⟩ := GoldbachZeroCount.primitive_tsum_tail_norm_bound χ hχ hT hA
    (fun z => ‖U z‖) (fun _ => norm_nonneg _) hU
  have hVzero (z : ℂ) (hz : z ∉ Z) : V z = 0 := if_neg hz
  have hVsum : Summable V := summable_of_ne_finset_zero (s := Z) hVzero
  have hVeq : (∑' z, V z) = ∑ z ∈ Z, ((analyticOrderNatAt χ.LFunction z : ℕ) : ℂ) * F z := by
    rw [tsum_eq_sum hVzero]
    exact Finset.sum_congr rfl fun z hz => if_pos hz
  have hsplit (z : ℂ) : dirichletCriticalZeroTerm χ (laplaceTransform H) z = V z + U z - L z := by
    rw [← criticalWeighted_eq_order]
    by_cases hRoot : 0 < z.re ∧ z.re < 1 ∧ χ.LFunction z = 0
    · have hz₀ : z ≠ 0 := fun he => by simpa [he] using hRoot.1
      have hZz : z ∈ Z ↔ |z.im| ≤ T := by simp [hZ, hRoot.1, hRoot.2.1, hRoot.2.2]
      have hL : L z = ((analyticOrderNatAt χ.LFunction z : ℕ) : ℂ) * lowerReference z := by
        simp only [L, criticalWeighted, if_pos hRoot]
      rw [criticalWeighted, if_pos hRoot, show H = goldbachWindow x δ from rfl,
        laplace_goldbachWindow hx hδ hz₀, hL]
      dsimp only [U, V]
      rcases le_or_gt |z.im| T with ht | ht
      · rw [if_pos (hZz.mpr ht), if_neg (not_lt.mpr ht), add_zero]
        dsimp [F]
        ring
      · rw [if_neg (fun h => (not_le.mpr ht) (hZz.mp h)), if_pos ht, criticalWeighted, if_pos hRoot, zero_add]
        dsimp [F]
        ring
    · have hZz : z ∉ Z := by
        intro hm
        have h := (hZ z).mp hm
        exact hRoot ⟨h.1, h.2.1, h.2.2.2⟩
      simp [criticalWeighted, hRoot, U, V, L, hZz]
  have hcrit : (∑' z, dirichletCriticalZeroTerm χ (laplaceTransform H) z) =
      (∑' z, V z) + (∑' z, U z) - (∑' z, L z) := by
    simp_rw [hsplit]
    rw [Summable.tsum_sub (hVsum.add hUsum.of_norm) hLower.of_norm,
      Summable.tsum_add hVsum hUsum.of_norm]
  have he := goldbachWindow_endpoints hx hδ hd
  have hcont : Continuous H := continuous_iff_continuousAt.mpr fun t =>
    (difference_hasDerivAt (c := Real.log x) (c₀ := 3 / 8) (d₀ := 1 / 4) hδ (by norm_num) t).continuousAt
  have hsupp : tsupport H ⊆ Icc (1 / 8 : ℝ) (Real.log x + δ) :=
    difference_tsupport hδ (by norm_num) he.1 he.2
  have hDecay : HasLaplaceCubicDecay H (1 / 8) (Real.log x + δ) :=
    laplace_difference_cubic_decay hδ (by norm_num) he.1 he.2
  have hab : (1 / 8 : ℝ) ≤ Real.log x + δ := by
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith [Real.log_two_gt_d9]
  have hmain := mangoldtSum_eq_full_zero_sums_of_cubic hχ hcont hsupp hab hDecay (by norm_num)
  rw [if_neg (by omega : q ≠ 1), zero_sub, hcrit, hVeq] at hmain
  have hprime := goldbachWindow_mangoldt_sum χ hx hδ
  change mangoldtSum χ H = _ at hprime
  have hprimary : (∑ z ∈ Z, ((analyticOrderNatAt χ.LFunction z : ℕ) : ℂ) * (x : ℂ) ^ z * mellin δ z / z) =
      ∑ z ∈ Z, ((analyticOrderNatAt χ.LFunction z : ℕ) : ℂ) * F z := by
    apply Finset.sum_congr rfl
    intro z _
    simp only [F, upperReference]
    rw [← mul_div_assoc, mul_assoc]
  rw [← hprime, hprimary, hmain]
  have htriv := norm_trivial_goldbachWindow χ hq hx hδ hd
  have hfinalTail : A * (8 * (Real.log ((q : ℝ) * T) + 6) / T ^ 2) =
      32 * Real.sqrt x * Real.exp (δ / 2) * (Real.log ((q : ℝ) * T) + 6) / (δ ^ 2 * T ^ 2) := by
    dsimp [A]
    field_simp [hδ.ne', (show T ≠ 0 by linarith)] <;> ring
  rw [show -(∑' n, laplaceTransform H (dirichletTrivialZero χ n)) -
      ((∑ z ∈ Z, ((analyticOrderNatAt χ.LFunction z : ℕ) : ℂ) * F z) + (∑' z, U z) - (∑' z, L z)) +
      (∑ z ∈ Z, ((analyticOrderNatAt χ.LFunction z : ℕ) : ℂ) * F z) =
      -(∑' z, U z) + ((∑' z, L z) - ∑' n, laplaceTransform H (dirichletTrivialZero χ n)) by abel]
  apply (norm_add_le _ _).trans
  rw [norm_neg, ← hfinalTail]
  refine add_le_add ((norm_tsum_le_tsum_norm hUsum).trans hUbound) ?_
  exact (norm_sub_le _ _).trans ((add_le_add (norm_tsum_le_tsum_norm hLower) htriv).trans hBudget)

end GoldbachR581.Triangular
end

section
open GoldbachR581.Triangular
open scoped BigOperators

theorem Conjectures.Goldbach.GmSmoothedExplicitFormula :
    (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0) → ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 2 ≤ q → χ.IsPrimitive → ∀ (x δ T : ℝ), 2 ≤ x → 0 < δ → δ ≤ 1 / 2 → 2 ≤ T → let Φ : ℝ → ℝ := fun w => if w ≤ -δ then 1 else if w ≤ 0 then 1 - (w + δ) ^ 2 / (2 * δ ^ 2) else if w < δ then (δ - w) ^ 2 / (2 * δ ^ 2) else 0; let M : ℂ → ℂ := fun s => ((Complex.exp (((δ / 2 : ℝ) : ℂ) * s) - Complex.exp (((-(δ / 2) : ℝ) : ℂ) * s)) / ((δ : ℂ) * s)) ^ 2; ∃ Z : Finset ℂ, (∀ s : ℂ, s ∈ Z ↔ 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ DirichletCharacter.LFunction χ s = 0) ∧ ‖(∑ n ∈ Finset.Icc 1 ⌊Real.exp δ * x⌋₊, ((ArithmeticFunction.vonMangoldt n * Φ (Real.log ((n : ℝ) / x)) : ℝ) : ℂ) * χ (n : ZMod q)) + ∑ ρ ∈ Z, ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℂ) * (x : ℂ) ^ ρ * M ρ / ρ‖ ≤ 32 * Real.sqrt x * Real.exp (δ / 2) * (Real.log ((q : ℝ) * T) + 6) / (δ ^ 2 * T ^ 2) + 16 * (Real.log ((q : ℝ) * x / δ) + 4) ^ 2 := by
  intro hGRH q _ χ hq hχ x δ T hx hδ hd hT
  classical
  have hnonprincipal : χ ≠ 1 := by
    intro he
    have heq : q = 1 := by simpa only [he, DirichletCharacter.conductor_one] using hχ.symm
    omega
  let F (z : ℂ) := ‖criticalWeighted χ lowerReference z‖
  obtain ⟨hSum, hBound⟩ := GoldbachZeroCount.tsum_reference_zero_bound χ hnonprincipal
    lowerReference F (fun _ => norm_nonneg _) (by
      intro z hz
      have hRoot : 0 < z.re ∧ z.re < 1 ∧ χ.LFunction z = 0 := by
        by_contra h
        exact hz (by simp [F, criticalWeighted, h])
      have hre := re_eq_half_of_grh hGRH hχ hRoot.1 hRoot.2.1 hRoot.2.2
      refine ⟨hre, ?_, ?_, ?_, ?_⟩
      · simp only [F, criticalWeighted, if_pos hRoot, norm_mul, Complex.norm_natCast, le_refl]
      · exact (norm_lowerReference_le_two hre).trans_eq (by norm_num)
      · intro hi
        exact norm_lowerReference_le_inv hre (by linarith) le_rfl
      · intro hi
        exact (norm_lowerReference_le_cube hre (by linarith) le_rfl).trans_eq (by norm_num))
  have hBudget := reference_and_trivial_budget (show (2 : ℝ) ≤ q by exact_mod_cast hq) hx hδ hd hBound
    (le_refl (5 * (Real.log x + δ - 1 / 8)))
  exact goldbach_explicit_formula_of_lower_budget hGRH hq hχ hx hδ hd hT hSum hBudget
end
