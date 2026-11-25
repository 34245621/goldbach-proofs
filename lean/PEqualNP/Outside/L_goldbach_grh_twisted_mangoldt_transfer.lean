import Mathlib
import PEqualNP.Outside.L_goldbach_grh_dirichlet_twisted_zero_prefix

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

/-- Transfer a sharp untwisted explicit-formula remainder for the character
Mangoldt sum to an additive twist. GRH supplies the zero-counting input.
The size of the sharp untwisted remainder E remains an explicit assumption. -/
theorem _root_.PEqualNP.Outside.L_goldbach_grh_twisted_mangoldt_transfer :
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
  obtain ⟨C,hC,prefixBound⟩ := PEqualNP.Outside.L_goldbach_grh_dirichlet_twisted_zero_prefix hGRH
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

end TwistedZeroApplication