import Mathlib

/-!
# Analytic steps for primes in short arithmetic progressions
These statements support the short-progression input of catalogue proposal 2844.
The prime-power transfer holds over the full stated range, and the twisted Heath-Brown
identity applies to moving endpoints. The high-frequency estimate integrates both signs
to infinity, for all characters of a fixed positive modulus, with an explicit constant.
The middle-frequency cancellation needed for the short-progression input remains open here.

The finite-character Parseval proof is adapted from LogTruSoul in goldbach-proofs PR 2829
(commit cfde193e18afc4e0ffac53868d514142e908cd36), derived from PR 2486
(commit f3613cf846dfb3e7fe7d04fe6ce51c6ee25e7d4f), Apache-2.0.
Mathematical reference: D. Koukoulopoulos, Primes in short arithmetic progressions,
Theorem 1.2 and Section 4.
-/

open Finset Filter MeasureTheory
open scoped Topology Interval Classical
namespace GBSkirtVariance
noncomputable section

def thetaClass (q : ℕ) [NeZero q] (r : ZMod q) (y h : ℝ) : ℝ :=
  ∑ k ∈ (Icc (⌊y⌋₊+1) ⌊y+(h:ℝ)⌋₊).filter (fun k : ℕ => (k:ZMod q)=r),
    if k.Prime then Real.log (k:ℝ) else 0

theorem theta_window_spec {y : ℝ} (hy : 0≤y) (h k : ℕ) :
    k ∈ Icc (⌊y⌋₊+1) ⌊y+(h:ℝ)⌋₊ ↔ y < (k:ℝ) ∧ (k:ℝ) ≤ y+h := by
  rw [mem_Icc,Nat.le_floor_iff (by positivity)]
  exact and_congr_left fun _ => by rw [Nat.succ_le_iff,Nat.floor_lt hy]

def realError (q : ℕ) (h y : ℝ) : ℝ := if hq : q=0 then 0 else
  letI : NeZero q := ⟨hq⟩
  (univ : Finset (ZMod q)).sup' univ_nonempty (fun r =>
    if IsUnit r then |thetaClass q r y h - (h:ℝ)/(q.totient:ℝ)| else 0)

def realRow (Q : ℕ) (h y : ℝ) := ∑ q ∈ Icc 1 Q, realError q h y

end
end GBSkirtVariance

open Filter MeasureTheory
open scoped Topology Interval Classical
namespace GBSkirtVariance
noncomputable section

/-- Fixed A=18 and ε=1/16 in the upper θ range in Theorem 1.2 of
D. Koukoulopoulos, Primes in short arithmetic progressions. -/
def PaperInput : Prop := ∃ C : ℝ, 0 < C ∧ ∃ X : ℕ,
  ∀ x θ : ℝ, (X:ℝ) ≤ x → 1 ≤ x → 5/8 ≤ θ → θ ≤ 1 → ∀ Q : ℕ, 1≤Q →
    (Q:ℝ)^2*x^((1-θ)/3+1/16) ≤ x^θ →
    (∫ y in x..2*x, realRow Q (x^θ) y) ≤ C*x*x^θ/(Real.log x)^18

end
end GBSkirtVariance

open Finset Filter MeasureTheory
open scoped Topology Interval Classical
namespace GBSkirtVariance
noncomputable section

def ordinary (k : ℕ) : ℝ := if k.Prime then Real.log (k:ℝ) else 0
def excess (k : ℕ) := ArithmeticFunction.vonMangoldt k - ordinary k

theorem excess_nonneg (k : ℕ) : 0 ≤ excess k := by
  unfold excess ordinary
  split_ifs with hp
  · simp [ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simpa using ArithmeticFunction.vonMangoldt_nonneg (n:=k)

def rollingExcess (y h : ℝ) := ∑ k ∈ Icc (⌊y⌋₊+1) ⌊y+h⌋₊, excess k

def windowHit (h : ℝ) (k : ℕ) := (Set.Ico ((k:ℝ)-h) (k:ℝ)).indicator (fun _ : ℝ => excess k)

theorem count_by_prime_power (x h y : ℝ) (hx : 0≤x) (hh : 0≤h) (hu : h≤x)
    (hy : y ∈ Set.Icc x (2*x)) :
    rollingExcess y h = ∑ k ∈ Ioc 0 ⌊3*x⌋₊, windowHit h k y := by
  let W := Icc (⌊y⌋₊+1) ⌊y+h⌋₊
  let R := Ioc 0 ⌊3*x⌋₊
  have hy0 := hx.trans hy.1
  have hmem (k : ℕ) : k ∈ W ↔ y < (k:ℝ) ∧ (k:ℝ) ≤ y+h := by
    unfold W
    rw [mem_Icc,Nat.succ_le_iff,Nat.floor_lt hy0,Nat.le_floor_iff (by linarith)]
  have hsub : W ⊆ R := by
    intro k hk
    obtain ⟨hl,hr⟩ := (hmem k).1 hk
    apply mem_Ioc.mpr
    exact ⟨by exact_mod_cast (hy0.trans_lt hl : (0:ℝ)<k),
      (Nat.le_floor_iff (by positivity)).2 (by linarith only [hr,hy.2,hu])⟩
  calc
    _ = ∑ k ∈ W, windowHit h k y := by
      apply sum_congr rfl
      intro k hk
      obtain ⟨hl,hr⟩ := (hmem k).1 hk
      exact (Set.indicator_of_mem (show y ∈ Set.Ico ((k:ℝ)-h) (k:ℝ) from ⟨by linarith,hl⟩) (fun _ : ℝ => excess k)).symm
    _ = _ := by
      apply sum_subset hsub
      intro k _ hk
      apply Set.indicator_of_notMem
      intro he
      exact hk ((hmem k).2 ⟨he.2,by linarith only [he.1]⟩)

theorem windowHit_integrable (h : ℝ) (k : ℕ) : Integrable (windowHit h k) volume := by
  apply (integrable_indicator_iff measurableSet_Ico).2
  exact integrableOn_const (hs:=by simp)

theorem windowHit_mass (h : ℝ) (hh : 0≤h) (k : ℕ) :
    (∫ y : ℝ, windowHit h k y) = h*excess k := by
  rw [windowHit,integral_indicator_const _ measurableSet_Ico]
  simp [measureReal_def,Real.volume_Ico,hh]

theorem averaged_prime_powers (x h : ℝ) (hx : 1≤x) (hh : 0≤h) (hu : h≤x) :
    (∫ y in x..2*x, rollingExcess y h) ≤ h*(2*Real.sqrt (3*x)*Real.log (3*x)) := by
  have hx0 : 0≤x := by linarith
  let R := Ioc 0 ⌊3*x⌋₊
  let F := fun y => ∑ k ∈ R, windowHit h k y
  have hF : Integrable F volume := integrable_finsetSum _ fun k _ => windowHit_integrable _ _
  have hF0 : 0 ≤ᵐ[volume] F := Eventually.of_forall fun y => sum_nonneg fun k _ =>
    Set.indicator_nonneg (fun _ _ => excess_nonneg k) y
  have hmass : (∑ k ∈ R, excess k) = Chebyshev.psi (3*x)-Chebyshev.theta (3*x) := by
    simp [R,excess,ordinary,Finset.sum_sub_distrib,Chebyshev.psi,Chebyshev.theta,Finset.sum_filter]
  rw [intervalIntegral.integral_of_le (by linarith : x≤2*x)]
  calc
    _ = ∫ y in Set.Ioc x (2*x), F y := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro y hy
      exact count_by_prime_power x h y hx0 hh hu ⟨hy.1.le,hy.2⟩
    _ ≤ ∫ y, F y := setIntegral_le_integral hF hF0
    _ = h*(∑ k ∈ R, excess k) := by
      unfold F
      rw [integral_finsetSum _ (fun k _ => windowHit_integrable _ _),Finset.mul_sum]
      exact sum_congr rfl fun k _ => windowHit_mass h hh k
    _ ≤ _ := by rw [hmass]; exact mul_le_mul_of_nonneg_left (Chebyshev.psi_sub_theta_le (by linarith)) hh

end
end GBSkirtVariance

open Finset Filter MeasureTheory
open scoped Topology Interval Classical
namespace GBSkirtVariance
noncomputable section

def classWeight (w : ℕ → ℝ) (I : Finset ℕ) {q : ℕ} [NeZero q] (r : ZMod q) :=
  ∑ k ∈ I.filter (fun k : ℕ => (k:ZMod q)=r), w k

def residual (w : ℕ → ℝ) (I : Finset ℕ) (q : ℕ) [NeZero q] (h : ℝ) :=
  (univ : Finset (ZMod q)).sup' univ_nonempty (fun r =>
    if IsUnit r then |classWeight w I r - h/(q.totient:ℝ)| else 0)

def allResidual (w : ℕ → ℝ) (I : Finset ℕ) (Q : ℕ) (h : ℝ) :=
  ∑ q ∈ Icc 1 Q, if hq : q=0 then 0 else
    letI : NeZero q := ⟨hq⟩
    residual w I q h

def realPsiRow (Q : ℕ) (h y : ℝ) := allResidual ArithmeticFunction.vonMangoldt
  (Icc (⌊y⌋₊+1) ⌊y+h⌋₊) Q h

theorem sup_change {q : ℕ} [NeZero q] (I : Finset ℕ) (h : ℝ) :
    residual ordinary I q h ≤ residual ArithmeticFunction.vonMangoldt I q h + ∑ k ∈ I, excess k := by
  let G := fun r : ZMod q => if IsUnit r then
    |classWeight ArithmeticFunction.vonMangoldt I r - h/(q.totient:ℝ)| else 0
  have hb (r : ZMod q) : G r ≤ residual ArithmeticFunction.vonMangoldt I q h :=
    Finset.le_sup' (f:=G) (s:=univ) (mem_univ r)
  have hmass := sum_nonneg (s:=I) (fun k _ => excess_nonneg k)
  apply Finset.sup'_le
  intro r _
  by_cases hr : IsUnit r
  · rw [ite_eq_left hr]
    have h₁ := hb r
    simp only [G,ite_eq_left hr] at h₁
    let J := I.filter (fun k : ℕ => (k:ZMod q)=r)
    have hdiff : |classWeight ordinary I r - classWeight ArithmeticFunction.vonMangoldt I r|
        ≤ ∑ k ∈ I, excess k := by
      rw [abs_sub_comm]
      change |(∑ k ∈ J, ArithmeticFunction.vonMangoldt k) - ∑ k ∈ J, ordinary k| ≤ _
      rw [← sum_sub_distrib]
      change |∑ k ∈ J, excess k| ≤ _
      rw [abs_of_nonneg (sum_nonneg fun k _ => excess_nonneg k)]
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k _ _ => excess_nonneg k)
    have hh := abs_sub_le (classWeight ordinary I r) (classWeight ArithmeticFunction.vonMangoldt I r)
      (h/(q.totient:ℝ))
    linarith only [hdiff,h₁,hh]
  · rw [ite_eq_right hr]
    have h₁ := hb r
    simp only [G,ite_eq_right hr] at h₁
    linarith only [h₁,hmass]

theorem row_psi_bound (Q : ℕ) (h y : ℝ) :
    realRow Q h y ≤ realPsiRow Q h y + (Q:ℝ)*rollingExcess y h := by
  let I := Icc (⌊y⌋₊+1) ⌊y+h⌋₊
  change allResidual ordinary I Q h ≤ allResidual ArithmeticFunction.vonMangoldt I Q h + _
  unfold allResidual
  have hcard : (Icc 1 Q).card = Q := by simp
  have hid : (Q:ℝ)*rollingExcess y h = ∑ _q ∈ Icc 1 Q, ∑ k ∈ I, excess k := by simp [rollingExcess,I]
  rw [hid,← sum_add_distrib]
  apply sum_le_sum
  intro q hq
  have hp : q ≠ 0 := by have := (mem_Icc.mp hq).1; omega
  letI : NeZero q := ⟨hp⟩
  simpa only [dite_eq_right hp] using sup_change (q:=q) I h

theorem floor_pair_integrable (F : ℕ×ℕ → ℝ) (x h : ℝ) (hx : 0≤x) (hh : 0≤h) :
    IntervalIntegrable (fun y : ℝ => F (⌊y⌋₊,⌊y+h⌋₊)) volume x (2*x) := by
  let g := fun y : ℝ => (⌊y⌋₊,⌊y+h⌋₊)
  let B := range (⌊2*x+h⌋₊+1) ×ˢ range (⌊2*x+h⌋₊+1)
  have hm : Measurable g := by dsimp [g]; fun_prop
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : x≤2*x)).2
  apply Measure.integrableOn_of_bounded (M:=∑ p ∈ B, ‖F p‖) (by simp)
    ((measurable_of_countable F).comp hm).aestronglyMeasurable
  apply (ae_restrict_iff' measurableSet_Ioc).2
  apply Eventually.of_forall
  intro y hy
  apply Finset.single_le_sum (fun p (_ : p ∈ B) => norm_nonneg (F p)) (a:=g y)
  apply mem_product.mpr
  constructor
  · exact mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (by linarith only [hy.2,hh] : y≤2*x+h)))
  · exact mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (by linarith only [hy.2] : y+h≤2*x+h)))

theorem integrated_prime_power_transfer (x h : ℝ) (Q : ℕ) (hx : 1≤x) (hh : 0≤h) (hu : h≤x) :
    (∫ y in x..2*x, realRow Q h y) ≤ (∫ y in x..2*x, realPsiRow Q h y) +
        (Q:ℝ)*h*(2*Real.sqrt (3*x)*Real.log (3*x)) := by
  have hx0 : 0≤x := by linarith
  have hθ := floor_pair_integrable (fun p => allResidual ordinary (Icc (p.1+1) p.2) Q h) x h hx0 hh
  have hψ := floor_pair_integrable (fun p => allResidual ArithmeticFunction.vonMangoldt (Icc (p.1+1) p.2) Q h) x h hx0 hh
  have hE := floor_pair_integrable (fun p => ∑ k ∈ Icc (p.1+1) p.2, excess k) x h hx0 hh
  change IntervalIntegrable (realRow Q h) volume x (2*x) at hθ
  change IntervalIntegrable (realPsiRow Q h) volume x (2*x) at hψ
  change IntervalIntegrable (fun y => rollingExcess y h) volume x (2*x) at hE
  have he := hE.const_mul (Q:ℝ)
  calc
    _ ≤ ∫ y in x..2*x, (realPsiRow Q h y + (Q:ℝ)*rollingExcess y h) :=
      intervalIntegral.integral_mono_on (by linarith) hθ (hψ.add he) (fun y _ => row_psi_bound Q h y)
    _ = _ + (Q:ℝ)*(∫ y in x..2*x, rollingExcess y h) := by
      rw [intervalIntegral.integral_add hψ he,intervalIntegral.integral_const_mul]
    _ ≤ _ := by
      rw [mul_assoc]
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (averaged_prime_powers x h hx hh hu) (Nat.cast_nonneg Q))

end
end GBSkirtVariance

open Filter MeasureTheory
open scoped Topology Interval Classical
namespace GBSkirtVariance
noncomputable section

theorem modulus_cap {x θ : ℝ} (Q : ℕ) (hx : 1≤x) (ht : θ≤1)
    (hq : (Q:ℝ)^2*x^((1-θ)/3+1/16) ≤ x^θ) : (Q:ℝ) ≤ x^(15/32:ℝ) := by
  have hx0 := zero_lt_one.trans_le hx
  have hl : (Q:ℝ)^2*x^(1/16:ℝ) ≤ x := by
    calc
      _ ≤ (Q:ℝ)^2*x^((1-θ)/3+1/16) := by gcongr; linarith
      _ ≤ _ := hq.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hx ht)
  have hid : (x^(15/32:ℝ))^2*x^(1/16:ℝ) = x := by
    rw [← Real.rpow_mul_natCast hx0.le,← Real.rpow_add hx0]
    norm_num
  by_contra! bad
  have hb := pow_lt_pow_left₀ bad (Real.rpow_nonneg hx0.le _) (by decide : 2 ≠ 0)
  linarith only [mul_lt_mul_of_pos_right hb (Real.rpow_pos_of_pos hx0 (1/16:ℝ)),hid,hl]

theorem power_scale : ∀ᶠ x : ℝ in atTop, 1≤x ∧ ∀ Q : ℕ, (Q:ℝ)≤x^(15/32:ℝ) →
    (Q:ℝ)*(2*Real.sqrt (3*x)*Real.log (3*x)) ≤ x/(Real.log x)^18 := by
  have hs := (isLittleO_log_rpow_rpow_atTop (19:ℝ) (by norm_num : (0:ℝ)<1/32)).bound
    (by norm_num : (0:ℝ)<1/8)
  filter_upwards [eventually_ge_atTop (1:ℝ), Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2:ℝ)),hs]
    with x hx hL hpow
  have hx0 := zero_lt_one.trans_le hx
  let L := Real.log x
  change 2≤L at hL
  have hl0 : 0≤L := by linarith
  have hlog : Real.log (3*x) ≤ 2*L := by
    rw [Real.log_mul (by norm_num) hx0.ne']
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : 0<(3:ℝ)),hL]
  have hlog0 := Real.log_nonneg (by linarith only [hx] : 1≤3*x)
  have hsqrt : Real.sqrt (3*x) ≤ 2*x^(1/2:ℝ) := by
    rw [Real.sqrt_mul (by norm_num),← Real.sqrt_eq_rpow]
    gcongr
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg 3]
  have hs : 8*L^19 ≤ x^(1/32:ℝ) := by
    change ‖L^(19:ℝ)‖ ≤ (1/8:ℝ)*‖x^(1/32:ℝ)‖ at hpow
    rw [show (19:ℝ)=(19:ℕ) by norm_num,Real.rpow_natCast,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hl0 _),Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at hpow
    linarith
  refine ⟨hx,?_⟩
  intro Q hQ
  apply (le_div_iff₀ (by change 0<L^18; positivity)).2
  change _ * L^18 ≤ x
  calc
    _ ≤ x^(15/32:ℝ)*(2*(2*x^(1/2:ℝ))*(2*L))*L^18 := by gcongr
    _ = (x^(15/32:ℝ)*x^(1/2:ℝ))*(8*L^19) := by ring
    _ ≤ (x^(15/32:ℝ)*x^(1/2:ℝ))*x^(1/32:ℝ) := by gcongr
    _ = x := by rw [← Real.rpow_add hx0,← Real.rpow_add hx0]; norm_num

def PsiInput : Prop := ∃ C : ℝ, 0<C ∧ ∃ X : ℕ,
  ∀ x θ : ℝ, (X:ℝ)≤x → 1≤x → 5/8≤θ → θ≤1 → ∀ Q : ℕ, 1≤Q →
    (Q:ℝ)^2*x^((1-θ)/3+1/16) ≤ x^θ →
    (∫ y in x..2*x, realPsiRow Q (x^θ) y) ≤ C*x*x^θ/(Real.log x)^18

theorem theta_of_psi (hp : PsiInput) : PaperInput := by
  obtain ⟨C,hC,X,hX⟩ := hp
  obtain ⟨Y,hY⟩ := eventually_atTop.mp power_scale
  obtain ⟨N,hN⟩ := exists_nat_ge Y
  refine ⟨C+1,by linarith,max X N,?_⟩
  intro x θ hx hx1 ht htu Q hQ hmod
  have hxx : (X:ℝ) ≤ x := (by exact_mod_cast le_max_left X N : (X:ℝ) ≤ (max X N:ℕ)).trans hx
  have hyy : Y≤x := hN.trans ((by exact_mod_cast le_max_right X N : (N:ℝ) ≤ (max X N:ℕ)).trans hx)
  have hcap := (hY x hyy).2 Q (modulus_cap Q hx1 htu hmod)
  have hr : x^θ ≤ x := by simpa using Real.rpow_le_rpow_of_exponent_le hx1 htu
  have hh := Real.rpow_nonneg (zero_le_one.trans hx1) θ
  have ha := hX x θ hxx hx1 ht htu Q hQ hmod
  apply (integrated_prime_power_transfer x (x^θ) Q hx1 hh hr).trans
  have hb := mul_le_mul_of_nonneg_right hcap hh
  calc
    _ ≤ C*x*x^θ/(Real.log x)^18 + x/(Real.log x)^18*x^θ := by
      apply add_le_add ha
      convert hb using 1 <;> ring
    _ = _ := by ring

end
end GBSkirtVariance

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction.vonMangoldt
namespace GBHeathBrown
noncomputable section
abbrev A := ArithmeticFunction ℝ

def cutMu (z : ℕ) : A := ⟨fun n => if n≤z then (ArithmeticFunction.moebius n:ℝ) else 0,by simp⟩
def defect (z : ℕ) : A := 1 - (ArithmeticFunction.zeta : A)*cutMu z

theorem defect_low (z n : ℕ) (hn : n≤z) : defect z n = 0 := by
  have hconv : ((ArithmeticFunction.zeta:A)*cutMu z) n =
      ((ArithmeticFunction.zeta:A)*(ArithmeticFunction.moebius:A)) n := by
    rw [ArithmeticFunction.mul_apply,ArithmeticFunction.mul_apply]
    apply sum_congr rfl
    intro p hp
    have hmul := (Nat.mem_divisorsAntidiagonal.mp hp).1
    have hp0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp
    have hpc : p.2 ≤ n := by
      rw [← hmul]
      exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hp0)
    congr 1
    change (if p.2≤z then (ArithmeticFunction.moebius p.2:ℝ) else 0) = _
    rw [ite_eq_left (hpc.trans hn)]
    rfl
  rw [ArithmeticFunction.coe_zeta_mul_coe_moebius] at hconv
  change (1:A) n - _ = 0
  exact sub_eq_zero.mpr hconv.symm

theorem vanish_product (f g : A) (a b : ℕ) (hf : ∀ n<a, f n=0) (hg : ∀ n<b, g n=0)
    (n : ℕ) (hn : n<a*b) : (f*g) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply sum_eq_zero
  intro p hp
  by_cases hx : p.1<a
  · rw [hf _ hx,zero_mul]
  · have hy : p.2<b := by
      by_contra! hy
      exact (not_le.mpr hn) ((Nat.mul_le_mul (by omega) hy).trans_eq (Nat.mem_divisorsAntidiagonal.mp hp).1)
    rw [hg _ hy,mul_zero]

theorem defect_pow_low (z K n : ℕ) (hn : n<(z+1)^K) : (defect z ^ K) n = 0 := by
  induction K generalizing n with
  | zero =>
    have h : n=0 := by simpa only [pow_zero,Nat.lt_one_iff] using hn
    simp [h]
  | succ K ih =>
    rw [pow_succ] at hn ⊢
    exact vanish_product _ _ _ _ ih (fun m hm => defect_low z m (by omega)) n hn

theorem vanish_remainder (z K n : ℕ) (hn : n<(z+1)^K) :
    (ArithmeticFunction.vonMangoldt * defect z^K) n = 0 := by
  apply vanish_product _ _ 1 ((z+1)^K) _ (defect_pow_low z K) n (by simpa using hn)
  intro m hm
  simp [show m=0 by omega]

/-- Each term is a convolution with one log factor, j unrestricted factors and
j+1 truncated Möbius factors. The term is multiplied by (-1)^j binom(K,j+1). -/
def term (z K j : ℕ) : A :=
  ((-1:A)^j * (K.choose (j+1):A)) *
    (ArithmeticFunction.log * (ArithmeticFunction.zeta:A)^j * (cutMu z)^(j+1))

theorem binomial_form (z K : ℕ) :
    ArithmeticFunction.vonMangoldt * (1 - defect z^K) =
      ∑ j ∈ range K, term z K j := by
  let U := (ArithmeticFunction.zeta:A)*cutMu z
  have hbin : defect z^K = ∑ i ∈ range (K+1), (-U)^i*(K.choose i:A) := by
    change (1-U)^K = _
    rw [show (1-U) = -U+1 by ring,add_pow]
    simp
  rw [hbin,Finset.sum_range_succ']
  simp only [pow_zero,Nat.choose_zero_right,Nat.cast_one,mul_one,Finset.mul_sum]
  rw [show (1:A) - ((∑ j ∈ range K, (-U)^(j+1)*(K.choose (j+1):A))+1) =
    -(∑ j ∈ range K, (-U)^(j+1)*(K.choose (j+1):A)) by ring, ← Finset.sum_neg_distrib,Finset.mul_sum]
  apply sum_congr rfl
  intro j _
  unfold U term
  rw [neg_eq_neg_one_mul ((ArithmeticFunction.zeta:A)*cutMu z),mul_pow,mul_pow,
    pow_succ (-1:A) j,pow_succ (ArithmeticFunction.zeta:A) j,← ArithmeticFunction.vonMangoldt_mul_zeta]
  ring

theorem identity (z K n : ℕ) (hn : n<(z+1)^K) :
    ArithmeticFunction.vonMangoldt n = (∑ j ∈ range K, term z K j) n := by
  rw [← binomial_form,mul_sub,mul_one]
  change _ = ArithmeticFunction.vonMangoldt n - (ArithmeticFunction.vonMangoldt * defect z^K) n
  rw [vanish_remainder z K n hn,sub_zero]

end
end GBHeathBrown

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction.vonMangoldt
namespace GBHeathBrown
noncomputable section

def coeff (K j : ℕ) : ℝ := (-1:ℝ)^j * (K.choose (j+1):ℝ)
def conv (z j : ℕ) : A := ArithmeticFunction.log * (ArithmeticFunction.zeta:A)^j * (cutMu z)^(j+1)

theorem term_apply (z K j n : ℕ) : term z K j n = coeff K j * conv z j n := by
  have hc : algebraMap ℝ A (coeff K j) = (-1:A)^j*(K.choose (j+1):A) := by simp [coeff]
  unfold term
  rw [← hc, ← Algebra.smul_def]
  rfl

theorem at_integer (z K n : ℕ) (hn : n<(z+1)^K) :
    ArithmeticFunction.vonMangoldt n = ∑ j ∈ range K, coeff K j * conv z j n := by
  rw [identity z K n hn]
  have hv : ∀ s : Finset ℕ, (∑ j ∈ s, term z K j) n = ∑ j ∈ s, term z K j n := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [sum_insert ha,ih]
  rw [hv]
  exact sum_congr rfl fun j _ => term_apply z K j n

theorem weighted_identity (z K : ℕ) (I : Finset ℕ) (w : ℕ → ℂ)
    (hI : ∀ n ∈ I, n<(z+1)^K) :
    (∑ n ∈ I, w n*(ArithmeticFunction.vonMangoldt n:ℂ)) =
      ∑ j ∈ range K, (coeff K j:ℂ)*∑ n ∈ I, w n*(conv z j n:ℂ) := by
  calc
    _ = ∑ n ∈ I, ∑ j ∈ range K, (coeff K j:ℂ)*(w n*(conv z j n:ℂ)) := by
      apply sum_congr rfl
      intro n hn
      rw [at_integer z K n (hI _ hn),Complex.ofReal_sum,Finset.mul_sum]
      apply sum_congr rfl
      intro j _
      rw [Complex.ofReal_mul]
      ring
    _ = _ := by rw [sum_comm]; simp only [Finset.mul_sum]

/-- The character and both moving endpoints are left unrestricted inside the proven range. -/
theorem twisted_window (z K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (y h : ℝ)
    (hu : ⌊y+h⌋₊ < (z+1)^K) :
    (∑ n ∈ Icc (⌊y⌋₊+1) ⌊y+h⌋₊, χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)) =
      ∑ j ∈ range K, (coeff K j:ℂ) *
        ∑ n ∈ Icc (⌊y⌋₊+1) ⌊y+h⌋₊, χ (n:ZMod q)*(conv z j n:ℂ) :=
  weighted_identity _ _ _ _ fun _ hn => (mem_Icc.mp hn).2.trans_lt hu

end
end GBHeathBrown

open Finset MeasureTheory Filter Complex
open scoped Interval ComplexConjugate Topology
namespace GBMean
noncomputable section

def wave (v t : ℝ) : ℂ := Complex.exp (((v*t:ℝ):ℂ)*Complex.I)
def gaussian (t : ℝ) := Real.exp (-(t^2))
def cross (v t : ℝ) : ℂ := (gaussian t:ℂ)*wave v t
def gaussConst : ℂ := (Real.pi:ℂ)^(1/2:ℂ)

theorem cross_form (v t : ℝ) : cross v t =
    Complex.exp ((-1:ℂ)*(t:ℂ)^2 + ((v:ℂ)*Complex.I)*t + 0) := by
  unfold cross gaussian wave
  rw [Complex.ofReal_exp,← Complex.exp_add]
  congr 1; push_cast; ring

theorem cross_integrable (v : ℝ) : Integrable (cross v) volume := by
  simpa only [funext (cross_form v)] using integrable_cexp_quadratic' (b:=(-1:ℂ))
    (by norm_num) ((v:ℂ)*Complex.I) 0

theorem cross_integral (v : ℝ) : (∫ t, cross v t) = gaussConst * (Real.exp (-(v^2)/4):ℝ) := by
  simp_rw [cross_form]
  rw [integral_cexp_quadratic (b:=(-1:ℂ)) (by norm_num)]
  unfold gaussConst
  simp only [neg_neg,div_one,Complex.ofReal_exp]
  congr 2
  push_cast; rw [mul_pow,Complex.I_sq]; ring

theorem wave_cross (v w t : ℝ) : wave v t * conj (wave w t) = wave (v-w) t := by
  unfold wave
  rw [← Complex.exp_conj,← Complex.exp_add]
  congr 1
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_mul,Complex.ofReal_sub]
  ring

theorem gaussian_weights (m n : ℕ) (a : ℝ) (h : 2*(Nat.dist m n:ℝ) ≤ |a|) :
    Real.exp (-(a^2)/4) ≤ (1/2:ℝ)^(Nat.dist m n) := by
  let d := Nat.dist m n
  have hd : 0≤(d:ℝ) := by positivity
  have hd₂ : (d:ℝ)≤(d:ℝ)^2 := by
    by_cases hz : d=0
    · simp [hz]
    · have hone : (1:ℝ)≤d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      nlinarith only [mul_le_mul_of_nonneg_right hone hd]
  have hl := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))
  have ha : (2*(d:ℝ))^2 ≤ a^2 := by
    simpa [sq_abs] using pow_le_pow_left₀ (by positivity : 0≤2*(d:ℝ)) h 2
  have he : -(a^2)/4 ≤ -((d:ℝ)*Real.log 2) := by
    nlinarith only [ha,hd₂,mul_le_mul_of_nonneg_left hl hd]
  apply (Real.exp_le_exp.mpr he).trans_eq
  rw [Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num : 0<(2:ℝ))]
  simp [d,inv_pow,one_div]

theorem row_geometric (s : Finset ℕ) (m : ℕ) :
    (∑ n ∈ s, (1/2:ℝ)^Nat.dist m n) ≤ 4 := by
  let r := (1/2:ℝ)
  have subsum (I : Finset ℕ) : (∑ i ∈ I, r^i) ≤ 2 := by
    have hs : Summable (fun i : ℕ => r^i) := summable_geometric_of_lt_one (by norm_num [r]) (by norm_num [r])
    exact (hs.sum_le_tsum _ (fun _ _ => by dsimp [r]; positivity)).trans_eq (by simpa [r] using tsum_geometric_two)
  let R := s.filter (fun n => m≤n)
  let L := s.filter (fun n => ¬m≤n)
  have hr : (∑ n ∈ R, r^Nat.dist m n) ≤ 2 := by
    apply le_trans _ (subsum (R.image (fun n => n-m)))
    rw [sum_image]
    · exact le_of_eq (sum_congr rfl fun n hn => by rw [Nat.dist_eq_sub_of_le (mem_filter.mp hn).2])
    · intro i hi j hj he
      have hi' : m ≤ i := (mem_filter.mp hi).2
      have hj' : m ≤ j := (mem_filter.mp hj).2
      change i-m=j-m at he
      omega
  have hl : (∑ n ∈ L, r^Nat.dist m n) ≤ 2 := by
    apply le_trans _ (subsum (L.image (fun n => m-n)))
    rw [sum_image]
    · exact le_of_eq (sum_congr rfl fun n hn => by
        rw [Nat.dist_eq_sub_of_le_right (Nat.le_of_lt (lt_of_not_ge (mem_filter.mp hn).2))])
    · intro i hi j hj he
      have hi' : ¬m ≤ i := (mem_filter.mp hi).2
      have hj' : ¬m ≤ j := (mem_filter.mp hj).2
      change m-i=m-j at he
      omega
  rw [← sum_filter_add_sum_filter_not (s:=s) (p:=fun n => m≤n)]
  change (∑ n ∈ R, r^Nat.dist m n) + (∑ n ∈ L, r^Nat.dist m n) ≤ _
  linarith

end
end GBMean

open Finset MeasureTheory Filter Complex
open scoped Interval ComplexConjugate Topology
namespace GBMean
noncomputable section

def poly (s : Finset ℕ) (c : ℕ → ℂ) (v : ℕ → ℝ) (t : ℝ) :=
  ∑ n ∈ s, c n * wave (v n) t

def kweight (m n : ℕ) : ℝ := (1/2:ℝ)^Nat.dist m n

theorem schur (s : Finset ℕ) (c : ℕ → ℂ) :
    (∑ m ∈ s, ∑ n ∈ s, ‖c m‖*‖c n‖*kweight m n) ≤ 4*∑ m ∈ s, ‖c m‖^2 := by
  have side : (∑ m ∈ s, ∑ n ∈ s, ‖c m‖^2*kweight m n) ≤ 4*∑ m ∈ s, ‖c m‖^2 := by
    rw [Finset.mul_sum]
    refine sum_le_sum fun m _ => ?_
    rw [← Finset.mul_sum,mul_comm (4:ℝ)]
    exact mul_le_mul_of_nonneg_left (row_geometric s m) (sq_nonneg _)
  have side' : (∑ m ∈ s, ∑ n ∈ s, ‖c n‖^2*kweight m n) ≤ 4*∑ m ∈ s, ‖c m‖^2 := by
    conv_lhs => rw [sum_comm]
    simpa only [kweight,Nat.dist_comm] using side
  have mid : 2*(∑ m ∈ s, ∑ n ∈ s, ‖c m‖*‖c n‖*kweight m n) ≤
      (∑ m ∈ s, ∑ n ∈ s, (‖c m‖^2*kweight m n + ‖c n‖^2*kweight m n)) := by
    simp only [Finset.mul_sum]
    refine sum_le_sum fun m _ => sum_le_sum fun n _ => ?_
    have h := mul_nonneg (sq_nonneg (‖c m‖-‖c n‖)) (by unfold kweight; positivity : 0≤kweight m n)
    nlinarith only [h]
  simp only [sum_add_distrib] at mid
  linarith

theorem pointwise (s : Finset ℕ) (c : ℕ → ℂ) (v : ℕ → ℝ) (t : ℝ) :
    ((gaussian t * ‖poly s c v t‖^2:ℝ):ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, (c m*conj (c n))*cross (v m-v n) t := by
  rw [Complex.ofReal_mul,Complex.ofReal_pow,← Complex.mul_conj']
  unfold poly
  simp only [map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
  conv_lhs => rw [sum_comm]
  refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
  rw [cross,← wave_cross]
  ring

theorem moment_gaussian (s : Finset ℕ) (c : ℕ → ℂ) (v : ℕ → ℝ)
    (sep : ∀ m ∈ s, ∀ n ∈ s, 2*(Nat.dist m n:ℝ) ≤ |v m-v n|) :
    Integrable (fun t => gaussian t*‖poly s c v t‖^2) volume ∧
      (∫ t, gaussian t*‖poly s c v t‖^2) ≤ 4*‖gaussConst‖*∑ m ∈ s, ‖c m‖^2 := by
  let F := fun t => gaussian t*‖poly s c v t‖^2
  let A := fun m n => c m*conj (c n)
  have hi (m n : ℕ) : Integrable (fun t => A m n*cross (v m-v n) t) volume :=
    (cross_integrable _).const_mul _
  have he (t : ℝ) : (F t:ℂ) = ∑ m ∈ s, ∑ n ∈ s, A m n*cross (v m-v n) t := pointwise s c v t
  have hI : Integrable (fun t => (F t:ℂ)) volume := by
    simp_rw [he]
    exact integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ => hi m n
  have hIr : Integrable F volume := by exact hI.re
  refine ⟨hIr,?_⟩
  have raw : ((∫ t : ℝ, F t : ℝ):ℂ) = ∑ m ∈ s, ∑ n ∈ s,
      A m n*(gaussConst * (Real.exp (-((v m-v n)^2)/4):ℝ)) := by
    rw [← integral_complex_ofReal]
    simp_rw [he]
    rw [integral_finsetSum _ (fun m _ => integrable_finsetSum _ (fun n _ => hi m n))]
    refine sum_congr rfl fun m _ => ?_
    rw [integral_finsetSum _ (fun n _ => hi m n)]
    refine sum_congr rfl fun n _ => ?_
    rw [integral_const_mul,cross_integral]
  have hnon : 0 ≤ ∫ t, F t := integral_nonneg fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  calc
    _ = ‖((∫ t : ℝ, F t : ℝ):ℂ)‖ := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnon]
    _ ≤ ∑ m ∈ s, ∑ n ∈ s, ‖A m n*(gaussConst * (Real.exp (-((v m-v n)^2)/4):ℝ))‖ := by
      rw [raw]
      exact (norm_sum_le _ _).trans (sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ ‖gaussConst‖*(∑ m ∈ s, ∑ n ∈ s, ‖c m‖*‖c n‖*kweight m n) := by
      simp only [Finset.mul_sum,A,norm_mul,norm_conj,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      refine sum_le_sum fun m hm => sum_le_sum fun n hn => ?_
      have h := gaussian_weights m n (v m-v n) (sep m hm n hn)
      change _ ≤ kweight m n at h
      nlinarith only [mul_le_mul_of_nonneg_left h (by positivity : 0≤‖c m‖*‖c n‖*‖gaussConst‖)]
    _ ≤ _ := (mul_le_mul_of_nonneg_left (schur s c) (norm_nonneg _)).trans_eq (by ring)

end
end GBMean

open Finset MeasureTheory Filter Complex
open scoped Interval Topology
namespace GBMean
noncomputable section

def constant := 4*Real.exp 1*‖gaussConst‖

theorem unit_bound (s : Finset ℕ) (c : ℕ → ℂ) (v : ℕ → ℝ)
    (sep : ∀ m ∈ s, ∀ n ∈ s, 2*(Nat.dist m n:ℝ) ≤ |v m-v n|)
    {u : ℝ} (hu : 0≤u) (hu1 : u≤1) :
    (∫ t in (-u)..u, ‖poly s c v t‖^2) ≤ constant*∑ j ∈ s, ‖c j‖^2 := by
  obtain ⟨hI,hbd⟩ := moment_gaussian s c v sep
  have hcont : Continuous (fun t => ‖poly s c v t‖^2) := by unfold poly wave; fun_prop
  have hint := hI.const_mul (Real.exp 1)
  have hpos : ∀ t : ℝ, 0 ≤ gaussian t*‖poly s c v t‖^2 := fun _ =>
    mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hup : -u ≤ u := by linarith
  calc
    _ ≤ ∫ t in (-u)..u, Real.exp 1*(gaussian t*‖poly s c v t‖^2) := by
      apply intervalIntegral.integral_mono_on hup (hcont.intervalIntegrable ..) hint.intervalIntegrable
      intro t ht
      have ht1 : 0≤1+t := by linarith only [ht.1,hu1]
      have ht2 : 0≤1-t := by linarith only [ht.2,hu1]
      have ht' : t^2 ≤ 1 := by nlinarith only [mul_nonneg ht1 ht2]
      have hg : 1 ≤ Real.exp 1 * gaussian t := by
        unfold gaussian; rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
      nlinarith only [mul_le_mul_of_nonneg_right hg (sq_nonneg ‖poly s c v t‖)]
    _ ≤ ∫ t, Real.exp 1*(gaussian t*‖poly s c v t‖^2) := by
      rw [intervalIntegral.integral_of_le hup]
      exact setIntegral_le_integral hint (Eventually.of_forall fun t => mul_nonneg (Real.exp_pos _).le (hpos t))
    _ ≤ _ := by
      rw [integral_const_mul]
      exact (mul_le_mul_of_nonneg_left hbd (Real.exp_pos _).le).trans_eq (by unfold constant; ring)

theorem scaled_bound (s : Finset ℕ) (c : ℕ → ℂ) (v : ℕ → ℝ) (T W : ℝ) (hT : 0≤T)
    (hW : 0<W) (hTW : T≤W) (sep : ∀ m ∈ s, ∀ n ∈ s,
      2*(Nat.dist m n:ℝ) ≤ W*|v m-v n|) :
    (∫ t in (-T)..T, ‖poly s c v t‖^2) ≤ constant*W*∑ j ∈ s, ‖c j‖^2 := by
  let V := fun n => W*v n
  have hsep (m : ℕ) (hm : m∈s) (n : ℕ) (hn : n∈s) : 2*(Nat.dist m n:ℝ) ≤ |V m-V n| := by
    simpa only [V,←mul_sub,abs_mul,abs_of_pos hW] using sep m hm n hn
  have hunit := unit_bound s c V hsep (div_nonneg hT hW.le) ((div_le_one hW).2 hTW)
  have hpol (t : ℝ) : poly s c V t = poly s c v (t*W) := by
    apply sum_congr rfl
    intro i _
    unfold wave
    simp only [V]
    rw [show W*v i*t = v i*(t*W) by ring]
  simp_rw [hpol] at hunit
  let F := fun t => ‖poly s c v t‖^2
  change (∫ x in -(T/W)..(T/W), F (x*W)) ≤ _ at hunit
  rw [intervalIntegral.integral_comp_mul_right F hW.ne',neg_mul,div_mul_cancel₀ _ hW.ne',
      smul_eq_mul,← div_eq_inv_mul] at hunit
  exact ((div_le_iff₀ hW).mp hunit).trans_eq (by ring)

theorem progression_gap {a b N W q : ℝ} (ha : 0<a) (hab : a≤b) (hbN : b≤N)
    (hW : 0<W) (hq : 2*N ≤ W*q) {d : ℝ} (hd : 0≤d) (hdiff : b-a=d*q) :
    2*d ≤ W*|Real.log a - Real.log b| := by
  have hb := ha.trans_le hab
  have hlog := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at hlog
  have hgap : (b-a) ≤ b*(Real.log b-Real.log a) := by
    have ht := mul_le_mul_of_nonneg_right hlog hb.le
    simp only [sub_mul,div_mul_cancel₀ _ hb.ne',one_mul] at ht
    linarith
  have hlogs := Real.log_le_log ha hab
  rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hlogs)]
  apply le_of_mul_le_mul_left (a:=b) _ hb
  have hcap := mul_le_mul_of_nonneg_right (show 2*b ≤ W*q by linarith only [hbN,hq]) hd
  have hgap' := mul_le_mul_of_nonneg_left hgap hW.le
  rw [hdiff] at hgap'
  nlinarith only [hcap,hgap']

/-- The coefficients may be restricted to an arbitrary subset of a single residue progression. -/
theorem progression_mean (r q N : ℕ) (s : Finset ℕ) (c : ℕ → ℂ) (T W : ℝ)
    (hT : 0≤T) (hW : 0<W) (hTW : T≤W) (hscale : 2*(N:ℝ) ≤ W*(q:ℝ))
    (hs : ∀ n∈s, 0<r+n*q ∧ r+n*q≤N) :
    (∫ t in (-T)..T, ‖poly s c (fun n => Real.log (r+n*q:ℕ)) t‖^2) ≤
       constant*W*∑ n ∈ s, ‖c n‖^2 := by
  let v := fun n : ℕ => Real.log (r+n*q:ℕ)
  have hpair (m n : ℕ) (hm : m∈s) (hn : n∈s) (hmn : m≤n) :
      2*(Nat.dist m n:ℝ) ≤ W*|v m-v n| := by
    apply progression_gap (N:=(N:ℝ)) (q:=(q:ℝ))
    · exact_mod_cast (hs m hm).1
    · exact_mod_cast Nat.add_le_add_left (Nat.mul_le_mul_right q hmn) r
    · exact_mod_cast (hs n hn).2
    · exact hW
    · exact hscale
    · positivity
    · rw [Nat.dist_eq_sub_of_le hmn,Nat.cast_sub hmn]
      push_cast; ring
  apply scaled_bound _ _ _ _ _ hT hW hTW
  intro m hm n hn
  rcases le_total m n with h | h
  · exact hpair m n hm hn h
  · simpa only [Nat.dist_comm n m,abs_sub_comm (v n) (v m)] using hpair n m hn hm h

end
end GBMean

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

end
end GoldbachGRHWindow
end GoldbachGRHWindowParseval

open Finset MeasureTheory Filter Complex
open scoped Interval Topology Classical
namespace GBMean
noncomputable section
variable {q : ℕ} [NeZero q]

def fiber (s : Finset ℕ) (r : ZMod q) := s.filter (fun n : ℕ => (n:ZMod q)=r)
def logPoly (s : Finset ℕ) (c : ℕ → ℂ) := poly s c (fun n : ℕ => Real.log (n:ℝ))
def twisted (s : Finset ℕ) (c : ℕ → ℂ) (χ : DirichletCharacter ℂ q) :=
  logPoly s (fun n => c n*χ (n:ZMod q))

theorem continuous_logPoly (s : Finset ℕ) (c : ℕ → ℂ) : Continuous (logPoly s c) := by
  unfold logPoly poly wave; fun_prop

theorem fiber_bound (r : ZMod q) (s : Finset ℕ) (c : ℕ → ℂ) (N : ℕ) (T W : ℝ)
    (hT : 0≤T) (hW : 0<W) (hTW : T≤W) (hscale : 2*(N:ℝ) ≤ W*(q:ℝ))
    (hs : ∀ n∈s, 0<n ∧ n≤N) :
    (∫ t in (-T)..T, ‖logPoly (fiber s r) c t‖^2) ≤
       constant*W*∑ n ∈ fiber s r, ‖c n‖^2 := by
  let J := fiber s r
  let I := J.image (fun n => n/q)
  let idx := fun i : ℕ => r.val+i*q
  have hrec (n : ℕ) (hn : n∈J) : idx (n/q) = n := by
    have hp := congrArg ZMod.val (mem_filter.mp hn).2
    rw [ZMod.val_natCast] at hp
    dsimp [idx]
    rw [←hp,Nat.mul_comm (n/q) q,Nat.mod_add_div]
  have hinj : Set.InjOn (fun n => n/q) J := by
    intro m hm n hn he
    exact (hrec m hm).symm.trans ((congrArg idx he).trans (hrec n hn))
  have hI (i : ℕ) (hi : i∈I) : 0 < idx i ∧ idx i ≤ N := by
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hi
    rw [hrec n hn]
    exact hs n (mem_filter.mp hn).1
  have hr := progression_mean r.val q N I (fun i => c (idx i)) T W hT hW hTW hscale hI
  have eqP (t : ℝ) : poly I (fun i => c (idx i)) (fun i => Real.log (r.val+i*q:ℕ)) t =
      logPoly J c t := by
    unfold poly logPoly
    rw [show I=J.image (fun n => n/q) by rfl,sum_image hinj]
    apply sum_congr rfl
    intro n hn
    change c (idx (n/q))*wave (Real.log (idx (n/q):ℕ)) t = _
    rw [hrec n hn]
  simp_rw [eqP] at hr
  have eqC : (∑ i ∈ I, ‖c (idx i)‖^2) = ∑ n ∈ J, ‖c n‖^2 := by
    rw [show I=J.image (fun n => n/q) by rfl,sum_image hinj]
    exact sum_congr rfl fun n hn => by rw [hrec n hn]
  rwa [eqC] at hr

theorem character_orthogonality (s : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) :
    (∑ χ : DirichletCharacter ℂ q, ‖twisted s c χ t‖^2) =
      (q.totient:ℝ)*∑ r ∈ (univ : Finset (ZMod q)).filter IsUnit, ‖logPoly (fiber s r) c t‖^2 := by
  rw [← GoldbachGRHWindow.multiplicative_energy]
  apply sum_congr rfl
  intro χ _
  congr 2
  symm
  calc
    _ = ∑ r : ZMod q, ∑ k ∈ fiber s r, c k * χ (k:ZMod q) * wave (Real.log (k:ℝ)) t := by
      apply sum_congr rfl
      intro r _
      unfold logPoly poly
      rw [Finset.sum_mul]
      apply sum_congr rfl
      intro k hk
      rw [(mem_filter.mp hk).2]
      ring
    _ = _ := Finset.sum_fiberwise s (fun k : ℕ => (k:ZMod q)) _

theorem hybrid_mean (s : Finset ℕ) (c : ℕ → ℂ) (N : ℕ) (T W : ℝ)
    (hT : 0≤T) (hW : 0<W) (hTW : T≤W) (hscale : 2*(N:ℝ) ≤ W*(q:ℝ))
    (hs : ∀ n∈s, 0<n ∧ n≤N) :
    (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T, ‖twisted s c χ t‖^2) ≤
       (q.totient:ℝ)*(constant*W)*∑ n ∈ s, ‖c n‖^2 := by
  let U := (univ : Finset (ZMod q)).filter IsUnit
  have ht (χ : DirichletCharacter ℂ q) : Continuous (fun t => ‖twisted s c χ t‖^2) :=
    (continuous_logPoly s _).norm.pow 2
  have hu (r : ZMod q) : Continuous (fun t => ‖logPoly (fiber s r) c t‖^2) :=
    (continuous_logPoly _ _).norm.pow 2
  rw [← intervalIntegral.integral_finsetSum (fun χ _ => (ht χ).intervalIntegrable ..)]
  simp_rw [character_orthogonality]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finsetSum (fun r _ => (hu r).intervalIntegrable ..)]
  rw [mul_assoc (q.totient:ℝ)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ r ∈ U, (constant*W)*∑ n ∈ fiber s r, ‖c n‖^2 :=
      sum_le_sum fun r _ => fiber_bound r s c N T W hT hW hTW hscale hs
    _ ≤ ∑ r : ZMod q, (constant*W)*∑ n ∈ fiber s r, ‖c n‖^2 := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro r _ _
      unfold constant
      positivity
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_fiberwise s (fun k : ℕ => (k:ZMod q)) _

end
end GBMean

open Finset MeasureTheory Filter Complex
open scoped Interval Topology Classical
namespace GBMean
noncomputable section

def energy {q : ℕ} [NeZero q] (s : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ q, ‖twisted s c χ t‖^2

theorem energy_cont (q : ℕ) [NeZero q] (s : Finset ℕ) (c : ℕ → ℂ) :
    Continuous (energy (q:=q) s c) := by
  unfold energy
  exact continuous_finsetSum _ fun χ _ => (continuous_logPoly s _).norm.pow 2

theorem energy_pos (q : ℕ) [NeZero q] (s : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) :
    0 ≤ energy (q:=q) s c t := sum_nonneg fun _ _ => sq_nonneg _

def both (F : ℝ → ℝ) (t : ℝ) := F t + F (-t)

theorem integrated_both (F : ℝ → ℝ) (hF : Continuous F) (T : ℝ) :
    (∫ t in (0:ℝ)..T, both F t) = ∫ t in (-T)..T, F t := by
  unfold both
  have hn : Continuous (fun t : ℝ => F (-t)) := hF.comp continuous_neg
  rw [intervalIntegral.integral_add (hF.intervalIntegrable ..) (hn.intervalIntegrable ..),
      intervalIntegral.integral_comp_neg,neg_zero,add_comm,
      intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable ..) (hF.intervalIntegrable ..)]

theorem character_energy_bound (q : ℕ) [NeZero q] (s : Finset ℕ) (c : ℕ → ℂ)
    (N : ℕ) {T : ℝ} (hT : 0<T) (hs : ∀ n∈s, 0<n ∧ n≤N) :
    (∫ t in (0:ℝ)..T, both (energy (q:=q) s c) t) ≤
      ((q.totient:ℝ)*T + 2*(N:ℝ))*(constant*∑ n ∈ s, ‖c n‖^2) := by
  have hq : 0 < (q:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  let W := T + 2*(N:ℝ)/(q:ℝ)
  have hTW : T≤W := by dsimp [W]; exact le_add_of_nonneg_right (by positivity)
  have hscale : 2*(N:ℝ)≤W*(q:ℝ) := by
    dsimp [W]; rw [add_mul,div_mul_cancel₀ _ hq.ne']; linarith only [mul_nonneg hT.le hq.le]
  have hm := hybrid_mean (q:=q) s c N T W hT.le (hT.trans_le hTW) hTW hscale hs
  rw [integrated_both _ (energy_cont ..)]
  unfold energy
  have ht (χ : DirichletCharacter ℂ q) : Continuous (fun t => ‖twisted s c χ t‖^2) := (continuous_logPoly s _).norm.pow 2
  rw [intervalIntegral.integral_finsetSum (fun χ _ => (ht χ).intervalIntegrable ..)]
  apply hm.trans
  have htot : (q.totient:ℝ)≤(q:ℝ) := by exact_mod_cast q.totient_le
  have he : (q.totient:ℝ)* (2*(N:ℝ)/(q:ℝ)) ≤ 2*(N:ℝ) := by
    have h := mul_le_mul_of_nonneg_right htot (show 0≤2*(N:ℝ)/(q:ℝ) by positivity)
    rw [mul_comm (q:ℝ),div_mul_cancel₀ _ hq.ne'] at h
    exact h
  have hc : 0≤constant*∑ n ∈ s, ‖c n‖^2 := by unfold constant; positivity
  calc
    _ = ((q.totient:ℝ)*T + (q.totient:ℝ)*(2*N/q))*(constant*∑ n ∈ s, ‖c n‖^2) := by dsimp [W]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (add_le_add le_rfl he) hc

def potential (a b r : ℝ) := 4*a/r + 2*b/r^2

theorem tail_integrable {F : ℝ → ℝ} (hF : Continuous F) {r u : ℝ} (hr : 0<r) (hru : r≤u) :
    IntervalIntegrable (fun t => F t/t^2) volume r u := by
  apply ContinuousOn.intervalIntegrable
  apply hF.continuousOn.div (continuous_id.pow 2).continuousOn
  intro t ht
  rw [Set.uIcc_of_le hru] at ht
  exact pow_ne_zero _ (hr.trans_le ht.1).ne'

theorem bound_slab {F : ℝ → ℝ} (hF : Continuous F) (hp : ∀ t, 0≤F t)
    {a b : ℝ} (hb : 0≤b) (H : ∀ T>0, (∫ t in (0:ℝ)..T, F t) ≤ a*T+b)
    {r : ℝ} (hr : 0<r) :
    (∫ t in r..(2*r), F t/t^2) ≤ potential a b r - potential a b (2*r) := by
  have hr2 : r≤2*r := by linarith
  calc
    _ ≤ ∫ t in r..(2*r), F t/r^2 := by
      apply intervalIntegral.integral_mono_on hr2 (tail_integrable hF hr hr2) ((hF.div_const _).intervalIntegrable ..)
      intro t ht
      exact div_le_div_of_nonneg_left (hp t) (sq_pos_of_pos hr) (by nlinarith only [sq_nonneg (t-r),mul_nonneg hr.le (sub_nonneg.mpr ht.1)])
    _ = (∫ t in r..(2*r), F t)/r^2 := intervalIntegral.integral_div ..
    _ ≤ (a*(2*r)+b)/r^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact (intervalIntegral.integral_mono_interval hr.le hr2 le_rfl (Eventually.of_forall hp) (hF.intervalIntegrable ..)).trans (H _ (by positivity))
    _ ≤ _ := by unfold potential; field_simp; nlinarith

theorem dyadic_tail {F : ℝ → ℝ} (hF : Continuous F) (hp : ∀ t, 0≤F t)
    {a b : ℝ} (hb : 0≤b) (H : ∀ T>0, (∫ t in (0:ℝ)..T, F t) ≤ a*T+b)
    (k : ℕ) {r : ℝ} (hr : 0<r) :
    (∫ t in r..(2^k*r), F t/t^2) ≤ potential a b r - potential a b (2^k*r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    let v := (2:ℝ)^k*r
    have hv : 0<v := by dsimp [v]; positivity
    have hrv : r≤v := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : 1≤(2:ℝ)) (n:=k)) hr.le
    rw [show (2:ℝ)^(k+1)*r=2*v by dsimp [v]; ring,
      ←intervalIntegral.integral_add_adjacent_intervals (tail_integrable hF hr hrv) (tail_integrable hF hv (show v≤2*v by linarith))]
    have h := bound_slab hF hp hb H hv
    change _ ≤ potential a b r - potential a b v at ih
    linarith

theorem finite_tail {F : ℝ → ℝ} (hF : Continuous F) (hp : ∀ t, 0≤F t)
    {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (H : ∀ T>0, (∫ t in (0:ℝ)..T, F t) ≤ a*T+b)
    {r u : ℝ} (hr : 0<r) (hu : r≤u) :
    (∫ t in r..u, F t/t^2) ≤ potential a b r := by
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (u/r) (by norm_num : 1<(2:ℝ))
  have hv := (div_lt_iff₀ hr).mp hk
  have h := dyadic_tail hF hp hb H k hr
  have hpv : 0≤potential a b (2^k*r) := by unfold potential; positivity
  apply (intervalIntegral.integral_mono_interval le_rfl hu hv.le
    (Eventually.of_forall fun t => div_nonneg (hp t) (sq_nonneg _)) (tail_integrable hF hr (hu.trans hv.le))).trans
  linarith
end
end GBMean

open Finset MeasureTheory Filter Complex
open scoped Interval Topology Classical
namespace GBMean
noncomputable section

theorem tail_infinite {F : ℝ → ℝ} (hF : Continuous F) (hp : ∀ t, 0≤F t)
    {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (H : ∀ T>0, (∫ t in (0:ℝ)..T, F t) ≤ a*T+b)
    {r : ℝ} (hr : 0<r) :
    IntegrableOn (fun t => F t/t^2) (Set.Ioi r) ∧
    (∫ t in Set.Ioi r, F t/t^2) ≤ potential a b r := by
  have hf (t : ℝ) : 0≤F t/t^2 := div_nonneg (hp t) (sq_nonneg _)
  have hbd : ∀ᶠ u : ℝ in atTop, (∫ t in r..u, F t/t^2) ≤ potential a b r :=
    (eventually_ge_atTop r).mono fun u hu => finite_tail hF hp ha hb H hr hu
  have hint : IntegrableOn (fun t => F t/t^2) (Set.Ioi r) := by
    apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (potential a b r) r (b:=id) (l:=atTop)
    · intro u
      by_cases hu : r≤u
      · exact (tail_integrable hF hr hu).1
      · simp [Set.Ioc_eq_empty_of_le (le_of_not_ge hu)]
    · exact tendsto_id
    · simpa only [id_eq,Real.norm_eq_abs,abs_of_nonneg (hf _)] using hbd
  exact ⟨hint,le_of_tendsto (intervalIntegral_tendsto_integral_Ioi r hint tendsto_id) hbd⟩

def lambdaCoeff (n : ℕ) : ℂ := ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ):ℂ)
def lambdaBound (N : ℕ) := 2*(Real.log 4+4)*Real.log (2*N:ℝ)

theorem lambda_coeff_norm (N : ℕ) (hN : 0<N) :
    (∑ n ∈ Ico N (2*N), ‖lambdaCoeff n‖^2) ≤ lambdaBound N := by
  have hNr : 0<(N:ℝ) := by exact_mod_cast hN
  have hlog : 0≤Real.log (2*N:ℝ) := Real.log_nonneg (by have : 1≤N := hN; exact_mod_cast (by omega : 1≤2*N))
  have hcoeff (n : ℕ) (hn : n ∈ Ico N (2*N)) :
      ‖lambdaCoeff n‖^2 ≤ (Real.log (2*N:ℝ)/(N:ℝ))*ArithmeticFunction.vonMangoldt n := by
    obtain ⟨hl,hh⟩ := mem_Ico.mp hn
    have hnr : (N:ℝ)≤(n:ℝ) := by exact_mod_cast hl
    have hnpos := hNr.trans_le hnr
    have hlambda := ArithmeticFunction.vonMangoldt_nonneg (n:=n)
    have hcap : ArithmeticFunction.vonMangoldt n ≤ Real.log (2*N:ℝ) :=
      ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hnpos (by exact_mod_cast hh.le))
    rw [lambdaCoeff,Complex.norm_real,Real.norm_eq_abs,sq_abs,div_pow,Real.sq_sqrt hnpos.le]
    calc
      _ ≤ (ArithmeticFunction.vonMangoldt n)^2 / N := div_le_div_of_nonneg_left (sq_nonneg _) hNr hnr
      _ ≤ _ := by rw [div_mul_eq_mul_div]; apply div_le_div_of_nonneg_right _ hNr.le; nlinarith only [mul_le_mul_of_nonneg_right hcap hlambda]
  have hsum : (∑ n ∈ Ico N (2*N), ArithmeticFunction.vonMangoldt n) ≤ (Real.log 4+4)*(2*N:ℝ) := by
    have hb := Chebyshev.sum_range_vonMangoldt_le (2*N)
    push_cast at hb
    apply (_ : _ ≤ ∑ n ∈ range (2*N), ArithmeticFunction.vonMangoldt n).trans hb
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn; exact mem_range.mpr (mem_Ico.mp hn).2
    · intros; exact ArithmeticFunction.vonMangoldt_nonneg
  calc
    _ ≤ _ := sum_le_sum hcoeff
    _ = (Real.log (2*N:ℝ)/N)*∑ n ∈ Ico N (2*N), ArithmeticFunction.vonMangoldt n := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (div_nonneg hlog hNr.le)
    _ = _ := by unfold lambdaBound; field_simp <;> ring

theorem lambda_high_tail (q N : ℕ) [NeZero q] (hN : 0<N) {r : ℝ} (hr : 0<r) :
    let F := both (energy (q:=q) (Ico N (2*N)) lambdaCoeff)
    IntegrableOn (fun t => F t/t^2) (Set.Ioi r) ∧
      (∫ t in Set.Ioi r, F t/t^2) ≤
        (4*(q.totient:ℝ)/r+8*(N:ℝ)/r^2)*(constant*lambdaBound N) := by
  let s := Ico N (2*N)
  let D := constant*lambdaBound N
  have hN1 : 1≤N := hN
  have hlog : 0≤Real.log (2*N:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤2*N))
  have hc : 0≤constant := by unfold constant; positivity
  have hD : 0≤D := by dsimp [D,lambdaBound]; positivity
  have hs (n : ℕ) (hn : n ∈ s) : 0<n ∧ n≤2*N := ⟨hN.trans_le (mem_Ico.mp hn).1,(mem_Ico.mp hn).2.le⟩
  have H (T : ℝ) (hT : 0<T) : (∫ t in (0:ℝ)..T, both (energy (q:=q) s lambdaCoeff) t) ≤
      ((q.totient:ℝ)*D)*T+4*(N:ℝ)*D := by
    have h := character_energy_bound q s lambdaCoeff (2*N) hT hs
    calc
      _ ≤ _ := h
      _ ≤ ((q.totient:ℝ)*T+2*((2*N:ℕ):ℝ))*D := by
        apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (lambda_coeff_norm N hN) hc)
        positivity
      _ = _ := by push_cast; ring
  have hct := energy_cont q s lambdaCoeff
  have hpos (t : ℝ) : 0≤both (energy (q:=q) s lambdaCoeff) t := add_nonneg (energy_pos ..) (energy_pos ..)
  have hcont : Continuous (both (energy (q:=q) s lambdaCoeff)) := hct.add (hct.comp continuous_neg)
  obtain ⟨hi,hb⟩ := tail_infinite hcont hpos (mul_nonneg (Nat.cast_nonneg _) hD)
    (show 0≤4*(N:ℝ)*D by positivity) H hr
  refine ⟨hi,hb.trans_eq ?_⟩
  unfold potential
  dsimp only [D]
  ring
end
end GBMean

theorem Conjectures.Goldbach.ShortProgressionsAnalyticSteps :
((let theta := fun (q : ℕ) [NeZero q] (r : ZMod q) (y h : ℝ) => Finset.sum ((Finset.Icc (⌊y⌋₊+1) ⌊y+h⌋₊).filter (fun k : ℕ => (k:ZMod q)=r)) (fun k => ArithmeticFunction.vonMangoldt k); let E := fun (q : ℕ) (h y : ℝ) => if hq : q=0 then (0:ℝ) else (letI : NeZero q := ⟨hq⟩; (Finset.univ : Finset (ZMod q)).sup' Finset.univ_nonempty (fun r => if IsUnit r then |theta q r y h - h/(q.totient:ℝ)| else 0)); ∃ C : ℝ, 0<C ∧ ∃ X : ℕ, ∀ x t : ℝ, (X:ℝ)≤x → 1≤x → 5/8≤t → t≤1 → ∀ Q : ℕ, 1≤Q → (Q:ℝ)^2*x^((1-t)/3+1/16) ≤ x^t → intervalIntegral (fun y => Finset.sum (Finset.Icc 1 Q) (fun q => E q (x^t) y)) x (2*x) MeasureTheory.volume ≤ C*x*x^t/(Real.log x)^18) → (let theta := fun (q : ℕ) [NeZero q] (r : ZMod q) (y h : ℝ) => Finset.sum ((Finset.Icc (⌊y⌋₊+1) ⌊y+h⌋₊).filter (fun k : ℕ => (k:ZMod q)=r)) (fun k => if k.Prime then Real.log (k:ℝ) else 0); let E := fun (q : ℕ) (h y : ℝ) => if hq : q=0 then (0:ℝ) else (letI : NeZero q := ⟨hq⟩; (Finset.univ : Finset (ZMod q)).sup' Finset.univ_nonempty (fun r => if IsUnit r then |theta q r y h - h/(q.totient:ℝ)| else 0)); ∃ C : ℝ, 0<C ∧ ∃ X : ℕ, ∀ x t : ℝ, (X:ℝ)≤x → 1≤x → 5/8≤t → t≤1 → ∀ Q : ℕ, 1≤Q → (Q:ℝ)^2*x^((1-t)/3+1/16) ≤ x^t → intervalIntegral (fun y => Finset.sum (Finset.Icc 1 Q) (fun q => E q (x^t) y)) x (2*x) MeasureTheory.volume ≤ C*x*x^t/(Real.log x)^18)) ∧ (∀ (z K q : ℕ) (χ : DirichletCharacter ℂ q) (y h : ℝ), ⌊y+h⌋₊ < (z+1)^K →
  let m : ArithmeticFunction ℝ := ⟨fun n => if n≤z then (ArithmeticFunction.moebius n:ℝ) else 0,by simp⟩
  let I := Finset.Icc (⌊y⌋₊+1) ⌊y+h⌋₊
  (∑ n ∈ I, χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)) =
    ∑ j ∈ Finset.range K, (((-1:ℝ)^j * (K.choose (j+1):ℝ):ℝ):ℂ) *
      ∑ n ∈ I, χ (n:ZMod q)*(((ArithmeticFunction.log*(ArithmeticFunction.zeta:ArithmeticFunction ℝ)^j*m^(j+1)) n:ℝ):ℂ)) ∧ (∀ (q N : ℕ) [NeZero q], 0<N → ∀ r : ℝ, 0<r →
  let E := fun t : ℝ => ∑ χ : DirichletCharacter ℂ q,
    ‖∑ n ∈ Finset.Ico N (2*N), (((ArithmeticFunction.vonMangoldt n / Real.sqrt n:ℝ):ℂ)*χ (n:ZMod q))*
      Complex.exp (((Real.log (n:ℝ)*t:ℝ):ℂ)*Complex.I)‖^2
  let F := fun t : ℝ => (E t + E (-t))/t^2
  MeasureTheory.IntegrableOn F (Set.Ioi r) ∧
    (∫ t in Set.Ioi r, F t) ≤
      (4*(q.totient:ℝ)/r+8*(N:ℝ)/r^2)*
        ((4*Real.exp 1*‖(Real.pi:ℂ)^(1/2:ℂ)‖)*(2*(Real.log 4+4)*Real.log (2*N:ℝ)))) := by
  refine ⟨GBSkirtVariance.theta_of_psi, ?_, ?_⟩
  · exact fun z K q χ y h hu => GBHeathBrown.twisted_window z K χ y h hu
  · exact fun q N _ hN r hr => GBMean.lambda_high_tail q N hN hr
