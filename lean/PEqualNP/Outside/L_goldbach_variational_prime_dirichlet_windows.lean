import Mathlib

/-!
# Quadratic variation in moving Dirichlet windows

Each reduced rational may choose disjoint coefficient intervals, with a separate
sample from its Dirichlet window on every interval. Dyadic endpoint differences
activate at most two blocks per level. A block can enter or leave at most twice
along a disjoint family. This yields the squared-logarithmic cost uniformly.
See Allison and Mark Lewko, A Variational Barban-Davenport-Halberstam Theorem,
https://doi.org/10.1016/j.jnt.2012.02.007 for the variational large sieve.
The moving-window base is from 34245621, commit 0706d414e060cf6f76c83ce6059c9413936c81b5.

A mesh cell of length 1/n meets at most seven square-root Dirichlet windows:
relative to the largest denominator, the integral determinants lie between -3
and 3 and distinguish all reduced pairs. Arbitrary samples in the mesh cells
are controlled by the total variation of the squared Fourier sum.

The continuous Parseval helper below reuses Clrs17's accepted proof from
https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/138
at commit 5ab2bcbb94ec2a8224686cc2cf35f1736f882a64. The namespace and
helper name are local to this file. The fixed-centre large-sieve roadmap
is https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/451.
-/

section
open scoped BigOperators ComplexConjugate

private noncomputable def parsevalPhase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

namespace GoldbachMovingWindows

private theorem continuous_parseval :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); ∀ n w, intervalIntegral (fun t => ‖S n w t‖^2) (0:ℝ) 1 MeasureTheory.volume = Finset.sum (Finset.range (n+1)) (fun k => (w k)^2) := by
  dsimp only
  intro n w
  let T := Finset.range (n + 1)
  let S : ℝ → ℂ := fun t => ∑ k ∈ T, (w k : ℂ) * parsevalPhase ((k : ℝ) * t)
  let z : ℝ → ℂ := fun t => ∑ k ∈ T, ∑ j ∈ T,
    ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t)
  change intervalIntegral (fun t => ‖S t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume = _
  have hphase_mul : ∀ x y : ℝ, parsevalPhase (x + y) = parsevalPhase x * parsevalPhase y := by
    intro x y
    unfold parsevalPhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hphase_cont : Continuous parsevalPhase := by
    unfold parsevalPhase
    fun_prop
  have hphase_exp : ∀ m : ℤ, Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I) = 1 := by
    intro m
    have h : 2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I =
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have hphase_one : ∀ m : ℤ, parsevalPhase (m : ℝ) = 1 := by
    intro m
    unfold parsevalPhase
    have h : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) =
        2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, hphase_exp m]
  have hphase_conj : ∀ x : ℝ, conj (parsevalPhase x) = parsevalPhase (-x) := by
    intro x
    unfold parsevalPhase
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have horth : ∀ m : ℤ, intervalIntegral (fun t : ℝ => parsevalPhase ((m : ℝ) * t))
      (0 : ℝ) 1 MeasureTheory.volume = if m = 0 then 1 else 0 := by
    intro m
    have hrewrite : intervalIntegral (fun t : ℝ => parsevalPhase ((m : ℝ) * t))
        (0 : ℝ) 1 MeasureTheory.volume =
        ∫ t in (0 : ℝ)..1, Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * (t : ℂ)) := by
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      unfold parsevalPhase
      congr 1
      push_cast
      ring
    rw [hrewrite]
    by_cases hm : m = 0
    · subst hm
      simp
    · have hmr : (m : ℝ) ≠ 0 := by
        intro hzero
        exact hm (by exact_mod_cast hzero)
      have h1 : (2 * Real.pi * (m : ℝ)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hmr
      have hc : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
        have h2 : ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) ≠ 0 := by
          simpa [Complex.ofReal_eq_zero] using h1
        exact mul_ne_zero h2 Complex.I_ne_zero
      have hval : Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ)) * Complex.I) = 1 := by
        have hone := hphase_one m
        simpa only [parsevalPhase] using hone
      rw [integral_exp_mul_complex hc]
      simp [hphase_exp m, hm]
  have hint_single : ∀ (c : ℂ) (a : ℝ),
      IntervalIntegrable (fun t : ℝ => c * parsevalPhase (a * t)) MeasureTheory.volume (0 : ℝ) 1 := by
    intro c a
    exact (continuous_const.mul (hphase_cont.comp (by fun_prop))).intervalIntegrable (0 : ℝ) 1
  have hpoint : ∀ t : ℝ, (Complex.normSq (S t) : ℂ) = z t := by
    intro t
    rw [Complex.normSq_eq_conj_mul_self]
    dsimp only [S, z]
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    simp only [map_mul, Complex.conj_ofReal, hphase_conj]
    have hmul : parsevalPhase (-((k : ℝ) * t)) * parsevalPhase ((j : ℝ) * t) =
        parsevalPhase (((j : ℝ) - (k : ℝ)) * t) := by
      rw [← hphase_mul]
      congr 1
      ring
    calc
      ((w k : ℂ) * parsevalPhase (-((k : ℝ) * t))) *
          ((w j : ℂ) * parsevalPhase ((j : ℝ) * t)) =
          ((w k : ℂ) * (w j : ℂ)) *
            (parsevalPhase (-((k : ℝ) * t)) * parsevalPhase ((j : ℝ) * t)) := by ring
      _ = ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t) := by
        rw [hmul]
  have hint_z : IntervalIntegrable z MeasureTheory.volume (0 : ℝ) 1 := by
    dsimp only [z]
    exact (continuous_finsetSum _ (fun k _ => continuous_finsetSum _
      (fun j _ => continuous_const.mul (hphase_cont.comp (by fun_prop))))).intervalIntegrable (0 : ℝ) 1
  have hmain : intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume =
      ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
    dsimp only [z]
    have houter (k : ℕ) (hk : k ∈ T) : IntervalIntegrable (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
        MeasureTheory.volume (0 : ℝ) 1 := by
      exact (continuous_finsetSum _ (fun j _ => continuous_const.mul
        (hphase_cont.comp (by fun_prop)))).intervalIntegrable (0 : ℝ) 1
    rw [intervalIntegral.integral_finsetSum houter]
    have hstep : ∀ k ∈ T, intervalIntegral (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
        (0 : ℝ) 1 MeasureTheory.volume = ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := by
      intro k hk
      rw [intervalIntegral.integral_finsetSum (fun j _ =>
        hint_single ((w k : ℂ) * (w j : ℂ)) (((j : ℝ) - (k : ℝ))))]
      apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_const_mul]
      congr 1
      have hm : ((j : ℝ) - (k : ℝ)) = (((j : ℤ) - (k : ℤ) : ℤ) : ℝ) := by
        push_cast
        ring
      simp_rw [hm]
      rw [horth]
    calc
      (∑ k ∈ T, intervalIntegral (fun t : ℝ => ∑ j ∈ T,
          ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
          (0 : ℝ) 1 MeasureTheory.volume) =
          ∑ k ∈ T, ∑ j ∈ T, ((w k : ℂ) * (w j : ℂ)) *
            (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := Finset.sum_congr rfl hstep
      _ = ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
        push_cast
        simp only [sub_eq_zero, Int.ofNat_inj]
        apply Finset.sum_congr rfl
        intro k hk
        simp [hk, pow_two]
  have hre : intervalIntegral (fun t => (z t).re) (0 : ℝ) 1 MeasureTheory.volume =
      (intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume).re := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc,
      intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp only [show (0 : ℝ) ≤ 1 by norm_num, ite_true, one_smul]
    exact integral_re hint_z.def'
  calc
    intervalIntegral (fun t => ‖S t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume =
        intervalIntegral (fun t => (z t).re) (0 : ℝ) 1 MeasureTheory.volume := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hp := congrArg Complex.re (hpoint t)
      simpa only [Complex.ofReal_re, Complex.normSq_eq_norm_sq] using hp
    _ = (intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume).re := hre
    _ = ∑ k ∈ T, (w k) ^ 2 := by rw [hmain]; exact Complex.ofReal_re _

end GoldbachMovingWindows
end

section
open Set Finset MeasureTheory Filter intervalIntegral
noncomputable section
namespace GoldbachMovingWindows

private theorem variation_on_cell {F D : ℝ → ℝ} (dF : ∀ x, HasDerivAt F (D x) x) (cD : Continuous D)
    {l r x y : ℝ} (hx : x ∈ Icc l r) (hy : y ∈ Icc l r) :
    F x ≤ F y + ∫ u in l..r, |D u| := by
  have step {a b : ℝ} (ha : l≤a) (hab : a≤b) (hb : b≤r) :
      |F b-F a| ≤ ∫ u in l..r, |D u| := by
    rw [← integral_eq_sub_of_hasDerivAt (fun t _ => dF t) (cD.intervalIntegrable ..)]
    exact (abs_integral_le_integral_abs hab).trans (integral_mono_interval ha hab hb
      (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) (cD.abs.intervalIntegrable ..))
  rcases le_total y x with h|h
  · linarith [(le_abs_self (F x-F y)).trans (step hy.1 h hx.2)]
  · linarith [(neg_le_abs (F y-F x)).trans (step hx.1 h hy.2)]

private theorem scaled_cell {F D : ℝ → ℝ} (dF : ∀ x, HasDerivAt F (D x) x) (cD : Continuous D)
    {l r x : ℝ} (hx : x ∈ Icc l r) :
    (r-l)*F x ≤ (∫ u in l..r, F u) + (r-l)*(∫ u in l..r, |D u|) := by
  let V := ∫ u in l..r, |D u|
  have hF : Continuous F := continuous_iff_continuousAt.mpr (fun t => (dF t).continuousAt)
  have h := integral_mono_on (μ:=volume) (hx.1.trans hx.2) (f:=fun _ : ℝ => F x) (g:=fun y => F y+V)
    (continuous_const.intervalIntegrable ..) ((hF.add continuous_const).intervalIntegrable ..)
    (fun _ hy => variation_on_cell dF cD hx hy)
  rw [intervalIntegral.integral_const,intervalIntegral.integral_add (hF.intervalIntegrable ..) (continuous_const.intervalIntegrable ..),intervalIntegral.integral_const] at h
  exact h

/-- Sample anywhere in each of the n equal closed cells; the variation budget
is charged just once across the whole interval. -/
theorem sample_mesh {F D : ℝ → ℝ} (dF : ∀ x, HasDerivAt F (D x) x) (cD : Continuous D)
    {n : ℕ} (hn : 0<n) (t : ℕ→ℝ)
    (h : ∀ j<n, t j ∈ Icc ((j:ℝ)/n) (((j:ℝ)+1)/n)) :
    (∑ j ∈ range n,F (t j)) ≤ (n:ℝ)*(∫ x in (0:ℝ)..1,F x) + ∫ x in (0:ℝ)..1, |D x| := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  let b := fun j : ℕ => (j:ℝ)/n
  have width (j : ℕ) : b (j+1)-b j = 1/(n:ℝ) := by dsimp [b];push_cast;ring
  have hF : Continuous F := continuous_iff_continuousAt.mpr (fun t => (dF t).continuousAt)
  have cell (j : ℕ) (hj : j∈range n) :
      F (t j) ≤ (n:ℝ)*(∫ x in (b j)..(b (j+1)), F x) + ∫ x in (b j)..(b (j+1)), |D x| := by
    have mem : t j ∈ Icc (b j) (b (j+1)) := by simpa [b] using h j (mem_range.mp hj)
    have z := scaled_cell dF cD mem
    rw [width] at z
    have zz := mul_le_mul_of_nonneg_left z hn0.le
    field_simp at zz
    linarith
  calc
    _ ≤ ∑ j ∈ range n, ((n:ℝ)*(∫ x in (b j)..(b (j+1)), F x) + ∫ x in (b j)..(b (j+1)), |D x|) :=
      sum_le_sum cell
    _ = _ := by
      rw [sum_add_distrib,←mul_sum,sum_integral_adjacent_intervals (fun _ _ => hF.intervalIntegrable ..),
        sum_integral_adjacent_intervals (fun _ _ => cD.abs.intervalIntegrable ..)]
      simp [b,hn0.ne']

end GoldbachMovingWindows
end
end

section
open Finset Set
noncomputable section
namespace GoldbachMovingWindows

private def det (p v : ℕ × ℕ) : ℤ := (p.2:ℤ)*v.1 - (v.2:ℤ)*p.1

private theorem det_injective {r b : ℕ} (hr : 0<r) (hb : b.Coprime r)
    {p u : ℕ×ℕ} (h1 : 0<p.1) (h2 : p.1≤r) (h3 : 0<u.1) (h4 : u.1≤r)
    (h : det p (r,b) = det u (r,b)) : p=u := by
  classical
  let : NeZero r := ⟨hr.ne'⟩
  have hz := congrArg (fun z : ℤ => (z : ZMod r)) h
  simp [det,Int.cast_sub,Int.cast_mul] at hz
  have hu := (ZMod.isUnit_iff_coprime b r).mpr hb
  have eq : (p.1 : ZMod r) = (u.1 : ZMod r) := hu.mul_left_cancel hz
  have pre : ((p.1-1:ℕ):ZMod r) = ((u.1-1:ℕ):ZMod r) := by
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega),eq]
  have hv := congrArg ZMod.val pre
  simp only [ZMod.val_natCast_of_lt (by omega : p.1-1<r),ZMod.val_natCast_of_lt (by omega : u.1-1<r)] at hv
  have eqd : p.1=u.1 := by omega
  have hmul : (p.2:ℤ)*r=(u.2:ℤ)*r := by
    dsimp [det] at h
    rw [eqd] at h
    linarith
  exact Prod.ext eqd (by exact_mod_cast (mul_right_cancel₀ (show (r:ℤ)≠0 by exact_mod_cast hr.ne') hmul))

private theorem det_bound {p v : ℕ×ℕ} {S x y : ℝ} (hS : 0<S) (hp : 0<p.1) (hv : 0<v.1)
    (hpS : (p.1:ℝ)≤S) (hvS : (v.1:ℝ)≤S)
    (hx : |x-(p.2:ℝ)/p.1| ≤ 1/((p.1:ℝ)*S)) (hy : |y-(v.2:ℝ)/v.1| ≤ 1/((v.1:ℝ)*S))
    (hxy : |x-y| ≤ 1/S^2) : |det p v| ≤ 3 := by
  have hP : 0<(p.1:ℝ) := by exact_mod_cast hp
  have hV : 0<(v.1:ℝ) := by exact_mod_cast hv
  have raw : ((det p v : ℤ):ℝ) = ((p.2/p.1:ℝ)-x+(x-y)+(y-v.2/v.1))*(p.1*v.1) := by
    simp only [det,Int.cast_sub,Int.cast_mul,Int.cast_natCast]
    field_simp
    ring
  have htriangle : |((det p v : ℤ):ℝ)| ≤
      (1/((p.1:ℝ)*S)+1/S^2+1/((v.1:ℝ)*S))*(p.1*v.1) := by
    rw [raw,abs_mul,abs_of_pos (mul_pos hP hV)]
    apply mul_le_mul_of_nonneg_right _ (mul_pos hP hV).le
    apply (abs_add_le ..).trans
    apply add_le_add _ hy
    exact (abs_add_le ..).trans (add_le_add (by rwa [abs_sub_comm]) hxy)
  have e : (1/((p.1:ℝ)*S)+1/S^2+1/((v.1:ℝ)*S))*(p.1*v.1) =
      v.1/S + (p.1:ℝ)*v.1/S^2 + p.1/S := by field_simp
  rw [e] at htriangle
  have hA := (div_le_one hS).mpr hvS
  have hB := (div_le_one hS).mpr hpS
  have hC : (p.1:ℝ)*v.1/S^2 ≤ 1 := (div_le_one (sq_pos_of_pos hS)).mpr
    (by simpa [sq] using mul_le_mul hpS hvS hV.le hS.le)
  exact_mod_cast (show |((det p v : ℤ):ℝ)|≤3 by linarith)

/-- At most seven distinct reduced fractions can have their square-root
Dirichlet windows touch the same cell of length 1/S². -/
theorem at_most_seven (A : Finset (ℕ×ℕ)) (S l : ℝ) (hS : 0<S)
    (good : ∀ p ∈ A, 0<p.1 ∧ (p.1:ℝ)≤S ∧ p.2.Coprime p.1 ∧
      ∃ x ∈ Set.Icc l (l+1/S^2), |x-(p.2:ℝ)/p.1|≤1/((p.1:ℝ)*S)) : A.card≤7 := by
  classical
  by_cases hA : A.Nonempty
  · obtain ⟨v,hv,hm⟩ := A.exists_max_image Prod.fst hA
    obtain ⟨hv0,hvS,hc,y,hy,hyv⟩ := good v hv
    have inj : Set.InjOn (fun p => det p v) A := by
      intro p hp u hu h
      exact det_injective hv0 hc (good p hp).1 (hm p hp) (good u hu).1 (hm u hu) h
    have sub : A.image (fun p => det p v) ⊆ Finset.Icc (-3:ℤ) 3 := by
      intro k hk
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hk
      obtain ⟨hp0,hpS,_,x,hx,hxp⟩ := good p hp
      have hxy : |x-y|≤1/S^2 := abs_le.mpr ⟨by linarith [hx.1,hy.2],by linarith [hx.2,hy.1]⟩
      exact mem_Icc.mpr (abs_le.mp (det_bound hS hp0 hv0 hpS hvS hxp hyv hxy))
    simpa [card_image_of_injOn inj] using Finset.card_le_card sub
  · simp [Finset.not_nonempty_iff_eq_empty.mp hA]

end GoldbachMovingWindows
end
end

section
open Set Finset MeasureTheory intervalIntegral Complex
noncomputable section
namespace GoldbachMovingWindows

private def c : ℂ := (2*Real.pi:ℝ)*I
def wave (k : ℕ) (t : ℝ) : ℂ := Complex.exp (c * k * (t : ℂ))
def series (n : ℕ) (w : ℕ→ℝ) (t : ℝ) : ℂ := ∑ k ∈ range (n+1), (w k : ℂ)*wave k t

theorem wave_eq (k : ℕ) (t : ℝ) :
    wave k t = Complex.exp ((((2*Real.pi*((k:ℝ)*t):ℝ):ℂ))*I) := by
  unfold wave c
  apply congrArg Complex.exp
  push_cast
  ring

theorem energy (n : ℕ) (w : ℕ→ℝ) :
    (∫ t in (0:ℝ)..1, ‖series n w t‖^2) = ∑ k ∈ range (n+1), (w k)^2 := by
  simpa only [series,wave_eq] using continuous_parseval n w

private theorem wave_deriv (k : ℕ) (t : ℝ) :
    HasDerivAt (wave k) (wave k t * (c*k)) t := by
  let C := c*(k:ℂ)
  have hd := (Complex.hasDerivAt_exp (C*(t:ℂ))).comp (t:ℂ) ((hasDerivAt_id (t:ℂ)).const_mul C)
  change HasDerivAt (fun x : ℝ => Complex.exp (C*(x:ℂ))) (Complex.exp (C*(t:ℂ))*C) t
  simpa [C] using! hd.comp_ofReal

theorem series_deriv (n : ℕ) (w : ℕ→ℝ) (t : ℝ) :
    HasDerivAt (series n w) (c * series n (fun k => k*w k) t) t := by
  have h := HasDerivAt.fun_sum (u:=range (n+1)) (fun k _ => (wave_deriv k t).const_mul (w k:ℂ))
  apply h.congr_deriv
  unfold series
  rw [Finset.mul_sum]
  refine sum_congr rfl fun k _ => ?_
  push_cast
  ring

theorem series_cont (n : ℕ) (w : ℕ→ℝ) : Continuous (series n w) :=
  continuous_iff_continuousAt.mpr (fun t => (series_deriv n w t).continuousAt)

private theorem energy_deriv_abs (n : ℕ) (w : ℕ→ℝ) (hn : 0<n) :
    (∫ t in (0:ℝ)..1, |2 * inner ℝ (series n w t) (c*series n (fun k => k*w k) t)|) ≤
      (4*Real.pi)*(n:ℝ)*(∑ k ∈ range (n+1),(w k)^2) := by
  let F := series n w
  let G := series n (fun k => k*w k)
  have cF : Continuous F := series_cont ..
  have cG : Continuous G := series_cont ..
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hc : ‖c‖ = 2*Real.pi := by simp [c]
  have major (t : ℝ) : |2 * inner ℝ (F t) (c*G t)| ≤
      (2*Real.pi)*((n:ℝ)*‖F t‖^2+(1/(n:ℝ))*‖G t‖^2) := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hv := abs_real_inner_le_norm (F t) (c*G t)
    rw [norm_mul,hc] at hv
    have key : 2*‖F t‖*‖G t‖ ≤ (n:ℝ)*‖F t‖^2+(1/(n:ℝ))*‖G t‖^2 := by
      apply (mul_le_mul_iff_right₀ hn0).mp
      field_simp
      nlinarith [sq_nonneg ((n:ℝ)*‖F t‖-‖G t‖)]
    nlinarith only [hv,mul_le_mul_of_nonneg_left key (show (0:ℝ)≤Real.pi by positivity)]
  have ci : Continuous (fun t => |2 * inner ℝ (F t) (c*G t)|) := by fun_prop
  have cj : Continuous (fun t => (2*Real.pi)*((n:ℝ)*‖F t‖^2+(1/(n:ℝ))*‖G t‖^2)) := by fun_prop
  have ii := intervalIntegral.integral_mono (μ:=volume) (by norm_num : (0:ℝ)≤1)
    (ci.intervalIntegrable ..) (cj.intervalIntegrable ..) major
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add (by exact (continuous_const.mul (cF.norm.pow 2)).intervalIntegrable ..)
    (by exact (continuous_const.mul (cG.norm.pow 2)).intervalIntegrable ..),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at ii
  dsimp only [F,G] at ii
  rw [energy,energy] at ii
  have edge : (∑ k ∈ range (n+1), ((k:ℝ)*w k)^2) ≤ (n:ℝ)^2 * ∑ k ∈ range (n+1),(w k)^2 := by
    rw [Finset.mul_sum]
    refine sum_le_sum fun k hk => ?_
    have hk' : (k:ℝ) ≤ n := by exact_mod_cast (show k≤n by have := mem_range.mp hk;omega)
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hk' 2) (sq_nonneg _)
  apply ii.trans
  have e := mul_le_mul_of_nonneg_left edge (show 0≤1/(n:ℝ) by positivity)
  have simpN : 1/(n:ℝ)*((n:ℝ)^2*(∑ k ∈ range (n+1),(w k)^2)) = n*(∑ k ∈ range (n+1),(w k)^2) := by field_simp
  rw [simpN] at e
  nlinarith only [mul_le_mul_of_nonneg_left e Real.pi_pos.le]

/-- A frequency polynomial may be sampled at an arbitrary point in every mesh
cell. The sample locations may depend on the coefficients. -/
theorem sample_series {n : ℕ} (hn : 0<n) (w : ℕ→ℝ) (t : ℕ→ℝ)
    (h : ∀ j<n,t j ∈ Icc ((j:ℝ)/n) (((j:ℝ)+1)/n)) :
    (∑ j ∈ range n, ‖series n w (t j)‖^2) ≤
      (1+4*Real.pi)*(n:ℝ)*(∑ k ∈ range (n+1),(w k)^2) := by
  have cF := series_cont n w
  have cG := series_cont n (fun k => k*w k)
  have ht := sample_mesh (fun x => (series_deriv n w x).norm_sq)
    (by fun_prop) hn t h
  rw [energy] at ht
  linarith only [ht,energy_deriv_abs n w hn]

end GoldbachMovingWindows
end
end

section
open Set Finset Complex
noncomputable section
namespace GoldbachMovingWindows
private def cell (n : ℕ) (t : ℝ) := min ⌊(n:ℝ)*t⌋₊ (n-1)

private theorem cell_mem {n : ℕ} (hn : 0<n) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    cell n t < n ∧ t ∈ Set.Icc ((cell n t:ℝ)/n) (((cell n t:ℝ)+1)/n) := by
  have hN : (0:ℝ)<n := by exact_mod_cast hn
  have h0 := mul_nonneg hN.le ht.1
  have upper := Nat.lt_floor_add_one ((n:ℝ)*t)
  have lower := Nat.floor_le h0
  have clamp : ((n-1:ℕ):ℝ) = (n:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  constructor
  · exact (min_le_right _ _).trans_lt (by omega)
  · rw [Set.mem_Icc,div_le_iff₀ hN,le_div_iff₀ hN]
    by_cases h : ⌊(n:ℝ)*t⌋₊ ≤ n-1
    · rw [cell,min_eq_left h]
      constructor <;> linarith
    · rw [cell,min_eq_right (by omega : n-1≤⌊(n:ℝ)*t⌋₊),clamp]
      have hv : n≤⌊(n:ℝ)*t⌋₊ := by omega
      have hvR : (n:ℝ)≤⌊(n:ℝ)*t⌋₊ := by exact_mod_cast hv
      have ht1 := mul_le_mul_of_nonneg_left ht.2 hN.le
      constructor <;> linarith

/-- A maximal large sieve over the square-root Dirichlet windows. Each sample
may be chosen independently after seeing the coefficients. -/
theorem moving_large_sieve {n : ℕ} (hn : 0<n) (w : ℕ→ℝ) (A : Finset (ℕ×ℕ)) (t : ℕ×ℕ → ℝ)
    (good : ∀ p ∈ A, 0<p.1 ∧ (p.1:ℝ)≤Real.sqrt n ∧ p.2.Coprime p.1 ∧
      t p ∈ Set.Icc (0:ℝ) 1 ∧ |t p-(p.2:ℝ)/p.1| ≤ 1/((p.1:ℝ)*Real.sqrt n)) :
    (∑ p ∈ A, ‖series n w (t p)‖^2) ≤ 7*(1+4*Real.pi)*(n:ℝ)*∑ k ∈ range (n+1), (w k)^2 := by
  classical
  have hN : (0:ℝ)<n := by exact_mod_cast hn
  have hS := Real.sqrt_pos.mpr hN
  let bucket (j : ℕ) := A.filter (fun p => cell n (t p)=j)
  have bucketMem (j : ℕ) (p : ℕ×ℕ) (hp : p ∈ bucket j) :
      t p ∈ Set.Icc ((j:ℝ)/n) (((j:ℝ)+1)/n) := by
    obtain ⟨ha,he⟩ := mem_filter.mp hp
    simpa only [←he] using (cell_mem hn (good p ha).2.2.2.1).2
  have few (j : ℕ) : (bucket j).card ≤ 7 := by
    apply at_most_seven (bucket j) (Real.sqrt n) ((j:ℝ)/n) hS
    intro p hp
    have ha := (mem_filter.mp hp).1
    obtain ⟨hp0,hpS,hcop,_⟩ := good p ha
    refine ⟨hp0,hpS,hcop,t p,?_,(good p ha).2.2.2.2⟩
    simpa only [Real.sq_sqrt hN.le,add_div] using bucketMem j p hp

  let v := fun p : ℕ×ℕ => ‖series n w (t p)‖^2
  let pick (j : ℕ) (h : (bucket j).Nonempty) := ((bucket j).exists_max_image v h).choose
  have best (j : ℕ) (h : (bucket j).Nonempty) :
      pick j h ∈ bucket j ∧ ∀ p ∈ bucket j, v p ≤ v (pick j h) :=
    ((bucket j).exists_max_image v h).choose_spec
  let sample (j : ℕ) := if h : (bucket j).Nonempty then t (pick j h) else (j:ℝ)/n
  have samples (j : ℕ) (_ : j<n) : sample j ∈ Set.Icc ((j:ℝ)/n) (((j:ℝ)+1)/n) := by
    by_cases h : (bucket j).Nonempty
    · simpa only [sample,dite_eq_left h] using bucketMem j (pick j h) (best j h).1
    · simp only [sample,dite_eq_right h,Set.mem_Icc,le_refl,true_and]
      exact div_le_div_of_nonneg_right (by linarith) hN.le
  have charge (j : ℕ) : (∑ p ∈ bucket j,v p) ≤ 7*‖series n w (sample j)‖^2 := by
    by_cases h : (bucket j).Nonempty
    · have h7 : ((bucket j).card:ℝ)≤7 := by exact_mod_cast few j
      rw [show sample j = t (pick j h) by simp [sample,h]]
      exact (Finset.sum_le_sum (best j h).2).trans (by
        simpa only [sum_const,nsmul_eq_mul] using
          (show ((bucket j).card : ℝ)*v (pick j h) ≤ 7*v (pick j h) from
            mul_le_mul_of_nonneg_right h7 (sq_nonneg _)))
    · rw [Finset.not_nonempty_iff_eq_empty.mp h]
      simp
  have cover (p : ℕ×ℕ) (hp : p∈A) : cell n (t p) ∈ range n :=
    mem_range.mpr (cell_mem hn (good p hp).2.2.2.1).1
  change (∑ p ∈ A, v p) ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to cover v]
  calc
    _ ≤ ∑ j ∈ range n, 7*‖series n w (sample j)‖^2 := sum_le_sum (fun j _ => charge j)
    _ = 7*∑ j ∈ range n, ‖series n w (sample j)‖^2 := (Finset.mul_sum ..).symm
    _ ≤ _ := (mul_le_mul_of_nonneg_left (sample_series hn w sample samples) (by norm_num : (0:ℝ)≤7)).trans_eq (by ring)

end GoldbachMovingWindows
end
end

section
open Finset Real Filter
noncomputable section
namespace GoldbachMovingWindows

def primeLog (k : ℕ) : ℝ := if k.Prime then Real.log k else 0

theorem primeLog_energy (n : ℕ) :
    (∑ k ∈ range (n+1),(primeLog k)^2) ≤ Real.log 4*(n:ℝ)*Real.log n := by
  have mass : (∑ k ∈ range (n+1),primeLog k) = Chebyshev.theta n := by
    unfold primeLog
    rw [←Finset.sum_filter,Chebyshev.theta_eq_sum_primesLE_log]
    congr 1
  calc
    _ ≤ ∑ k ∈ range (n+1),Real.log n*primeLog k := by
      refine sum_le_sum fun k hk => ?_
      have hn : k≤n := by have := mem_range.mp hk;omega
      by_cases hp : k.Prime
      · have hk0 : 0 < (k:ℝ) := by exact_mod_cast hp.pos
        have hu := Real.log_le_log hk0 (by exact_mod_cast hn : (k:ℝ)≤n)
        have h0 := Real.log_natCast_nonneg k
        simpa [primeLog,hp,pow_two] using mul_le_mul_of_nonneg_right hu h0
      · simp [primeLog,hp]
    _ ≤ _ := by
      rw [← mul_sum,mass]
      have := mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)) (Real.log_natCast_nonneg n)
      linarith only [this]

def windowConstant : ℝ := 7*(1+4*Real.pi)*Real.log 4

end GoldbachMovingWindows
end
end

section
open Finset
noncomputable section
namespace GoldbachMovingWindows

private def flag (P : Prop) [Decidable P] : ℤ := if P then 1 else 0
def leftBlock (d j k : ℕ) : Prop := k/2^d=2*j
def activeBlock (d j m : ℕ) : Prop := m/2^d=2*j+1
instance (d j k : ℕ) : Decidable (leftBlock d j k) := inferInstanceAs (Decidable (_=_))
instance (d j k : ℕ) : Decidable (activeBlock d j k) := inferInstanceAs (Decidable (_=_))

private theorem prefix_level (d k m : ℕ) :
    flag (k/2^d < m/2^d) - flag (k/2^(d+1) < m/2^(d+1)) =
      if leftBlock d ((k/2^d)/2) k ∧ activeBlock d ((k/2^d)/2) m then 1 else 0 := by
  simp only [pow_succ,←Nat.div_div_eq_div_mul,leftBlock,activeBlock,flag]
  split_ifs <;> omega

private theorem prefix_indicator {n k m H : ℕ} (hk : k ≤ n) (hm : m < 2^H) :
    flag (k < m) = ∑ d ∈ range H, ∑ j ∈ range (n+1),
      if leftBlock d j k ∧ activeBlock d j m then 1 else 0 := by
  have single (d : ℕ) : (∑ j ∈ range (n+1),
      if leftBlock d j k ∧ activeBlock d j m then (1:ℤ) else 0) =
      flag (k/2^d < m/2^d) - flag (k/2^(d+1) < m/2^(d+1)) := by
    rw [prefix_level]
    apply sum_eq_single ((k/2^d)/2)
    · intro j _ hj
      apply ite_eq_right
      rintro ⟨hl,_⟩
      dsimp [leftBlock] at hl
      omega
    · intro hn
      exact False.elim (hn (mem_range.mpr (Nat.lt_succ_of_le (((Nat.div_le_self _ _).trans (Nat.div_le_self _ _)).trans hk))))
  simp_rw [single]
  have tele (h : ℕ) : (∑ d ∈ range h, (flag (k/2^d < m/2^d)-flag (k/2^(d+1) < m/2^(d+1)))) =
      flag (k < m)-flag (k/2^h < m/2^h) := by
    induction h with
    | zero => simp
    | succ h ih => rw [sum_range_succ,ih];abel
  rw [tele,Nat.div_eq_of_lt hm]
  simp [flag]

def toggled (d j : ℕ) (I : ℕ×ℕ) : Prop :=
  (activeBlock d j I.2 ∧ ¬activeBlock d j I.1) ∨ (activeBlock d j I.1 ∧ ¬activeBlock d j I.2)
instance (d j : ℕ) (I : ℕ×ℕ) : Decidable (toggled d j I) := by unfold toggled;infer_instance

theorem active_bounds (d j m : ℕ) : activeBlock d j m ↔
    (2*j+1)*2^d  ≤  m ∧ m < (2*j+2)*2^d := by
  have hp : 0 < 2^d := pow_pos (by decide) _
  unfold activeBlock
  rw [show m/2^d=2*j+1 ↔ 2*j+1 ≤ m/2^d ∧ m/2^d < 2*j+2 by omega,
    Nat.le_div_iff_mul_le hp,Nat.div_lt_iff_lt_mul hp]

private theorem toggled_crossing (d j : ℕ) (I : ℕ×ℕ) (hI : I.1 ≤ I.2) (ht : toggled d j I) :
    (2*j+1)*2^d ∈ Ioc I.1 I.2 ∨ (2*j+2)*2^d ∈ Ioc I.1 I.2 := by
  simp only [toggled,active_bounds] at ht
  simp only [mem_Ioc]
  rcases ht with h|h <;> omega

/-- A dyadic block enters a growing sum once and leaves it once as the endpoint moves. -/
theorem toggled_card {J : Finset (ℕ×ℕ)} (nonemptyI : ∀ I ∈ J,I.1 < I.2)
    (disj : ∀ I ∈ J, ∀ K ∈ J, I≠K → I.2 ≤ K.1 ∨ K.2 ≤ I.1) (d j : ℕ) :
    (J.filter (toggled d j)).card ≤ 2 := by
  let G (x : ℕ) := J.filter (fun I => x ∈ Ioc I.1 I.2)
  have atmost (x : ℕ) : (G x).card ≤ 1 := by
    apply card_le_one.mpr
    intro I hi K hk
    obtain ⟨hiJ,hix⟩ := mem_filter.mp hi
    obtain ⟨hkJ,hkx⟩ := mem_filter.mp hk
    by_contra hne
    have hc := disj I hiJ K hkJ hne
    simp only [mem_Ioc] at hix hkx
    omega
  have sub : J.filter (toggled d j) ⊆ G ((2*j+1)*2^d) ∪ G ((2*j+2)*2^d) := by
    intro I hi
    obtain ⟨hJ,ht⟩ := mem_filter.mp hi
    rcases toggled_crossing d j I (nonemptyI I hJ).le ht with h|h
    · exact mem_union_left _ (mem_filter.mpr ⟨hJ,h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hJ,h⟩)
  exact (card_le_card sub).trans ((card_union_le ..).trans (add_le_add (atmost _) (atmost _)))

theorem toggled_per_level (n d : ℕ) (I : ℕ×ℕ) :
    ((range (n+1)).filter (fun j => toggled d j I)).card ≤ 2 := by
  have sub : (range (n+1)).filter (fun j => toggled d j I) ⊆ {I.1/2^d/2,I.2/2^d/2} := by
    intro j hj
    rcases (mem_filter.mp hj).2 with h|h <;> simp only [activeBlock] at h <;> simp <;> omega
  exact (card_le_card sub).trans (card_le_two ..)


def blockWeight (w : ℕ→ℝ) (d j k : ℕ) : ℝ := if leftBlock d j k then w k else 0

private theorem block_series (n : ℕ) (w : ℕ→ℝ) (d j : ℕ) (t : ℝ) :
    series n (blockWeight w d j) t = ∑ k ∈ range (n+1), if leftBlock d j k then (w k:ℂ)*wave k t else 0 := by
  unfold series
  refine sum_congr rfl fun k _ => ?_
  by_cases h : leftBlock d j k <;> simp [blockWeight,h]

private theorem prefix_expand {n m H : ℕ} (hm : m ≤ n+1) (hH : m < 2^H) (w : ℕ→ℝ) (t : ℝ) :
    (∑ k ∈ range m,(w k:ℂ)*wave k t) = ∑ d ∈ range H, ∑ j ∈ range (n+1),
      if activeBlock d j m then series n (blockWeight w d j) t else 0 := by
  let V := fun k => (w k:ℂ)*wave k t
  have per (k : ℕ) (hk : k∈range (n+1)) : (if k < m then V k else 0) =
      ∑ d ∈ range H,∑ j ∈ range (n+1), if activeBlock d j m then (if leftBlock d j k then V k else 0) else 0 := by
    have hi := congrArg (fun z : ℤ => (z:ℂ)*V k) (prefix_indicator (Nat.le_of_lt_succ (mem_range.mp hk)) hH)
    simp only [Int.cast_sum,Finset.sum_mul] at hi
    convert hi using 1
    · by_cases h : k < m <;> simp [flag,h]
    · refine sum_congr rfl fun d _ => sum_congr rfl fun j _ => ?_
      by_cases h : activeBlock d j m <;> by_cases h' : leftBlock d j k <;> simp [h,h']
  change (∑ k ∈ range m,V k) = _
  calc
    _ = ∑ k ∈ range (n+1), if k < m then V k else 0 := by
      rw [←sum_filter]
      congr 1
      ext k
      simp only [mem_filter,mem_range]
      omega
    _ = ∑ k ∈ range (n+1),∑ d ∈ range H,∑ j ∈ range (n+1),
          if activeBlock d j m then (if leftBlock d j k then V k else 0) else 0 := sum_congr rfl per
    _ = _ := by
      rw [sum_comm]
      refine sum_congr rfl fun d _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun j _ => ?_
      by_cases h : activeBlock d j m <;> simp [h,block_series,V]

def intervalSum (I : ℕ×ℕ) (w : ℕ→ℝ) (t : ℝ) : ℂ := ∑ k ∈ Ico I.1 I.2,(w k:ℂ)*wave k t

theorem span_block_bound {n H : ℕ} (I : ℕ×ℕ) (hI : I.1≤I.2) (hvn : I.2≤n+1) (hH : n+1 < 2^H)
    (w : ℕ→ℝ) (t : ℝ) :
    ‖intervalSum I w t‖^2 ≤ (2*(H:ℝ))*
      ∑ d ∈ range H,∑ j ∈ (range (n+1)).filter (fun j => toggled d j I), ‖series n (blockWeight w d j) t‖^2 := by
  let G := fun d j => series n (blockWeight w d j) t
  let T := fun d => (range (n+1)).filter (fun j => toggled d j I)
  let F := fun d j => (if activeBlock d j I.2 then G d j else 0) - (if activeBlock d j I.1 then G d j else 0)
  have normF (d j : ℕ) : ‖F d j‖ = if toggled d j I then ‖G d j‖ else 0 := by
    by_cases h : activeBlock d j I.2 <;> by_cases h' : activeBlock d j I.1 <;> simp [F,toggled,h,h']
  have eq : intervalSum I w t = ∑ d ∈ range H,∑ j ∈ range (n+1),F d j := by
    rw [intervalSum,sum_Ico_eq_sub _ hI,prefix_expand hvn (hvn.trans_lt hH),
      prefix_expand (hI.trans hvn) ((hI.trans hvn).trans_lt hH),←sum_sub_distrib]
    exact sum_congr rfl fun d _ => (sum_sub_distrib ..).symm
  have tri : ‖intervalSum I w t‖ ≤ ∑ d ∈ range H,∑ j ∈ T d,‖G d j‖ := by
    rw [eq]
    apply (norm_sum_le ..).trans
    apply sum_le_sum
    intro d _
    apply (norm_sum_le ..).trans_eq
    simp_rw [normF]
    rw [←sum_filter]
  have lev (d : ℕ) :
      (∑ j ∈ T d,‖G d j‖)^2 ≤ 2*∑ j ∈ T d,‖G d j‖^2 := by
    exact (sq_sum_le_card_mul_sum_sq (s:=T d) (f:=fun j => ‖G d j‖)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast toggled_per_level n d I) (sum_nonneg fun _ _ => sq_nonneg _))
  apply (pow_le_pow_left₀ (norm_nonneg _) tri 2).trans
  apply (sq_sum_le_card_mul_sum_sq (s:=range H) (f:=fun d => ∑ j ∈ T d,‖G d j‖)).trans
  rw [card_range]
  exact (mul_le_mul_of_nonneg_left (sum_le_sum fun d _ => lev d) (Nat.cast_nonneg H)).trans_eq (by rw [←mul_sum];ring)


end GoldbachMovingWindows
end
end

section
open Finset Set
noncomputable section
namespace GoldbachMovingWindows

def rationalWindow (n : ℕ) (p : ℕ×ℕ) (t : ℝ) : Prop :=
  t ∈ Set.Icc (0:ℝ) 1 ∧ |t-(p.2:ℝ)/p.1| ≤ 1/((p.1:ℝ)*Real.sqrt n)

def windowPair (n : ℕ) (p : ℕ×ℕ) : Prop :=
  0 < p.1 ∧ (p.1:ℝ)≤Real.sqrt n ∧ p.2≤p.1 ∧ p.2.Coprime p.1

def intervalFamily (n : ℕ) (J : Finset (ℕ×ℕ)) : Prop :=
  (∀ I ∈ J, I.1 < I.2 ∧ I.2≤n+1) ∧
  ∀ I ∈ J, ∀ K ∈ J, I≠K → I.2≤K.1 ∨ K.2≤I.1

private theorem center_window {n : ℕ} {p : ℕ×ℕ} (hp : windowPair n p) :
    rationalWindow n p ((p.2:ℝ)/p.1) := by
  have h0 : 0<(p.1:ℝ) := by exact_mod_cast hp.1
  refine ⟨⟨by positivity,(div_le_one h0).mpr (by exact_mod_cast hp.2.2.1)⟩,?_⟩
  rw [sub_self,abs_zero]
  positivity

private theorem sum_toggled_samples {n : ℕ} (hn : 0<n) (w : ℕ→ℝ)
    (A : Finset (ℕ×ℕ)) (J : ℕ×ℕ → Finset (ℕ×ℕ)) (t : (ℕ×ℕ) → (ℕ×ℕ) → ℝ)
    (good : ∀ p ∈ A,windowPair n p ∧ intervalFamily n (J p) ∧ ∀ I ∈ J p,rationalWindow n p (t p I))
    (d j : ℕ) :
    (∑ p ∈ A, ∑ I ∈ (J p).filter (toggled d j), ‖series n w (t p I)‖^2) ≤
      2*(7*(1+4*Real.pi)*(n:ℝ)*∑ k ∈ range (n+1),(w k)^2) := by
  classical
  let B := fun p => (J p).filter (toggled d j)
  let val := fun p I => ‖series n w (t p I)‖^2
  let pick (p) (h : (B p).Nonempty) := ((B p).exists_max_image (val p) h).choose
  have best (p) (h : (B p).Nonempty) : pick p h ∈ B p ∧ ∀ I ∈ B p,val p I ≤ val p (pick p h) :=
    ((B p).exists_max_image (val p) h).choose_spec
  let sample (p : ℕ×ℕ) := if h : (B p).Nonempty then t p (pick p h) else (p.2:ℝ)/p.1
  have samplegood (p) (hp : p∈A) : rationalWindow n p (sample p) := by
    dsimp only [sample];split_ifs with h
    · exact (good p hp).2.2 _ (mem_filter.mp (best p h).1).1
    · exact center_window (good p hp).1
  have bound (p) (hp : p∈A) : (∑ I ∈ B p, val p I) ≤ 2*‖series n w (sample p)‖^2 := by
    by_cases h : (B p).Nonempty
    · rw [show sample p = t p (pick p h) by simp only [sample,dite_eq_left h]]
      have lim : ((B p).card:ℝ)≤2 := by exact_mod_cast toggled_card (fun I hI => ((good p hp).2.1.1 I hI).1) (good p hp).2.1.2 d j
      exact (sum_le_sum (best p h).2).trans (by
        rw [sum_const,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right lim (sq_nonneg _))
    · rw [Finset.not_nonempty_iff_eq_empty.mp h,sum_empty];positivity
  have sieve := moving_large_sieve hn w A sample (fun p hp => ⟨(good p hp).1.1,(good p hp).1.2.1,
    (good p hp).1.2.2.2,(samplegood p hp).1,(samplegood p hp).2⟩)
  apply (sum_le_sum bound).trans
  rw [←Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left sieve (by norm_num)

private theorem block_energy (n d : ℕ) (w : ℕ→ℝ) :
    (∑ j ∈ range (n+1), ∑ k ∈ range (n+1), (blockWeight w d j k)^2) ≤ ∑ k ∈ range (n+1),(w k)^2 := by
  rw [sum_comm]
  refine sum_le_sum fun k hk => ?_
  have eq : (∑ j ∈ range (n+1),(blockWeight w d j k)^2) = (blockWeight w d (k/2^d/2) k)^2 := by
    apply sum_eq_single
    · intro j _ hj
      have h : ¬leftBlock d j k := by unfold leftBlock;omega
      simp [blockWeight,h]
    · intro h
      exact False.elim (h (mem_range.mpr (((Nat.div_le_self _ _).trans (Nat.div_le_self _ _)).trans_lt (mem_range.mp hk))))
  rw [eq]
  by_cases h : leftBlock d (k/2^d/2) k <;> simp [blockWeight,h,sq_nonneg]

/-- A variational large sieve. Every reduced pair can choose a disjoint family
of coefficient intervals and a separate frequency in its window for each interval. -/
theorem variation_sieve {n H : ℕ} (hn : 0<n) (hH : n+1 < 2^H) (w : ℕ→ℝ)
    (A : Finset (ℕ×ℕ)) (J : ℕ×ℕ → Finset (ℕ×ℕ)) (t : (ℕ×ℕ) → (ℕ×ℕ) → ℝ)
    (good : ∀ p ∈ A,windowPair n p ∧ intervalFamily n (J p) ∧ ∀ I ∈ J p,rationalWindow n p (t p I)) :
    (∑ p ∈ A,∑ I ∈ J p,‖intervalSum I w (t p I)‖^2) ≤
      4*(H:ℝ)^2*(7*(1+4*Real.pi)*(n:ℝ))*(∑ k ∈ range (n+1),(w k)^2) := by
  let G := fun d j p I => ‖series n (blockWeight w d j) (t p I)‖^2
  let E := fun d j => ∑ k ∈ range (n+1),(blockWeight w d j k)^2
  let C := 7*(1+4*Real.pi)*(n:ℝ)
  let L := fun d j p => ∑ I ∈ (J p).filter (toggled d j),G d j p I
  have hC : 0≤C := by dsimp [C];positivity
  have rearrange (p : ℕ×ℕ) : (∑ I ∈ J p, ∑ d ∈ range H,
        ∑ j ∈ (range (n+1)).filter (fun j => toggled d j I),G d j p I) =
      ∑ d ∈ range H,∑ j ∈ range (n+1),L d j p := by
    rw [sum_comm]
    apply sum_congr rfl
    intro d _
    simp only [L,sum_filter]
    rw [sum_comm]
  have localBound (p) (hp : p∈A) : (∑ I ∈ J p,‖intervalSum I w (t p I)‖^2) ≤
      (2*H)*∑ d ∈ range H,∑ j ∈ range (n+1),L d j p := by
    calc
      _ ≤ ∑ I ∈ J p,(2*(H:ℝ))*∑ d ∈ range H,∑ j ∈ (range (n+1)).filter (fun j => toggled d j I),G d j p I :=
        sum_le_sum fun I hI => span_block_bound I ((good p hp).2.1.1 I hI).1.le ((good p hp).2.1.1 I hI).2 hH w (t p I)
      _ = _ := by rw [←mul_sum,rearrange]
  have each (d : ℕ) :
      (∑ j ∈ range (n+1),∑ p ∈ A,L d j p) ≤ (2*C)*∑ k ∈ range (n+1),(w k)^2 := by
    calc
      _ ≤ ∑ j ∈ range (n+1), (2*C)*E d j := by
        refine sum_le_sum fun j _ => ?_
        exact (sum_toggled_samples hn (blockWeight w d j) A J t good d j).trans_eq (by dsimp [E,C];ring)
      _ ≤ _ := by rw [←mul_sum];exact mul_le_mul_of_nonneg_left (block_energy n d w) (by positivity)
  apply (sum_le_sum localBound).trans
  rw [←mul_sum,sum_comm]
  have swap (d : ℕ) : (∑ p ∈ A,∑ j ∈ range (n+1),L d j p) = ∑ j ∈ range (n+1),∑ p ∈ A,L d j p := sum_comm
  simp_rw [swap]
  exact (mul_le_mul_of_nonneg_left (sum_le_sum fun d _ => each d) (by positivity : 0≤2*(H:ℝ))).trans_eq (by
    rw [sum_const,card_range,nsmul_eq_mul];dsimp [C];ring)

end GoldbachMovingWindows
end
end

section
open Finset Set Filter
noncomputable section
namespace GoldbachMovingWindows

def variationDepth (n : ℕ) := Nat.log 2 (n+1)+1

def exceptionalVariation (n : ℕ) (η : ℝ) (p : ℕ×ℕ) : Prop :=
  ∃ (J : Finset (ℕ×ℕ)) (t : ℕ×ℕ → ℝ),
    intervalFamily n J ∧ (∀ I ∈ J,rationalWindow n p (t I)) ∧
    ((n:ℝ)^(3/4+η))^2 ≤ ∑ I ∈ J, ‖intervalSum I primeLog (t I)‖^2

theorem variation_pair_count {n : ℕ} (hn : 0<n) (η : ℝ) (A : Finset (ℕ×ℕ))
    (good : ∀ p∈A, windowPair n p ∧ exceptionalVariation n η p) :
    (A.card:ℝ) ≤ 4*(variationDepth n:ℝ)^2*windowConstant*(n:ℝ)^(1/2-2*η)*Real.log n := by
  classical
  let J (p : ℕ×ℕ) := if h : p∈A then (good p h).2.choose else ∅
  let t (p : ℕ×ℕ) := if h : p∈A then (good p h).2.choose_spec.choose else fun _ : ℕ×ℕ => (0:ℝ)
  have spec p (hp : p∈A) : intervalFamily n (J p) ∧ (∀ I ∈ J p,rationalWindow n p (t p I)) ∧
      ((n:ℝ)^(3/4+η))^2 ≤ ∑ I ∈ J p,‖intervalSum I primeLog (t p I)‖^2 := by
    simpa only [J,t,dite_eq_left hp] using (good p hp).2.choose_spec.choose_spec
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hH : n+1 < 2^variationDepth n := Nat.lt_pow_succ_log_self (by decide) _
  have s := variation_sieve hn hH primeLog A J t (fun p hp => ⟨(good p hp).1,(spec p hp).1,(spec p hp).2.1⟩)
  have charge := sum_le_sum (s:=A) (fun p hp => (spec p hp).2.2)
  rw [sum_const,nsmul_eq_mul] at charge
  have h := (charge.trans s).trans (mul_le_mul_of_nonneg_left (primeLog_energy n) (by positivity))
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos (Real.rpow_pos_of_pos hnR (3/4+η)))).mp
  apply h.trans_eq
  have poweq : (n:ℝ)^(1/2-2*η)*((n:ℝ)^(3/4+η))^2 = (n:ℝ)^2 := by
    rw [←Real.rpow_mul_natCast hnR.le,←Real.rpow_add hnR]
    norm_num [show (1/2-2*η)+(3/4+η)*(2:ℝ) = 2 by ring]
  dsimp only [windowConstant]
  linear_combination -(4*(variationDepth n:ℝ)^2*(7*(1+4*Real.pi))*Real.log 4*Real.log n)*poweq

private theorem depth_bound (n : ℕ) (hn : 1≤n) :
    (variationDepth n:ℝ) ≤ 2 + Real.log n / Real.log 2 := by
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hnat := Real.natLog_le_logb (n+1) 2
  rw [Real.logb] at hnat
  push_cast at hnat
  have hlog : Real.log ((n:ℝ)+1) ≤ Real.log 2 + Real.log n := by
    rw [←Real.log_mul (by norm_num) hnR.ne']
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show n+1≤2*n by omega)
  unfold variationDepth
  push_cast
  have hd := div_le_div_of_nonneg_right hlog h2.le
  rw [add_div,div_self h2.ne'] at hd
  linarith only [hnat,hd]

theorem eventually_variation_count {η : ℝ} (hη : 0<η) :
    ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ A : Finset (ℕ×ℕ),
      (∀ p∈A, windowPair n p ∧ exceptionalVariation n η p) → (A.card:ℝ)≤(n:ℝ)^(1/2-η) := by
  let u := η/6
  have hu : 0<u := by dsimp [u];linarith
  let K := 2+(1/u)/Real.log 2
  let C := 4*K^2*windowConstant*(1/u)
  have htwo : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hW : 0≤windowConstant := by unfold windowConstant;positivity
  have hK : 0≤K := by dsimp [K];positivity
  have lim : Tendsto (fun n : ℕ => (n:ℝ)^(η/2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hη)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp (lim.eventually_ge_atTop C)
  refine ⟨max 1 N,?_⟩
  intro n hn A good
  have hn1 : 1≤n := by omega
  have hnR : 1≤(n:ℝ) := by exact_mod_cast hn1
  have hn0 := zero_lt_one.trans_le hnR
  let x := (n:ℝ)^u
  have hx : 1≤x := Real.one_le_rpow hnR hu.le
  have hlog : Real.log n ≤ (1/u)*x := (Real.log_le_rpow_div hn0.le hu).trans_eq (by dsimp [x];ring)
  have hD : (variationDepth n:ℝ)≤K*x := by
    apply (depth_bound n hn1).trans
    have hh := div_le_div_of_nonneg_right hlog htwo.le
    calc
      _ ≤ 2*x + ((1/u)*x)/Real.log 2 := add_le_add (by linarith only [hx]) hh
      _ = _ := by dsimp [K];ring
  have budget : 4*(variationDepth n:ℝ)^2*windowConstant*Real.log n ≤ (n:ℝ)^η := by
    calc
      _ ≤ 4*(K*x)^2*windowConstant*((1/u)*x) := by gcongr
      _ = C*((n:ℝ)^u*(n:ℝ)^u*(n:ℝ)^u) := by dsimp [x,C];ring
      _ = C*(n:ℝ)^(η/2) := by
        rw [←Real.rpow_add hn0,←Real.rpow_add hn0]
        have he : u+u+u=η/2 := by dsimp [u];ring
        rw [he]
      _ ≤ (n:ℝ)^(η/2)*(n:ℝ)^(η/2) := mul_le_mul_of_nonneg_right (hN n (by omega)) (Real.rpow_nonneg hn0.le _)
      _ = _ := by rw [←Real.rpow_add hn0];congr 1;ring
  apply (variation_pair_count hn1 η A good).trans
  calc
    _ = (4*(variationDepth n:ℝ)^2*windowConstant*Real.log n)*(n:ℝ)^(1/2-2*η) := by ring
    _ ≤ (n:ℝ)^η*(n:ℝ)^(1/2-2*η) := mul_le_mul_of_nonneg_right budget (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [←Real.rpow_add hn0];congr 1;ring

end GoldbachMovingWindows
end
end

open GoldbachMovingWindows Finset
theorem PEqualNP.Outside.L_goldbach_variational_prime_dirichlet_windows :
let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0
let S := fun (I : ℕ×ℕ) (u : ℕ→ℝ) (t : ℝ) => ∑ k ∈ Finset.Ico I.1 I.2,(u k:ℂ)*E ((k:ℝ)*t)
let pair := fun (n : ℕ) (p : ℕ×ℕ) => 0<p.1 ∧ (p.1:ℝ)≤Real.sqrt n ∧ p.2≤p.1 ∧ p.2.Coprime p.1
let window := fun (n : ℕ) (p : ℕ×ℕ) (t : ℝ) => t ∈ Set.Icc (0:ℝ) 1 ∧ |t-(p.2:ℝ)/p.1| ≤ 1/((p.1:ℝ)*Real.sqrt n)
let family := fun (n : ℕ) (J : Finset (ℕ×ℕ)) =>
  (∀ I ∈ J,I.1 < I.2 ∧ I.2≤n+1) ∧ ∀ I ∈ J, ∀ K ∈ J, I≠K → I.2≤K.1 ∨ K.2≤I.1
(∀ (n : ℕ), 0<n → ∀ (u : ℕ→ℝ) (A : Finset (ℕ×ℕ)) (J : ℕ×ℕ → Finset (ℕ×ℕ)) (t : (ℕ×ℕ) → (ℕ×ℕ) → ℝ),
  (∀ p∈A, pair n p ∧ family n (J p) ∧ ∀ I ∈ J p, window n p (t p I)) →
  (∑ p ∈ A,∑ I ∈ J p,‖S I u (t p I)‖^2) ≤ 4*((Nat.log 2 (n+1)+1:ℕ):ℝ)^2*
    (7*(1+4*Real.pi)*(n:ℝ))*(∑ k ∈ Finset.range (n+1),(u k)^2)) ∧
(∀ η : ℝ, 0<η → ∃ N : ℕ, ∀ n : ℕ, N≤n → ∃ bad : Finset ℕ, (bad.card:ℝ)≤(n:ℝ)^(1/2-η) ∧
  ∀ (q : ℕ), 0<q → (q:ℝ)≤Real.sqrt n → q∉bad → ∀ (a : ℕ), a≤q → a.Coprime q →
  ∀ (J : Finset (ℕ×ℕ)), family n J → ∀ (t : ℕ×ℕ → ℝ), (∀ I ∈ J, window n (q,a) (t I)) →
    (∑ I ∈ J, ‖S I w (t I)‖^2) < ((n:ℝ)^(3/4+η))^2) := by
  classical
  intro E w S pair window family
  have eqS (I : ℕ×ℕ) (u : ℕ→ℝ) (t : ℝ) : S I u t = intervalSum I u t := by
    dsimp only [S,E,intervalSum]
    simp_rw [wave_eq]
  simp_rw [eqS]
  constructor
  · intro n hn u A J t good
    exact variation_sieve hn (Nat.lt_pow_succ_log_self (by decide : 1<2) (n+1)) u A J t good
  · intro η hη
    obtain ⟨N,count⟩ := eventually_variation_count hη
    refine ⟨max N 1,?_⟩
    intro n hn
    have hnR : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
    let U := (range (n+1)) ×ˢ (range (n+1))
    let A := U.filter (fun p => windowPair n p ∧ exceptionalVariation n η p)
    have hcnt := count n (by omega) A (fun _ hp => (mem_filter.mp hp).2)
    refine ⟨A.image Prod.fst,(show ((A.image Prod.fst).card:ℝ)≤A.card by exact_mod_cast card_image_le).trans hcnt,?_⟩
    intro q hq hqs hgood a ha hc J hJ t ht
    by_contra! hlarge
    have hqn : q≤n := by exact_mod_cast hqs.trans (Real.sqrt_le_self_iff.mpr (Or.inr hnR))
    have hu : (q,a)∈U := mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩
    have he : exceptionalVariation n η (q,a) := ⟨J,t,hJ,ht,hlarge⟩
    exact hgood (mem_image.mpr ⟨(q,a),mem_filter.mpr ⟨hu,⟨hq,hqs,ha,hc⟩,he⟩,rfl⟩)
