import Mathlib

/-!
# Quadratic variation in moving Dirichlet windows

Each reduced rational may choose disjoint coefficient intervals, with a separate
sample from its Dirichlet window on every interval. Dyadic endpoint differences
activate at most two blocks per level. A block can enter or leave at most twice
along a disjoint family. This yields the squared-logarithmic cost uniformly.
See Allison and Mark Lewko, A Variational Barban-Davenport-Halberstam Theorem,
https://doi.org/10.1016/j.jnt.2012.02.007 for the variational large sieve.
Gauss inversion on reduced numerators transfers the same moving-window estimate to
primitive Dirichlet characters. A large collective twisted prime bias forces a deep
rational-window peak. The additive offset may vary by denominator and by interval.
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
private theorem additive_window_variation :
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


section
open Complex Finset DirichletCharacter
open scoped Classical ComplexConjugate
noncomputable section
namespace GoldbachPrimeBias

def numerator {q : ℕ} [NeZero q] (f : ℕ → ℂ) (V : Finset ℕ) (a : (ZMod q)ˣ) : ℂ :=
  ∑ k ∈ V, f k*ZMod.stdAddChar ((a:ZMod q)*(k:ZMod q))

def characterSum {q : ℕ} (f : ℕ → ℂ) (V : Finset ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ k ∈ V, f k*χ (k:ZMod q)

private theorem energy_from_orthogonality {A B : Type*} [Fintype A] [Fintype B]
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

private theorem dual_orth {q : ℕ} [NeZero q] (a b : (ZMod q)ˣ) :
    (∑ χ : DirichletCharacter ℂ q,conj (χ a)*χ b) = if a=b then (q.totient:ℂ) else 0 := by
  have h (χ : DirichletCharacter ℂ q) : conj (χ a)=χ ((a:ZMod q)⁻¹) := by
    change star (χ (a:ZMod q)) = _
    rw [MulChar.star_apply',MulChar.inv_apply_eq_inv']
    apply inv_eq_of_mul_eq_one_right
    rw [←map_mul,ZMod.mul_inv_of_unit _ a.isUnit,map_one]
  simp_rw [h]
  simpa only [Units.val_inj] using (sum_char_inv_mul_char_eq ℂ a.isUnit (b:ZMod q))

private theorem unit_gauss_shift {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (k : ℕ) :
    (∑ a : (ZMod q)ˣ, χ a*ZMod.stdAddChar ((a:ZMod q)*(k:ZMod q))) =
      gaussSum χ (ZMod.stdAddChar.mulShift (k:ZMod q)) := by
  let e : (ZMod q)ˣ ↪ ZMod q := ⟨(↑),Units.val_injective⟩
  have h : (univ : Finset (ZMod q)).filter IsUnit = (univ : Finset (ZMod q)ˣ).map e := by
    ext r;simp [e,IsUnit]
  let v (r : ZMod q) := χ r*ZMod.stdAddChar (r*(k:ZMod q))
  calc
    _ = ∑ r ∈ (univ : Finset (ZMod q)).filter IsUnit,v r := by rw [h,sum_map];rfl
    _ = ∑ r : ZMod q,v r := sum_subset (filter_subset ..) (fun r _ hr => by
      dsimp [v];rw [MulChar.map_nonunit χ (by simpa using hr),zero_mul])
    _ = _ := by unfold gaussSum;apply sum_congr rfl;intro r _;dsimp [v,AddChar.mulShift_apply];rw [mul_comm r]

/-- Fourier inversion on the reduced numerators extracts every primitive
Dirichlet bias exactly, even when some indices share a factor with q. -/
theorem extract {q : ℕ} [NeZero q] (f : ℕ → ℂ) (V : Finset ℕ) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    (∑ a : (ZMod q)ˣ, numerator f V a*χ a) = gaussSum χ ZMod.stdAddChar * characterSum f V χ⁻¹ := by
  unfold numerator characterSum
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm,Finset.mul_sum]
  refine sum_congr rfl fun k _ => ?_
  calc
    _ = f k*(∑ a : (ZMod q)ˣ,χ a*ZMod.stdAddChar ((a:ZMod q)*(k:ZMod q))) := by
      rw [Finset.mul_sum];apply sum_congr rfl;intro a _;ring
    _ = _ := by rw [unit_gauss_shift,gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ];ring

/-- The joint primitive energy forces one peak among the reduced numerators. -/
theorem primitive_energy {q : ℕ} [NeZero q] (f : ℕ → ℂ) (V : Finset ℕ) :
    (q:ℝ)*(∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter IsPrimitive, ‖characterSum f V χ⁻¹‖^2) ≤
        (q.totient:ℝ)*(∑ a : (ZMod q)ˣ, ‖numerator f V a‖^2) := by
  let P := (univ : Finset (DirichletCharacter ℂ q)).filter IsPrimitive
  let W := fun χ : DirichletCharacter ℂ q => ∑ a : (ZMod q)ˣ,numerator f V a*χ a
  have each (χ : DirichletCharacter ℂ q) (hc : χ∈P) : ‖W χ‖^2 = (q:ℝ)*‖characterSum f V χ⁻¹‖^2 := by
    have hp : χ.IsPrimitive := (mem_filter.mp hc).2
    dsimp [W];rw [extract f V χ hp,norm_mul,mul_pow,DirichletCharacter.norm_gaussSum_stdAddChar hp,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  have total := energy_from_orthogonality (fun (a : (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) => χ a)
    (fun _ => (q.totient:ℝ)) (fun a b => by simpa using dual_orth a b) (numerator f V)
  calc
    _ = ∑ χ ∈ P,‖W χ‖^2 := by rw [Finset.mul_sum];exact sum_congr rfl fun χ hc => (each χ hc).symm
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖W χ‖^2 := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
    _ = ∑ b : (ZMod q)ˣ,(q.totient:ℝ)*‖numerator f V b‖^2 := total
    _ = _ := (Finset.mul_sum ..).symm
end GoldbachPrimeBias
end
end

section
open Complex Finset Set DirichletCharacter GoldbachMovingWindows
open scoped Classical ComplexConjugate
noncomputable section
namespace GoldbachPrimeBias

def reduced (q : ℕ) := (range q).filter (fun a => a.Coprime q)
private def unitVal {q : ℕ} [NeZero q] : (ZMod q)ˣ ↪ ℕ :=
  ⟨fun a => (a:ZMod q).val, fun _ _ e => Units.val_injective (ZMod.val_injective q e)⟩

theorem units_to_reduced {q : ℕ} [NeZero q] (f : ℕ→ℝ) :
    (∑ a : (ZMod q)ˣ,f (a:ZMod q).val) = ∑ a ∈ reduced q,f a := by
  have eq : (univ : Finset (ZMod q)ˣ).map unitVal = reduced q := by
    ext a
    simp only [Finset.mem_map,Finset.mem_univ,true_and,reduced,Finset.mem_filter,Finset.mem_range]
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨ZMod.val_lt _,(ZMod.isUnit_iff_coprime _ q).mp (by change IsUnit (((u:ZMod q).val:ℕ):ZMod q);rw [ZMod.natCast_zmod_val];exact u.isUnit)⟩
    · rintro ⟨hlt,hc⟩
      obtain ⟨u,hu⟩ := (ZMod.isUnit_iff_coprime a q).mpr hc
      exact ⟨u,by change (u:ZMod q).val=a;rw [hu,ZMod.val_natCast_of_lt hlt]⟩
  rw [←eq,sum_map];rfl

def oscillating (w : ℕ→ℝ) (β : ℝ) (k : ℕ) : ℂ := (w k:ℂ)*wave k β

private theorem wave_rational {q : ℕ} [NeZero q] (a k : ℕ) (β : ℝ) :
    wave k β*ZMod.stdAddChar ((a:ZMod q)*(k:ZMod q)) = wave k ((a:ℝ)/q+β) := by
  have h (m : ℕ) : ZMod.stdAddChar ((m:ℕ):ZMod q) = Complex.exp (2*(Real.pi:ℂ)*I*(m:ℂ)/(q:ℂ)) := by
    simpa only [Int.cast_natCast] using ZMod.stdAddChar_coe (N:=q) (m:ℤ)
  rw [←Nat.cast_mul,h,wave_eq,wave_eq,←Complex.exp_add]
  congr 1;push_cast;ring

theorem sample_eq {q : ℕ} [NeZero q] (I : ℕ×ℕ) (u : (ZMod q)ˣ) (w : ℕ→ℝ) (β : ℝ) :
    numerator (oscillating w β) (Finset.Ico I.1 I.2) u =
      intervalSum I w (((u:ZMod q).val:ℝ)/q+β) := by
  unfold numerator intervalSum
  apply sum_congr rfl
  intro k _
  rw [oscillating,mul_assoc,←wave_rational]
  simp only [ZMod.natCast_zmod_val]

private theorem reflected_interval (I : ℕ×ℕ) (w : ℕ→ℝ) (t : ℝ) :
    ‖intervalSum I w (-t)‖ = ‖intervalSum I w t‖ := by
  have hc : intervalSum I w (-t)=conj (intervalSum I w t) := by
    unfold intervalSum
    simp only [map_sum,map_mul,Complex.conj_ofReal]
    apply sum_congr rfl
    intro k _
    rw [wave_eq,wave_eq,←Complex.exp_conj]
    congr 2
    simp;norm_num [map_ofNat]
  rw [hc,Complex.norm_conj]

def samplePoint (q a : ℕ) (β : ℝ) := if q=1 then |β| else (a:ℝ)/q+β

theorem sample_norm {q : ℕ} [NeZero q] (I : ℕ×ℕ) (u : (ZMod q)ˣ) (w : ℕ→ℝ) (β : ℝ) :
    ‖numerator (oscillating w β) (Finset.Ico I.1 I.2) u‖ =
      ‖intervalSum I w (samplePoint q (u:ZMod q).val β)‖ := by
  rw [sample_eq];unfold samplePoint
  split_ifs with h
  · subst q
    have z : (u:ZMod 1).val=0 := by have := ZMod.val_lt (u:ZMod 1);omega
    simp only [z,Nat.cast_zero,zero_div,zero_add]
    rcases le_total 0 β with hb|hb
    · rw [abs_of_nonneg hb]
    · rw [abs_of_nonpos hb,reflected_interval]
  · rfl

theorem sample_window {n q a : ℕ} (hn : 1≤n) (hq : 0<q) (ha : a∈reduced q) {β : ℝ}
    (hβ : |β|≤1/((q:ℝ)*Real.sqrt n)) : rationalWindow n (q,a) (samplePoint q a β) := by
  obtain ⟨har,hac⟩ := mem_filter.mp ha
  have hal := mem_range.mp har
  have hs : 1≤Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have hqR : 0<(q:ℝ) := by exact_mod_cast hq
  have off : |β|≤1/(q:ℝ) := hβ.trans (div_le_div_of_nonneg_left zero_le_one hqR (le_mul_of_one_le_right hqR.le hs))
  by_cases h : q=1
  · subst q
    have z : a=0 := by omega
    subst a;simpa [rationalWindow,samplePoint,abs_nonneg, abs_abs] using
      (show |β|≤1 ∧ |β|≤1/((1:ℝ)*Real.sqrt n) from ⟨by simpa using off,by simpa using hβ⟩)
  · have ha0 : 1≤a := by
      by_contra! hh
      have z : a=0 := by omega
      subst a;simp at hac;contradiction
    have a1 : (1:ℝ)≤a := by exact_mod_cast ha0
    have aq : (a:ℝ)+1≤q := by exact_mod_cast hal
    have bound := abs_le.mp off
    simp only [rationalWindow,samplePoint,ite_eq_right h]
    constructor
    · constructor
      · have x := (div_le_div_iff_of_pos_right hqR).mpr a1
        linarith
      · have x := (div_le_one hqR).mpr aq
        rw [add_div] at x;linarith
    · simpa only [add_sub_cancel_left] using hβ
end GoldbachPrimeBias
end
end

section
open Finset Complex DirichletCharacter GoldbachMovingWindows
open scoped Classical
noncomputable section
namespace GoldbachPrimeBias

/-- The natural q/φ(q) normalization of primitive character energy. -/
def sector (q : ℕ) (w : ℕ→ℝ) (I : ℕ×ℕ) (β : ℝ) : ℝ := if h : q=0 then 0 else
  let _ : NeZero q := ⟨h⟩
  (q:ℝ)/q.totient * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter IsPrimitive,
    ‖characterSum (oscillating w β) (Ico I.1 I.2) χ⁻¹‖^2

theorem sector_le {q : ℕ} (hq : 0<q) (w : ℕ→ℝ) (I : ℕ×ℕ) (β : ℝ) :
    sector q w I β ≤ ∑ a ∈ reduced q,‖intervalSum I w (samplePoint q a β)‖^2 := by
  let : NeZero q := ⟨hq.ne'⟩
  have e := primitive_energy (q:=q) (oscillating w β) (Ico I.1 I.2)
  simp_rw [sample_norm] at e
  rw [units_to_reduced (q:=q) (fun a => ‖intervalSum I w (samplePoint q a β)‖^2)] at e
  have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  simp only [sector,dite_eq_right hq.ne']
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hφ).mpr
  rwa [mul_comm _ (q.totient:ℝ)]

private def pairs (q : ℕ) := (reduced q).image (fun a => (q,a))

/-- The disjoint intervals and their additive offsets may be selected afresh
for each denominator. Within an interval the offset is shared by all characters. -/
theorem primitive_variation_sieve {n : ℕ} (hn : 0<n) (w : ℕ→ℝ) (D : Finset ℕ)
    (J : ℕ → Finset (ℕ×ℕ)) (β : ℕ → (ℕ×ℕ) → ℝ)
    (good : ∀ q∈D, 0<q ∧ (q:ℝ)≤Real.sqrt n ∧ intervalFamily n (J q) ∧
      ∀ I ∈ J q, |β q I|≤1/((q:ℝ)*Real.sqrt n)) :
    (∑ q ∈ D,∑ I ∈ J q,sector q w I (β q I)) ≤
      4*((Nat.log 2 (n+1)+1:ℕ):ℝ)^2*(7*(1+4*Real.pi)*(n:ℝ))*(∑ k ∈ range (n+1),(w k)^2) := by
  let A := D.biUnion pairs
  let t := fun (p : ℕ×ℕ) I => samplePoint p.1 p.2 (β p.1 I)
  let F := fun (p : ℕ×ℕ) => ∑ I ∈ J p.1,‖intervalSum I w (t p I)‖^2
  have mapgood (p : ℕ×ℕ) (hp : p∈A) :
      windowPair n p ∧ intervalFamily n (J p.1) ∧ ∀ I∈J p.1, rationalWindow n p (t p I) := by
    obtain ⟨q,hq,hp⟩ := mem_biUnion.mp hp
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hp
    obtain ⟨hq0,hs,hf,ho⟩ := good q hq
    obtain ⟨haq,hc⟩ := mem_filter.mp ha
    exact ⟨⟨hq0,hs,(mem_range.mp haq).le,hc⟩,hf,fun I hi => sample_window hn hq0 ha (ho I hi)⟩
  have disj : (↑D : Set ℕ).Pairwise (Function.onFun Disjoint pairs) := by
    intro p _ q _ hne
    apply disjoint_left.mpr
    intro x hp hq
    obtain ⟨a,_,rfl⟩ := mem_image.mp hp
    obtain ⟨b,_,he⟩ := mem_image.mp hq
    exact hne (congrArg Prod.fst he).symm
  calc
    _ ≤ ∑ q ∈ D,∑ I ∈ J q,∑ a ∈ reduced q,‖intervalSum I w (samplePoint q a (β q I))‖^2 :=
      sum_le_sum fun q hq => sum_le_sum fun I _ => sector_le (good q hq).1 w I (β q I)
    _ = ∑ p ∈ A,F p := by
      rw [show A=D.biUnion pairs from rfl,sum_biUnion disj]
      apply sum_congr rfl
      intro q _
      rw [Finset.sum_comm,pairs,sum_image (fun a _ b _ he => congrArg Prod.snd he)]
    _ ≤ _ := variation_sieve hn (Nat.lt_pow_succ_log_self (by decide : 1<2) (n+1)) w A (fun p => J p.1) t mapgood
end GoldbachPrimeBias
end
end

section
open Set Filter Real
noncomputable section
namespace GoldbachPrimeBias
noncomputable def cutoff (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊

noncomputable def width (n : ℕ) : ℕ := 256 * cutoff n * (Nat.log 2 (n+2)) ^ 2

noncomputable def wideArcs (n : ℕ) : Set ℝ := {t | ∃ q a : ℕ,
  1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ a.Coprime q ∧
  |t - (a : ℝ) / q| ≤ (width n : ℝ) / ((q : ℝ) * n)}

def logScale (x : ℝ) := 1+Real.log (2*x)
theorem logScale_one {x : ℝ} (hx : 1 ≤ x) : 1 ≤ logScale x := by
  dsimp [logScale]
  linarith only [Real.log_nonneg (by linarith : 1 ≤ 2*x)]
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




private theorem integer_spacing {a b q r : ℕ} (hne : a*r ≠ b*q) :
    1 ≤ |(a:ℝ)*r-(b:ℝ)*q| := by
  rcases lt_or_gt_of_ne hne with h|h
  · have hh : (a:ℝ)*r+1 ≤ (b:ℝ)*q := by exact_mod_cast h
    exact (le_abs.mpr (Or.inr (by linarith)))
  · have hh : (b:ℝ)*q+1 ≤ (a:ℝ)*r := by exact_mod_cast h
    exact (le_abs.mpr (Or.inl (by linarith)))

/-- Once the wide arcs are short compared with square-root Dirichlet windows,
membership depends only on the denominator and distance to its own centre. -/
theorem dirichlet_wide_iff {n a q : ℕ} [NeZero q] (hn : 1 ≤ n) (ha : a≤q) (hc : a.Coprime q)
    (hcut : 2*(cutoff n:ℝ) < Real.sqrt n) (hw : 2*(width n:ℝ) < Real.sqrt n)
    (hq : (q:ℝ)≤Real.sqrt n) {t : ℝ} (ht : |t-(a:ℝ)/q| ≤ 1/((q:ℝ)*Real.sqrt n)) :
    t ∈ wideArcs n ↔ q ≤ cutoff n ∧ |t-(a:ℝ)/q| ≤ (width n:ℝ)/(q*n) := by
  have hN : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hQ : (0:ℝ)<q := by exact_mod_cast NeZero.pos q
  have hS := Real.sqrt_pos.mpr hN
  constructor
  · rintro ⟨r,b,hr,hcutr,hb,hcr,hd⟩
    have hR : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
    have hprod : (0:ℝ)<(q:ℝ)*r := by positivity
    have hdet : (a:ℝ)*r-(b:ℝ)*q = ((a:ℝ)/q-t+(t-(b:ℝ)/r))*(q*r) := by field_simp;ring
    have htri : |(a:ℝ)*r-(b:ℝ)*q| ≤ (1/((q:ℝ)*Real.sqrt n)+(width n:ℝ)/(r*n))*(q*r) := by
      rw [hdet,abs_mul,abs_of_pos hprod]
      apply mul_le_mul_of_nonneg_right _ hprod.le
      exact (abs_add_le ..).trans (add_le_add (by simpa only [abs_sub_comm (a/q:ℝ) t] using ht) hd)
    have hsmall : (1/((q:ℝ)*Real.sqrt n)+(width n:ℝ)/(r*n))*(q*r) < 1 := by
      have eq : (1/((q:ℝ)*Real.sqrt n)+(width n:ℝ)/(r*n))*(q*r) =
          (r:ℝ)/Real.sqrt n + (width n:ℝ)*(q:ℝ)/n := by field_simp
      rw [eq]
      have hrr : (r:ℝ) ≤ cutoff n := by exact_mod_cast hcutr
      have hfirst : (r:ℝ)/Real.sqrt n < 1/2 := by apply (div_lt_iff₀ hS).mpr;linarith
      have hww := mul_lt_mul_of_pos_right hw hS
      have hqq := mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg (width n) : (0:ℝ) ≤ _)
      have hsecond : (width n:ℝ)*(q:ℝ)/n < 1/2 := by
        apply (div_lt_iff₀ hN).mpr
        nlinarith only [hww,hqq,Real.sq_sqrt hN.le]
      linarith
    have same : a*r=b*q := by
      by_contra hh
      exact (not_lt_of_ge (integer_spacing hh)) (htri.trans_lt hsmall)
    have hqr : q ∣ r := hc.symm.dvd_mul_left.mp (same ▸ dvd_mul_left q b)
    have hrq : r ∣ q := hcr.symm.dvd_mul_left.mp (same.symm ▸ dvd_mul_left r a)
    have hr' : r=q := Nat.dvd_antisymm hrq hqr
    subst r
    have hab := Nat.eq_of_mul_eq_mul_right (NeZero.pos q) same
    subst b
    exact ⟨hcutr,hd⟩
  · rintro ⟨h1,h2⟩
    exact ⟨q,a,NeZero.pos q,h1,ha,hc,h2⟩


/-- The separation hypotheses hold uniformly beyond a fixed threshold. -/
theorem eventually_short_wide : ∀ᶠ n : ℕ in atTop,
    2*(cutoff n:ℝ)<Real.sqrt n ∧ 2*(width n:ℝ)<Real.sqrt n := by
  obtain ⟨D,hD,hlog⟩ := quartic_log_scale (by norm_num : 0<(1/12:ℝ))
  let C := 256*(1/Real.log 2)^2*D
  have hlim : Tendsto (fun n : ℕ => (n:ℝ)^(1/12:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0<(1/12:ℝ))).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_gt_atTop (2*max 1 C),eventually_ge_atTop 2] with n hpow hn
  have hnR : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hn0 := zero_lt_one.trans_le hnR
  have hg : (0:ℝ)<Real.log 2 := Real.log_pos (by norm_num)
  have hcut : (cutoff n:ℝ) ≤ (n:ℝ)^(1/3:ℝ) := Nat.floor_le (Real.rpow_nonneg hn0.le _)
  have hL := logScale_one hnR
  have hx := Real.natLog_le_logb (n+2) 2
  have hlogle : (Nat.log 2 (n+2):ℝ) ≤ (1/Real.log 2)*logScale n := by
    rw [Real.logb] at hx
    push_cast at hx
    have hna : (n:ℝ)+2≤2*n := by exact_mod_cast (show n+2≤2*n by omega)
    have hl := Real.log_le_log (by positivity : (0:ℝ)<n+2) hna
    dsimp [logScale]
    calc
      _ ≤ Real.log ((n:ℝ)+2) / Real.log 2 := hx
      _ ≤ (1+Real.log (2*n))/Real.log 2 := div_le_div_of_nonneg_right (by linarith) hg.le
      _ = _ := by ring
  have hsq : (Nat.log 2 (n+2):ℝ)^2 ≤ (1/Real.log 2)^2*(D*(n:ℝ)^(1/12:ℝ)) := by
    calc
      _ ≤ ((1/Real.log 2)*logScale n)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hlogle 2
      _ = (1/Real.log 2)^2*logScale n^2 := mul_pow ..
      _ ≤ _ := mul_le_mul_of_nonneg_left ((pow_le_pow_right₀ hL (by omega : 2≤4)).trans (hlog _ hnR)) (sq_nonneg _)
  have hw : (width n:ℝ) ≤ C*(n:ℝ)^(5/12:ℝ) := by
    unfold width
    push_cast
    calc
      _ ≤ 256*((n:ℝ)^(1/3:ℝ))*((1/Real.log 2)^2*(D*(n:ℝ)^(1/12:ℝ))) := by gcongr
      _ = _ := by
        have hh : (n:ℝ)^(1/3:ℝ)*(n:ℝ)^(1/12:ℝ) = (n:ℝ)^(5/12:ℝ) := by rw [←Real.rpow_add hn0];norm_num
        dsimp [C]
        rw [←hh]
        ring
  have hc : (cutoff n:ℝ)≤(n:ℝ)^(5/12:ℝ) := hcut.trans (Real.rpow_le_rpow_of_exponent_le hnR (by norm_num))
  have strict := mul_lt_mul_of_pos_right hpow (Real.rpow_pos_of_pos hn0 (5/12:ℝ))
  rw [←Real.rpow_add hn0,show (1/12:ℝ)+5/12 = 1/2 by norm_num,←Real.sqrt_eq_rpow] at strict
  have h1 := mul_le_mul_of_nonneg_right (le_max_left 1 C) (Real.rpow_nonneg hn0.le (5/12:ℝ))
  have h2 := mul_le_mul_of_nonneg_right (le_max_right 1 C) (Real.rpow_nonneg hn0.le (5/12:ℝ))
  constructor <;> nlinarith only [strict,h1,h2,hc,hw]

end GoldbachPrimeBias
end
end

section
open Finset Set Filter GoldbachMovingWindows
open scoped Classical
noncomputable section
namespace GoldbachPrimeBias

private theorem card_reduced {q : ℕ} [NeZero q] : ((reduced q).card:ℝ)=q.totient := by
  simpa using (units_to_reduced (q:=q) (fun _ => (1:ℝ))).symm

/-- The finite inverse bound provides a reduced numerator witnessing a large
primitive character energy for any common additive offset. -/
theorem bias_witness {q : ℕ} (hq : 0<q) (w : ℕ→ℝ) (I : ℕ×ℕ) (β : ℝ) :
    ∃ a∈reduced q, sector q w I β ≤ (q.totient:ℝ)*‖intervalSum I w (samplePoint q a β)‖^2 := by
  let : NeZero q := ⟨hq.ne'⟩
  have ne : (reduced q).Nonempty := by
    apply card_pos.mp
    have e := card_reduced (q:=q)
    have hp : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
    exact_mod_cast (e.symm ▸ hp : 0<((reduced q).card:ℝ))
  obtain ⟨a,ha,hmax⟩ := (reduced q).exists_max_image (fun a => ‖intervalSum I w (samplePoint q a β)‖^2) ne
  refine ⟨a,ha,(sector_le hq w I β).trans ?_⟩
  exact (sum_le_sum hmax).trans_eq (by simp only [sum_const,nsmul_eq_mul,card_reduced])

/-- An unconditional bound for the collective prime character variation
outside the same sparse set of denominators. -/
theorem prime_character_variation {n q : ℕ} (hn : 0<n) (hq : 0<q)
    (η : ℝ) (J : Finset (ℕ×ℕ)) (β : (ℕ×ℕ)→ℝ)
    (off : ∀ I∈J, |β I|≤1/((q:ℝ)*Real.sqrt n))
    (uniform : ∀ a∈reduced q, ∀ t : (ℕ×ℕ)→ℝ, (∀ I∈J,rationalWindow n (q,a) (t I)) →
      (∑ I∈J,‖intervalSum I primeLog (t I)‖^2) < ((n:ℝ)^(3/4+η))^2) :
    (∑ I∈J,sector q primeLog I (β I)) < (q.totient:ℝ)*((n:ℝ)^(3/4+η))^2 := by
  let : NeZero q := ⟨hq.ne'⟩
  have ne : (reduced q).Nonempty := by
    obtain ⟨a,ha,_⟩ := bias_witness hq primeLog (0,0) 0
    exact ⟨a,ha⟩
  calc
    _ ≤ ∑ I ∈ J,∑ a∈reduced q,‖intervalSum I primeLog (samplePoint q a (β I))‖^2 :=
      sum_le_sum fun I _ => sector_le hq primeLog I (β I)
    _ = ∑ a ∈ reduced q,∑ I∈J, ‖intervalSum I primeLog (samplePoint q a (β I))‖^2 := Finset.sum_comm
    _ < ∑ _a ∈ reduced q,((n:ℝ)^(3/4+η))^2 := by
      apply sum_lt_sum_of_nonempty ne
      intro a ha
      exact uniform a ha _ (fun I hi => sample_window hn hq ha (off I hi))
    _ = _ := by simp only [sum_const,nsmul_eq_mul,card_reduced]

/-- The frozen pointwise three-quarters conjecture bounds the combined
primitive-character energy for every deep denominator, including the bad ones
left over by the variational estimate. -/
theorem collective_necessary
    (target : ∀ η : ℝ, 0<η → ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ t ∈ Set.Icc (0:ℝ) 1, t∉wideArcs n →
      ‖intervalSum (0,n+1) primeLog t‖ ≤ (n:ℝ)^(3/4+η)) :
    ∀ η : ℝ, 0<η → ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ q : ℕ, cutoff n<q → (q:ℝ)≤Real.sqrt n →
      ∀ β : ℝ, |β|≤1/((q:ℝ)*Real.sqrt n) →
        sector q primeLog (0,n+1) β ≤ (q.totient:ℝ)*((n:ℝ)^(3/4+η))^2 := by
  intro η hη
  obtain ⟨M,hm⟩ := target η hη
  obtain ⟨P,hp⟩ := eventually_atTop.mp eventually_short_wide
  refine ⟨max 1 (max M P),?_⟩
  intro n hn q hcut hq β hβ
  have hq0 : 0<q := by omega
  let : NeZero q := ⟨hq0.ne'⟩
  obtain ⟨a,ha,bnd⟩ := bias_witness hq0 primeLog (0,n+1) β
  have win := sample_window (by omega : 1≤n) hq0 ha hβ
  obtain ⟨haq,hc⟩ := mem_filter.mp ha
  have iff := dirichlet_wide_iff (q:=q) (a:=a) (by omega : 1≤n) (Finset.mem_range.mp haq).le hc
    (hp n (by omega)).1 (hp n (by omega)).2 hq win.2
  have deep := fun h => hcut.not_ge (iff.mp h).1
  exact bnd.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hm n (by omega) _ win.1 deep) 2) (Nat.cast_nonneg _))
end GoldbachPrimeBias
end
end

section
open Finset Real
noncomputable section
/-!
# Bounds for the reciprocal totient density

The finite-product argument and logarithmic bound below are the proof of the
private helpers `harm_prod` and `ratio_bound` from the accepted Goldbach Research
PR #1810 (TH-0073), https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/1810/files.
The logarithmic estimate is exposed here for reuse independently of that PR's
energy theorem. The power bounds are consequences for the deep minor arcs.
-/

namespace GoldbachPrimeBias

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


end GoldbachPrimeBias
end
end

section
open Finset Filter GoldbachMovingWindows
open scoped Classical
noncomputable section
namespace GoldbachPrimeBias

def exceptionalBias (n : ℕ) (η : ℝ) (q : ℕ) : Prop :=
  ∃ (J : Finset (ℕ×ℕ)) (β : (ℕ×ℕ)→ℝ), intervalFamily n J ∧
    (∀ I∈J, |β I|≤1/((q:ℝ)*Real.sqrt n)) ∧
    (q.totient:ℝ)*((n:ℝ)^(3/4+η))^2 ≤ ∑ I∈J,sector q primeLog I (β I)

/-- Every bad denominator spends its full totient from the common large-sieve
budget. The witnesses are allowed to use different intervals and offsets. -/
theorem bad_totient_budget {n : ℕ} (hn : 0<n) (η : ℝ) (D : Finset ℕ)
    (good : ∀ q∈D, 0<q ∧ (q:ℝ)≤Real.sqrt n ∧ exceptionalBias n η q) :
    (∑ q∈D,(q.totient:ℝ))*((n:ℝ)^(3/4+η))^2 ≤
      4*(variationDepth n:ℝ)^2*windowConstant*(n:ℝ)^2*Real.log n := by
  let J (q : ℕ) := if h : q∈D then (good q h).2.2.choose else ∅
  let β (q : ℕ) := if h : q∈D then (good q h).2.2.choose_spec.choose else fun _ : ℕ×ℕ => (0:ℝ)
  have spec (q : ℕ) (hq : q∈D) : intervalFamily n (J q) ∧
      (∀ I∈J q, |β q I|≤1/((q:ℝ)*Real.sqrt n)) ∧
      (q.totient:ℝ)*((n:ℝ)^(3/4+η))^2 ≤ ∑ I∈J q,sector q primeLog I (β q I) := by
    simpa only [J,β,dite_eq_left hq] using (good q hq).2.2.choose_spec.choose_spec
  have s := primitive_variation_sieve hn primeLog D J β (fun q hq =>
    ⟨(good q hq).1,(good q hq).2.1,(spec q hq).1,(spec q hq).2.1⟩)
  rw [Finset.sum_mul]
  apply ((sum_le_sum (fun q hq => (spec q hq).2.2)).trans s).trans
  exact (mul_le_mul_of_nonneg_left (primeLog_energy n) (by positivity)).trans_eq (by dsimp [windowConstant,variationDepth];ring)

private theorem log_depth_bound {n : ℕ} (hn : 2≤n) :
    (variationDepth n:ℝ)≤(1+1/Real.log 2)*logScale n := by
  have hnR : 1≤(n:ℝ) := by exact_mod_cast (show 1≤n by omega)
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have h := Real.natLog_le_logb (n+1) 2
  rw [Real.logb] at h
  push_cast at h
  have hln := Real.log_le_log (by positivity : (0:ℝ)<(n:ℝ)+1) (by linarith : (n:ℝ)+1≤2*n)
  have hL := logScale_one hnR
  have hh : Real.log ((n:ℝ)+1)≤logScale n := by dsimp [logScale];linarith
  have h' := h.trans (div_le_div_of_nonneg_right hh h2.le)
  unfold variationDepth
  push_cast
  calc
    _ ≤ logScale n/Real.log 2+logScale n := add_le_add h' hL
    _ = _ := by ring

/-- At height n^θ or above, the exponent for bad denominators drops by θ.
The common exceptional set covers every admissible family of disjoint intervals. -/
theorem sparse_high_bias (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ η θ : ℝ, ∀ D : Finset ℕ,
    (∀ q∈D, 0<q ∧ (q:ℝ)≤Real.sqrt n ∧ (n:ℝ)^θ≤q ∧ exceptionalBias n η q) →
      (D.card:ℝ)≤(n:ℝ)^(1/2-θ-2*η+ε) := by
  obtain ⟨K,hK,logs⟩ := quartic_log_scale (half_pos hε)
  let c := 1+1/Real.log 2
  let C := 16*c^2*windowConstant*K
  have hc : 0≤c := by dsimp [c];have := Real.log_pos (by norm_num : (1:ℝ)<2);positivity
  have hw : 0≤windowConstant := by dsimp [windowConstant];positivity
  have lim : Tendsto (fun n : ℕ => (n:ℝ)^(ε/2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hε)).comp tendsto_natCast_atTop_atTop
  obtain ⟨M,hM⟩ := eventually_atTop.mp (lim.eventually_ge_atTop C)
  refine ⟨max M 2,?_⟩
  intro n hn η θ D good
  let L := logScale n
  let T := ((n:ℝ)^(3/4+η))^2
  have hnR : 1≤(n:ℝ) := by exact_mod_cast (show 1≤n by omega)
  have hn0 := zero_lt_one.trans_le hnR
  have hL : 1≤L := logScale_one hnR
  have hL0 := zero_le_one.trans hL
  have hT : 0<T := sq_pos_of_pos (Real.rpow_pos_of_pos hn0 _)
  have qn (q : ℕ) (hq : q∈D) := (good q hq).2.1.trans (Real.sqrt_le_self_iff.mpr (Or.inr hnR))
  have per (q : ℕ) (hq : q∈D) : (n:ℝ)^θ ≤ (4*L)*(q.totient:ℝ) := by
    have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (good q hq).1
    have upper : Real.log ((q+2:ℕ):ℝ)≤L := by
      have hn2 : (2:ℝ)≤n := by exact_mod_cast (show 2≤n by omega)
      have le := Real.log_le_log (by positivity : (0:ℝ)<((q+2:ℕ):ℝ)) (show ((q+2:ℕ):ℝ)≤2*n by push_cast;linarith only [qn q hq,hn2])
      dsimp [L,logScale];linarith
    exact (good q hq).2.2.1.trans ((div_le_iff₀ hφ).mp ((totient_ratio_le_four_log q (good q hq).1).trans
      (mul_le_mul_of_nonneg_left upper (by norm_num))))
  have charge := sum_le_sum per
  rw [sum_const,nsmul_eq_mul,←Finset.mul_sum] at charge
  have bill := bad_totient_budget (by omega : 0<n) η D (fun q hq => ⟨(good q hq).1,(good q hq).2.1,(good q hq).2.2.2⟩)
  have hlog : Real.log n≤L := by
    dsimp [L,logScale]
    linarith only [Real.log_le_log hn0 (by linarith : (n:ℝ)≤2*n)]
  have hx := log_depth_bound (by omega : 2≤n)
  have hx' : ((variationDepth n):ℝ)^2 ≤ (c*L)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hx 2
  have hconst : 16*c^2*windowConstant*L^4 ≤ (n:ℝ)^ε := by
    calc
      _ ≤ (16*c^2*windowConstant)*(K*(n:ℝ)^(ε/2)) := mul_le_mul_of_nonneg_left (logs _ hnR) (by positivity)
      _ = C*(n:ℝ)^(ε/2) := by dsimp [C];ring
      _ ≤ (n:ℝ)^(ε/2)*(n:ℝ)^(ε/2) := mul_le_mul_of_nonneg_right (hM n (by omega)) (Real.rpow_nonneg hn0.le _)
      _ = _ := by rw [←Real.rpow_add hn0];congr 1;ring
  apply (mul_le_mul_iff_left₀ (mul_pos (Real.rpow_pos_of_pos hn0 θ) hT)).mp
  calc
    _ = ((D.card:ℝ)*(n:ℝ)^θ)*T := by ring
    _ ≤ ((4*L)*(∑ q∈D,(q.totient:ℝ)))*T := mul_le_mul_of_nonneg_right charge hT.le
    _ = (4*L)*((∑ q∈D,(q.totient:ℝ))*T) := by ring
    _ ≤ (4*L)*(4*(variationDepth n:ℝ)^2*windowConstant*(n:ℝ)^2*Real.log n) := mul_le_mul_of_nonneg_left bill (by positivity)
    _ ≤ (4*L)*(4*(c*L)^2*windowConstant*(n:ℝ)^2*L) := by
      have := Real.log_nonneg hnR
      gcongr
    _ = (16*c^2*windowConstant*L^4)*(n:ℝ)^2 := by ring
    _ ≤ (n:ℝ)^ε*(n:ℝ)^2 := mul_le_mul_of_nonneg_right hconst (sq_nonneg _)
    _ = (n:ℝ)^(1/2-θ-2*η+ε)*((n:ℝ)^θ*T) := by
      dsimp only [T]
      rw [←Real.rpow_natCast (n:ℝ) 2,←Real.rpow_mul_natCast hn0.le,←Real.rpow_add hn0,
        ←Real.rpow_add hn0,←Real.rpow_add hn0]
      congr 1;push_cast;ring
end GoldbachPrimeBias
end
end

section
open Finset Filter GoldbachMovingWindows
open scoped Classical
noncomputable section
namespace GoldbachPrimeBias

/-- Uniformly in the exponent defining the denominator band, extract the set
of bad moduli. The finite estimate already allows different witnesses for them. -/
theorem uniform_high_bias {ε : ℝ} (hε : 0<ε) :
    ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ η θ : ℝ, ∃ bad : Finset ℕ,
      (bad.card:ℝ)≤(n:ℝ)^(1/2-θ-2*η+ε) ∧
      ∀ q : ℕ, 0<q → (q:ℝ)≤Real.sqrt n → (n:ℝ)^θ≤q → q∉bad →
      ∀ J : Finset (ℕ×ℕ), intervalFamily n J → ∀ β : (ℕ×ℕ)→ℝ, (∀ I∈J, |β I|≤1/((q:ℝ)*Real.sqrt n)) →
        (∑ I∈J,sector q primeLog I (β I)) < (q.totient:ℝ)*((n:ℝ)^(3/4+η))^2 := by
  obtain ⟨M,hM⟩ := sparse_high_bias ε hε
  refine ⟨max M 2,?_⟩
  intro n hn η θ
  let bad : Finset ℕ := (range (n+1)).filter (fun (q : ℕ) => 0<q ∧ (q:ℝ)≤Real.sqrt n ∧ (n:ℝ)^θ≤q ∧ exceptionalBias n η q)
  refine ⟨bad,hM n (by omega) η θ bad (fun q hq => (mem_filter.mp hq).2),?_⟩
  intro q hq hs ht hg J hJ β off
  by_contra! hlarge
  have hnR : 1≤(n:ℝ) := by exact_mod_cast (show 1≤n by omega)
  have qn : q≤n := by exact_mod_cast hs.trans (Real.sqrt_le_self_iff.mpr (Or.inr hnR))
  exact hg (mem_filter.mpr ⟨mem_range.mpr (by omega),hq,hs,ht,⟨J,β,hJ,off,hlarge⟩⟩)

/-- At the square-root threshold there are no exceptional denominators
for the collective character bound. More generally the pointwise-in-q
exponent over q≥n^θ is 1-θ/2, up to arbitrary positive slack. -/
theorem all_high_bias {δ : ℝ} (hδ : 0<δ) :
    ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ θ : ℝ, ∀ q : ℕ, 0<q → (q:ℝ)≤Real.sqrt n → (n:ℝ)^θ≤q →
      ∀ J : Finset (ℕ×ℕ), intervalFamily n J → ∀ β : (ℕ×ℕ)→ℝ, (∀ I∈J, |β I|≤1/((q:ℝ)*Real.sqrt n)) →
        (∑ I∈J,sector q primeLog I (β I)) < (q.totient:ℝ)*((n:ℝ)^(1-θ/2+δ))^2 := by
  obtain ⟨M,hM⟩ := uniform_high_bias hδ
  refine ⟨max M 2,?_⟩
  intro n hn θ q hq hs ht J hJ β off
  let η := 1/4-θ/2+δ
  obtain ⟨bad,hbad,good⟩ := hM n (by omega) η θ
  have hnR : 1<(n:ℝ) := by exact_mod_cast (show 1<n by omega)
  have expn : 1/2-θ-2*η+δ = -δ := by dsimp [η];ring
  rw [expn] at hbad
  have lt : (n:ℝ)^(-δ)<1 := Real.rpow_lt_one_of_one_lt_of_neg hnR (neg_neg_of_pos hδ)
  have hz : (bad.card:ℝ)<1 := hbad.trans_lt lt
  have hzN : bad.card<1 := by exact_mod_cast hz
  have z : bad.card=0 := by omega
  have hh := good q hq hs ht (by rw [card_eq_zero.mp z];simp) J hJ β off
  rwa [show 3/4+η=1-θ/2+δ by dsimp [η];ring] at hh
end GoldbachPrimeBias
end
end

open GoldbachMovingWindows GoldbachPrimeBias Finset
theorem PEqualNP.Outside.L_goldbach_variational_prime_dirichlet_windows :
let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0
let S := fun (I : ℕ×ℕ) (u : ℕ→ℝ) (t : ℝ) => ∑ k ∈ Finset.Ico I.1 I.2,(u k:ℂ)*E ((k:ℝ)*t)
let pair := fun (n : ℕ) (p : ℕ×ℕ) => 0<p.1 ∧ (p.1:ℝ)≤Real.sqrt n ∧ p.2≤p.1 ∧ p.2.Coprime p.1
let window := fun (n : ℕ) (p : ℕ×ℕ) (t : ℝ) => t ∈ Set.Icc (0:ℝ) 1 ∧ |t-(p.2:ℝ)/p.1| ≤ 1/((p.1:ℝ)*Real.sqrt n)
let family := fun (n : ℕ) (J : Finset (ℕ×ℕ)) =>
  (∀ I ∈ J,I.1 < I.2 ∧ I.2≤n+1) ∧ ∀ I ∈ J, ∀ K ∈ J, I≠K → I.2≤K.1 ∨ K.2≤I.1
let B := fun (q : ℕ) (u : ℕ→ℝ) (I : ℕ×ℕ) (β : ℝ) => if h : q=0 then (0:ℝ) else
  let _ : NeZero q := ⟨h⟩
  (q:ℝ)/q.totient * ∑ χ ∈ @Finset.filter (DirichletCharacter ℂ q) DirichletCharacter.IsPrimitive (fun _ => Classical.propDecidable _) Finset.univ,
    ‖∑ k ∈ Finset.Ico I.1 I.2, (u k:ℂ)*E ((k:ℝ)*β)*χ⁻¹ (k:ZMod q)‖^2
let cut := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊
let W := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤cut n ∧ a≤q ∧ a.Coprime q ∧
  |t-(a:ℝ)/q|≤((256*cut n*(Nat.log 2 (n+2))^2:ℕ):ℝ)/((q:ℝ)*n)}
(∀ (n : ℕ), 0<n → ∀ (u : ℕ→ℝ) (A : Finset (ℕ×ℕ)) (J : ℕ×ℕ → Finset (ℕ×ℕ)) (t : (ℕ×ℕ) → (ℕ×ℕ) → ℝ),
  (∀ p∈A, pair n p ∧ family n (J p) ∧ ∀ I ∈ J p, window n p (t p I)) →
  (∑ p ∈ A,∑ I ∈ J p,‖S I u (t p I)‖^2) ≤ 4*((Nat.log 2 (n+1)+1:ℕ):ℝ)^2*
    (7*(1+4*Real.pi)*(n:ℝ))*(∑ k ∈ Finset.range (n+1),(u k)^2)) ∧
(∀ (n : ℕ), 0<n → ∀ (u : ℕ→ℝ) (D : Finset ℕ) (J : ℕ→Finset (ℕ×ℕ)) (β : ℕ→(ℕ×ℕ)→ℝ),
  (∀ q∈D, 0<q ∧ (q:ℝ)≤Real.sqrt n ∧ family n (J q) ∧ ∀ I∈J q, |β q I|≤1/((q:ℝ)*Real.sqrt n)) →
  (∑ q∈D,∑ I∈J q,B q u I (β q I)) ≤ 4*((Nat.log 2 (n+1)+1:ℕ):ℝ)^2*
    (7*(1+4*Real.pi)*(n:ℝ))*(∑ k ∈ Finset.range (n+1),(u k)^2)) ∧
(∀ η : ℝ, 0<η → ∃ N : ℕ, ∀ n : ℕ, N≤n → ∃ bad : Finset ℕ, (bad.card:ℝ)≤(n:ℝ)^(1/2-η) ∧
  ∀ (q : ℕ), 0<q → (q:ℝ)≤Real.sqrt n → q∉bad →
  (∀ (a : ℕ), a≤q → a.Coprime q → ∀ (J : Finset (ℕ×ℕ)), family n J → ∀ (t : ℕ×ℕ → ℝ),
    (∀ I ∈ J, window n (q,a) (t I)) → (∑ I ∈ J, ‖S I w (t I)‖^2) < ((n:ℝ)^(3/4+η))^2) ∧
  (∀ (J : Finset (ℕ×ℕ)), family n J → ∀ (β : (ℕ×ℕ)→ℝ), (∀ I∈J, |β I|≤1/((q:ℝ)*Real.sqrt n)) →
    (∑ I ∈ J, B q w I (β I)) < (q.totient:ℝ)*((n:ℝ)^(3/4+η))^2)) ∧
((∀ η : ℝ, 0<η → ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ t∈Set.Icc (0:ℝ) 1, t∉W n →
   ‖∑ k ∈ Finset.range (n+1),(w k:ℂ)*E ((k:ℝ)*t)‖≤(n:ℝ)^(3/4+η)) →
 ∀ η : ℝ, 0<η → ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ q : ℕ, cut n<q → (q:ℝ)≤Real.sqrt n →
   ∀ β : ℝ, |β|≤1/((q:ℝ)*Real.sqrt n) → B q w (0,n+1) β≤(q.totient:ℝ)*((n:ℝ)^(3/4+η))^2) ∧
(∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ η θ : ℝ, ∃ bad : Finset ℕ,
  (bad.card:ℝ)≤(n:ℝ)^(1/2-θ-2*η+ε) ∧ ∀ q : ℕ, 0<q → (q:ℝ)≤Real.sqrt n → (n:ℝ)^θ≤q → q∉bad →
  ∀ J : Finset (ℕ×ℕ), family n J → ∀ β : (ℕ×ℕ)→ℝ, (∀ I∈J, |β I|≤1/((q:ℝ)*Real.sqrt n)) →
    (∑ I∈J,B q w I (β I)) < (q.totient:ℝ)*((n:ℝ)^(3/4+η))^2) ∧
(∀ δ : ℝ, 0<δ → ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ θ : ℝ, ∀ q : ℕ, 0<q → (q:ℝ)≤Real.sqrt n → (n:ℝ)^θ≤q →
  ∀ J : Finset (ℕ×ℕ), family n J → ∀ β : (ℕ×ℕ)→ℝ, (∀ I∈J, |β I|≤1/((q:ℝ)*Real.sqrt n)) →
    (∑ I∈J,B q w I (β I)) < (q.totient:ℝ)*((n:ℝ)^(1-θ/2+δ))^2) := by
  classical
  intro E w S pair window family B cut W
  have eqS (I : ℕ×ℕ) (u : ℕ→ℝ) (t : ℝ) : S I u t = intervalSum I u t := by
    dsimp only [S,E,intervalSum]
    simp_rw [wave_eq]
  have eqB (q : ℕ) (u : ℕ→ℝ) (I : ℕ×ℕ) (β : ℝ) : B q u I β=sector q u I β := by
    dsimp only [B,sector]
    split_ifs with h
    · rfl
    · simp only [characterSum,oscillating,wave_eq,E]
  have ew : w=GoldbachMovingWindows.primeLog := by
    funext k;by_cases h : k.Prime <;> simp [w,GoldbachMovingWindows.primeLog,h]
  simp_rw [eqS,eqB,ew]
  constructor
  · intro n hn u A J t h
    exact variation_sieve hn (Nat.lt_pow_succ_log_self (by decide : 1<2) (n+1)) u A J t h
  constructor
  · intro n hn u D J β h
    exact primitive_variation_sieve hn u D J β h
  constructor
  · intro η hη
    obtain ⟨M,hm⟩ := additive_window_variation.2 η hη
    refine ⟨max M 1,?_⟩
    intro n hn
    obtain ⟨bad,count,unif⟩ := hm n (by omega)
    refine ⟨bad,count,?_⟩
    intro q hq hqs good
    have h (a : ℕ) (ha : a≤q) (hc : a.Coprime q) (J : Finset (ℕ×ℕ)) (hf : intervalFamily n J) (t : (ℕ×ℕ)→ℝ)
        (ht : ∀ I∈J, rationalWindow n (q,a) (t I)) :
        (∑ I ∈ J, ‖intervalSum I primeLog (t I)‖^2) < ((n:ℝ)^(3/4+η))^2 := by
      have orig := unif q hq hqs good a ha hc J hf t ht
      change (∑ I∈J,‖S I w (t I)‖^2)<_ at orig
      simpa only [eqS,ew] using orig
    refine ⟨h,?_⟩
    intro J hJ β off
    apply prime_character_variation (by omega) hq η J β off
    intro a ha t ht
    obtain ⟨hl,hc⟩ := mem_filter.mp ha
    exact h a (mem_range.mp hl).le hc J hJ t ht
  · constructor
    · intro target
      apply collective_necessary
      intro η hη
      obtain ⟨N,hN⟩ := target η hη
      refine ⟨N,?_⟩
      intro n hn t ht hd
      have eq := eqS (0,n+1) primeLog t
      rw [←eq]
      simpa only [S,Nat.Ico_zero_eq_range] using hN n hn t ht hd
    · exact ⟨fun _ h => uniform_high_bias h,fun _ h => all_high_bias h⟩
