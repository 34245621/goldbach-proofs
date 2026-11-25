import Mathlib
import PEqualNP.Outside.L_goldbach_zero_additive_twist_dyadic

import PEqualNP.Outside.L_goldbach_frontier_grh_medium_zones

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

/-- Glue dyadic bounds on [v/2,v] into a prefix estimate. The geometric
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

/-- A single truncated Dirichlet zero sum across the entire interval [1,Y].
The exponent in each integral is the real part of that zero. The constant is
uniform in the character, conductor parameter, truncation height and twist. -/
theorem _root_.PEqualNP.Outside.L_goldbach_grh_dirichlet_twisted_zero_prefix (hGRH : Goldbach.GRH) :
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

end TwistedZeroApplication