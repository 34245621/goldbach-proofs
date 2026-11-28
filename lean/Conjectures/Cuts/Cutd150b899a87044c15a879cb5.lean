import Mathlib

open scoped BigOperators
open MeasureTheory

-- child 1 en: On the central Type II band, the sum of the within-class reflected covariances at the small-modulus wheel is at least minus epsilon times n eventually on even targets.
-- child 1 zh: 对充分大的偶数，按小模数公倍数分组后，中心带权重与其反射在各组内的协方差总和至少为负的任意小常数乘以目标数。
-- child 2 en: The real wide-arc coefficient is at most the residue-class mean-field convolution plus epsilon times n eventually on even targets.
-- child 2 zh: 对充分大的偶数，宽弧系数实部不超过各剩余类内两侧均值乘积的加权和加上任意小的线性误差。
-- Full-circle Fourier calculation adapted from Type2CenterWideSubtraction in goldbach-proofs, Apache-2.0, revision bda6b09d27a8fb11511be83d7b648d1b9a91e6c5.

theorem Conjectures.Cuts.Cutd150b899a87044c15a879cb5
    (hCov : let u := fun (n m : ℕ) =>
      let root := fun h : ℝ => ⌊(n : ℝ) ^ h⌋₊
      ∑ a ∈ m.divisors with root (1/3) < a ∧ a ≤ root (2/3) ∧ root (1/16) < m/a,
        (∑ d ∈ a.divisors with root (1/16) < d, ((ArithmeticFunction.moebius d : ℤ) : ℝ)) * ArithmeticFunction.vonMangoldt (m/a)
    let wheel := fun n : ℕ => (Finset.Icc 1 (Nat.log 2 (n+2) / 64)).lcm id
    let cell := fun (n r : ℕ) => (Finset.range (n+1)).filter (fun (k : ℕ) => Nat.mod k (wheel n) = r)
    let residues := fun n : ℕ => (Finset.range (n+1)).image (fun (k : ℕ) => Nat.mod k (wheel n))
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, Even n →
    -(δ*(n:ℝ)) ≤ ∑ r ∈ residues n,
            let f := cell n r
            let a := (∑ j ∈ f, u n j) / (f.card : ℝ)
            let b := (∑ j ∈ f, u n (n-j)) / (f.card : ℝ)
            ∑ k ∈ f, (u n k-a)*(u n (n-k)-b))
    (hWide : let u := fun (n m : ℕ) =>
      let root := fun h : ℝ => ⌊(n : ℝ) ^ h⌋₊
      ∑ a ∈ m.divisors with root (1/3) < a ∧ a ≤ root (2/3) ∧ root (1/16) < m/a,
        (∑ d ∈ a.divisors with root (1/16) < d, ((ArithmeticFunction.moebius d : ℤ) : ℝ)) * ArithmeticFunction.vonMangoldt (m/a)
    let wheel := fun n : ℕ => (Finset.Icc 1 (Nat.log 2 (n+2) / 64)).lcm id
    let cell := fun (n r : ℕ) => (Finset.range (n+1)).filter (fun (k : ℕ) => Nat.mod k (wheel n) = r)
    let residues := fun n : ℕ => (Finset.range (n+1)).image (fun (k : ℕ) => Nat.mod k (wheel n))
    let e := fun x : ℝ => Complex.exp (((2*Real.pi*x : ℝ) : ℂ)*Complex.I)
    let arc := fun n : ℕ =>
      let b := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
      {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ b ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t-(a:ℝ)/(q:ℝ)| ≤ ((256*b*(Nat.log 2 (n+2))^2 : ℕ):ℝ)/((q:ℝ)*n)}
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, Even n →
    (∫ t in (0:ℝ)..1, (arc n).indicator (fun x =>
            (∑ k ∈ Finset.range (n+1), (u n k : ℂ)*e ((k:ℝ)*x))^2 * e (-(n:ℝ)*x)) t).re ≤ (∑ r ∈ residues n,
            let f := cell n r
            (∑ j ∈ f, u n j) * (∑ j ∈ f, u n (n-j)) / (f.card : ℝ)) + δ*(n:ℝ)) : (let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Λ := ArithmeticFunction.vonMangoldt; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₂ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let B₃ := fun n : ℕ => ⌊(n:ℝ)^(2/3:ℝ)⌋₊; let τ₃ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₂ n < a ∧ a ≤ B₃ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (Jdeep n (τ₃ n) (τ₃ n)).re) := by
  classical
  let osc (z : ℤ) (x : ℝ) : ℂ :=
    Complex.exp (((z : ℂ) * (2 * Real.pi * Complex.I)) * x)
  have osc_integral (z : ℤ) :
      (∫ x : ℝ in 0..1, osc z x) = if z = 0 then 1 else 0 := by
    by_cases hz : z = 0
    · simp [hz, osc]
    · have hc : (z : ℂ) * (2 * Real.pi * Complex.I) ≠ 0 := by
        exact mul_ne_zero (by exact_mod_cast hz)
          (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
      simp only [osc, integral_exp_mul_complex hc, Complex.ofReal_one, Complex.ofReal_zero,
        mul_one, mul_zero, Complex.exp_zero, Complex.exp_int_mul_two_pi_mul_I, sub_self, zero_div,
        ite_eq_right hz]
  have full_coeff (n : ℕ) (w : ℕ → ℝ) :
      (∫ x : ℝ in 0..1,
        (∑ k ∈ Finset.range (n+1), (w k : ℂ) * osc k x)^2 * osc (-(n : ℤ)) x) =
        ((∑ k ∈ Finset.range (n+1), w k * w (n-k) : ℝ) : ℂ) := by
    let A (k l : ℕ) (x : ℝ) := ((w k : ℂ) * w l) * osc ((k : ℤ) + l - n) x
    have hA (k l : ℕ) : Continuous (A k l) := by unfold A osc; fun_prop
    have expand (x : ℝ) :
        (∑ k ∈ Finset.range (n+1), (w k : ℂ) * osc k x)^2 * osc (-(n : ℤ)) x =
        ∑ k ∈ Finset.range (n+1), ∑ l ∈ Finset.range (n+1), A k l x := by
      rw [sq, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      simp only [A, osc, Int.cast_sub, Int.cast_add, Int.cast_neg, Int.cast_natCast]
      have regroup (a b c d e : ℂ) : a * b * (c * d) * e = (a*c)*((b*d)*e) := by ring
      rw [regroup, ← Complex.exp_add, ← Complex.exp_add]
      congr 2; ring
    simp_rw [expand]
    rw [intervalIntegral.integral_finsetSum (fun k _ =>
      (continuous_finsetSum _ (fun l _ => hA k l)).intervalIntegrable 0 1)]
    push_cast
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := by simpa using Finset.mem_range.mp hk
    rw [intervalIntegral.integral_finsetSum (fun l _ => (hA k l).intervalIntegrable 0 1)]
    simp only [A, intervalIntegral.integral_const_mul, osc_integral]
    rw [Finset.sum_eq_single (n-k)]
    · simp [show (k : ℤ) + (n-k : ℕ) - n = 0 by omega]
    · intro l _ hl
      simp [show (k : ℤ) + l - n ≠ 0 by omega]
    · intro h
      exact (h (Finset.mem_range.mpr (by omega))).elim
  intro E S Q Q₁ H wideArcs Λ μ U B₂ B₃ τ₃ Jdeep
  have subAt (n : ℕ) :
      let f := fun t : ℝ => (S n (τ₃ n) t)^2 * E (-(n:ℝ)*t)
      Jdeep n (τ₃ n) (τ₃ n) = ((∑ k ∈ Finset.range (n+1), τ₃ n k * τ₃ n (n-k)) : ℝ) - intervalIntegral ((wideArcs n).indicator f) 0 1 MeasureTheory.volume := by
    intro f
    have aosc (k : ℕ) (x : ℝ) : E ((k : ℝ)*x) = osc k x := by
      dsimp [E, osc]; push_cast; congr 1; ring
    have nosc (x : ℝ) : E (-(n : ℝ)*x) = osc (-(n : ℤ)) x := by
      dsimp [E, osc]; push_cast; congr 1; ring
    have hfull : (∫ x : ℝ in 0..1, f x) =
        ((∑ k ∈ Finset.range (n+1), τ₃ n k * τ₃ n (n-k) : ℝ) : ℂ) := by
      simpa only [f, S, aosc, nosc] using full_coeff n (τ₃ n)
    have hcont : Continuous f := by dsimp [f, S, E]; fun_prop
    have hmeas : MeasurableSet (wideArcs n) := by
      simp only [wideArcs, Set.ofPred_exists]
      apply MeasurableSet.iUnion
      intro q
      apply MeasurableSet.iUnion
      intro a
      by_cases h : 1 ≤ q ∧ q ≤ Q₁ n ∧ a ≤ q ∧ Nat.Coprime a q
      · rcases h with ⟨h₁, h₂, h₃, h₄⟩
        convert (isClosed_le (f := fun t : ℝ => |t-(a:ℝ)/(q:ℝ)|)
          (g := fun _ : ℝ => (H n:ℝ)/((q:ℝ)*(n:ℝ))) (by fun_prop) continuous_const).measurableSet using 1
        ext x
        exact ⟨fun hx => hx.2.2.2.2, fun hx => ⟨h₁, h₂, h₃, h₄, hx⟩⟩
      · convert MeasurableSet.empty (α := ℝ) using 1
        ext x
        exact iff_of_false (fun hx => h ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1⟩) (fun hx => hx)
    change (∫ t : ℝ in 0..1, (wideArcs n)ᶜ.indicator _ t) = _
    simp only [← sq]
    rw [← hfull]
    change (∫ t : ℝ in 0..1, (wideArcs n)ᶜ.indicator f t) = _
    simp only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    rw [integral_indicator hmeas.compl, integral_indicator hmeas]
    exact setIntegral_compl hmeas ((hcont.intervalIntegrable 0 1).1)
  have cell_identity (s : Finset ℕ) (x y : ℕ → ℝ) (hs : s.Nonempty) :
      (∑ k ∈ s, x k * y k) =
        (∑ k ∈ s, (x k - (∑ j ∈ s, x j)/(s.card:ℝ)) * (y k - (∑ j ∈ s, y j)/(s.card:ℝ))) +
        (∑ j ∈ s, x j) * (∑ j ∈ s, y j) / (s.card:ℝ) := by
    have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr hs)
    simp_rw [sub_mul, mul_sub]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul]
    field_simp
    ring
  intro ε hε
  obtain ⟨N₁, h₁⟩ := hCov (ε/2) (half_pos hε)
  obtain ⟨N₂, h₂⟩ := hWide (ε/2) (half_pos hε)
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn heven
  let modW := (Finset.Icc 1 (Nat.log 2 (n+2) / 64)).lcm id
  let I := Finset.range (n+1)
  let label := fun k : ℕ => Nat.mod k modW
  let R := I.image label
  let F := fun r => I.filter (fun k => label k = r)
  let x := τ₃ n
  let y := fun k => x (n-k)
  let cov := fun r => ∑ k ∈ F r, (x k - (∑ j ∈ F r, x j)/((F r).card:ℝ)) * (y k - (∑ j ∈ F r, y j)/((F r).card:ℝ))
  let model := fun r => (∑ j ∈ F r, x j) * (∑ j ∈ F r, y j) / ((F r).card:ℝ)
  let f := fun t : ℝ => (S n x t)^2 * E (-(n:ℝ)*t)
  let W := (intervalIntegral ((wideArcs n).indicator f) (0:ℝ) 1 MeasureTheory.volume).re
  have hs : (∑ k ∈ I, x k * y k) = (∑ r ∈ R, cov r) + ∑ r ∈ R, model r := by
    calc
      _ = ∑ r ∈ R, ∑ k ∈ F r, x k * y k := (Finset.sum_fiberwise_of_maps_to (s := I) (t := R) (g := label) (fun k hk => Finset.mem_image_of_mem label hk) (fun k => x k*y k)).symm
      _ = ∑ r ∈ R, (cov r + model r) := by
        apply Finset.sum_congr rfl
        intro r hr
        obtain ⟨k, hk, hkr⟩ := Finset.mem_image.mp hr
        exact cell_identity (F r) x y ⟨k, Finset.mem_filter.mpr ⟨hk, hkr⟩⟩
      _ = _ := Finset.sum_add_distrib
  have hc : -(ε/2*(n:ℝ)) ≤ ∑ r ∈ R, cov r := h₁ n (le_trans (le_max_left ..) hn) heven
  have hw : W ≤ (∑ r ∈ R, model r) + ε/2*(n:ℝ) := h₂ n (le_trans (le_max_right ..) hn) heven
  have hdeep : (Jdeep n x x).re = (∑ k ∈ I, x k*y k) - W := congrArg Complex.re (subAt n)
  linarith only [hs, hc, hw, hdeep]
