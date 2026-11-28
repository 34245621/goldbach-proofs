import Mathlib

open Filter Asymptotics Topology

private theorem moment_count (X : ℕ) (hX : 4 ≤ X) :
    (Nat.log 2 X / 2 / 2) * ((2*X).primeCounting - X.primeCounting - (X.sqrt + 1)) ≤
      ∑ m ∈ (Finset.Ico X (2*X)).filter Odd,
        ((Finset.Icc 1 (Nat.log 2 X / 2 / 2)).filter (fun e => Nat.Prime (m-2^e))).card := by
  classical
  let k := Nat.log 2 X / 2 / 2
  let E := Finset.Icc 1 k
  let O := (Finset.Ico X (2*X)).filter Odd
  let T := (2*X).primesLE \ X.primesLE
  let B := Finset.Icc (2*X-X.sqrt) (2*X)
  let G := T \ B
  have hT : T.card = (2*X).primeCounting - X.primeCounting := by
    rw [Finset.card_sdiff_of_subset (Nat.primesLE_mono (show X ≤ 2*X by omega))]
    simp [Nat.primesLE_card_eq_primeCounting]
  have hB : B.card = X.sqrt + 1 := by
    simp only [B, Nat.card_Icc]
    have := Nat.sqrt_le_self X
    omega
  have hG : (2*X).primeCounting - X.primeCounting - (X.sqrt + 1) ≤ G.card := by
    rw [← hT, ← hB]
    exact Finset.le_card_sdiff B T
  have heBound (e : ℕ) (he : e ∈ E) :
      G.card ≤ (O.filter (fun m => Nat.Prime (m-2^e))).card := by
    obtain ⟨he1, hek⟩ := Finset.mem_Icc.mp he
    have hs : 2^e ≤ X.sqrt := by
      apply Nat.le_sqrt'.mpr
      rw [← pow_mul]
      apply Nat.pow_le_of_le_log (by omega)
      dsimp [k] at hek
      omega
    apply Finset.card_le_card_of_injOn (fun p : ℕ => p+2^e)
    · intro p hp
      obtain ⟨hpT,hpB⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨hp2,hpX⟩ := Finset.mem_sdiff.mp hpT
      obtain ⟨hp2,hpp⟩ := Nat.mem_primesLE.mp hp2
      have hpLo : X < p := by
        by_contra! h
        exact hpX (Nat.mem_primesLE.mpr ⟨h,hpp⟩)
      have hpHi : p < 2*X-X.sqrt := by
        by_contra! h
        exact hpB (Finset.mem_Icc.mpr ⟨h,hp2⟩)
      have hodd := hpp.odd_of_ne_two (by omega)
      have hEven : Even ((2:ℕ)^e) := even_two.pow_of_ne_zero (by omega)
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
        ⟨hpLo.le.trans (Nat.le_add_right p (2^e)), by change p + 2 ^ e < 2 * X; omega⟩,
        hodd.add_even hEven⟩, ?_⟩
      simpa using hpp
    · intro p hp q hq heq
      exact Nat.add_right_cancel heq
  change k * _ ≤ ∑ m ∈ O, (E.filter (fun e => Nat.Prime (m-2^e))).card
  calc
    k * _ ≤ k * G.card := Nat.mul_le_mul_left k hG
    _ = ∑ _ ∈ E, G.card := by simp [E, Nat.card_Icc]
    _ ≤ ∑ e ∈ E, (O.filter (fun m => Nat.Prime (m-2^e))).card :=
      Finset.sum_le_sum heBound
    _ = ∑ m ∈ O, (E.filter (fun e => Nat.Prime (m-2^e))).card := by
      calc
        _ = ∑ e ∈ E, ∑ m ∈ O, (if Nat.Prime (m-2^e) then 1 else 0 : ℕ) := by simp
        _ = ∑ m ∈ O, ∑ e ∈ E, (if Nat.Prime (m-2^e) then 1 else 0 : ℕ) :=
          Finset.sum_comm
        _ = _ := by simp

private theorem moment_odd_bound (X : ℕ) :
    2 * ((Finset.Ico X (2 * X)).filter Odd).card ≤ X + 1 := by
  classical
  have him : ((Finset.Ico X (2 * X)).filter Odd) =
      (Finset.Ico (X / 2) X).image (fun j => 2 * j + 1) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image]
    constructor
    · rintro ⟨⟨hm₁, hm₂⟩, j, hj⟩
      exact ⟨j, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨j, ⟨hl, hu⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, j, by omega⟩
  rw [him, Finset.card_image_of_injective _ (by intro i j h; dsimp at h; omega), Nat.card_Ico]
  omega

private theorem moment_quarter_log_limit :
    Tendsto (fun X : ℕ => ((Nat.log 2 X / 2 / 2 : ℕ) : ℝ) / Real.log X)
      atTop (nhds (1 / (4 * Real.log 2))) := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have herror : Tendsto (fun X : ℕ => 1 / Real.log X) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hlower : Tendsto (fun X : ℕ => 1 / (4 * Real.log 2) - 1 / Real.log X)
      atTop (nhds (1 / (4 * Real.log 2))) := by
    simpa using (herror.const_sub (1 / (4 * Real.log 2)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with X hX
    have hlX : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    have hf : Real.logb 2 X < (Nat.log 2 X : ℝ) + 1 := by
      simpa only [← Real.natFloor_logb_natCast 2 X, Nat.cast_ofNat] using
        (Nat.lt_floor_add_one (Real.logb 2 X))
    have hr : Nat.log 2 X ≤ 4 * (Nat.log 2 X / 2 / 2) + 3 := by omega
    have hr' : (Nat.log 2 X : ℝ) ≤ 4 * ((Nat.log 2 X / 2 / 2 : ℕ) : ℝ) + 3 := by
      exact_mod_cast hr
    rw [Real.logb] at hf
    apply (le_div_iff₀ hlX).2
    rw [sub_mul, div_mul_cancel₀ _ hlX.ne']
    calc
      1 / (4 * Real.log 2) * Real.log X - 1 = (Real.log X / Real.log 2) / 4 - 1 := by ring
      _ ≤ _ := by linarith
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with X hX
    have hlX : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    have hf := Real.natLog_le_logb X 2
    simp only [Nat.cast_ofNat, Real.logb] at hf
    have hr : 4 * (Nat.log 2 X / 2 / 2) ≤ Nat.log 2 X := by omega
    have hr' : 4 * ((Nat.log 2 X / 2 / 2 : ℕ) : ℝ) ≤ Nat.log 2 X := by exact_mod_cast hr
    apply (div_le_iff₀ hlX).2
    change _ ≤ 1 / (4 * Real.log 2) * Real.log X
    calc
      _ ≤ (Real.log X / Real.log 2) / 4 := by linarith
      _ = _ := by ring

private theorem moment_pnt :
    Tendsto (fun X : ℕ =>
      (((2*X).primeCounting : ℝ) - (X.primeCounting : ℝ) - ((Nat.sqrt X : ℝ) + 1)) /
        ((X : ℝ) / Real.log X)) atTop (𝓝 1) := by
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
  have hpntR := Nat.isEquivalent_primeCounting
  rw [isEquivalent_iff_tendsto_one (by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_ne_zero (by linarith) (Real.log_pos hx).ne')] at hpntR
  have hpnt : Tendsto (fun X : ℕ => (X.primeCounting : ℝ) / ((X : ℝ) / Real.log X))
      atTop (𝓝 1) := by
    simpa [Function.comp_def, Pi.div_apply] using hpntR.comp hcast
  have hdouble : Tendsto (fun X : ℕ => 2 * X) atTop atTop :=
    tendsto_atTop.2 (fun m => (eventually_ge_atTop m).mono (fun k hk => by omega))
  have hlog := Real.tendsto_log_atTop.comp hcast
  have hl2 : Tendsto (fun X : ℕ => Real.log 2 / Real.log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hratio : Tendsto (fun X : ℕ => (1 + Real.log 2 / Real.log X)⁻¹) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add hl2).inv₀ (by norm_num)
  have h2 : Tendsto (fun X : ℕ => ((2*X).primeCounting : ℝ) / ((X : ℝ) / Real.log X))
      atTop (𝓝 2) := by
    have h := ((hpnt.comp hdouble).mul hratio).mul_const 2
    simp only [one_mul] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with X hX
    have hx : (1 : ℝ) < X := by exact_mod_cast hX
    have lx := Real.log_pos hx
    have lx2 : 0 < Real.log (2 : ℝ) + Real.log X := add_pos (Real.log_pos (by norm_num)) lx
    simp only [Function.comp_apply, Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.log_mul (by norm_num) (by positivity)]
    field_simp
    nlinarith
  have hs : Tendsto (fun X : ℕ => Real.log X / Real.sqrt X) atTop (𝓝 0) := by
    simpa [Function.comp_def, Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp hcast
  have he : Tendsto (fun X : ℕ => ((Nat.sqrt X : ℝ) + 1) / ((X : ℝ) / Real.log X))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using hs.const_mul 2 : Tendsto _ _ (𝓝 (0 : ℝ)))
    · filter_upwards [eventually_gt_atTop (1 : ℕ)] with X hX
      have hx : (1 : ℝ) < X := by exact_mod_cast hX
      exact div_nonneg (by positivity) (div_nonneg (by positivity) (Real.log_pos hx).le)
    · filter_upwards [eventually_gt_atTop (1 : ℕ)] with X hX
      have hx : (1 : ℝ) < X := by exact_mod_cast hX
      have hx0 : (0 : ℝ) < X := by linarith
      have hs0 := Real.sqrt_pos.2 hx0
      have hs1 : 1 ≤ Real.sqrt (X : ℝ) := by simpa using Real.sqrt_le_sqrt hx.le
      have hns := Real.nat_sqrt_le_real_sqrt (a := X)
      have hl := Real.log_pos hx
      calc ((Nat.sqrt X : ℝ) + 1) / ((X : ℝ) / Real.log X)
          ≤ (2 * Real.sqrt X) / ((X : ℝ) / Real.log X) :=
            div_le_div_of_nonneg_right (by linarith) (by positivity)
        _ = 2 * (Real.log X / Real.sqrt X) := by
          field_simp
          nlinarith [Real.sq_sqrt hx0.le]
  simpa only [← sub_div, sub_self, sub_zero, show (2 : ℝ) - 1 = 1 by norm_num] using
    (h2.sub hpnt).sub he

theorem Conjectures.Cuts.Task8ae106b0db9c9d3ae9a141a5 : (∀ (x1 : ℝ),   (0 : ℝ) < x1 →     ∃ (x3 : ℕ),       ∀ x4 ≥ x3,         have x6 : Finset ℕ := Finset.filter Odd (Finset.Ico x4 ((2 : ℕ) * x4));         have x7 : ℕ → ℕ := fun (x7 : ℕ) => {x8 ∈ Finset.Icc (1 : ℕ) (Nat.log (2 : ℕ) x4 / (2 : ℕ) / (2 : ℕ)) | Nat.Prime (x7 - (2 : ℕ) ^ x8)}.card;         ((1 : ℝ) / ((2 : ℝ) * Real.log (2 : ℝ)) - x1) * ↑x6.card ≤ ↑(∑ x8 ∈ x6, x7 x8)) := by
  classical
  intro ε hε
  let μ : ℝ := 1 / (2 * Real.log 2)
  by_cases hz : μ - ε ≤ 0
  · refine ⟨0, ?_⟩
    intro X _
    exact (mul_nonpos_of_nonpos_of_nonneg hz (Nat.cast_nonneg _)).trans (Nat.cast_nonneg _)
  have hinv : Tendsto (fun X : ℕ => (X : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hleft : Tendsto (fun X : ℕ => ((μ - ε) / 2) * (1 + (X : ℝ)⁻¹))
      atTop (𝓝 ((μ - ε) / 2)) := by
    simpa only [add_zero, mul_one] using
      ((tendsto_const_nhds (x := (μ - ε) / 2)).mul
        ((tendsto_const_nhds (x := (1:ℝ))).add hinv))
  have hsep : (μ - ε) / 2 < 1 / (4 * Real.log 2) := by
    have hμ : μ / 2 = 1 / (4 * Real.log 2) := by
      dsimp [μ]
      ring
    linarith
  have hp := moment_quarter_log_limit.mul moment_pnt
  rw [mul_one] at hp
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hleft.eventually_lt hp hsep)
  refine ⟨max N 4, ?_⟩
  intro X hX
  have hfour : 4 ≤ X := (le_max_right _ _).trans hX
  have hXpos : (0:ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlog : Real.log (X : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < X by omega))).ne'
  let k := Nat.log 2 X / 2 / 2
  let A := (2 * X).primeCounting
  let B := X.primeCounting
  let S := Nat.sqrt X
  let O := (Finset.Ico X (2 * X)).filter Odd
  let r (m : ℕ) := ((Finset.Icc 1 k).filter (fun e => Nat.Prime (m - 2 ^ e))).card
  have hcomparison := hN X ((le_max_left _ _).trans hX)
  change (μ - ε) / 2 * (1 + (X : ℝ)⁻¹) <
      (k / Real.log X) * (((A : ℝ) - B - ((S : ℝ) + 1)) / ((X : ℝ) / Real.log X)) at hcomparison
  have hscaled := mul_lt_mul_of_pos_right hcomparison hXpos
  have hleftscale : ((μ - ε) / 2 * (1 + (X : ℝ)⁻¹)) * (X : ℝ) =
      (μ - ε) * (((X : ℝ) + 1) / 2) := by
    field_simp [hXpos.ne']
  have hrightscale : (k / Real.log X) *
      (((A : ℝ) - B - ((S : ℝ) + 1)) / ((X : ℝ) / Real.log X)) * X =
      (k : ℝ) * ((A : ℝ) - B - ((S : ℝ) + 1)) := by
    field_simp [hXpos.ne', hlog]
  rw [hleftscale, hrightscale] at hscaled
  have hodd : 2 * (O.card : ℝ) ≤ (X : ℝ) + 1 := by exact_mod_cast moment_odd_bound X
  have hnat : A ≤ (A - B - (S + 1)) + B + (S + 1) := by omega
  have hcast : (A : ℝ) ≤ ((A - B - (S + 1) : ℕ) : ℝ) + (B:ℝ) + ((S:ℝ) + 1) := by
    exact_mod_cast hnat
  have hcomb : ((k * (A - B - (S + 1)) : ℕ) : ℝ) ≤ ((∑ m ∈ O, r m : ℕ) : ℝ) := by
    exact_mod_cast moment_count X hfour
  change (μ - ε) * (O.card : ℝ) ≤ ((∑ m ∈ O, r m : ℕ) : ℝ)
  calc
    _ ≤ (μ - ε) * (((X : ℝ) + 1) / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_not_ge hz)
    _ ≤ (k : ℝ) * ((A : ℝ) - B - ((S : ℝ) + 1)) := hscaled.le
    _ ≤ (k : ℝ) * ((A - B - (S + 1) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    _ ≤ _ := by simpa only [Nat.cast_mul] using hcomb
