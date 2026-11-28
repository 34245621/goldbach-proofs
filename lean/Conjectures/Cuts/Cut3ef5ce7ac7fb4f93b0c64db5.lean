import Mathlib
import Conjectures.Goldbach.PacketMangoldtUniformSpectralError

open Finset MeasureTheory Filter
open scoped Topology

-- child 1 zh: 在分母至 n 的 2/7 次幂的窄弧上，控制冻结共振掩码内的 Ramanujan 主项平方能量。
-- child 1 en: Bound the squared energy of the Ramanujan pole on resonant narrow arcs up to the frozen denominator cap.
-- child 2 zh: 在全部共振窄弧上，控制冯·芒戈尔特指数和减去 Ramanujan 主项后的平方能量。
-- child 2 en: Bound the squared energy of the von Mangoldt sum after subtracting the Ramanujan pole on all resonant narrow arcs.

set_option maxHeartbeats 1800000 in
theorem Conjectures.Cuts.Cut3ef5ce7ac7fb4f93b0c64db5
  (pole :
    ∃ N : ℕ, ∀ n ≥ N,
      let L := max 1 (Nat.log 2 n / 2)
      let P := ⌊(n : ℝ) ^ (2 / 7 : ℝ)⌋₊
      let B := {t : ℝ | (1 / 2 : ℝ) < (∑ j ∈ Finset.range L,
        Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) / (L : ℝ)}
      let U := ((Nat.log 2 (n + 2)) ^ 2) ^ 2
      let W := {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ U ∧ a ≤ q ∧ a.Coprime q ∧
        |t - (a : ℝ) / q| ≤ (U : ℝ) / ((q : ℝ) * n)}
      let S := fun (w : ℕ → ℂ) (t : ℝ) => ∑ k ∈ Finset.range (n + 1),
        w k * Complex.exp (((2 * Real.pi * ((k : ℝ) * t) : ℝ) : ℂ) * Complex.I)
      (∫ t in (0 : ℝ)..1, ∑ q ∈ Finset.Icc 1 P,
        ∑ a ∈ (Finset.range (q + 1)).filter (fun a => a.Coprime q),
          ({s : ℝ | |s - (a : ℝ) / q| ≤ (P : ℝ) / ((q : ℝ) * n)} ∩ (B \ W)).indicator
            (fun s => ‖(((ArithmeticFunction.moebius q : ℤ) : ℂ) / (q.totient : ℂ)) *
              S (fun _ => (1 : ℂ)) (s - (a : ℝ) / q)‖ ^ 2) t) ≤
        (n : ℝ) / (1600000 * (1 + Real.log (n : ℝ)) ^ 2))
  (residual :
    ∃ N : ℕ, ∀ n ≥ N,
      let L := max 1 (Nat.log 2 n / 2)
      let P := ⌊(n : ℝ) ^ (2 / 7 : ℝ)⌋₊
      let B := {t : ℝ | (1 / 2 : ℝ) < (∑ j ∈ Finset.range L,
        Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) / (L : ℝ)}
      let S := fun (w : ℕ → ℂ) (t : ℝ) => ∑ k ∈ Finset.range (n + 1),
        w k * Complex.exp (((2 * Real.pi * ((k : ℝ) * t) : ℝ) : ℂ) * Complex.I)
      (∫ t in (0 : ℝ)..1, ∑ q ∈ Finset.Icc 1 P,
        ∑ a ∈ (Finset.range (q + 1)).filter (fun a => a.Coprime q),
          ({s : ℝ | |s - (a : ℝ) / q| ≤ (P : ℝ) / ((q : ℝ) * n)} ∩ B).indicator
            (fun s => ‖S (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) s - (((ArithmeticFunction.moebius q : ℤ) : ℂ) / (q.totient : ℂ)) *
              S (fun _ => (1 : ℂ)) (s - (a : ℝ) / q)‖ ^ 2) t) ≤
        (n : ℝ) / (1600000 * (1 + Real.log (n : ℝ)) ^ 2)) :
  (have x1 : ℕ → ℕ := fun (x1 : ℕ) => Max.max (1 : ℕ) (Nat.log (2 : ℕ) x1 / (2 : ℕ)); have x2 : ℕ → ℕ := fun (x2 : ℕ) => Nat.log (2 : ℕ) (x2 + (2 : ℕ)) ^ (2 : ℕ); have x3 : ℕ → ℕ → Set ℝ := fun (x3 x4 : ℕ) => {x5 : ℝ | ∃ (x6 : ℕ) (x7 : ℕ), (1 : ℕ) ≤ x6 ∧ x6 ≤ x4 ∧ x7 ≤ x6 ∧ x7.Coprime x6 ∧ |x5 - (↑x7 : ℝ) / (↑x6 : ℝ)| ≤ (↑x4 : ℝ) / ((↑x6 : ℝ) * (↑x3 : ℝ))}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => if Nat.Prime x4 then Real.log (↑x4 : ℝ) else (0 : ℝ); have x5 : ℕ → ℝ → ℝ := fun (x5 : ℕ) (x6 : ℝ) => ‖∑ x7 ∈ Finset.range (x5 + (1 : ℕ)), (↑(x4 x7 - if x7 ^ (3 : ℕ) ≤ x5 then x4 x7 else (0 : ℝ)) : ℂ) * Complex.exp ((↑((2 : ℝ) * Real.pi * ((↑x7 : ℝ) * x6)) : ℂ) * Complex.I)‖ ^ (2 : ℕ); have x6 : ℕ → ℝ := fun (x6 : ℕ) => (1 : ℝ) + Real.log (↑x6 : ℝ); have x7 : ℕ → ℝ → Set ℝ := fun (x7 : ℕ) (x8 : ℝ) => {x9 : ℝ | x9 ∉ x3 x7 (x2 x7) ∧ (1 / 2 : ℝ) < (∑ x10 ∈ Finset.range (x1 x7), Real.cos ((2 : ℝ) * Real.pi * (2 : ℝ) ^ (x10 + (1 : ℕ)) * x9)) / (↑(x1 x7) : ℝ) ∧ x9 ∉ x3 x7 (x2 x7 ^ (2 : ℕ)) ∧ x8 < x5 x7 x9 ∧ x5 x7 x9 ≤ (2 : ℝ) * x8}; ∃ (x8 : ℕ),   ∀ x9 ≥ x8,     Even x9 →       ∀ (x12 : ℕ),         x1 x9 / (4 : ℕ) < x12 →           x12 < Nat.log (2 : ℕ) x9 + (3 : ℕ) →             have x15 : ℝ := (2 : ℝ) ^ x12 * ((↑x9 : ℝ) * x6 x9 ^ (4 : ℕ));             x15 < (4 : ℝ) * (↑x9 : ℝ) ^ (2 : ℕ) → (↑x9 : ℝ) ^ (7 / 4 : ℝ) ≤ x15 → x15 * ∫ (x18 : ℝ) in (0 : ℝ)..(1 : ℝ), (x7 x9 x15 ∩ x3 x9 ⌊(↑x9 : ℝ) ^ (2 / 7 : ℝ)⌋₊).indicator (fun (x19 : ℝ) => (1 : ℝ)) x18 ≤ (↑x9 : ℝ) / ((100000 : ℝ) * x6 x9 ^ (2 : ℕ))) := by
  classical
  let L := fun n : ℕ => max 1 (Nat.log 2 n / 2)
  let P := fun n : ℕ => ⌊(n : ℝ) ^ (2 / 7 : ℝ)⌋₊
  let I := fun (n b q a : ℕ) => {t : ℝ |
    |t - (a : ℝ) / q| ≤ (b : ℝ) / ((q : ℝ) * n)}
  let A := fun (n b : ℕ) => {t : ℝ | ∃ q a : ℕ,
    1 ≤ q ∧ q ≤ b ∧ a ≤ q ∧ a.Coprime q ∧ t ∈ I n b q a}
  let R := fun (n q a : ℕ) => I n (P n) q a ∩
    ({t : ℝ | (1 / 2 : ℝ) < (∑ j ∈ Finset.range (L n),
      Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) / (L n : ℝ)} \
      A n (((Nat.log 2 (n + 2)) ^ 2) ^ 2))
  let e := fun t : ℝ => Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
  let M := fun (n q a : ℕ) (t : ℝ) =>
    (((ArithmeticFunction.moebius q : ℤ) : ℂ) / (q.totient : ℂ)) *
      ∑ k ∈ Finset.range (n + 1), (1 : ℂ) * e ((k : ℝ) * (t - (a : ℝ) / q))
  let w := fun k : ℕ => if k.Prime then Real.log (k : ℝ) else 0
  let V (n : ℕ) (t : ℝ) := ∑ k ∈ Finset.range (n + 1),
    (ArithmeticFunction.vonMangoldt k : ℂ) * e ((k : ℝ) * t)
  let S (n : ℕ) (t : ℝ) := ∑ k ∈ Finset.range (n + 1),
    ((w k - if k ^ 3 ≤ n then w k else 0 : ℝ) : ℂ) * e ((k : ℝ) * t)
  let resonant (n : ℕ) := {t : ℝ | (1 / 2 : ℝ) < (∑ j ∈ Finset.range (L n),
    Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) / (L n : ℝ)}
  let Q (n : ℕ) := Nat.log 2 (n + 2) ^ 2
  let nums (q : ℕ) := (Finset.range (q + 1)).filter (fun a => a.Coprime q)
  have masked_integrable {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → ℝ}
      (hf : Continuous f) : IntervalIntegrable (s.indicator f) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (hf.intervalIntegrable 0 1)).indicator hs
  have interval_measurable (n b q a : ℕ) : MeasurableSet (I n b q a) :=
    (isClosed_le (continuous_abs.comp (continuous_id.sub continuous_const))
      continuous_const).measurableSet
  have arcs_measurable (n b : ℕ) : MeasurableSet (A n b) := by
    have cover : A n b = ⋃ i : {pr : ℕ × ℕ // 1 ≤ pr.1 ∧ pr.1 ≤ b ∧
        pr.2 ≤ pr.1 ∧ pr.2.Coprime pr.1}, I n b i.val.1 i.val.2 := by
      ext t
      constructor
      · rintro ⟨q, a, hq, hb, ha, hc, ht⟩
        exact Set.mem_iUnion.mpr ⟨⟨(q, a), hq, hb, ha, hc⟩, ht⟩
      · intro ht
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
        exact ⟨i.val.1, i.val.2, i.property.1, i.property.2.1,
          i.property.2.2.1, i.property.2.2.2, hi⟩
    rw [cover]
    exact MeasurableSet.iUnion (fun i => interval_measurable n b i.val.1 i.val.2)
  have resonant_measurable (n : ℕ) : MeasurableSet (resonant n) := by
    have h : Continuous (fun t : ℝ => (∑ j ∈ Finset.range (L n),
        Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) / (L n : ℝ)) := by
      fun_prop
    exact (isOpen_lt continuous_const h).measurableSet
  have region_measurable (n q a : ℕ) : MeasurableSet (R n q a) :=
    (interval_measurable n (P n) q a).inter
      ((resonant_measurable n).diff (arcs_measurable n ((Q n) ^ 2)))
  have finite_integrable {ι : Type} (s : Finset ι) (f : ι → ℝ → ℝ)
      (h : ∀ i ∈ s, IntervalIntegrable (f i) volume 0 1) :
      IntervalIntegrable (fun t => ∑ i ∈ s, f i t) volume 0 1 := by
    have hEq : (∑ i ∈ s, f i) = (fun t => ∑ i ∈ s, f i t) := by
      funext t
      simp only [Finset.sum_apply]
    rw [← hEq]
    exact IntervalIntegrable.sum s h
  have spectral_small : ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ,
      ‖V n t - S n t‖ ≤ (n : ℝ) ^ (7 / 8 : ℝ) / 2 := by
    have hnInf : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hl := ((isLittleO_log_rpow_rpow_atTop (1 : ℝ)
      (by norm_num : (0 : ℝ) < 3 / 8)).comp_tendsto hnInf).bound
        (by norm_num : (0 : ℝ) < 1 / 8)
    apply eventually_atTop.mp
    filter_upwards [eventually_ge_atTop (1 : ℕ), hl] with n hn hl
    intro t
    have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    have hlogbound : Real.log (n : ℝ) ≤ (1 / 8 : ℝ) * (n : ℝ) ^ (3 / 8 : ℝ) := by
      simpa only [Function.comp_apply, Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg hlog,
        abs_of_nonneg (Real.rpow_nonneg hpos.le (3 / 8 : ℝ))] using hl
    have hp : Real.sqrt (n : ℝ) * (n : ℝ) ^ (3 / 8 : ℝ) =
        (n : ℝ) ^ (7 / 8 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hpos]
      norm_num
    calc
      _ ≤ 4 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) :=
        Conjectures.Goldbach.PacketMangoldtUniformSpectralError n hn t
      _ ≤ 4 * Real.sqrt (n : ℝ) * ((1 / 8 : ℝ) * (n : ℝ) ^ (3 / 8 : ℝ)) := by
        gcongr
      _ = (n : ℝ) ^ (7 / 8 : ℝ) / 2 := by rw [← hp]; ring
  obtain ⟨Np, hp⟩ := pole
  obtain ⟨Nr, hr⟩ := residual
  obtain ⟨Ns, hs⟩ := spectral_small
  refine ⟨max Np (max Nr (max Ns 1)), ?_⟩
  intro n hn _heven
  dsimp only
  intro j _hj _htop _hycap hylarge
  let y := (2 : ℝ) ^ j * ((n : ℝ) * (1 + Real.log (n : ℝ)) ^ 4)
  let band := {t : ℝ | t ∉ A n (Q n) ∧ t ∈ resonant n ∧ t ∉ A n ((Q n) ^ 2) ∧
    y < ‖S n t‖ ^ 2 ∧ ‖S n t‖ ^ 2 ≤ 2 * y} ∩ A n (P n)
  change y * (∫ t in (0 : ℝ)..1, band.indicator (fun _ => (1 : ℝ)) t) ≤
    (n : ℝ) / (100000 * (1 + Real.log (n : ℝ)) ^ 2)
  let fm (q a : ℕ) := (R n q a).indicator (fun t => ‖M n q a t‖ ^ 2)
  let residualRegion (q a : ℕ) := I n (P n) q a ∩ resonant n
  let fr (q a : ℕ) := (residualRegion q a).indicator (fun t => ‖V n t - M n q a t‖ ^ 2)
  let sumPole (t : ℝ) := ∑ q ∈ Finset.Icc 1 (P n), ∑ a ∈ nums q, fm q a t
  let sumResidual (t : ℝ) := ∑ q ∈ Finset.Icc 1 (P n), ∑ a ∈ nums q, fr q a t
  have hPole := hp n (by omega)
  have hResidual := hr n (by omega)
  change (∫ t in (0 : ℝ)..1, sumPole t) ≤
    (n : ℝ) / (1600000 * (1 + Real.log (n : ℝ)) ^ 2) at hPole
  change (∫ t in (0 : ℝ)..1, sumResidual t) ≤
    (n : ℝ) / (1600000 * (1 + Real.log (n : ℝ)) ^ 2) at hResidual
  have hm_cont (q a : ℕ) : Continuous (M n q a) := by
    simp only [M, e]
    fun_prop
  have hv_cont : Continuous (V n) := by
    simp only [V, e]
    fun_prop
  have hs_cont : Continuous (fun t => ‖S n t‖ ^ 2) := by
    simp only [S, e]
    fun_prop
  have hm_int : IntervalIntegrable sumPole volume 0 1 := by
    apply finite_integrable
    intro q _
    apply finite_integrable
    intro a _
    exact masked_integrable (region_measurable n q a) ((hm_cont q a).norm.pow 2)
  have hr_int : IntervalIntegrable sumResidual volume 0 1 := by
    apply finite_integrable
    intro q _
    apply finite_integrable
    intro a _
    exact masked_integrable
      ((interval_measurable n (P n) q a).inter (resonant_measurable n))
      ((hv_cont.sub (hm_cont q a)).norm.pow 2)
  have hband : MeasurableSet band :=
    ((arcs_measurable n (Q n)).compl.inter
      ((resonant_measurable n).inter ((arcs_measurable n ((Q n) ^ 2)).compl.inter
        ((isOpen_lt continuous_const hs_cont).measurableSet.inter
          (isClosed_le hs_cont continuous_const).measurableSet)))).inter
      (arcs_measurable n (P n))
  have hband_int := masked_integrable hband (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))
  have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hpow : ((n : ℝ) ^ (7 / 8 : ℝ)) ^ 2 = (n : ℝ) ^ (7 / 4 : ℝ) := by
    rw [← Real.rpow_mul_natCast hpos.le]
    norm_num
  have hErrSq (t : ℝ) : ‖V n t - S n t‖ ^ 2 ≤ y / 4 := by
    have ht := pow_le_pow_left₀ (norm_nonneg _) (hs n (by omega) t) 2
    change (n : ℝ) ^ (7 / 4 : ℝ) ≤ y at hylarge
    nlinarith only [ht, hylarge, hpow]
  have hnonneg (t : ℝ) (q a : ℕ) : 0 ≤ fm q a t ∧ 0 ≤ fr q a t := by
    constructor
    · by_cases h : t ∈ R n q a
      · simp [fm, h, Set.indicator_of_mem]
      · simp [fm, h, Set.indicator_of_notMem]
    · by_cases h : t ∈ residualRegion q a
      · simp [fr, h, Set.indicator_of_mem]
      · simp [fr, h, Set.indicator_of_notMem]
  have hpoint (t : ℝ) : y * band.indicator (fun _ => (1 : ℝ)) t ≤
      8 * (sumPole t + sumResidual t) := by
    by_cases ht : t ∈ band
    · obtain ⟨q, a, hq, hP, ha, hc, hi⟩ := ht.2
      have hregion : t ∈ R n q a := ⟨hi, ht.1.2.1, ht.1.2.2.1⟩
      have hregionResidual : t ∈ residualRegion q a := ⟨hi, ht.1.2.1⟩
      have hqy : q ∈ Finset.Icc 1 (P n) := Finset.mem_Icc.mpr ⟨hq, hP⟩
      have hay : a ∈ nums q := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ha), hc⟩
      have hAbove : y < ‖S n t‖ ^ 2 := ht.1.2.2.2.1
      have hhalf : ‖V n t - S n t‖ ≤ ‖S n t‖ / 2 := by
        apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
        nlinarith only [hAbove, hErrSq t]
      have htri := norm_sub_le (V n t) (V n t - S n t)
      rw [sub_sub_cancel] at htri
      have htri' := norm_add_le (V n t - M n q a t) (M n q a t)
      rw [sub_add_cancel] at htri'
      have htotal : ‖S n t‖ ≤ 2 * (‖V n t - M n q a t‖ + ‖M n q a t‖) := by
        linarith only [htri, htri', hhalf]
      have htotal_sq := pow_le_pow_left₀ (norm_nonneg _) htotal 2
      have hweight : y ≤ 8 * (‖M n q a t‖ ^ 2 + ‖V n t - M n q a t‖ ^ 2) := by
        nlinarith only [hAbove, htotal_sq, sq_nonneg (‖M n q a t‖ - ‖V n t - M n q a t‖)]
      have hpm : ‖M n q a t‖ ^ 2 ≤ sumPole t := by
        calc
          _ = fm q a t := (Set.indicator_of_mem hregion _).symm
          _ ≤ ∑ b ∈ nums q, fm q b t := Finset.single_le_sum (fun b _ => (hnonneg t q b).1) hay
          _ ≤ _ := Finset.single_le_sum
            (fun r _ => Finset.sum_nonneg (fun b _ => (hnonneg t r b).1)) hqy
      have hpr : ‖V n t - M n q a t‖ ^ 2 ≤ sumResidual t := by
        calc
          _ = fr q a t := (Set.indicator_of_mem hregionResidual _).symm
          _ ≤ ∑ b ∈ nums q, fr q b t := Finset.single_le_sum (fun b _ => (hnonneg t q b).2) hay
          _ ≤ _ := Finset.single_le_sum
            (fun r _ => Finset.sum_nonneg (fun b _ => (hnonneg t r b).2)) hqy
      rw [Set.indicator_of_mem ht, mul_one]
      linarith only [hweight, hpm, hpr]
    · have hp0 : 0 ≤ sumPole t := Finset.sum_nonneg (fun q _ =>
        Finset.sum_nonneg (fun a _ => (hnonneg t q a).1))
      have hr0 : 0 ≤ sumResidual t := Finset.sum_nonneg (fun q _ =>
        Finset.sum_nonneg (fun a _ => (hnonneg t q a).2))
      rw [Set.indicator_of_notMem ht, mul_zero]
      exact mul_nonneg (by norm_num) (add_nonneg hp0 hr0)
  calc
    _ = ∫ t in (0 : ℝ)..1, y * band.indicator (fun _ => (1 : ℝ)) t :=
      (intervalIntegral.integral_const_mul y (band.indicator (fun _ => (1 : ℝ)))).symm
    _ ≤ ∫ t in (0 : ℝ)..1, 8 * (sumPole t + sumResidual t) :=
      intervalIntegral.integral_mono_on (by norm_num) (hband_int.const_mul y)
        ((hm_int.add hr_int).const_mul 8) (fun t _ => hpoint t)
    _ = 8 * ((∫ t in (0 : ℝ)..1, sumPole t) + ∫ t in (0 : ℝ)..1, sumResidual t) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hm_int hr_int]
    _ ≤ 8 * ((n : ℝ) / (1600000 * (1 + Real.log (n : ℝ)) ^ 2) +
        (n : ℝ) / (1600000 * (1 + Real.log (n : ℝ)) ^ 2)) := by
      gcongr
    _ = _ := by
      have ht : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
      have hne : (1 : ℝ) + Real.log (n : ℝ) ≠ 0 := by
        linarith only [Real.log_nonneg ht]
      field_simp [hne] <;> ring
