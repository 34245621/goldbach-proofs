import Mathlib

-- The complex orthogonality calculation adapts community task 91500b604fdcc58571ab069f.
-- child 1 zh: 在每个数字字母表中，左半中心窗口内候选素数个数的平方至多为目标值的偶数字词数满足幂节省。
-- child 1 en: Bound the even words whose lower central window contains at most the square root of the target in primes, with a power saving in the number of words.
-- child 2 zh: 对中心候选素数个数的平方大于目标值、但每个候选的补数均非素数的偶数字词数给出幂节省。
-- child 2 en: Bound the even words having more central prime candidates than the square root of the target but no prime complement, with a power saving in the number of words.

theorem Conjectures.Cuts.Cut5947aca05c25f70c8e7ed3a7
    (hThin : by
      classical
      let P := fun n : ℕ => (Finset.range (n + 1)).filter fun p =>
        Nat.Prime p ∧ p ≤ n - p ∧ p.dist (n - p) ^ 3 ≤ n ^ 2
      exact ∀ b : ℕ, 2 ≤ b → ∃ δ C : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < C ∧
        ∀ (k : ℕ) (D : Finset ℕ), D ⊆ Finset.range b → 2 ≤ D.card →
          let W := Fintype.piFinset (fun _ : Fin k => D)
          let val := fun w : Fin k → ℕ => ∑ i : Fin k, w i * b ^ (i : ℕ)
          ((W.filter (fun w => let n := val w; Even n ∧ (P n).card ^ 2 ≤ n)).card : ℝ) ≤
            C * (1 + (D.card : ℝ) ^ k) ^ (1 - δ))
    (hUnpaired : by
      classical
      let P := fun n : ℕ => (Finset.range (n + 1)).filter fun p =>
        Nat.Prime p ∧ p ≤ n - p ∧ p.dist (n - p) ^ 3 ≤ n ^ 2
      exact ∀ b : ℕ, 2 ≤ b → ∃ δ C : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < C ∧
        ∀ (k : ℕ) (D : Finset ℕ), D ⊆ Finset.range b → 2 ≤ D.card →
          let W := Fintype.piFinset (fun _ : Fin k => D)
          let val := fun w : Fin k → ℕ => ∑ i : Fin k, w i * b ^ (i : ℕ)
          ((W.filter (fun w => let n := val w; Even n ∧ n < (P n).card ^ 2 ∧ ∀ p ∈ P n, ¬ Nat.Prime (n - p))).card : ℝ) ≤
            C * (1 + (D.card : ℝ) ^ k) ^ (1 - δ))
    : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑x1 : ℂ) * (↑x2 : ℂ)); ∀ (x2 : ℕ), (2 : ℕ) ≤ x2 → ∃ (x4 : ℝ) (x5 : ℝ), (0 : ℝ) < x4 ∧ x4 < (1 : ℝ) ∧ (0 : ℝ) < x5 ∧ ∀ (x6 : ℕ), ∀ x7 ⊆ Finset.range x2, (2 : ℕ) ≤ x7.card → ∀ (x10 : Finset ℕ), (∀ x11 ∈ x10, Even x11 ∧ ¬∃ (x13 : ℕ) (x14 : ℕ), Nat.Prime x13 ∧ Nat.Prime x14 ∧ x13 + x14 = x11 ∧ x13.dist x14 ^ (3 : ℕ) ≤ x11 ^ (2 : ℕ)) → ‖∫ (x12 : ℝ) in (0 : ℝ)..(1 : ℝ), (∏ x13 : Fin x6, ∑ x14 ∈ x7, x1 (x14 * x2 ^ (↑x13 : ℕ)) x12) * Star.star (∑ x13 ∈ x10, x1 x13 x12)‖ ≤ x5 * ((1 : ℝ) + (↑(∏ x12 : Fin x6, x7.card) : ℝ)) ^ ((1 : ℝ) - x4)) := by
  classical
  let phase (k : ℕ) (t : ℝ) : ℂ :=
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * k * t)

  have phase_orth (k j : ℕ) :
      (∫ t in (0 : ℝ)..1, phase k t * star (phase j t)) = if k = j then 1 else 0 := by
    let a : ℂ := ((k : ℂ) - j) * (2 * (Real.pi : ℂ) * Complex.I)
    have h (t : ℝ) : phase k t * star (phase j t) = Complex.exp (a * t) := by
      dsimp only [phase]
      rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      congr 1
      have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
        simpa only [Nat.cast_ofNat] using (map_natCast (starRingEnd ℂ) 2)
      simp [a, map_mul, htwo]
      ring
    simp_rw [h]
    by_cases hk : k = j
    · subst k
      simp [a]
    · have ha : a ≠ 0 := by
        dsimp [a]
        exact mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast hk))
          (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
      have he : Complex.exp a = 1 := by
        simpa [a] using Complex.exp_int_mul_two_pi_mul_I ((k : ℤ) - j)
      rw [integral_exp_mul_complex ha]
      simp [hk, he]

  have digit_pairing (b k : ℕ) (D R : Finset ℕ) :
      (∫ t in (0 : ℝ)..1, (∏ i : Fin k, ∑ d ∈ D, phase (d*b^(i:ℕ)) t) *
        star (∑ n ∈ R, phase n t)) =
      (((Fintype.piFinset (fun _ : Fin k => D)).filter
        (fun w => (∑ i : Fin k, w i * b ^ (i : ℕ)) ∈ R)).card : ℂ) := by
    classical
    let B := Fintype.piFinset (fun _ : Fin k => D)
    let v (w : Fin k → ℕ) := ∑ i, w i * b ^ (i : ℕ)
    have prod_phase (w : Fin k → ℕ) (t : ℝ) :
        (∏ i, phase (w i * b ^ (i : ℕ)) t) = phase (v w) t := by
      dsimp only [phase, v]
      rw [← Complex.exp_sum]
      congr 1
      push_cast
      rw [Finset.mul_sum, Finset.sum_mul]
    have expand (t : ℝ) :
        (∏ i : Fin k, ∑ d ∈ D, phase (d*b^(i:ℕ)) t) * star (∑ n ∈ R, phase n t) =
        ∑ s ∈ B, ∑ n ∈ R, phase (v s) t * star (phase n t) := by
      rw [Finset.prod_univ_sum]
      simp_rw [prod_phase]
      rw [star_sum, Finset.sum_mul_sum]
    have hint (s : Fin k → ℕ) (n : ℕ) :
        IntervalIntegrable (fun t => phase (v s) t * star (phase n t)) MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable
      dsimp only [phase]
      fun_prop
    have outer (s : Fin k → ℕ) :
        IntervalIntegrable (fun t => ∑ n ∈ R, phase (v s) t * star (phase n t))
          MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable
      dsimp only [phase]
      fun_prop
    change (∫ t in (0 : ℝ)..1, (∏ i : Fin k, ∑ d ∈ D, phase (d*b^(i:ℕ)) t) *
      star (∑ n ∈ R, phase n t)) = ((B.filter (fun s => v s ∈ R)).card : ℂ)
    simp_rw [expand]
    rw [intervalIntegral.integral_finsetSum (fun s _ => outer s)]
    simp_rw [intervalIntegral.integral_finsetSum (fun n _ => hint _ n), phase_orth]
    simp

  dsimp only
  intro b hb
  obtain ⟨u, A, hu, hu1, hA, hlow⟩ := hThin b hb
  obtain ⟨v, B, hv, hv1, hB, hhigh⟩ := hUnpaired b hb
  refine ⟨min u v, A + B, lt_min hu hv, lt_of_le_of_lt (min_le_left _ _) hu1,
    by linarith only [hA, hB], ?_⟩
  intro k D hD hsize R hR
  let W := Fintype.piFinset (fun _ : Fin k => D)
  let val := fun w : Fin k → ℕ => ∑ i : Fin k, w i * b ^ (i : ℕ)
  let P := fun n : ℕ => (Finset.range (n + 1)).filter fun p =>
        Nat.Prime p ∧ p ≤ n - p ∧ p.dist (n - p) ^ 3 ≤ n ^ 2
  let thin := W.filter fun w => Even (val w) ∧ (P (val w)).card ^ 2 ≤ val w
  let unpaired := W.filter fun w => Even (val w) ∧ val w < (P (val w)).card ^ 2 ∧
    ∀ p ∈ P (val w), ¬ Nat.Prime (val w - p)
  let hit := W.filter fun w => val w ∈ R
  have cover : hit ⊆ thin ∪ unpaired := by
    intro w hw
    obtain ⟨hwW, hwR⟩ := Finset.mem_filter.mp hw
    obtain ⟨heven, hbad⟩ := hR (val w) hwR
    by_cases hs : (P (val w)).card ^ 2 ≤ val w
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwW, heven, hs⟩)
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hwW, heven, lt_of_not_ge hs, ?_⟩)
      intro p hp hq
      obtain ⟨hrange, hpPrime, _, hdist⟩ := Finset.mem_filter.mp hp
      have hle : p ≤ val w := by
        have := Finset.mem_range.mp hrange
        omega
      exact hbad ⟨p, val w - p, hpPrime, hq, Nat.add_sub_of_le hle, hdist⟩
  have hcard : (hit.card : ℝ) ≤ (thin.card : ℝ) + (unpaired.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card cover).trans (Finset.card_union_le thin unpaired)
  let M : ℝ := 1 + (D.card : ℝ) ^ k
  have hM : 1 ≤ M := le_add_of_nonneg_right (by positivity : 0 ≤ (D.card : ℝ) ^ k)
  have lo : (thin.card : ℝ) ≤ A * M ^ (1-u) := hlow k D hD hsize
  have hi : (unpaired.card : ℝ) ≤ B * M ^ (1-v) := hhigh k D hD hsize
  have budget : (hit.card : ℝ) ≤ (A+B) * M ^ (1-min u v) := by
    rw [add_mul]
    apply hcard.trans (add_le_add (lo.trans ?_) (hi.trans ?_))
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hM (sub_le_sub_left (min_le_left u v) 1)) hA.le
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hM (sub_le_sub_left (min_le_right u v) 1)) hB.le
  change ‖∫ t in (0 : ℝ)..1, (∏ i : Fin k, ∑ d ∈ D, phase (d*b^(i:ℕ)) t) *
    star (∑ n ∈ R, phase n t)‖ ≤ _
  rw [digit_pairing]
  simpa [M, hit, W, val] using budget
