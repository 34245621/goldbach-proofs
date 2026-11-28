import Mathlib
import Conjectures.Cuts.Task99950cab5c8977334dbea5e5

/-!
The coarse positive-shift correlation is bounded below by the square of
the mass in nonzero residue classes, after allowing for the diagonal.
The exact expansion of squared residue masses is the verified companion
lemma Task99950cab5c8977334dbea5e5.
-/

open Finset Filter

private noncomputable def shiftCorrelation (w : ℕ → ℝ) (X q : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ((X - 1) / q),
    ∑ k ∈ Finset.range (X - q * d), w k * w (k + q * d)

private noncomputable def nonzeroResidueMass (w : ℕ → ℝ) (X p : ℕ) : ℝ :=
  ∑ k ∈ Finset.range X with ¬ p ∣ k, w k

private noncomputable def residueMass (w : ℕ → ℝ) (X p a : ℕ) : ℝ :=
  ∑ k ∈ Finset.range X with Nat.mod k p = a, w k

private theorem residueMassCauchy (w : ℕ → ℝ) (X p : ℕ) (hp : 0 < p) :
    nonzeroResidueMass w X p ^ 2 ≤
      ((p : ℝ) - 1) * ∑ a ∈ Finset.range p, residueMass w X p a ^ 2 := by
  let nonzero := (Finset.range p).erase 0
  let coprime := (Finset.range X).filter (fun k => ¬ p ∣ k)
  have fibers (k : ℕ) (hk : k ∈ coprime) : Nat.mod k p ∈ nonzero :=
    Finset.mem_erase.mpr
      ⟨fun hz => (Finset.mem_filter.mp hk).2 (Nat.dvd_iff_mod_eq_zero.mpr hz),
       Finset.mem_range.mpr (Nat.mod_lt k hp)⟩
  have massSum : (∑ a ∈ nonzero, residueMass w X p a) = nonzeroResidueMass w X p := by
    calc
      _ = ∑ a ∈ nonzero, ∑ k ∈ coprime with Nat.mod k p = a, w k := by
        apply Finset.sum_congr rfl
        intro a ha
        have ha0 := (Finset.mem_erase.mp ha).1
        unfold residueMass
        congr 1
        ext k
        simp only [coprime, Finset.mem_filter]
        constructor
        · rintro ⟨hk, he⟩
          exact ⟨⟨hk, fun hd => ha0 (he.symm.trans (Nat.dvd_iff_mod_eq_zero.mp hd))⟩, he⟩
        · rintro ⟨⟨hk, _⟩, he⟩
          exact ⟨hk, he⟩
      _ = _ := Finset.sum_fiberwise_of_maps_to fibers w
  have count : (nonzero.card : ℝ) = (p : ℝ) - 1 := by
    rw [show nonzero.card = p - 1 by
      simp [nonzero, Finset.card_erase_of_mem (Finset.mem_range.mpr hp)]]
    rw [Nat.cast_sub (Nat.succ_le_iff.mpr hp), Nat.cast_one]
  have nonzeroSquares :
      (∑ a ∈ nonzero, residueMass w X p a ^ 2) ≤
        ∑ a ∈ Finset.range p, residueMass w X p a ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset 0 _) (by
      intro a _ _
      exact sq_nonneg _)
  have pOne : (1 : ℝ) ≤ p := by exact_mod_cast hp
  calc
    _ = (∑ a ∈ nonzero, residueMass w X p a) ^ 2 := by rw [massSum]
    _ ≤ (nonzero.card : ℝ) * ∑ a ∈ nonzero, residueMass w X p a ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ _ := by
      rw [count]
      exact mul_le_mul_of_nonneg_left nonzeroSquares (sub_nonneg.mpr pOne)

private theorem coarseShortfall (w : ℕ → ℝ) (X p : ℕ) (hp : 1 < p) :
    nonzeroResidueMass w X p ^ 2 / (2 * (p : ℝ) * ((p : ℝ) - 1)) -
      shiftCorrelation w X p / (p : ℝ) ≤
        (∑ k ∈ Finset.range X, w k ^ 2) / (2 * (p : ℝ)) := by
  let V := ∑ a ∈ Finset.range p, residueMass w X p a ^ 2
  let D := ∑ k ∈ Finset.range X, w k ^ 2
  have pReal : (1 : ℝ) < p := by exact_mod_cast hp
  have pPos : (0 : ℝ) < p := by linarith
  have Vsplit : V = D + 2 * shiftCorrelation w X p :=
    Conjectures.Cuts.Task99950cab5c8977334dbea5e5 w X p (by omega)
  have massBound : nonzeroResidueMass w X p ^ 2 / ((p : ℝ) - 1) ≤ V := by
    apply (div_le_iff₀ (sub_pos.mpr pReal)).2
    rw [mul_comm]
    exact residueMassCauchy w X p (by omega)
  have mainBound : nonzeroResidueMass w X p ^ 2 / (2 * (p : ℝ) * ((p : ℝ) - 1)) ≤
      V / (2 * (p : ℝ)) := by
    calc
      _ = (nonzeroResidueMass w X p ^ 2 / ((p : ℝ) - 1)) / (2 * (p : ℝ)) := by
        rw [div_div, mul_comm ((p : ℝ) - 1)]
      _ ≤ _ := div_le_div_of_nonneg_right massBound (by positivity)
  change _ ≤ D / (2 * (p : ℝ))
  calc
    _ ≤ V / (2 * (p : ℝ)) - shiftCorrelation w X p / (p : ℝ) :=
      sub_le_sub_right mainBound _
    _ = _ := by
      rw [Vsplit]
      ring

private theorem mangoldtDiagonalLe (N X : ℕ) (hX : X ≤ N) :
    (∑ k ∈ Finset.range X, ArithmeticFunction.vonMangoldt k ^ 2) ≤
      (N : ℝ) * Real.log (N : ℝ) ^ 2 := by
  calc
    _ ≤ ∑ _k ∈ Finset.range X, Real.log (N : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hk0 : k = 0
      · subst k
        simpa using sq_nonneg (Real.log (N : ℝ))
      · have kPos : 0 < (k : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hk0)
        have kLe : (k : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hk).le.trans hX
        exact pow_le_pow_left₀ ArithmeticFunction.vonMangoldt_nonneg
          (ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log kPos kLe)) 2
    _ = (X : ℝ) * Real.log (N : ℝ) ^ 2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hX) (sq_nonneg _)

theorem Conjectures.Cuts.Taskee6ccf76eddb18ca90726957 :
    (have x1 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x1 : ℕ → ℝ) (x2 x3 : ℕ) => ∑ x4 ∈ Finset.Icc (1 : ℕ) ((x2 - (1 : ℕ)) / x3), ∑ x5 ∈ Finset.range (x2 - x3 * x4), x1 x5 * x1 (x5 + x3 * x4); have x2 : ℕ → ℕ → ℝ := fun (x2 x3 : ℕ) => (∑ x4 ∈ Finset.range x2 with ¬x3 ∣ x4, ArithmeticFunction.vonMangoldt x4) ^ (2 : ℕ) / ((2 : ℝ) * ↑x3 * (↑x3 - (1 : ℝ))); ∀ (x3 : ℝ), (0 : ℝ) < x3 → ∃ (x5 : ℕ), ∀ (x6 x7 : ℕ), x5 ≤ x6 → (2 : ℕ) ≤ x6 → Nat.Prime x7 → (x7 ^ (2 : ℕ)) ^ (2 : ℕ) ≤ x6 → x6 ≤ (4 : ℕ) * (x7 ^ (2 : ℕ)) ^ (2 : ℕ) → ∀ x13 ≤ x6, x2 x13 x7 - x1 (fun (x15 : ℕ) => ArithmeticFunction.vonMangoldt x15) x13 x7 / ↑x7 ≤ ↑x6 ^ ((1 : ℝ) + x3) / (2 : ℝ)) := by
  intro corr main ε hε
  have eventuallyLog : ∀ᶠ n : ℕ in atTop,
      ‖Real.log (n : ℝ) ^ (2 : ℝ)‖ ≤ 1 * ‖(n : ℝ) ^ ε‖ := by
    exact (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      ((isLittleO_log_rpow_rpow_atTop 2 hε).bound (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp eventuallyLog
  refine ⟨N₀, ?_⟩
  intro N p hN hN2 hp _ _ X hX
  let w : ℕ → ℝ := fun k => ArithmeticFunction.vonMangoldt k
  let D := ∑ k ∈ Finset.range X, w k ^ 2
  have logBound : Real.log (N : ℝ) ^ 2 ≤ (N : ℝ) ^ ε := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (N : ℝ))),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) ε), one_mul] using hN₀ N hN
  have pOne : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have diagonalNonneg : 0 ≤ D := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have diagBound : D ≤ (N : ℝ) ^ (1 + ε) := by
    calc
      _ ≤ (N : ℝ) * Real.log (N : ℝ) ^ 2 := mangoldtDiagonalLe N X hX
      _ ≤ (N : ℝ) * (N : ℝ) ^ ε := mul_le_mul_of_nonneg_left logBound (by positivity)
      _ = _ := by
        rw [Real.rpow_add (by exact_mod_cast (show 0 < N by omega)), Real.rpow_one]
  change nonzeroResidueMass w X p ^ 2 / (2 * (p : ℝ) * ((p : ℝ) - 1)) -
    shiftCorrelation w X p / (p : ℝ) ≤ _
  calc
    _ ≤ D / (2 * (p : ℝ)) := coarseShortfall w X p hp.one_lt
    _ ≤ D / 2 := div_le_div_of_nonneg_left diagonalNonneg (by norm_num) (by linarith)
    _ ≤ _ := div_le_div_of_nonneg_right diagBound (by norm_num)
