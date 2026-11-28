import Mathlib

-- child 1 zh: 在中央粗筛候选集上，反射 Möbius 和最终以固定正余量低于候选数的五分之二。
-- child 1 en: On the central sifted candidates the reflected Moebius sum eventually stays below two fifths of the count by a fixed positive fraction of that count.
-- child 2 zh: 在充分大的偶数上，补数含平方因子的候选数占全部中央粗筛候选数的比例可任意小。
-- child 2 en: For each positive tolerance the number of candidates with a nonsquarefree complement is eventually at most that fraction of all central sifted candidates along even targets.

theorem Conjectures.Cuts.Cut9cfcbdade396c22b4be2ba03
    (hMobius :
      let C := fun N : ℕ => (Finset.range N).filter (fun p =>
        Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧ 1 < N-p ∧ N < (N-p).minFac^5)
      ∃ δ : ℝ, 0 < δ ∧ δ < 2/5 ∧ ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → Even N →
        (C N).sum (fun p => (ArithmeticFunction.moebius (N-p) : ℝ)) ≤
          (2/5 - δ) * ((C N).card : ℝ))
    (hSquares :
      let C := fun N : ℕ => (Finset.range N).filter (fun p =>
        Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧ 1 < N-p ∧ N < (N-p).minFac^5)
      ∀ ε : ℝ, 0 < ε → ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N → Even N →
        (((C N).filter (fun p => ¬ Squarefree (N-p))).card : ℝ) ≤
          ε * ((C N).card : ℝ)) :
    (let C := fun N : ℕ => (Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧ 1 < N-p ∧ N < (N-p).minFac^5); ∃ η : ℝ, 0 < η ∧ η < 2/5 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → (C N).sum (fun p => (ArithmeticFunction.liouville (N-p) : ℝ)) ≤ (2/5-η)*((C N).card:ℝ)) := by
  classical
  intro C
  obtain ⟨δ, hδ, hδlt, N₁, h₁⟩ := hMobius
  obtain ⟨N₂, h₂⟩ := hSquares (δ / 2) (by positivity)
  refine ⟨δ / 2, by positivity, by linarith, max N₁ N₂, ?_⟩
  intro N hN heven
  let S := C N
  have hM : S.sum (fun p => (ArithmeticFunction.moebius (N-p) : ℝ)) ≤
      (2/5 - δ) * (S.card : ℝ) :=
    h₁ N ((le_max_left N₁ N₂).trans hN) heven
  have hD : ((S.filter (fun p => ¬ Squarefree (N-p))).card : ℝ) ≤
      (δ / 2) * (S.card : ℝ) :=
    h₂ N ((le_max_right N₁ N₂).trans hN) heven
  have pointwise (m : ℕ) :
      (ArithmeticFunction.liouville m : ℝ) ≤
        (ArithmeticFunction.moebius m : ℝ) + (if ¬ Squarefree m then 1 else 0) := by
    by_cases hm : m = 0
    · subst m
      norm_num
    by_cases hs : Squarefree m
    · simp [hs, ArithmeticFunction.liouville_apply hm,
        ArithmeticFunction.moebius_apply_of_squarefree hs]
    · have hsign : ((-1 : ℤ) ^ ArithmeticFunction.cardFactors m) ≤ 1 := by
        calc
          _ ≤ |(-1 : ℤ) ^ ArithmeticFunction.cardFactors m| := le_abs_self _
          _ = 1 := by simp [abs_pow]
      rw [ArithmeticFunction.liouville_apply hm,
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
      simpa [hs] using (show (((-1 : ℤ) ^ ArithmeticFunction.cardFactors m : ℤ) : ℝ) ≤ 1
        from by exact_mod_cast hsign)
  calc
    S.sum (fun p => (ArithmeticFunction.liouville (N-p) : ℝ)) ≤
        S.sum (fun p => (ArithmeticFunction.moebius (N-p) : ℝ) +
          (if ¬ Squarefree (N-p) then 1 else 0)) :=
      Finset.sum_le_sum (fun p _ => pointwise (N-p))
    _ = S.sum (fun p => (ArithmeticFunction.moebius (N-p) : ℝ)) +
        ((S.filter (fun p => ¬ Squarefree (N-p))).card : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.natCast_card_filter]
    _ ≤ (2/5 - δ) * (S.card : ℝ) + (δ / 2) * (S.card : ℝ) := by
      linarith only [hM, hD]
    _ = (2/5 - δ / 2) * (S.card : ℝ) := by ring
