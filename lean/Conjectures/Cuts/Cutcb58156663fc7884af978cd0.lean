import Mathlib

-- child 1 zh: 在每个充分大的偶数 n，容许移位上截断到 √n 的第一目标表示数之和超过满容量的四分之一。
-- child 1 en: For each sufficiently large even n, the first-target representation counts capped at the integer square root fill more than a quarter of total capacity.
-- child 2 zh: 目标从 n 平移到 n+2 后，逐移位的截断表示数只计下降、不抵扣增长，下降量之和至多为同一满容量的四分之一。
-- child 2 en: Under translation by two the total downward change of the capped counts, ignoring all increases, is at most a quarter of total capacity.
theorem Conjectures.Cuts.Cutcb58156663fc7884af978cd0
    (h₁ :
      let G := fun m : ℕ => ((Finset.range (m + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m - p))).card
      let E := fun n : ℕ => (Finset.Icc 2 n).filter (fun e => (2 ^ e) ^ 2 ≤ n)
      let W := fun n m : ℕ => min (Nat.sqrt n) (G m)
      ∃ N : ℕ, ∀ n ≥ N, Even n →
        Nat.sqrt n * (E n).card < 4 * ∑ e ∈ E n, W n (n - 2 ^ e))
    (h₂ :
      let G := fun m : ℕ => ((Finset.range (m + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m - p))).card
      let E := fun n : ℕ => (Finset.Icc 2 n).filter (fun e => (2 ^ e) ^ 2 ≤ n)
      let W := fun n m : ℕ => min (Nat.sqrt n) (G m)
      ∃ N : ℕ, ∀ n ≥ N, Even n →
        4 * (∑ e ∈ E n, (W n (n - 2 ^ e) - W n (n + 2 - 2 ^ e))) ≤
          Nat.sqrt n * (E n).card) :
    (let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card; ∃ N : ℕ, ∀ n ≥ N, Even n → ∃ e : ℕ, 2 ≤ e ∧ (2^e)^2 ≤ n ∧ 0 < G (n-2^e) ∧ 0 < G (n+2-2^e)) := by
  classical
  let G := fun m : ℕ => ((Finset.range (m + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m - p))).card
  let E := fun n : ℕ => (Finset.Icc 2 n).filter (fun e => (2 ^ e) ^ 2 ≤ n)
  let W := fun n m : ℕ => min (Nat.sqrt n) (G m)
  obtain ⟨N₁, mass⟩ := h₁
  obtain ⟨N₂, loss⟩ := h₂
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn heven
  have hm : Nat.sqrt n * (E n).card < 4 * ∑ e ∈ E n, W n (n - 2 ^ e) :=
    mass n (le_trans (le_max_left _ _) hn) heven
  have hl : 4 * (∑ e ∈ E n, (W n (n - 2 ^ e) - W n (n + 2 - 2 ^ e))) ≤
      Nat.sqrt n * (E n).card := loss n (le_trans (le_max_right _ _) hn) heven
  by_contra hnone
  have heq : (∑ e ∈ E n, (W n (n - 2 ^ e) - W n (n + 2 - 2 ^ e))) =
      ∑ e ∈ E n, W n (n - 2 ^ e) := by
    apply Finset.sum_congr rfl
    intro e he
    have he' := Finset.mem_filter.mp he
    by_cases hleft : G (n - 2 ^ e) = 0
    · simp [W, hleft]
    · have hright : G (n + 2 - 2 ^ e) = 0 := by
        by_contra hpos
        exact hnone ⟨e, (Finset.mem_Icc.mp he'.1).1, he'.2,
          Nat.pos_of_ne_zero hleft, Nat.pos_of_ne_zero hpos⟩
      simp [W, hright]
  rw [heq] at hl
  exact (not_lt_of_ge hl) hm
