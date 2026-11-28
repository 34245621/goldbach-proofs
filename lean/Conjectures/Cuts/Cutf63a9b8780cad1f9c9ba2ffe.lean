import Mathlib

-- child 1 zh: 对每个充分靠后的平方根长度以上的窗口，所有奇数的素数加二次幂表示总数至少是窗口长度的 1.3 倍。
-- child 1 en: On every sufficiently late window of length at least the square root of its start, the total number of representations of odd targets is at least thirteen tenths of the length.
-- child 2 zh: 在相同尺度的每个窗口，表示同一奇数的有序表示对总数至多是窗口长度的十三倍，允许一对中的两个表示相同。
-- child 2 en: On every sufficiently late window in the same range, the total number of ordered pairs of representations of the same odd target, including identical pairs, is at most thirteen times the window length.

theorem Conjectures.Cuts.Cutf63a9b8780cad1f9c9ba2ffe
    (h₁ : by
      classical
      exact let R := fun n : ℕ => ((Finset.Icc 1 (Nat.log 2 n)).filter (fun e => Nat.Prime (n - 2 ^ e))).card
            ∃ T : ℕ, ∀ X H : ℕ, T ≤ X → X ≤ H ^ 2 → H ≤ X →
              13 * H ≤ 10 * ∑ n ∈ (Finset.Ico X (X + H)).filter Odd, R n)
    (h₂ : by
      classical
      exact let R := fun n : ℕ => ((Finset.Icc 1 (Nat.log 2 n)).filter (fun e => Nat.Prime (n - 2 ^ e))).card
            ∃ T : ℕ, ∀ X H : ℕ, T ≤ X → X ≤ H ^ 2 → H ≤ X →
              (∑ n ∈ (Finset.Ico X (X + H)).filter Odd, (R n) ^ 2) ≤ 13 * H) : (by
  classical
  exact let R := fun n : ℕ => ((Finset.Icc 1 (Nat.log 2 n)).filter (fun e => Nat.Prime (n-2^e))).card; ∃ T : ℕ, ∀ X H : ℕ, T ≤ X → X ≤ H^2 → H ≤ X → 13*H ≤ 100*((Finset.Ico X (X+H)).filter (fun n => Odd n ∧ 0 < R n)).card) := by
  classical
  let R := fun n : ℕ => ((Finset.Icc 1 (Nat.log 2 n)).filter (fun e => Nat.Prime (n - 2 ^ e))).card
  obtain ⟨T₁, mass⟩ := h₁
  obtain ⟨T₂, pairs⟩ := h₂
  refine ⟨max T₁ T₂, ?_⟩
  intro X H hT hw hH
  by_cases hz : H = 0
  · simp [hz]
  let S := (Finset.Ico X (X + H)).filter Odd
  let A := S.filter (fun n => 0 < R n)
  have hsub : A ⊆ S := Finset.filter_subset _ _
  have hsum : (∑ n ∈ A, R n) = ∑ n ∈ S, R n := by
    apply Finset.sum_subset hsub
    intro n hn hna
    by_contra hne
    exact hna (Finset.mem_filter.mpr ⟨hn, Nat.pos_of_ne_zero hne⟩)
  have hfirst : 13 * H ≤ 10 * ∑ n ∈ A, R n := by
    rw [hsum]
    exact mass X H (le_trans (le_max_left _ _) hT) hw hH
  have hsecond : (∑ n ∈ A, (R n) ^ 2) ≤ 13 * H := by
    exact (Finset.sum_le_sum_of_subset hsub).trans (pairs X H (le_trans (le_max_right _ _) hT) hw hH)
  have hcs : (∑ n ∈ A, R n) ^ 2 ≤ A.card * ∑ n ∈ A, (R n) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq A (fun _ => (1 : ℕ)) R
  have hproduct : (13 * H) * (13 * H) ≤ (100 * A.card) * (13 * H) := calc
    (13 * H) * (13 * H) = (13 * H) ^ 2 := by ring
    _ ≤ (10 * ∑ n ∈ A, R n) ^ 2 := Nat.pow_le_pow_left hfirst 2
    _ = 100 * (∑ n ∈ A, R n) ^ 2 := by ring
    _ ≤ 100 * (A.card * (13 * H)) := Nat.mul_le_mul_left _ (hcs.trans (Nat.mul_le_mul_left _ hsecond))
    _ = (100 * A.card) * (13 * H) := by ring
  have hcard : 13 * H ≤ 100 * A.card := Nat.le_of_mul_le_mul_right hproduct (by positivity)
  simpa only [A, S, Finset.filter_filter] using hcard
