import Mathlib

theorem Conjectures.Cuts.Task9af5a49dc4a0c1dfbbd64ad9 : (∀ (x1 : Finset ℕ) (x2 : ℕ → ℝ) (x3 x4 x5 : ℝ), (0 : ℝ) < x3 → (0 : ℝ) ≤ x4 → (∀ x8 ∈ x1, (0 : ℝ) ≤ x2 x8) → (∑ x9 ∈ x1, x2 x9) * x4 ≤ x3 * x5 → ∃ x10 ⊆ x1, ↑x10.card * x4 ≤ x5 ∧ ∀ x11 ∈ x1, x11 ∉ x10 → x2 x11 ≤ x3) := by
  classical
  intro S f c w R hc hw hf hsum
  let T := S.filter (fun q => c < f q)
  have hsub : T ⊆ S := Finset.filter_subset _ _
  have hcount : (T.card : ℝ) * c ≤ ∑ q ∈ S, f q := by
    calc
      (T.card : ℝ) * c = ∑ _q ∈ T, c := by simp
      _ ≤ ∑ q ∈ T, f q := Finset.sum_le_sum fun q hq => (Finset.mem_filter.mp hq).2.le
      _ ≤ ∑ q ∈ S, f q := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq _ => hf q hq)
  refine ⟨T, hsub, ?_, ?_⟩
  · apply le_of_mul_le_mul_left _ hc
    calc
      c * ((T.card : ℝ) * w) = ((T.card : ℝ) * c) * w := by ring
      _ ≤ (∑ q ∈ S, f q) * w := mul_le_mul_of_nonneg_right hcount hw
      _ ≤ c * R := hsum
  · intro q hq hout
    exact le_of_not_gt (fun h => hout (Finset.mem_filter.mpr ⟨hq, h⟩))
