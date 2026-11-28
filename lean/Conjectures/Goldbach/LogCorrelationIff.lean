import Mathlib

namespace Conjectures.Goldbach

theorem LogCorrelationIff :
    ∀ n : ℕ,
      let w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k : ℝ) else 0
      0 < Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) ↔
        (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n) := by
  intro n
  let w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k : ℝ) else 0
  change 0 < Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) ↔ _
  have weight_pos {p : ℕ} (hp : Nat.Prime p) : 0 < w p := by
    have hone : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    simpa [w, hp] using Real.log_pos hone
  have weight_nonneg (p : ℕ) : 0 ≤ w p := by
    by_cases hp : Nat.Prime p
    · exact (weight_pos hp).le
    · simp [w, hp]
  have term_nonneg : ∀ p ∈ Finset.range (n + 1), 0 ≤ w p * w (n - p) :=
    fun p _ => mul_nonneg (weight_nonneg p) (weight_nonneg (n - p))
  constructor
  · intro hsum
    obtain ⟨p, hmem, hpos⟩ := (Finset.sum_pos_iff_of_nonneg term_nonneg).mp hsum
    have hp : Nat.Prime p := by
      by_contra hp
      simpa [w, hp] using hpos
    have hq : Nat.Prime (n - p) := by
      by_contra hq
      simpa [w, hq] using hpos
    have hbound := Finset.mem_range.mp hmem
    exact ⟨p, n - p, hp, hq, by omega⟩
  · rintro ⟨p, q, hp, hq, hsum⟩
    have hmem : p ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have hsub : n - p = q := by omega
    have hpos : 0 < w p * w (n - p) := by
      rw [hsub]
      exact mul_pos (weight_pos hp) (weight_pos hq)
    exact hpos.trans_le (Finset.single_le_sum term_nonneg hmem)

end Conjectures.Goldbach
