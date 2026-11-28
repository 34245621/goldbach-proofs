import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic

/-! For each modulus q ≥ 2 the reduced pairs (a, b) with a, b < q form a finite nonempty set
(it contains (1, 1)), so f q · · attains a maximum on it (`Finset.exists_max_image`); choosing
such a maximizer for every q (and 0 otherwise) gives the two selector functions. -/

theorem Conjectures.Cuts.Task2381f715cb778cea010d810a : (∀ (x1 : Finset ℕ) (x2 : ℕ → ℕ → ℕ → ℝ), (∀ x3 ∈ x1, (2 : ℕ) ≤ x3) → ∃ (x4 : ℕ → ℕ) (x5 : ℕ → ℕ), ∀ x6 ∈ x1, x4 x6 < x6 ∧ x5 x6 < x6 ∧ (x4 x6).Coprime x6 ∧ (x5 x6).Coprime x6 ∧ ∀ (x8 x9 : ℕ), x8 < x6 → x9 < x6 → x8.Coprime x6 → x9.Coprime x6 → x2 x6 x8 x9 ≤ x2 x6 (x4 x6) (x5 x6)) := by
  intro S f hS
  classical
  have hex : ∀ q : ℕ, 2 ≤ q → ∃ p : ℕ × ℕ, p.1 < q ∧ p.2 < q ∧ p.1.Coprime q ∧ p.2.Coprime q ∧
      ∀ a b : ℕ, a < q → b < q → a.Coprime q → b.Coprime q → f q a b ≤ f q p.1 p.2 := by
    intro q hq
    have hne : (((Finset.range q) ×ˢ (Finset.range q)).filter
        (fun p : ℕ × ℕ => p.1.Coprime q ∧ p.2.Coprime q)).Nonempty := by
      refine ⟨(1, 1), ?_⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, by omega⟩, Nat.coprime_one_left q, Nat.coprime_one_left q⟩
    obtain ⟨p, hpT, hmax⟩ := Finset.exists_max_image _ (fun p : ℕ × ℕ => f q p.1 p.2) hne
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hpT
    refine ⟨p, hpT.1.1, hpT.1.2, hpT.2.1, hpT.2.2, fun a b ha hb hac hbc => hmax (a, b) ?_⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨ha, hb⟩, hac, hbc⟩
  refine ⟨fun q => if h : 2 ≤ q then (Classical.choose (hex q h)).1 else 0,
    fun q => if h : 2 ≤ q then (Classical.choose (hex q h)).2 else 0, ?_⟩
  intro q hq
  have h2 := hS q hq
  simp only [dif_pos h2]
  exact Classical.choose_spec (hex q h2)
