import Mathlib

theorem Conjectures.NoThreeInLine.Cert111 :
    ∀ n:ℕ, (((Finset.range n) ×ˢ (Finset.range n)).filter (fun z => z.1+22<n ∧ z.2+2<n)).card=(n-22)*(n-2) := by
  intro n
  have h : (((Finset.range n) ×ˢ (Finset.range n)).filter (fun z : ℕ × ℕ => z.1+22<n ∧ z.2+2<n))
      = (Finset.range (n-22)) ×ˢ (Finset.range (n-2)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [h, Finset.card_product, Finset.card_range, Finset.card_range]
