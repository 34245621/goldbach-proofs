import Mathlib

theorem Conjectures.NoThreeInLine.Cert83 :
    ∀ n : ℕ,
      (((Finset.range n).product (Finset.range n)).filter
        (fun z => z.1 + 16 < n ∧ z.2 + 6 < n)).card
        = (n - 16) * (n - 6) := by
  intro n
  change (((Finset.range n) ×ˢ (Finset.range n)).filter
      (fun z => z.1 + 16 < n ∧ z.2 + 6 < n)).card = (n - 16) * (n - 6)
  have hset : ((Finset.range n) ×ˢ (Finset.range n)).filter
      (fun z => z.1 + 16 < n ∧ z.2 + 6 < n)
        = (Finset.range (n - 16)) ×ˢ (Finset.range (n - 6)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [hset, Finset.card_product, Finset.card_range, Finset.card_range]
