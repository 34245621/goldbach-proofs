import Mathlib

theorem Conjectures.NoThreeInLine.Cert72 :
    ∀ n : ℕ,
      (((Finset.range n).product (Finset.range n)).filter
        (fun z => z.1 + 14 < n ∧ z.2 + 4 < n)).card
        = (n - 14) * (n - 4) := by
  intro n
  change (((Finset.range n) ×ˢ (Finset.range n)).filter
      (fun z => z.1 + 14 < n ∧ z.2 + 4 < n)).card = (n - 14) * (n - 4)
  have hset : ((Finset.range n) ×ˢ (Finset.range n)).filter
      (fun z => z.1 + 14 < n ∧ z.2 + 4 < n)
        = (Finset.range (n - 14)) ×ˢ (Finset.range (n - 4)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [hset, Finset.card_product, Finset.card_range, Finset.card_range]
