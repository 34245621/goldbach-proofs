import Mathlib

theorem Conjectures.NoThreeInLine.Cert1715 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+34<n ∧ z.2+30<n)).card=(n-34)*(n-30) := by
  intro n
  change ((Finset.range n ×ˢ Finset.range n).filter _).card = _
  have starts :
      (Finset.range n ×ˢ Finset.range n).filter
          (fun z => z.1 + 34 < n ∧ z.2 + 30 < n) =
        Finset.range (n - 34) ×ˢ Finset.range (n - 30) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [starts]
  simp only [Finset.card_product, Finset.card_range]
