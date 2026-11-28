import Mathlib

theorem Conjectures.NoThreeInLine.Cert1914 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+38<n ∧ z.2+28<n)).card=(n-38)*(n-28) := by
  intro n
  have starts :
      (((Finset.range n).product (Finset.range n)).filter
        (fun z => z.1 + 38 < n ∧ z.2 + 28 < n)) =
        (Finset.range (n - 38)).product (Finset.range (n - 28)) := by
    ext ⟨x, y⟩
    simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [starts, Finset.product_eq_sprod, Finset.card_product, Finset.card_range, Finset.card_range]
