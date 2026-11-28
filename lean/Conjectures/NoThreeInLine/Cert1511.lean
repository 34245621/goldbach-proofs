import Mathlib

theorem Conjectures.NoThreeInLine.Cert1511 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+30<n ∧ z.2+22<n)).card=(n-30)*(n-22) := by
  intro n
  have h : (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+30<n ∧ z.2+22<n)) = (Finset.range (n-30)) ×ˢ (Finset.range (n-22)) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
    omega
  rw [h, Finset.card_product, Finset.card_range, Finset.card_range]
