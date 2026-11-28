import Mathlib

theorem Conjectures.NoThreeInLine.Cert95 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+18<n ∧ z.2+10<n)).card=(n-18)*(n-10) := by
  intro n
  have h : (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+18<n ∧ z.2+10<n)) = (Finset.range (n-18)) ×ˢ (Finset.range (n-10)) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
    omega
  rw [h, Finset.card_product, Finset.card_range, Finset.card_range]
