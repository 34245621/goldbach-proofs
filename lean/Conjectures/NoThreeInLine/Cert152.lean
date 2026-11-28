import Mathlib

theorem Conjectures.NoThreeInLine.Cert152 :
    ∀ n:ℕ, (((Finset.range n) ×ˢ (Finset.range n)).filter (fun z => z.1+30<n ∧ z.2+4<n)).card=(n-30)*(n-4) := by
  intro n
  have h : (((Finset.range n) ×ˢ (Finset.range n)).filter (fun z : ℕ × ℕ => z.1+30<n ∧ z.2+4<n))
      = (Finset.range (n-30)) ×ˢ (Finset.range (n-4)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [h, Finset.card_product, Finset.card_range, Finset.card_range]
