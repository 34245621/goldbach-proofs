import Mathlib

theorem Conjectures.Cuts.Task8691fedee32e90b5ba19ee70 : (∀ d c k : ℕ, d.Coprime 6 → ((d*k+c) % 6=4 ↔ k % 6=(if d % 6=1 then (10-c % 6) % 6 else (c % 6+2) % 6))) := by
  intro d c k h
  have cop : Nat.Coprime (d % 6) 6 := by simpa [Nat.Coprime, Nat.gcd_rec 6 d] using h
  rw [Nat.add_mod, Nat.mul_mod]
  generalize hd : d % 6 = a at *
  generalize hc : c % 6 = b at *
  generalize hk : k % 6 = u at *
  have ha : a < 6 := hd ▸ Nat.mod_lt _ (by decide)
  have hb : b < 6 := hc ▸ Nat.mod_lt _ (by decide)
  have hu : u < 6 := hk ▸ Nat.mod_lt _ (by decide)
  have hcases : a = 1 ∨ a = 5 := by interval_cases a <;> norm_num [Nat.Coprime,Nat.gcd] at *
  rcases hcases with rfl | rfl <;> norm_num <;> omega
