import Mathlib

theorem Conjectures.Cuts.Taskecdd7ada3a577e3f6f4cc77d : (∀ (x1 x2 x3 x4 : ℕ), x2 < x1 → x3 < x1 → x4 % x1 = (x2 + x3) % x1 → ((∃ (x8 : ℕ) (x9 : ℕ), Nat.Prime x8 ∧ Nat.Prime x9 ∧ x8 + x9 = x4 ∧ x8 % x1 = x2 ∧ x9 % x1 = x3) ↔ ∃ x8 ∈ Finset.Icc (2 : ℕ) x4, Nat.Prime x8 ∧ x8 % x1 = x2 ∧ Nat.Prime (x4 - x8))) := by
  intro m a b n ha hb hn
  constructor
  · rintro ⟨p, q, hp, hq, rfl, hpa, _⟩
    exact ⟨p, Finset.mem_Icc.mpr ⟨hp.two_le, Nat.le_add_right p q⟩,
      hp, hpa, by simpa using hq⟩
  · rintro ⟨p, hpn, hp, hpa, hq⟩
    have hsum : p + (n - p) = n := by
      have := (Finset.mem_Icc.mp hpn).2
      omega
    have hpmod : Nat.ModEq m p a := by
      change p % m = a % m
      rwa [Nat.mod_eq_of_lt ha]
    have htotal : Nat.ModEq m (p + (n - p)) (a + b) := by
      rw [hsum]
      exact hn
    have hqmod := hpmod.add_left_cancel htotal
    change (n - p) % m = b % m at hqmod
    exact ⟨p, n - p, hp, hq, hsum, hpa, hqmod.trans (Nat.mod_eq_of_lt hb)⟩
