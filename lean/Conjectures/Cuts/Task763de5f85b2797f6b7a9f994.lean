import Mathlib

/-- A prime different from `2` and `3` is congruent to `1` or `5` modulo `6`. -/
private lemma six_mod (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have hlt : p % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hdec : p = 6 * (p / 6) + p % 6 := by
    have := Nat.div_add_mod p 6
    omega
  have h2d : ¬ 2 ∣ p := by
    intro h
    exact h2 ((hp.dvd_iff_eq (by norm_num)).mp h)
  have h3d : ¬ 3 ∣ p := by
    intro h
    exact h3 ((hp.dvd_iff_eq (by norm_num)).mp h)
  have hcases : p % 6 = 0 ∨ p % 6 = 1 ∨ p % 6 = 2 ∨ p % 6 = 3 ∨ p % 6 = 4 ∨ p % 6 = 5 := by
    omega
  rcases hcases with h | h | h | h | h | h
  · exact absurd ⟨3 * (p / 6), by omega⟩ h2d
  · exact Or.inl h
  · exact absurd ⟨3 * (p / 6) + 1, by omega⟩ h2d
  · exact absurd ⟨2 * (p / 6) + 1, by omega⟩ h3d
  · exact absurd ⟨3 * (p / 6) + 2, by omega⟩ h2d
  · exact Or.inr h

theorem Conjectures.Cuts.Task763de5f85b2797f6b7a9f994 : (have x1 : ℕ → Prop := fun (x1 : ℕ) => Nat.Prime x1 ∧ (x1 + (2 : ℕ)).primeFactorsList.length ≤ (2 : ℕ); ∀ (x2 : ℕ), (1 : ℕ) ≤ x2 → ((∃ (x4 : ℕ) (x5 : ℕ), x1 x4 ∧ x1 x5 ∧ x4 + x5 = (6 : ℕ) * x2 + (4 : ℕ)) ↔ x1 ((6 : ℕ) * x2 + (1 : ℕ)) ∨ ∃ (x4 : ℕ) (x5 : ℕ), x4 + x5 + (1 : ℕ) = x2 ∧ x1 ((6 : ℕ) * x4 + (5 : ℕ)) ∧ x1 ((6 : ℕ) * x5 + (5 : ℕ)))) := by
  intro x1 s hs
  constructor
  · rintro ⟨p, q, hp, hq, hsum⟩
    obtain ⟨hpp, hpq⟩ := hp
    obtain ⟨hqp, hqq⟩ := hq
    have hp2 : p ≠ 2 := by
      intro h
      subst h
      have hqeq : q = 6 * s + 2 := by omega
      have h2d : 2 ∣ q := ⟨3 * s + 1, by omega⟩
      have hq2 : q = 2 := (hqp.dvd_iff_eq (by norm_num)).mp h2d
      omega
    have hq2 : q ≠ 2 := by
      intro h
      subst h
      have hpeq : p = 6 * s + 2 := by omega
      have h2d : 2 ∣ p := ⟨3 * s + 1, by omega⟩
      have hp2' : p = 2 := (hpp.dvd_iff_eq (by norm_num)).mp h2d
      omega
    rcases eq_or_ne p 3 with hp3 | hp3
    · subst hp3
      have hqeq : q = 6 * s + 1 := by omega
      refine Or.inl ?_
      rw [← hqeq]
      exact ⟨hqp, hqq⟩
    · rcases eq_or_ne q 3 with hq3 | hq3
      · subst hq3
        have hpeq : p = 6 * s + 1 := by omega
        refine Or.inl ?_
        rw [← hpeq]
        exact ⟨hpp, hpq⟩
      · have hpdec : p = 6 * (p / 6) + p % 6 := by
          have := Nat.div_add_mod p 6
          omega
        have hqdec : q = 6 * (q / 6) + q % 6 := by
          have := Nat.div_add_mod q 6
          omega
        have hplt : p % 6 < 6 := Nat.mod_lt _ (by norm_num)
        have hqlt : q % 6 < 6 := Nat.mod_lt _ (by norm_num)
        rcases six_mod p hpp hp2 hp3 with hp1 | hp5
        · -- `p ≡ 1`: then `q ≡ 3 (mod 6)`, forcing `q = 3`
          exfalso
          have hq6 : q % 6 = 3 := by omega
          have h3d : 3 ∣ q := ⟨2 * (q / 6) + 1, by omega⟩
          have hqe : q = 3 := (hqp.dvd_iff_eq (by norm_num)).mp h3d
          omega
        · have hq6 : q % 6 = 5 := by omega
          refine Or.inr ⟨p / 6, q / 6, ?_, ?_, ?_⟩
          · omega
          · have hpdec' : p = 6 * (p / 6) + 5 := by omega
            rw [← hpdec']
            exact ⟨hpp, hpq⟩
          · have hqdec' : q = 6 * (q / 6) + 5 := by omega
            rw [← hqdec']
            exact ⟨hqp, hqq⟩
  · rintro (h | ⟨a, b, hab, ha, hb⟩)
    · refine ⟨3, 6 * s + 1, ?_, h, by omega⟩
      refine ⟨by norm_num, ?_⟩
      rw [show (3 + 2) = 5 from rfl, Nat.primeFactorsList_prime (by norm_num : Nat.Prime 5)]
      simp
    · refine ⟨6 * a + 5, 6 * b + 5, ha, hb, by omega⟩
