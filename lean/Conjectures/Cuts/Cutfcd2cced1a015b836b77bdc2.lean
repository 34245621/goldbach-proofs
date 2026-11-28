import Mathlib

open scoped Pointwise

-- child 1 zh: 设 h=(log x)²，P 为 (x/2,(x+123h)/2] 中的奇素数。对每个 x≥2，证明 |P|² 至少为 a h，其中 a 是统一的正常数。
-- child 1 en: For every x at least 2, let h be log squared and P the odd primes in (x/2,(x+123h)/2]. Bound the squared size of P below by a fixed positive multiple of h.
-- child 2 zh: 对同一区间中的奇素数集 P，证明同和有序四元组数至多为 |P|²+|P|⁴/h 的一个固定正常数倍。
-- child 2 en: For the odd primes P in the same interval, bound the number of ordered equal-sum quadruples by a fixed positive multiple of the squared size plus the fourth power of the size divided by h.

theorem Conjectures.Cuts.Cutfcd2cced1a015b836b77bdc2
    (abundance : ∃ a : ℝ, 0 < a ∧ ∀ x : ℝ, 2 ≤ x →
      let h := (Real.log x)^2
      let P := (Finset.Ioc ⌊x/2⌋₊ ⌊(x + 123*h)/2⌋₊).filter
        (fun p : ℕ => p.Prime ∧ Odd p)
      a * h ≤ (P.card : ℝ)^2)
    (collisions : ∃ b : ℝ, 0 < b ∧ ∀ x : ℝ, 2 ≤ x →
      let h := (Real.log x)^2
      let P := (Finset.Ioc ⌊x/2⌋₊ ⌊(x + 123*h)/2⌋₊).filter
        (fun p : ℕ => p.Prime ∧ Odd p)
      let pairs := (P.card : ℝ)^2
      (Finset.addEnergy P P : ℝ) * h ≤ b * (pairs * h + pairs^2)) :
    (let good := fun n : ℕ => ∃ p q : ℕ, Nat.Prime p ∧ Odd p ∧ Nat.Prime q ∧ Odd q ∧ p + q = n
     ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 2 ≤ x →
       let h := (Real.log x)^2
       let W := Finset.Ioc ⌊x⌋₊ ⌊x + 123*h⌋₊
       1 + ⌊c*h⌋₊ ≤ (@Finset.filter ℕ good (Classical.decPred good) W).card) := by
  classical
  intro good
  obtain ⟨a, ha, hcount⟩ := abundance
  obtain ⟨b, hb, hcoll⟩ := collisions
  let D := b * (1 + a)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨a / (2*D), by positivity, ?_⟩
  intro x hx h W
  let I := Finset.Ioc ⌊x/2⌋₊ ⌊(x + 123*h)/2⌋₊
  let P := I.filter (fun p : ℕ => p.Prime ∧ Odd p)
  let pairs := (P.card : ℝ)^2
  let energy := (Finset.addEnergy P P : ℝ)
  let sums := ((P + P).card : ℝ)
  have hh : 0 < h := sq_pos_of_pos (Real.log_pos (by linarith : 1 < x))
  have hmass : a*h ≤ pairs := hcount x hx
  have hpairs : 0 < pairs := (mul_pos ha hh).trans_le hmass
  have henergy : energy*h ≤ b*(pairs*h + pairs^2) := hcoll x hx
  have hpairCast : pairs = ((P.card^2 : ℕ) : ℝ) := (Nat.cast_pow P.card 2).symm
  have hdiag : pairs ≤ energy := calc
    pairs = ((P.card^2 : ℕ) : ℝ) := hpairCast
    _ ≤ energy := Nat.cast_le.mpr (Finset.le_addEnergy_self (s := P))
  have hcs : pairs^2 ≤ sums * energy := calc
    pairs^2 = pairs*pairs := pow_two pairs
    _ = ((P.card^2 : ℕ) : ℝ)*((P.card^2 : ℕ) : ℝ) :=
      congrArg₂ (fun u v : ℝ => u*v) hpairCast hpairCast
    _ = ((P.card^2 * P.card^2 : ℕ) : ℝ) := (Nat.cast_mul _ _).symm
    _ ≤ (((P+P).card * Finset.addEnergy P P : ℕ) : ℝ) :=
      Nat.cast_le.mpr (Finset.le_card_add_mul_addEnergy P P)
    _ = sums * energy := Nat.cast_mul _ _
  have hbudget : a*(pairs*h + pairs^2) ≤ (1+a)*pairs^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hmass hpairs.le]
  have hscaled : a*h*energy ≤ D*sums*energy := calc
    _ = a*(energy*h) := by ring
    _ ≤ a*(b*(pairs*h + pairs^2)) := mul_le_mul_of_nonneg_left henergy ha.le
    _ = b*(a*(pairs*h + pairs^2)) := by ring
    _ ≤ b*((1+a)*pairs^2) := mul_le_mul_of_nonneg_left hbudget hb.le
    _ = D*pairs^2 := by dsimp [D]; ring
    _ ≤ D*(sums*energy) := mul_le_mul_of_nonneg_left hcs hD.le
    _ = D*sums*energy := by ring
  have hdensity : a*h ≤ D*sums :=
    le_of_mul_le_mul_right hscaled (hpairs.trans_le hdiag)
  have hstrict : a/(2*D)*h < sums := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < 2*D)]
    nlinarith only [hdensity, mul_pos ha hh]
  have endpoints (p : ℕ) (hp : p ∈ I) :
      x/2 < (p : ℝ) ∧ (p : ℝ) ≤ (x + 123*h)/2 := by
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hp
    exact ⟨Nat.lt_of_floor_lt hlo,
      (Nat.cast_le.mpr hhi).trans (Nat.floor_le (by linarith))⟩
  have hsubset : P + P ⊆ @Finset.filter ℕ good (Classical.decPred good) W := by
    intro n hn
    obtain ⟨p, hp, q, hq, rfl⟩ := Finset.mem_add.mp hn
    obtain ⟨hIp, hpp, hpo⟩ := Finset.mem_filter.mp hp
    obtain ⟨hIq, hqp, hqo⟩ := Finset.mem_filter.mp hq
    obtain ⟨hpl, hpu⟩ := endpoints p hIp
    obtain ⟨hql, hqu⟩ := endpoints q hIq
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, p, q, hpp, hpo, hqp, hqo, rfl⟩
    · apply (Nat.floor_lt (by linarith : 0 ≤ x)).mpr
      push_cast
      linarith
    · apply Nat.le_floor
      push_cast
      linarith
  have hfloor : ⌊a/(2*D)*h⌋₊ < (P + P).card :=
    (Nat.floor_lt (by positivity)).mpr hstrict
  have hcard := Finset.card_le_card hsubset
  omega
