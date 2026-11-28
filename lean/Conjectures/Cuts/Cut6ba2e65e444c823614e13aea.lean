import Mathlib

-- child 1 zh: 对任意 m 元自然数集，证明同和有序四元组数至多为 4m²+8Q，其中 Q 只计 a<b<c<d 且 a+d=b+c 的构型。
-- child 1 en: For any m-element set of naturals, bound ordered equal-sum quadruples by 4m squared plus eight times the number of increasing quadruples with equal outer and inner sums.
-- child 2 zh: 令 h=(log x)²，对半宽短窗内的 m 个奇素数，证明 a<b<c<d 且 a+d=b+c 的构型数至多是 m²+m⁴/h 的某个固定正常数倍。
-- child 2 en: Bound increasing equal-sum quadruples of odd primes in the half window by a uniform multiple of the squared prime count plus its fourth power divided by log squared.

theorem Conjectures.Cuts.Cut6ba2e65e444c823614e13aea
    (ordered : ∀ A : Finset ℕ,
      let Q := ((A.product A).product (A.product A)).filter
        (fun t => t.1.1 < t.1.2 ∧ t.1.2 < t.2.1 ∧ t.2.1 < t.2.2 ∧
          t.1.1 + t.2.2 = t.1.2 + t.2.1)
      A.addEnergy A ≤ 4*A.card^2 + 8*Q.card)
    (patterns : ∃ k : ℝ, 0 < k ∧ ∀ x : ℝ, 2 ≤ x →
      let h := (Real.log x)^2
      let P := (Finset.Ioc ⌊x/2⌋₊ ⌊(x+123*h)/2⌋₊).filter (fun p : ℕ => p.Prime ∧ Odd p)
      let pairs := (P.card : ℝ)^2
      let Q := ((P.product P).product (P.product P)).filter
        (fun t => t.1.1 < t.1.2 ∧ t.1.2 < t.2.1 ∧ t.2.1 < t.2.2 ∧
          t.1.1 + t.2.2 = t.1.2 + t.2.1)
      (Q.card : ℝ)*h ≤ k*(pairs*h + pairs^2)) :
    (∃ b : ℝ, 0 < b ∧ ∀ x : ℝ, 2 ≤ x →
      let h := (Real.log x)^2
      let P := (Finset.Ioc ⌊x/2⌋₊ ⌊(x+123*h)/2⌋₊).filter (fun p : ℕ => p.Prime ∧ Odd p)
      let pairs := (P.card : ℝ)^2
      (P.addEnergy P : ℝ)*h ≤ b*(pairs*h + pairs^2)) := by
  obtain ⟨k, hk, hkx⟩ := patterns
  refine ⟨4+8*k, by positivity, ?_⟩
  intro x hx h P pairs
  let Q := ((P.product P).product (P.product P)).filter
    (fun t => t.1.1 < t.1.2 ∧ t.1.2 < t.2.1 ∧ t.2.1 < t.2.2 ∧
      t.1.1 + t.2.2 = t.1.2 + t.2.1)
  have hQ : (Q.card : ℝ)*h ≤ k*(pairs*h + pairs^2) := hkx x hx
  have hcount : P.addEnergy P ≤ 4*P.card^2 + 8*Q.card := ordered P
  have castCount (m r : ℕ) : ((4*m^2 + 8*r : ℕ) : ℝ) = 4*(m : ℝ)^2 + 8*(r : ℝ) := by
    push_cast <;> rfl
  have hE : (P.addEnergy P : ℝ) ≤ 4*pairs + 8*(Q.card : ℝ) := calc
    _ ≤ ((4*P.card^2 + 8*Q.card : ℕ) : ℝ) := Nat.cast_le.mpr hcount
    _ = _ := castCount _ _
  have hh : 0 ≤ h := sq_nonneg _
  calc
    (P.addEnergy P : ℝ)*h ≤ (4*pairs + 8*(Q.card : ℝ))*h :=
      mul_le_mul_of_nonneg_right hE hh
    _ ≤ (4+8*k)*(pairs*h + pairs^2) := by nlinarith only [hQ, sq_nonneg pairs]
