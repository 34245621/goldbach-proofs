import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

-- child 1 zh: 在模数至少为平方根时，用剩余类的项数与欧拉函数直接证明无条件界。
-- child 1 en: Prove the unconditional estimate for large moduli by counting a residue class and bounding the totient.
-- child 2 zh: 在小模数范围控制各特征扭曲和扣去主项后的平均绝对误差。
-- child 2 en: For small moduli bound the mean absolute error of the character twists after subtracting the principal term.

open ArithmeticFunction
open scoped Classical in
theorem Conjectures.Cuts.Cut3cf101eed185c8da5bc478ec
    (hLarge : ∀ (x : ℝ) (d a : ℕ), 100 ≤ x → Real.sqrt x ≤ (d:ℝ) → |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => Nat.ModEq d n a), ArithmeticFunction.vonMangoldt n) - x / (Nat.totient d : ℝ)| ≤ Real.sqrt x * ((Real.log x) ^ 2 / (8 * Real.pi) + Real.log (d : ℝ) * Real.log x / (2 * Real.pi) + (3 / 4 : ℝ) * Real.log x + (1 / 2 : ℝ) * Real.log (d : ℝ)))
    (hSmall : (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0) → ∀ (x : ℝ) (d : ℕ) [NeZero d], 100 ≤ x → 3 ≤ d → (d:ℝ) < Real.sqrt x → (∑ χ : DirichletCharacter ℂ d, ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ)*χ n) - ((x:ℂ)/(d.totient:ℂ) * (∑ b : ZMod d, χ b))‖) ≤ (d.totient:ℝ)*(Real.sqrt x * ((Real.log x) ^ 2 / (8 * Real.pi) + Real.log (d : ℝ) * Real.log x / (2 * Real.pi) + (3 / 4 : ℝ) * Real.log x + (1 / 2 : ℝ) * Real.log (d : ℝ)))) :
    ((∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0) → ∀ (x : ℝ) (d a : ℕ), 100 ≤ x → 3 ≤ d → Nat.Coprime a d → |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => Nat.ModEq d n a), ArithmeticFunction.vonMangoldt n) - x / (Nat.totient d : ℝ)| ≤ Real.sqrt x * ((Real.log x) ^ 2 / (8 * Real.pi) + Real.log (d : ℝ) * Real.log x / (2 * Real.pi) + (3 / 4 : ℝ) * Real.log x + (1 / 2 : ℝ) * Real.log (d : ℝ))) := by
  classical
  have from_character_mean (d a : ℕ) [NeZero d] (ha : a.Coprime d)
      (I : Finset ℕ) (x B : ℝ)
      (H : ∑ χ : DirichletCharacter ℂ d, ‖(∑ n ∈ I, (vonMangoldt n : ℂ)*χ n) -
        (if χ = 1 then (x:ℂ) else 0)‖ ≤ (d.totient:ℝ)*B) :
      |(∑ n ∈ I.filter (fun n => Nat.ModEq d n a), vonMangoldt n) - x/(d.totient:ℝ)| ≤ B := by
    classical
    let A := (a:ZMod d)
    have hu : IsUnit A := (ZMod.isUnit_iff_coprime ..).mpr ha
    let coeff (χ : DirichletCharacter ℂ d) := χ A⁻¹
    let psi (χ : DirichletCharacter ℂ d) := ∑ n ∈ I, (vonMangoldt n : ℂ)*χ n
    let mean (χ : DirichletCharacter ℂ d) : ℂ := if χ = 1 then x else 0
    let ap := ∑ n ∈ I.filter (fun n => Nat.ModEq d n a), vonMangoldt n
    have hp : 0 < (d.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos d)
    have orth : ∑ χ : DirichletCharacter ℂ d, coeff χ * psi χ = (d.totient:ℂ) * (ap:ℂ) := by
      simp only [psi, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [ap, Complex.ofReal_sum, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hr : ∑ χ : DirichletCharacter ℂ d, coeff χ*χ n =
          if A = (n:ZMod d) then (d.totient:ℂ) else 0 := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu n
      calc
        (∑ χ : DirichletCharacter ℂ d, coeff χ*((vonMangoldt n : ℂ)*χ n)) =
            (∑ χ : DirichletCharacter ℂ d, coeff χ*χ n)*(vonMangoldt n:ℂ) := by
          rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro _ _; ring
        _ = _ := by
          rw [hr]
          by_cases ha' : Nat.ModEq d n a
          · have e : A = (n:ZMod d) := ((ZMod.natCast_eq_natCast_iff ..).mpr ha').symm
            simp [ha',e]
          · have e : A ≠ (n:ZMod d) := fun h => ha' ((ZMod.natCast_eq_natCast_iff ..).mp h.symm)
            simp [ha',e]
    have principal : ∑ χ : DirichletCharacter ℂ d, coeff χ * mean χ = (x:ℂ) := by
      simp only [mean, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      have hui : IsUnit A⁻¹ := by rw [← hu.unit_spec, ZMod.inv_coe_unit]; exact (hu.unit⁻¹).isUnit
      rw [show coeff 1 = 1 from MulChar.one_apply hui, one_mul]
    have eqn : ∑ χ : DirichletCharacter ℂ d, coeff χ*(psi χ-mean χ) = (d.totient:ℂ)*(ap:ℂ)-x := by
      simp only [mul_sub, Finset.sum_sub_distrib,orth,principal]
    have bound : ‖(d.totient:ℂ)*(ap:ℂ)-x‖ ≤ (d.totient:ℝ)*B := by
      rw [← eqn]
      refine (norm_sum_le ..).trans ((Finset.sum_le_sum (fun χ _ => ?_)).trans H)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
    have eqreal : (d.totient:ℂ)*(ap:ℂ)-x = (((d.totient:ℝ)*(ap-x/(d.totient:ℝ)):ℝ):ℂ) := by
      push_cast; field_simp [show (d.totient:ℂ) ≠ 0 by exact_mod_cast hp.ne']
    rw [eqreal, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hp] at bound
    exact (mul_le_mul_iff_right₀ hp).mp bound
  intro h x d a hx hd ha
  by_cases hq : Real.sqrt x ≤ (d:ℝ)
  · exact hLarge x d a hx hq
  · have hdpos : 0 < d := by omega
    let : NeZero d := ⟨hdpos.ne'⟩
    have center (χ : DirichletCharacter ℂ d) :
        (if χ = 1 then (x:ℂ) else 0) = (x:ℂ)/(d.totient:ℂ) * (∑ b : ZMod d, χ b) := by
      by_cases hχ : χ = 1
      · subst χ
        rw [if_pos rfl, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient,
          div_mul_cancel₀ _ (show (d.totient:ℂ) ≠ 0 by exact_mod_cast (Nat.totient_pos.mpr hdpos).ne')]
      · rw [if_neg hχ,MulChar.sum_eq_zero_of_ne_one hχ,mul_zero]
    apply from_character_mean d a ha _ x _
    simp only [center]
    exact
      (hSmall h x d hx hd (lt_of_not_ge hq))
