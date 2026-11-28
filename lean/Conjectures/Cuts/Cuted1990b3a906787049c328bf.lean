import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

-- child 1 zh: 用有限大筛对任意平移和连续权函数证明一致二阶矩上界。
-- child 1 en: Use the finite large sieve for a uniform second moment over all shifts and continuous weights.
-- child 2 zh: 在有理逼近分母的中间范围和小移位分母范围证明改进指数的二阶矩界。
-- child 2 en: Establish the improved exponent for interior rational-approximation denominators and small shift denominators.

theorem Conjectures.Cuts.Cuted1990b3a906787049c328bf
  (hUniform : let S := fun (w : ℝ → ℝ) (X t : ℝ) => ∑ n ∈ Finset.range (⌊X⌋₊+1), (((ArithmeticFunction.vonMangoldt n : ℝ)*w ((n : ℝ)/X) : ℝ) : ℂ)*Complex.exp (((2*Real.pi*(n : ℝ)*t : ℝ) : ℂ)*Complex.I); ∀ w : ℝ → ℝ, Continuous w → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X D x : ℝ, 2 ≤ X → 1 ≤ D → D ≤ X → (∑ d ∈ Finset.Icc ⌈D⌉₊ ⌊2*D⌋₊, ∑ b ∈ Finset.range d, ‖S w X (x+(b : ℝ)/(d : ℝ))‖^2) ≤ C*X^(2+ε)*D)
  (hInterior : let S := fun (w : ℝ → ℝ) (X t : ℝ) => ∑ n ∈ Finset.range (⌊X⌋₊+1), (((ArithmeticFunction.vonMangoldt n : ℝ)*w ((n : ℝ)/X) : ℝ) : ℂ)*Complex.exp (((2*Real.pi*(n : ℝ)*t : ℝ) : ℂ)*Complex.I); ∀ w : ℝ → ℝ, ContDiff ℝ ⊤ w → Function.support w ⊆ Set.Icc 0 1 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X D x : ℝ, 2 ≤ X → 1 ≤ D → D ≤ X → x ∈ Set.Icc 0 1 → ∀ q : ℕ, 0 < q → ∀ a : ℤ, Nat.Coprime a.natAbs q → |x-(a : ℝ)/(q : ℝ)| ≤ 1/(q : ℝ)^2 → X^(ε/2) < (q:ℝ) → (q:ℝ)*X^(ε/2) < X → D*X^(ε/2) < X^(3/8:ℝ) → (∑ d ∈ Finset.Icc ⌈D⌉₊ ⌊2*D⌋₊, ∑ b ∈ Finset.range d, ‖S w X (x+(b : ℝ)/(d : ℝ))‖^2) ≤ C*X^(2+ε)*(D/(q : ℝ)+(q : ℝ)*D/X+D^2/X^(3/8 : ℝ))) : (let S := fun (w : ℝ → ℝ) (X t : ℝ) => ∑ n ∈ Finset.range (⌊X⌋₊+1), (((ArithmeticFunction.vonMangoldt n : ℝ)*w ((n : ℝ)/X) : ℝ) : ℂ)*Complex.exp (((2*Real.pi*(n : ℝ)*t : ℝ) : ℂ)*Complex.I); ∀ w : ℝ → ℝ, ContDiff ℝ ⊤ w → Function.support w ⊆ Set.Icc 0 1 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X D x : ℝ, 2 ≤ X → 1 ≤ D → D ≤ X → x ∈ Set.Icc 0 1 → ∀ q : ℕ, 0 < q → ∀ a : ℤ, Nat.Coprime a.natAbs q → |x-(a : ℝ)/(q : ℝ)| ≤ 1/(q : ℝ)^2 → (∑ d ∈ Finset.Icc ⌈D⌉₊ ⌊2*D⌋₊, ∑ b ∈ Finset.range d, ‖S w X (x+(b : ℝ)/(d : ℝ))‖^2) ≤ C*X^(2+ε)*(D/(q : ℝ)+(q : ℝ)*D/X+D^2/X^(3/8 : ℝ))) := by
  intro S w hw hs ε he
  have he2 : 0 < ε/2 := by linarith
  obtain ⟨A,hA,huniform⟩ := hUniform w hw.continuous (ε/2) he2
  obtain ⟨B,hB,hsmall⟩ := hInterior w hw hs ε he
  let C := max A B
  have hAC : A ≤ C := le_max_left _ _
  have hBC : B ≤ C := le_max_right _ _
  refine ⟨C,hA.trans_le hAC,?_⟩
  intro X D x hX hD hDX hx q hq a ha happ
  have hX0 : 0 < X := by linarith
  have hD0 : 0 < D := by linarith
  have hq0 : 0 < (q:ℝ) := by exact_mod_cast hq
  let P := X^(ε/2)
  let R := X^(3/8:ℝ)
  let T := D/(q:ℝ)+(q:ℝ)*D/X+D^2/R
  have hp : 0 < P := Real.rpow_pos_of_pos hX0 _
  have hr : 0 < R := Real.rpow_pos_of_pos hX0 _
  have t1 : 0 ≤ D/(q:ℝ) := by positivity
  have t2 : 0 ≤ (q:ℝ)*D/X := by positivity
  have t3 : 0 ≤ D^2/R := by positivity
  have ht : 0 ≤ T := by dsimp [T]; positivity
  have hxp : 0 < X^(2+ε) := Real.rpow_pos_of_pos hX0 _
  by_cases hi : P < (q:ℝ) ∧ (q:ℝ)*P < X ∧ D*P < R
  · apply (hsmall X D x hX hD hDX hx q hq a ha happ hi.1 hi.2.1 hi.2.2).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBC hxp.le) ht
  have budget : D ≤ P*T := by
    by_cases fq : P < (q:ℝ)
    · by_cases gx : (q:ℝ)*P < X
      · have hh : R ≤ D*P := by
          exact le_of_not_gt fun h => hi ⟨fq,gx,h⟩
        have hh' := mul_le_mul_of_nonneg_left hh hD0.le
        calc
          D ≤ P*(D^2/R) := by
            rw [← mul_div_assoc, le_div_iff₀ hr]
            linarith only [show D*R ≤ P*D^2 by convert hh' using 1 <;> ring]
          _ ≤ _ := mul_le_mul_of_nonneg_left (by dsimp [T]; linarith) hp.le
      · have hh := mul_le_mul_of_nonneg_left (le_of_not_gt gx) hD0.le
        calc
          D ≤ P*((q:ℝ)*D/X) := by
            rw [← mul_div_assoc, le_div_iff₀ hX0]
            convert hh using 1 <;> ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (by dsimp [T]; linarith) hp.le
    · have hh := mul_le_mul_of_nonneg_left (le_of_not_gt fq) hD0.le
      calc
        D ≤ P*(D/(q:ℝ)) := by
          rw [← mul_div_assoc, le_div_iff₀ hq0]
          convert hh using 1 <;> ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by dsimp [T]; linarith) hp.le
  apply (huniform X D x hX hD hDX).trans
  change A*X^(2+ε/2)*D ≤ C*X^(2+ε)*T
  calc
    _ ≤ A*X^(2+ε/2)*(P*T) := mul_le_mul_of_nonneg_left budget (by positivity)
    _ = A*X^(2+ε)*T := by
      dsimp [P]
      rw [← mul_assoc, mul_assoc A, ← Real.rpow_add hX0]
      congr 3
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAC hxp.le) ht
