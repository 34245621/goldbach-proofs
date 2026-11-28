import Conjectures.Goldbach.FiniteLargeSieve
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

namespace LargeFractionBlock
open Finset

private noncomputable def phase (x : ℝ) : ℂ :=
  Complex.exp (((2*Real.pi*x : ℝ):ℂ)*Complex.I)

private noncomputable def coeff (w : ℝ → ℝ) (X x : ℝ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt n * w ((n:ℝ)/X):ℝ):ℂ) * phase ((n:ℝ)*x)

private noncomputable def S (w : ℝ → ℝ) (X t : ℝ) : ℂ :=
  ∑ n ∈ range (⌊X⌋₊+1), coeff w X t n

private theorem fixed_d
    (sieve : ∀ (N Q : ℕ) [NeZero Q] (a : ℕ → ℂ),
      (∑ r : ZMod Q, ‖∑ n ∈ range (N+1), a n * ZMod.stdAddChar (r*(n:ZMod Q))‖^2) ≤
      (N+Q:ℝ) * ∑ n ∈ range (N+1), ‖a n‖^2)
    (w : ℝ → ℝ) (X x : ℝ) (d : ℕ) (hd : 0 < d) :
    (∑ b ∈ range d, ‖S w X (x+(b:ℝ)/d)‖^2) ≤
      ((⌊X⌋₊:ℕ):ℝ) * (∑ n ∈ range (⌊X⌋₊+1), ‖coeff w X x n‖^2) +
      (d:ℝ) * (∑ n ∈ range (⌊X⌋₊+1), ‖coeff w X x n‖^2) := by
  let _ : NeZero d := ⟨hd.ne'⟩
  let inner (r : ZMod d) := ‖∑ n ∈ range (⌊X⌋₊+1),
      coeff w X x n * ZMod.stdAddChar (r*(n:ZMod d))‖ ^ 2
  have phase_eq (b n : ℕ) :
      phase ((n:ℝ)*(x+(b:ℝ)/d)) =
      phase ((n:ℝ)*x) * ZMod.stdAddChar ((b:ZMod d)*(n:ZMod d)) := by
    have hchar : ZMod.stdAddChar ((b:ZMod d)*(n:ZMod d)) =
      Complex.exp (2*Real.pi*Complex.I*(b:ℂ)*(n:ℂ)/(d:ℂ)) := by
      convert ZMod.stdAddChar_coe (N := d) ((b:ℤ)*(n:ℤ)) using 1 <;> push_cast <;> ring
    rw [hchar, phase, phase, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have sums (b : ℕ) : ‖S w X (x+(b:ℝ)/d)‖^2 = inner (b:ZMod d) := by
    simp only [S, coeff, phase_eq, inner, mul_assoc]
  have equiv_nat (b : Fin d) : ZMod.finEquiv d b = (b.val : ZMod d) := by
    cases d with
    | zero => omega
    | succ n =>
      apply ZMod.val_injective
      rw [ZMod.val_natCast_of_lt b.isLt]
      rfl
  calc
    _ = ∑ b ∈ range d, inner (b:ZMod d) := sum_congr rfl (fun b _ => sums b)
    _ = ∑ b : Fin d, inner (b.val:ZMod d) := (Fin.sum_univ_eq_sum_range _ _).symm
    _ = ∑ r : ZMod d, inner r := by
      simp_rw [← equiv_nat]
      exact Equiv.sum_comp (ZMod.finEquiv d).toEquiv _
    _ ≤ _ := by simpa only [add_mul] using sieve ⌊X⌋₊ d (coeff w X x)

private theorem coeff_bound (w : ℝ → ℝ) (X x B : ℝ) (hX : 2 ≤ X)
    (hw : ∀ t ∈ Set.Icc (0:ℝ) 1, |w t| ≤ B) (n : ℕ) (hn : n ∈ range (⌊X⌋₊+1)) :
    ‖coeff w X x n‖ ≤ Real.log X * B := by
  have hnX : (n:ℝ) ≤ X := (Nat.cast_le.mpr (by simpa using mem_range.mp hn :
    n ≤ ⌊X⌋₊)).trans (Nat.floor_le (by linarith))
  have hphase : ‖phase ((n:ℝ)*x)‖ = 1 := by
    simp [phase, Complex.norm_exp]
  rw [coeff, norm_mul, hphase, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log X := by
    by_cases hz : n = 0
    · simpa [hz] using Real.log_nonneg (show 1 ≤ X by linarith)
    · exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz) hnX)
  exact mul_le_mul hΛ (hw _ ⟨by positivity, (div_le_one (by linarith)).mpr hnX⟩)
    (abs_nonneg _) (Real.log_nonneg (by linarith))

private theorem large_block
    (sieve : ∀ (N Q : ℕ) [NeZero Q] (a : ℕ → ℂ),
      (∑ r : ZMod Q, ‖∑ n ∈ range (N+1), a n * ZMod.stdAddChar (r*(n:ZMod Q))‖^2) ≤
      (N+Q:ℝ) * ∑ n ∈ range (N+1), ‖a n‖^2)
    (w : ℝ → ℝ) (hw : Continuous w) (ε : ℝ) (he : 0 < ε) :
    ∃ C : ℝ, 0<C ∧ ∀ X D x : ℝ, 2≤X → 1≤D → D≤X →
      (∑ d ∈ Icc ⌈D⌉₊ ⌊2*D⌋₊, ∑ b ∈ range d, ‖S w X (x+(b:ℝ)/d)‖^2) ≤
      C*X^(2+ε)*D := by
  obtain ⟨B₀,hB₀⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).bddAbove_image hw.abs.continuousOn
  let B := max 1 B₀
  have hB : 0 < B := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)
  have hwt (t : ℝ) (ht : t ∈ Set.Icc 0 1) : |w t| ≤ B :=
    (hB₀ (Set.mem_image_of_mem _ ht)).trans (le_max_right _ _)
  have hε : 0 < ε/2 := by linarith
  refine ⟨18*(B/(ε/2))^2, by positivity, ?_⟩
  intro X D x hX hD hDX
  let I := Icc ⌈D⌉₊ ⌊2*D⌋₊
  have hX0 : 0 < X := by linarith
  have hD0 : 0 < D := by linarith
  have hlog := Real.log_nonneg (show 1 ≤ X by linarith)
  have hf : (⌊X⌋₊:ℝ) ≤ X := Nat.floor_le hX0.le
  have hcard : (I.card:ℝ) ≤ 3*D := by
    have h : I.card ≤ ⌊2*D⌋₊+1 := by simp [I,Nat.card_Icc]
    have hh : (I.card:ℝ) ≤ (⌊2*D⌋₊:ℝ)+1 := by exact_mod_cast h
    linarith [Nat.floor_le (show 0≤2*D by linarith)]
  have coeffs : (∑ n ∈ range (⌊X⌋₊+1), ‖coeff w X x n‖^2) ≤
      (2*X) * (Real.log X * B)^2 := by
    calc
      _ ≤ ∑ _n ∈ range (⌊X⌋₊+1), (Real.log X*B)^2 :=
        sum_le_sum (fun n hn => pow_le_pow_left₀ (norm_nonneg _) (coeff_bound _ _ _ _ hX hwt n hn) 2)
      _ = ((⌊X⌋₊:ℝ)+1) * (Real.log X*B)^2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have fix (d : ℕ) (hd : d ∈ I) : (∑ b ∈ range d, ‖S w X (x+(b:ℝ)/d)‖^2)
      ≤ 6*X^2*(Real.log X*B)^2 := by
    obtain ⟨hd₁,hd₂⟩ := mem_Icc.mp hd
    have dl : D ≤ (d:ℝ) := (Nat.ceil_le).mp hd₁
    have dh : (d:ℝ) ≤ 2*D := (Nat.cast_le.mpr hd₂).trans (Nat.floor_le (by linarith))
    have dp : 0 < d := Nat.cast_pos.mp (hD0.trans_le dl)
    have h := fixed_d sieve w X x d dp
    rw [← add_mul] at h
    apply h.trans
    calc
      _ ≤ (3*X)*((2*X)*(Real.log X * B)^2) :=
        mul_le_mul (by linarith) coeffs (sum_nonneg (fun i _ => sq_nonneg _)) (by positivity)
      _ = _ := by ring
  have logb := Real.log_le_rpow_div hX0.le hε
  have logs : Real.log X*B ≤ (B/(ε/2))*X^(ε/2) := by
    calc
      _ ≤ (X^(ε/2)/(ε/2))*B := mul_le_mul_of_nonneg_right logb hB.le
      _ = _ := by ring
  have square : (Real.log X*B)^2 ≤ (B/(ε/2))^2 * X^ε := by
    apply (pow_le_pow_left₀ (mul_nonneg hlog hB.le) logs 2).trans_eq
    rw [mul_pow, pow_two (X^(ε/2)), ← Real.rpow_add hX0]
    congr 2
    ring
  change (∑ d ∈ I, _) ≤ _
  calc
    _ ≤ ∑ _d ∈ I, (6*X^2*(Real.log X*B)^2) := sum_le_sum fix
    _ = (I.card:ℝ)*(6*X^2*(Real.log X*B)^2) := by simp
    _ ≤ (3*D)*(6*X^2*((B/(ε/2))^2 * X^ε)) :=
      mul_le_mul hcard (mul_le_mul_of_nonneg_left square (by positivity)) (by positivity) (by positivity)
    _ = 18*(B/(ε/2))^2 * X^(2+ε) * D := by
      rw [Real.rpow_add hX0, Real.rpow_two]
      ring

end LargeFractionBlock

theorem Conjectures.Cuts.Taskcdcaf775551daa1bc9cdb597 : let S := fun (w : ℝ → ℝ) (X t : ℝ) => ∑ n ∈ Finset.range (⌊X⌋₊+1), (((ArithmeticFunction.vonMangoldt n : ℝ)*w ((n : ℝ)/X) : ℝ) : ℂ)*Complex.exp (((2*Real.pi*(n : ℝ)*t : ℝ) : ℂ)*Complex.I); ∀ w : ℝ → ℝ, Continuous w → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X D x : ℝ, 2 ≤ X → 1 ≤ D → D ≤ X → (∑ d ∈ Finset.Icc ⌈D⌉₊ ⌊2*D⌋₊, ∑ b ∈ Finset.range d, ‖S w X (x+(b : ℝ)/(d : ℝ))‖^2) ≤ C*X^(2+ε)*D := by
  intro S w hw ε he
  have eqS (X t : ℝ) : S w X t = LargeFractionBlock.S w X t := by
    dsimp only [S, LargeFractionBlock.S, LargeFractionBlock.coeff, LargeFractionBlock.phase]
    simp only [mul_assoc]
  obtain ⟨C, hC, bound⟩ := LargeFractionBlock.large_block Conjectures.Goldbach.FiniteLargeSieve w hw ε he
  refine ⟨C,hC,?_⟩
  intro X D x hX hD hDX
  simp_rw [eqS]
  exact bound X D x hX hD hDX
