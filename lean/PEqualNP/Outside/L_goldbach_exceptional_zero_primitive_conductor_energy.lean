import Mathlib

/-!
# Primitive-conductor energy for the canonical exceptional-zero correction

The finite sums use the same dyadic blocks, ordinate cutoff and trapezoidal Mellin kernel
as the deep-arc criterion. The proof retains analytic multiplicities and counts
at each conductor only primitive characters.
-/

noncomputable section

namespace Goldbach
open Complex Set DirichletCharacter MeromorphicOn

noncomputable def regularizedL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ := by
  classical
  exact if χ = 1 then LFunctionTrivChar₁ q else LFunction χ
theorem analytic_regularizedL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (regularizedL χ) univ := by
  intro s _
  by_cases hχ : χ = 1
  · simpa only [regularizedL, hχ, ite_true] using (differentiable_LFunctionTrivChar₁ q).analyticAt s
  · simpa only [regularizedL, hχ, ite_false] using (differentiable_LFunction hχ).analyticAt s
theorem regularizedL_ne_zero_at_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    regularizedL χ 1 ≠ 0 := by
  by_cases hχ : χ = 1
  · simpa only [regularizedL, hχ, ite_true] using LFunctionTrivChar₁_apply_one_ne_zero q
  · simpa only [regularizedL, hχ, ite_false] using LFunction_apply_one_ne_zero hχ

theorem regularizedL_analyticOrder_ne_top {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (z : ℂ) : analyticOrderAt (regularizedL χ) z ≠ ⊤ := by
  let c : ℂ := 1
  have hC : regularizedL χ c ≠ 0 := regularizedL_ne_zero_at_one χ
  have hOrderC : analyticOrderAt (regularizedL χ) c ≠ ⊤ := by
    rw [((analytic_regularizedL χ) c (mem_univ c)).analyticOrderAt_eq_zero.mpr hC]
    exact ENat.zero_ne_top
  exact (analytic_regularizedL χ).analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ c) (mem_univ z) hOrderC

theorem regularizedL_analyticOrderNatAt_pos_iff {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (z : ℂ) :
    0 < analyticOrderNatAt (regularizedL χ) z ↔ regularizedL χ z = 0 := by
  constructor
  · intro h
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero h.ne'
  · intro h
    apply Nat.pos_of_ne_zero
    intro hzero
    apply ((analytic_regularizedL χ) z (mem_univ z)).analyticOrderAt_ne_zero.mpr h
    rw [← Nat.cast_analyticOrderNatAt (regularizedL_analyticOrder_ne_top χ z), hzero, Nat.cast_zero]

theorem regularizedL_divisor_apply {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {U : Set ℂ} {z : ℂ} (hz : z ∈ U) :
    divisor (regularizedL χ) U z = (analyticOrderNatAt (regularizedL χ) z : ℤ) := by
  rw [((analytic_regularizedL χ).mono (subset_univ U)).divisor_apply hz,
    ← Nat.cast_analyticOrderNatAt (regularizedL_analyticOrder_ne_top χ z),
    ENat.map_natCast, WithTop.untop₀_coe]

end Goldbach

namespace GoldbachTwistedMellin
open Set Finset Complex Goldbach DirichletCharacter MeromorphicOn
open scoped ComplexConjugate

theorem finite_box_zeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a b c d : ℝ) :
    {z : ℂ | z ∈ Icc a b ×ℂ Icc c d ∧ regularizedL χ z = 0}.Finite := by
  let U := Icc a b ×ℂ Icc c d
  have hcompact : IsCompact U := isCompact_Icc.reProdIm isCompact_Icc
  apply ((divisor (regularizedL χ) U).finiteSupport hcompact).subset
  intro z hz
  change divisor (regularizedL χ) U z ≠ 0
  rw [regularizedL_divisor_apply χ hz.1]
  exact_mod_cast ((regularizedL_analyticOrderNatAt_pos_iff χ z).mpr hz.2).ne'

noncomputable def boxZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b c d : ℝ) : Finset ℂ := (finite_box_zeros χ a b c d).toFinset

theorem mem_boxZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a b c d : ℝ) (z : ℂ) :
    z ∈ boxZeros χ a b c d ↔ z ∈ Icc a b ×ℂ Icc c d ∧ regularizedL χ z = 0 :=
  (finite_box_zeros χ a b c d).mem_toFinset

theorem regularizedL_ne_zero_right {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {z : ℂ} (hz : 1 < z.re) : regularizedL χ z ≠ 0 := by
  have hz1 : z ≠ 1 := by intro h; simp [h] at hz
  have hn := LFunction_ne_zero_of_one_le_re χ (Or.inr hz1) hz.le
  by_cases hχ : χ = 1
  · subst χ
    simpa only [regularizedL, ite_true, LFunctionTrivChar₁, Function.update_of_ne hz1] using
      mul_ne_zero (sub_ne_zero.mpr hz1) hn
  · simpa only [regularizedL, ite_eq_right hχ] using hn

def taper (a b x : ℝ) : ℝ := max 0 (min (x-a) (min 1 (b+1-x)))

def phase (β x : ℝ) : ℂ := Complex.exp (((β*x:ℝ):ℂ)*Complex.I)

def test (a b β x : ℝ) : ℂ := (taper a b x:ℂ)*phase β x

def transform (a b β : ℝ) (s : ℂ) : ℂ := mellin (test a b β) s

def heightCut (X : ℝ) : ℝ := (2*X)^8

noncomputable def exceptionalZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (B : ℝ) : Finset ℂ :=
  (boxZeros χ (1/2) 2 (-B) B).filter (fun z => 1/2 < z.re)

theorem mem_exceptionalZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (B : ℝ) (z : ℂ) :
    z ∈ exceptionalZeros χ B ↔ 1/2 < z.re ∧ |z.im| ≤ B ∧ regularizedL χ z = 0 := by
  classical
  rw [exceptionalZeros,mem_filter,mem_boxZeros,mem_reProdIm]
  constructor
  · rintro ⟨⟨⟨_,hi⟩,hz⟩,hl⟩
    exact ⟨hl,abs_le.mpr hi,hz⟩
  · rintro ⟨hl,hi,hz⟩
    have hr : z.re ≤ 2 := by by_contra! h;exact regularizedL_ne_zero_right χ (by linarith) hz
    exact ⟨⟨⟨⟨hl.le,hr⟩,abs_le.mp hi⟩,hz⟩,hl⟩

noncomputable def fixedZeroTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a b X β : ℝ) : ℂ :=
  ∑ z ∈ exceptionalZeros χ (heightCut X), (analyticOrderNatAt (regularizedL χ) z:ℂ)*transform a b β z

def prefixBlocks (m : ℕ) : List (ℕ × ℕ) :=
  if h : m < 2 then [] else (m/2+2,m+2)::prefixBlocks (m/2)
termination_by m
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

section
variable {q : ℕ} [NeZero q]
noncomputable def additiveWeight (a : ZMod q) (χ : DirichletCharacter ℂ q) : ℂ :=
  conj (∑ r : ZMod q, conj (ZMod.stdAddChar (a*r))*χ r) / (q.totient:ℂ)

theorem weight_expansion (a : ZMod q) (χ : DirichletCharacter ℂ q) :
    additiveWeight a χ = (∑ r : ZMod q, ZMod.stdAddChar (a*r)*conj (χ r))/(q.totient:ℂ) := by
  simp [additiveWeight,map_sum]
end

noncomputable def canonicalCorrection {q : ℕ} [NeZero q] (n : ℕ) (v : ZMod q) (β : ℝ) : ℂ :=
  ((prefixBlocks (n-2)).map fun p => ∑ χ : DirichletCharacter ℂ q,additiveWeight v χ *
    fixedZeroTerm χ p.1 p.2 p.1 (2*Real.pi*β)).sum

end GoldbachTwistedMellin
end

section
open Complex Finset
open scoped ComplexConjugate BigOperators
noncomputable section
namespace GoldbachTwistedMellin
variable {q : ℕ} [NeZero q]

theorem additiveWeight_gauss (a : ZMod q) (χ : DirichletCharacter ℂ q) :
    additiveWeight a χ = gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift a) / (q.totient : ℂ) := by
  rw [weight_expansion, gaussSum]
  congr 1
  apply sum_congr rfl
  intro r _
  rw [AddChar.mulShift_apply, mul_comm]
  exact congrArg (fun z => z * _) (MulChar.star_apply' χ r)

theorem additiveWeight_unit (a : (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) :
    additiveWeight a χ = χ a * additiveWeight 1 χ := by
  simp only [additiveWeight_gauss, gaussSum_mulShift_eq, inv_inv, AddChar.mulShift_one, mul_div_assoc]

theorem norm_primitive_weight (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖additiveWeight 1 χ‖ = Real.sqrt q / q.totient := by
  simp only [additiveWeight_gauss, AddChar.mulShift_one, norm_div,
    DirichletCharacter.norm_gaussSum_stdAddChar hχ.inv, Complex.norm_natCast]

noncomputable def characterZeroSum (n : ℕ) (χ : DirichletCharacter ℂ q) (β : ℝ) : ℂ :=
  ((prefixBlocks (n-2)).map fun p => fixedZeroTerm χ p.1 p.2 p.1 (2*Real.pi*β)).sum

private theorem exchange_blocks {α ι : Type*} [Fintype ι] (l : List α) (w : ι → ℂ) (z : α → ι → ℂ) :
    (l.map fun p => ∑ i : ι, w i * z p i).sum =
      ∑ i : ι, w i * (l.map fun p => z p i).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons,List.sum_cons,ih,mul_add,sum_add_distrib]

theorem canonical_character_expansion (n : ℕ) (v : ZMod q) (β : ℝ) :
    canonicalCorrection n v β = ∑ χ : DirichletCharacter ℂ q, additiveWeight v χ * characterZeroSum n χ β :=
  exchange_blocks _ _ _

private theorem char_unit_sum (χ : DirichletCharacter ℂ q) :
    (∑ a : (ZMod q)ˣ, χ a) = ∑ r : ZMod q, χ r := by
  classical
  let e : (ZMod q)ˣ ↪ ZMod q := ⟨(↑), Units.val_injective⟩
  have h : (univ : Finset (ZMod q)).filter IsUnit = (univ : Finset (ZMod q)ˣ).map e := by
    ext r
    simp [e, IsUnit]
  calc
    _ = ∑ r ∈ (univ : Finset (ZMod q)).filter IsUnit, χ r := by rw [h, sum_map]; rfl
    _ = _ := sum_subset (filter_subset ..) (fun r _ hr => MulChar.map_nonunit _ (by simpa using hr))

private theorem char_unit_orth (χ ψ : DirichletCharacter ℂ q) :
    (∑ a : (ZMod q)ˣ, conj (χ a) * ψ a) = if χ = ψ then (q.totient : ℂ) else 0 := by
  classical
  have c (a : (ZMod q)ˣ) : conj (χ a) = χ⁻¹ a := MulChar.star_apply' χ a
  simp_rw [c, ← MulChar.mul_apply]
  rw [char_unit_sum]
  by_cases h : χ = ψ
  · subst ψ
    simp [MulChar.sum_one_eq_card_units,ZMod.card_units_eq_totient]
  · rw [ite_eq_right h]
    exact MulChar.sum_eq_zero_of_ne_one (fun he => h (by calc
      χ = χ * (χ⁻¹ * ψ) := by rw [he, mul_one]
      _ = ψ := by group))

private theorem norm_energy_of_columns {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] (K : A → B → ℂ) (D : A → ℝ)
    (hK : ∀ r s : A, (∑ b : B, conj (K r b) * K s b) =
      if r = s then (D r : ℂ) else 0) (f : A → ℂ) :
    (∑ b : B, ‖∑ r : A, f r * K r b‖ ^ 2) =
      ∑ r : A, D r * ‖f r‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.conj_mul']
  calc
    _ = ∑ b : B, ∑ r : A, ∑ s : A, conj (f r) * f s * (conj (K r b) * K s b) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
      ring
    _ = ∑ r : A, ∑ s : A, conj (f r) * f s * (∑ b : B, conj (K r b) * K s b) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [hK, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      ring


/-- Exact numerator mean square, with all cancellations between different
characters accounted for and the zero sum within each character kept signed. -/
theorem canonical_unit_energy (n : ℕ) (β : ℝ) :
    (∑ a : (ZMod q)ˣ, ‖canonicalCorrection n (a : ZMod q) β‖^2) =
      (q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q, ‖additiveWeight 1 χ‖^2 * ‖characterZeroSum n χ β‖^2 := by
  classical
  let f := fun χ : DirichletCharacter ℂ q => additiveWeight 1 χ * characterZeroSum n χ β
  have expn (a : (ZMod q)ˣ) : canonicalCorrection n (a : ZMod q) β =
      ∑ χ : DirichletCharacter ℂ q, f χ * χ a := by
    rw [canonical_character_expansion]
    apply sum_congr rfl
    intro χ _
    rw [additiveWeight_unit]
    dsimp [f]
    ring
  simp_rw [expn]
  have h := norm_energy_of_columns (fun (χ : DirichletCharacter ℂ q) (a : (ZMod q)ˣ) => χ a)
    (fun _ => (q.totient : ℝ)) (fun χ ψ => by simpa using char_unit_orth χ ψ) f
  simpa only [f,norm_mul,mul_pow,Finset.mul_sum] using h

/-- A uniform bound on the share of reduced numerators exhibiting a large
exceptional-zero correction, expressed through the weighted character energy. -/
theorem canonical_large_numerators (n : ℕ) (β B : ℝ) (hB : 0 ≤ B) :
    (((univ : Finset (ZMod q)ˣ).filter (fun a : (ZMod q)ˣ => B ≤ ‖canonicalCorrection n (a : ZMod q) β‖)).card : ℝ) * B^2 ≤
      (q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q, ‖additiveWeight 1 χ‖^2 * ‖characterZeroSum n χ β‖^2 := by
  classical
  rw [← canonical_unit_energy]
  let bad := (univ : Finset (ZMod q)ˣ).filter (fun a : (ZMod q)ˣ => B ≤ ‖canonicalCorrection n (a : ZMod q) β‖)
  calc
    _ = ∑ _a ∈ bad, B^2 := by simp [bad]
    _ ≤ ∑ a ∈ bad, ‖canonicalCorrection n (a : ZMod q) β‖^2 := by
      apply Finset.sum_le_sum
      intro a ha
      exact pow_le_pow_left₀ hB (mem_filter.mp ha).2 2
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun a _ _ => sq_nonneg _)

end GoldbachTwistedMellin
end
end

section
open Complex Finset
noncomputable section
namespace GoldbachConductorGauss

theorem sum_multiples_range (d t : ℕ) (hd : 0 < d) (F : ℕ → ℂ) :
    (∑ r ∈ range (d*t), if d ∣ r then F r else 0) = ∑ j ∈ range t, F (d*j) := by
  rw [← sum_filter]
  refine sum_nbij' (fun r => r/d) (fun j => d*j) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    rw [mem_filter] at hr
    exact mem_range.mpr ((Nat.div_lt_iff_lt_mul hd).mpr (by simpa only [mul_comm t d] using mem_range.mp hr.1))
  · intro j hj
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hj) hd), dvd_mul_right d j⟩
  · intro r hr
    exact Nat.mul_div_cancel' (mem_filter.mp hr).2
  · intro j _
    exact Nat.mul_div_cancel_left j hd
  · intro r hr
    rw [Nat.mul_div_cancel' (mem_filter.mp hr).2]

theorem phase_multiple {d t : ℕ} [NeZero d] [NeZero t] (j : ℕ) :
    ZMod.stdAddChar ((d*j : ℕ) : ZMod (d*t)) = ZMod.stdAddChar (j : ZMod t) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, ZMod.toCircle_natCast, ZMod.toCircle_natCast]
  apply congrArg Complex.exp
  push_cast
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  field_simp
end GoldbachConductorGauss
end
end

section
open Finset Complex ArithmeticFunction
open scoped ComplexConjugate
noncomputable section
namespace GoldbachConductorGauss

private theorem sum_residues {q : ℕ} [NeZero q] (F : ZMod q → ℂ) :
    (∑ a : ZMod q, F a) = ∑ j ∈ range q, F j := by
  exact sum_nbij' ZMod.val (fun j : ℕ => (j : ZMod q))
    (fun a _ => mem_range.mpr (ZMod.val_lt a)) (fun _ _ => mem_univ _)
    (fun a _ => ZMod.natCast_zmod_val a)
    (fun j hj => ZMod.val_natCast_of_lt (mem_range.mp hj))
    (fun a _ => by rw [ZMod.natCast_zmod_val])

private theorem sum_moebius_indicator (m r : ℕ) (hm : m ≠ 0) :
    (∑ d ∈ m.divisors, if d ∣ r then (ArithmeticFunction.moebius d : ℂ) else 0) =
       if r.Coprime m then 1 else 0 := by
  classical
  rw [← sum_filter]
  have hdiv : m.divisors.filter (fun d => d ∣ r) = (r.gcd m).divisors := by
    ext d
    simp [Nat.mem_divisors, hm, (show r.gcd m ≠ 0 from fun he => hm (Nat.gcd_eq_zero_iff.mp he).2), Nat.dvd_gcd_iff, and_comm]
  rw [hdiv]
  have hz := congrArg (fun F : ArithmeticFunction ℤ => F (r.gcd m)) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply,ArithmeticFunction.one_apply] at hz
  rw [← Int.cast_sum, hz]
  by_cases h : r.Coprime m <;> simp [Nat.Coprime] at h ⊢

private theorem induced_value {f m : ℕ} [NeZero f] [NeZero m] (χ : DirichletCharacter ℂ f) (r : ℕ) :
    DirichletCharacter.changeLevel (dvd_mul_right f m) χ (r : ZMod (f*m)) =
      χ (r : ZMod f) * ∑ d ∈ m.divisors, if d ∣ r then (ArithmeticFunction.moebius d : ℂ) else 0 := by
  rw [sum_moebius_indicator _ _ (NeZero.ne m)]
  by_cases hf : r.Coprime f <;> by_cases hm : r.Coprime m
  · have hu := (ZMod.isUnit_iff_coprime r (f*m)).mpr (Nat.coprime_mul_iff_right.mpr ⟨hf,hm⟩)
    rw [ite_eq_left hm, mul_one]
    simpa [ZMod.cast_natCast (dvd_mul_right f m)] using
      DirichletCharacter.changeLevel_eq_cast_of_dvd χ (dvd_mul_right f m) hu.unit
  all_goals
    have hnot : ¬ r.Coprime (f*m) := by simp_all only [Nat.coprime_mul_iff_right, not_false_eq_true, and_false, false_and]
    rw [MulChar.map_nonunit _ (mt (ZMod.isUnit_iff_coprime _ _).mp hnot)]
  · simp [hm]
  · simp [MulChar.map_nonunit χ (mt (ZMod.isUnit_iff_coprime _ _).mp hf)]
  · simp [hm]

set_option maxHeartbeats 1800000 in
private theorem collapse_lift {f k : ℕ} [NeZero f] [NeZero k] (χ : DirichletCharacter ℂ f) :
    (∑ j ∈ range (f*k), χ (j : ZMod f) * ZMod.stdAddChar (j : ZMod (f*k))) =
      if k=1 then gaussSum χ ZMod.stdAddChar else 0 := by
  classical
  by_cases hk : k=1
  · subst k
    simp only [mul_one,ite_true]
    rw [gaussSum, sum_residues]
    apply sum_congr rfl
    intro j _
    apply congrArg (fun z => χ (j : ZMod f) * z)
    rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, ZMod.toCircle_natCast, ZMod.toCircle_natCast]
    simp
  rw [ite_eq_right hk]
  let c : ZMod (f*k) →+* ZMod f := ZMod.castHom (dvd_mul_right f k) _
  let F := fun j : ZMod (f*k) => χ (c j) * ZMod.stdAddChar j
  have hr : (∑ j : ZMod (f*k), F j) = ∑ j ∈ range (f*k), χ (j : ZMod f) * ZMod.stdAddChar (j : ZMod (f*k)) := by
    simpa [F] using sum_residues F
  rw [← hr]
  have hne : (f : ZMod (f*k)) ≠ 0 := by
    have hl : f < f*k := by simpa using (Nat.mul_lt_mul_of_pos_left (show 1<k by have := NeZero.pos k; omega) (NeZero.pos f))
    intro h
    have hv := congrArg ZMod.val h
    simp [ZMod.val_natCast_of_lt hl, NeZero.ne f] at hv
  have phase : ZMod.stdAddChar (f : ZMod (f*k)) ≠ 1 := by
    intro h
    apply hne
    exact ZMod.injective_toCircle (by ext; simpa [ZMod.stdAddChar_apply] using h)
  apply eq_zero_of_mul_eq_self_left phase
  calc
    _ = ∑ j : ZMod (f*k), F ((f : ZMod (f*k)) + j) := by
      rw [Finset.mul_sum]
      refine sum_congr rfl fun j _ => ?_
      simp [F,AddChar.map_add_eq_mul]
      ring
    _ = _ := (Equiv.addLeft (f : ZMod (f*k))).bijective.sum_comp F


private noncomputable def phase (N j : ℕ) : ℂ := Complex.exp (2*Real.pi*I*j/N)
private theorem phase_cast {N : ℕ} [NeZero N] (j : ℕ) :
    ZMod.stdAddChar (j : ZMod N) = phase N j := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_natCast, phase]
private theorem phase_rescale {d t : ℕ} [NeZero d] [NeZero t] (j : ℕ) :
    phase (d*t) (d*j) = phase t j := by
  simpa only [phase_cast] using phase_multiple (d:=d) (t:=t) j

private theorem divisor_block {f m d : ℕ} [NeZero f] [NeZero m] (hd : d ∣ m)
    (χ : DirichletCharacter ℂ f) :
    (∑ r ∈ range (f*m), if d ∣ r then χ (r : ZMod f) * phase (f*m) r else 0) =
      if d=m then χ (m : ZMod f) * gaussSum χ ZMod.stdAddChar else 0 := by
  classical
  obtain ⟨k,rfl⟩ := hd
  have hd0 : d ≠ 0 := by intro h; exact NeZero.ne (d*k) (by simp [h])
  have hk0 : k ≠ 0 := by intro h; exact NeZero.ne (d*k) (by simp [h])
  let : NeZero d := ⟨hd0⟩
  let : NeZero k := ⟨hk0⟩
  have reindex : f*(d*k) = d*(f*k) := by ring
  rw [reindex,sum_multiples_range _ _ (Nat.pos_of_ne_zero hd0)]
  simp_rw [phase_rescale, Nat.cast_mul,map_mul,mul_assoc,←Finset.mul_sum]
  have c := collapse_lift (k:=k) χ
  simp only [phase_cast] at c
  rw [c]
  by_cases hk : k = 1
  · simp [hk]
  · have hne : d ≠ d*k := by
      intro h
      apply hk
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd0) (by simpa using h.symm : d*k = d*1)
    simp [hk,hne]

/-- The Gauss sum of a character inflated from modulus f to f*m.
The factor μ(m)χ(m) includes both the squarefree and coprimality conditions. -/
theorem induced_gaussSum {f m : ℕ} [NeZero f] [NeZero m] (χ : DirichletCharacter ℂ f) :
    gaussSum (DirichletCharacter.changeLevel (dvd_mul_right f m) χ) ZMod.stdAddChar =
      (ArithmeticFunction.moebius m : ℂ) * χ (m : ZMod f) * gaussSum χ ZMod.stdAddChar := by
  classical
  rw [gaussSum,sum_residues]
  calc
    _ = ∑ r ∈ range (f*m), ∑ d ∈ m.divisors,
        (ArithmeticFunction.moebius d : ℂ) * (if d ∣ r then χ (r : ZMod f) * phase (f*m) r else 0) := by
      apply sum_congr rfl
      intro r _
      rw [induced_value,phase_cast]
      simp only [Finset.mul_sum,Finset.sum_mul]
      refine sum_congr rfl fun d _ => ?_
      by_cases h : d ∣ r <;> simp [h]
      ring
    _ = ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ) *
        (if d=m then χ (m : ZMod f)*gaussSum χ ZMod.stdAddChar else 0) := by
      rw [Finset.sum_comm]
      refine sum_congr rfl fun d hd => ?_
      rw [← Finset.mul_sum,divisor_block (Nat.dvd_of_mem_divisors hd) χ]
    _ = _ := by
      rw [Finset.sum_eq_single m]
      · simp [mul_assoc]
      · intro d _ hne; simp [hne]
      · intro h; exact False.elim (h (Nat.mem_divisors.mpr ⟨dvd_refl _,NeZero.ne m⟩))


theorem norm_induced_gaussSum {f q : ℕ} [NeZero f] [NeZero q] (hd : f ∣ q)
    (χ : DirichletCharacter ℂ f) (hχ : χ.IsPrimitive) :
    ‖gaussSum (DirichletCharacter.changeLevel hd χ) ZMod.stdAddChar‖ =
      if Squarefree (q/f) ∧ (q/f).Coprime f then Real.sqrt f else 0 := by
  classical
  obtain ⟨m,rfl⟩ := hd
  have hm : m ≠ 0 := by intro h; exact NeZero.ne (f*m) (by simp [h])
  let : NeZero m := ⟨hm⟩
  rw [Nat.mul_div_cancel_left m (NeZero.pos f),induced_gaussSum, norm_mul, norm_mul,
    DirichletCharacter.norm_gaussSum_stdAddChar hχ]
  by_cases hs : Squarefree m
  · have hmu : ‖(ArithmeticFunction.moebius m : ℂ)‖ = 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hs
    rw [hmu,one_mul]
    by_cases hc : m.Coprime f
    · have hu := (ZMod.isUnit_iff_coprime m f).mpr hc
      have hu' : ‖χ (m : ZMod f)‖ = 1 := χ.unit_norm_eq_one hu.unit
      simp [hs,hc,hu']
    · simp [hs,hc, MulChar.map_nonunit χ (mt (ZMod.isUnit_iff_coprime _ _).mp hc)]
  · simp [hs,ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]

/-- A conductor-resolved norm, valid for primitive and imprimitive characters. -/
theorem norm_gauss_by_conductor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ ZMod.stdAddChar‖ =
      if Squarefree (q/χ.conductor) ∧ (q/χ.conductor).Coprime χ.conductor
      then Real.sqrt χ.conductor else 0 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h := norm_induced_gaussSum χ.conductor_dvd_level χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
  rwa [DirichletCharacter.changeLevel_primitiveCharacter] at h

end GoldbachConductorGauss
end
end

section
open Complex Finset GoldbachConductorGauss
noncomputable section
namespace GoldbachTwistedMellin
variable {q : ℕ} [NeZero q]

theorem conductor_weight_sq (χ : DirichletCharacter ℂ q) :
    (q.totient : ℝ)^2 * ‖additiveWeight 1 χ‖^2 =
      if Squarefree (q/χ.conductor) ∧ (q/χ.conductor).Coprime χ.conductor then (χ.conductor : ℝ) else 0 := by
  classical
  rw [additiveWeight_gauss, AddChar.mulShift_one,norm_div, Complex.norm_natCast,
    norm_gauss_by_conductor,DirichletCharacter.conductor_inv]
  have hφ : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  by_cases h : Squarefree (q/χ.conductor) ∧ (q/χ.conductor).Coprime χ.conductor
  · rw [ite_eq_left h,ite_eq_left h, div_pow]
    field_simp
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  · simp [h]

/-- The exact mean square of the canonical signed-zero correction over all
reduced numerators. A contributing character has conductor f, squarefree
quotient q/f coprime to f, and carries weight f, independently of the numerator. -/
theorem canonical_conductor_energy (n : ℕ) (β : ℝ) :
    (q.totient : ℝ) * ∑ a : (ZMod q)ˣ, ‖canonicalCorrection n (a : ZMod q) β‖^2 =
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
        (fun χ => Squarefree (q/χ.conductor) ∧ (q/χ.conductor).Coprime χ.conductor),
        (χ.conductor : ℝ) * ‖characterZeroSum n χ β‖^2 := by
  classical
  rw [canonical_unit_energy,← mul_assoc,← sq, Finset.mul_sum,Finset.sum_filter]
  refine sum_congr rfl fun χ _ => ?_
  rw [← mul_assoc,conductor_weight_sq]
  split_ifs <;> simp

/-- The number of reduced numerators with correction at least B, in terms only
of the primitive-conductor weights and signed zero sums of contributing characters. -/
theorem canonical_bad_conductor_bound (n : ℕ) (β B : ℝ) (hB : 0 ≤ B) :
    (q.totient : ℝ) *
      ((((univ : Finset (ZMod q)ˣ).filter (fun a : (ZMod q)ˣ => B ≤ ‖canonicalCorrection n (a : ZMod q) β‖)).card : ℝ) * B^2) ≤
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter
        (fun χ => Squarefree (q/χ.conductor) ∧ (q/χ.conductor).Coprime χ.conductor),
        (χ.conductor : ℝ) * ‖characterZeroSum n χ β‖^2 := by
  rw [←canonical_conductor_energy]
  exact mul_le_mul_of_nonneg_left ((canonical_large_numerators (q:=q) n β B hB).trans_eq
    (canonical_unit_energy n β).symm) (Nat.cast_nonneg _)
end GoldbachTwistedMellin
end
end

section
open Complex Set Finset Goldbach DirichletCharacter
noncomputable section
namespace GoldbachTwistedMellin
variable {f q : ℕ} [NeZero f] [NeZero q]

private def removedEuler (q : ℕ) (χ : DirichletCharacter ℂ f) (s : ℂ) : ℂ :=
  ∏ p ∈ q.primeFactors, (1 - χ p * (p : ℂ) ^ (-s))

omit [NeZero f] [NeZero q] in
private theorem diff_removedEuler (χ : DirichletCharacter ℂ f) :
    Differentiable ℂ (removedEuler q χ) := by
  unfold removedEuler
  apply Differentiable.fun_finsetProd
  intro p hp
  have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
  fun_prop

omit [NeZero f] [NeZero q] in
private theorem removedEuler_ne_zero (χ : DirichletCharacter ℂ f) {s : ℂ} (hs : 0<s.re) :
    removedEuler q χ s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hpR : 1 < (p:ℝ) := by exact_mod_cast hp'.one_lt
  apply sub_ne_zero.mpr
  intro e
  have hlt : ‖χ p * (p:ℂ)^(-s)‖ < 1 := by
    rw [norm_mul,norm_natCast_cpow_of_pos hp'.pos, neg_re]
    calc
      _ ≤ 1*(p:ℝ)^(-s.re) := mul_le_mul_of_nonneg_right (χ.norm_le_one _) (by positivity)
      _ < 1 := by simpa using Real.rpow_lt_one_of_one_lt_of_neg hpR (neg_lt_zero.mpr hs)
  simp [←e] at hlt

private theorem regularized_changeLevel (hd : f ∣ q) (χ : DirichletCharacter ℂ f) :
    regularizedL (changeLevel hd χ) = regularizedL χ * removedEuler q χ := by
  have lhs := (analytic_regularizedL (changeLevel hd χ)).continuousOn
  have rhs := (analytic_regularizedL χ).continuousOn.mul (diff_removedEuler (q:=q) χ).continuous.continuousOn
  apply (continuousOn_univ.mp lhs).ext_on (dense_compl_singleton 1) (continuousOn_univ.mp rhs)
  intro s hs
  have hs1 : s ≠ 1 := hs
  change regularizedL (changeLevel hd χ) s = regularizedL χ s * _
  by_cases hχ : χ = 1
  · subst χ
    have hL := LFunction_changeLevel hd (1 : DirichletCharacter ℂ f) (Or.inr hs1)
    simp only [map_one] at hL ⊢
    simp only [regularizedL,ite_true,LFunctionTrivChar₁,Function.update_of_ne hs1,LFunctionTrivChar]
    rw [hL]
    change _ = _ * ∏ p ∈ q.primeFactors, _
    ring
  · have hi : changeLevel hd χ ≠ 1 := mt (changeLevel_eq_one_iff hd).mp hχ
    simpa only [regularizedL, ite_eq_right hχ, ite_eq_right hi, removedEuler] using
      LFunction_changeLevel hd χ (Or.inl hχ) (s:=s)

theorem zeros_changeLevel (hd : f ∣ q) (χ : DirichletCharacter ℂ f) (B : ℝ) :
    exceptionalZeros (changeLevel hd χ) B = exceptionalZeros χ B := by
  ext s
  rw [mem_exceptionalZeros,mem_exceptionalZeros,regularized_changeLevel,Pi.mul_apply]
  constructor
  · rintro ⟨hl,hi,hz⟩
    exact ⟨hl,hi,(mul_eq_zero.mp hz).resolve_right (removedEuler_ne_zero χ (show 0<s.re by linarith))⟩
  · rintro ⟨hl,hi,hz⟩
    exact ⟨hl,hi,by rw [hz,zero_mul]⟩

theorem order_changeLevel (hd : f ∣ q) (χ : DirichletCharacter ℂ f) {s : ℂ} (hs : 0<s.re) :
    analyticOrderNatAt (regularizedL (changeLevel hd χ)) s = analyticOrderNatAt (regularizedL χ) s := by
  have h := (diff_removedEuler (q:=q) χ).analyticAt s
  rw [regularized_changeLevel,analyticOrderNatAt,analyticOrderAt_mul
    ((analytic_regularizedL χ) _ (Set.mem_univ _)) h,
    h.analyticOrderAt_eq_zero.mpr (removedEuler_ne_zero χ hs),add_zero]
  rfl

theorem fixedZeroTerm_changeLevel (hd : f ∣ q) (χ : DirichletCharacter ℂ f) (a b X β : ℝ) :
    fixedZeroTerm (changeLevel hd χ) a b X β = fixedZeroTerm χ a b X β := by
  unfold fixedZeroTerm
  rw [zeros_changeLevel]
  refine sum_congr rfl fun z hz => ?_
  have h := ((mem_exceptionalZeros χ _ z).mp hz).1
  rw [order_changeLevel hd χ (show 0<z.re by linarith)]

theorem characterZeroSum_changeLevel (hd : f ∣ q) (χ : DirichletCharacter ℂ f) (n : ℕ) (β : ℝ) :
    characterZeroSum n (changeLevel hd χ) β = characterZeroSum n χ β := by
  simp only [characterZeroSum, fixedZeroTerm_changeLevel]

end GoldbachTwistedMellin
end
end

section
open Complex Finset DirichletCharacter
open scoped Classical
noncomputable section
namespace GoldbachTwistedMellin

/-- The signed exceptional-zero energy of the primitive characters of one
conductor. The zero argument contributes nothing in sums indexed by naturals. -/
def primitiveEnergy (d n : ℕ) (β : ℝ) : ℝ := by
  classical
  exact if h : d=0 then 0 else
    let _ : NeZero d := ⟨h⟩
    ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter DirichletCharacter.IsPrimitive,
      ‖characterZeroSum n ψ β‖^2

theorem primitiveEnergy_eq {d : ℕ} [NeZero d] (n : ℕ) (β : ℝ) :
    primitiveEnergy d n β =
      ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter DirichletCharacter.IsPrimitive,
        ‖characterZeroSum n ψ β‖^2 := by
  simp [primitiveEnergy,NeZero.ne d]

theorem primitiveEnergy_nonneg (d n : ℕ) (β : ℝ) : 0 ≤ primitiveEnergy d n β := by
  classical
  by_cases h : d=0
  · simp [primitiveEnergy,h]
  · let : NeZero d := ⟨h⟩
    rw [primitiveEnergy_eq]
    exact sum_nonneg (fun _ _ => sq_nonneg _)

private theorem conductor_fibre {d q : ℕ} [NeZero d] [NeZero q] (hd : d ∣ q) :
    (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor=d) =
      ((univ : Finset (DirichletCharacter ℂ d)).filter DirichletCharacter.IsPrimitive).image (changeLevel hd) := by
  classical
  ext χ
  simp only [mem_filter,mem_univ,true_and, mem_image]
  constructor
  · intro hχ
    have hf : χ.FactorsThrough d := hχ ▸ χ.factorsThrough_conductor
    obtain ⟨hd',ψ,hψ⟩ := hf
    refine ⟨ψ,?_,hψ.symm⟩
    rw [isPrimitive_def,←conductor_changeLevel ψ hd,←hψ]
    exact hχ
  · rintro ⟨ψ,hp,rfl⟩
    exact (conductor_changeLevel ψ hd).trans hp

private theorem fibre_energy {d q : ℕ} [NeZero d] [NeZero q] (hd : d ∣ q) (n : ℕ) (β : ℝ) :
    (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor=d),
      ‖characterZeroSum n χ β‖^2) = primitiveEnergy d n β := by
  classical
  rw [conductor_fibre hd,Finset.sum_image (fun _ _ _ _ h => changeLevel_injective hd h),primitiveEnergy_eq]
  simp only [characterZeroSum_changeLevel]

/-- Exact conductor decomposition over the primitive characters themselves,
reusing the same zeros and multiplicities across every induced level. -/
theorem canonical_primitive_energy {q : ℕ} [NeZero q] (n : ℕ) (β : ℝ) :
    (q.totient : ℝ) * ∑ a : (ZMod q)ˣ, ‖canonicalCorrection n (a : ZMod q) β‖^2 =
    ∑ d ∈ q.divisors, if Squarefree (q/d) ∧ (q/d).Coprime d then (d:ℝ)*primitiveEnergy d n β else 0 := by
  classical
  rw [canonical_conductor_energy, Finset.sum_filter]
  let F := fun χ : DirichletCharacter ℂ q => if Squarefree (q/χ.conductor) ∧ (q/χ.conductor).Coprime χ.conductor
    then (χ.conductor:ℝ)*‖characterZeroSum n χ β‖^2 else 0
  change (∑ χ : DirichletCharacter ℂ q, F χ) = _
  have inD (χ : DirichletCharacter ℂ q) (_ : χ ∈ univ) : χ.conductor ∈ q.divisors :=
    Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level,NeZero.ne q⟩
  rw [← Finset.sum_fiberwise_of_maps_to inD F]
  refine sum_congr rfl fun d hd => ?_
  have hdq := Nat.dvd_of_mem_divisors hd
  let : NeZero d := ⟨fun h => NeZero.ne q (Nat.eq_zero_of_zero_dvd (h ▸ hdq))⟩
  by_cases h : Squarefree (q/d) ∧ (q/d).Coprime d
  · rw [ite_eq_left h,←fibre_energy hdq n β,Finset.mul_sum]
    refine sum_congr rfl fun χ hχ => ?_
    simp only [F,(mem_filter.mp hχ).2,ite_eq_left h]
  · rw [ite_eq_right h]
    refine sum_eq_zero fun χ hχ => ?_
    simp only [F,(mem_filter.mp hχ).2,ite_eq_right h]

end GoldbachTwistedMellin
end
end

section
open Complex Finset
open scoped Classical
noncomputable section
namespace GoldbachTwistedMellin

private def lifts (Q d : ℕ) : Finset ℕ :=
  (range Q).filter (fun k => d ∣ k+1 ∧ Squarefree ((k+1)/d) ∧ ((k+1)/d).Coprime d)

private theorem lifts_card_le (Q d : ℕ) : (lifts Q d).card ≤ Q/d := by
  rw [← Nat.card_multiples Q d]
  exact card_le_card (fun k h => mem_filter.mpr ⟨(mem_filter.mp h).1,(mem_filter.mp h).2.1⟩)

private theorem level_on_common_range {Q k : ℕ} (hk : k<Q) (n : ℕ) (β : ℝ) :
    ((k+1).totient : ℝ) * ∑ a : (ZMod (k+1))ˣ, ‖canonicalCorrection n (a : ZMod (k+1)) β‖^2 =
    ∑ d ∈ Icc 1 Q, if d ∣ k+1 ∧ Squarefree ((k+1)/d) ∧ ((k+1)/d).Coprime d
      then (d:ℝ)*primitiveEnergy d n β else 0 := by
  rw [canonical_primitive_energy]
  have sub : (k+1).divisors ⊆ Icc 1 Q := by
    intro d hd
    exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)).trans (by omega)⟩
  calc
    _ = ∑ d ∈ (k+1).divisors, if d ∣ k+1 ∧ Squarefree ((k+1)/d) ∧ ((k+1)/d).Coprime d
        then (d:ℝ)*primitiveEnergy d n β else 0 := by
      refine sum_congr rfl fun d hd => ?_
      simp [Nat.dvd_of_mem_divisors hd]
    _ = _ := sum_subset sub (fun d _ hd => by
      have h : ¬ d ∣ k+1 := fun hv => hd (Nat.mem_divisors.mpr ⟨hv,Nat.succ_ne_zero _⟩)
      simp [h])

/-- Exact accounting across all levels up to Q; the multiplicity is the number of
squarefree, coprime lifts of the primitive conductor in the requested range. -/
theorem summed_primitive_energy (Q n : ℕ) (β : ℝ) :
    (∑ k ∈ range Q, ((k+1).totient : ℝ) * ∑ a : (ZMod (k+1))ˣ,
      ‖canonicalCorrection n (a : ZMod (k+1)) β‖^2) =
    ∑ d ∈ Icc 1 Q, ((lifts Q d).card : ℝ)*((d:ℝ)*primitiveEnergy d n β) := by
  calc
    _ = ∑ k ∈ range Q, ∑ d ∈ Icc 1 Q, if d ∣ k+1 ∧ Squarefree ((k+1)/d) ∧ ((k+1)/d).Coprime d
          then (d:ℝ)*primitiveEnergy d n β else 0 := by
      exact sum_congr rfl (fun k hk => level_on_common_range (mem_range.mp hk) n β)
    _ = _ := by
      rw [Finset.sum_comm]
      refine sum_congr rfl fun d _ => ?_
      rw [←Finset.sum_filter]
      simp [lifts]

/-- Mean-square majorant requiring the primitive zero energy only once per conductor. -/
theorem summed_primitive_energy_le (Q n : ℕ) (β : ℝ) :
    (∑ k ∈ range Q, ((k+1).totient : ℝ) * ∑ a : (ZMod (k+1))ˣ,
      ‖canonicalCorrection n (a : ZMod (k+1)) β‖^2) ≤
    (Q : ℝ) * ∑ d ∈ Icc 1 Q, primitiveEnergy d n β := by
  rw [summed_primitive_energy, Finset.mul_sum]
  refine sum_le_sum fun d _ => ?_
  rw [←mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (primitiveEnergy_nonneg _ _ _)
  exact_mod_cast (Nat.mul_le_mul_right d (lifts_card_le Q d)).trans (Nat.div_mul_le_self Q d)
end GoldbachTwistedMellin
end
end

open Goldbach GoldbachTwistedMellin
theorem PEqualNP.Outside.L_goldbach_exceptional_zero_primitive_conductor_energy :
let f := fun (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) =>
  @ite (ℂ → ℂ) (χ=1) (Classical.propDecidable _) (DirichletCharacter.LFunctionTrivChar₁ q) (DirichletCharacter.LFunction χ)
let W := fun (l r : ℕ) (β : ℝ) (z : ℂ) =>
  mellin (fun x : ℝ => ((max 0 (min (x-(l:ℝ)) (min 1 ((r:ℝ)+1-x))) : ℝ):ℂ) *
    Complex.exp ((((2*Real.pi*β)*x:ℝ):ℂ)*Complex.I)) z
let g := fun (q : ℕ) [NeZero q] (v : ZMod q) (χ : DirichletCharacter ℂ q) =>
  (starRingEnd ℂ) (∑ r : ZMod q,(starRingEnd ℂ) (ZMod.stdAddChar (v*r))*χ r)/(q.totient:ℂ)
∃ blocks : ℕ → List (ℕ×ℕ), ∃ zeros : (q : ℕ) → [NeZero q] → DirichletCharacter ℂ q → ℝ → Finset ℂ,
  (∀ m, blocks m = if m<2 then [] else (m/2+2,m+2)::blocks (m/2)) ∧
  (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (B : ℝ) (z : ℂ),
    z ∈ zeros q χ B ↔ 1/2<z.re ∧ |z.im|≤B ∧ f q χ z=0) ∧
  let Z := fun (q : ℕ) [NeZero q] (n : ℕ) (χ : DirichletCharacter ℂ q) (β : ℝ) =>
    ((blocks (n-2)).map fun p => ∑ z ∈ zeros q χ ((2*(p.1:ℝ))^8),
      (analyticOrderNatAt (f q χ) z:ℂ)*W p.1 p.2 β z).sum
  let R := fun (q : ℕ) [NeZero q] (n : ℕ) (a : ZMod q) (β : ℝ) =>
    ∑ χ : DirichletCharacter ℂ q, g q a χ * Z q n χ β
  let P := fun (d n : ℕ) (β : ℝ) => if h : d=0 then (0:ℝ) else
    let _ : NeZero d := ⟨h⟩
    ∑ χ : DirichletCharacter ℂ d, @ite ℝ χ.IsPrimitive (Classical.propDecidable _) (‖Z d n χ β‖^2) 0
  (∀ (q : ℕ) [NeZero q] (n : ℕ) (β : ℝ),
    (q.totient:ℝ) * ∑ a : (ZMod q)ˣ, ‖R q n a β‖^2 =
    ∑ d ∈ q.divisors, if Squarefree (q/d) ∧ (q/d).Coprime d then (d:ℝ)*P d n β else 0) ∧
  (∀ (Q n : ℕ) (β : ℝ),
    (∑ k ∈ Finset.range Q, ((k+1).totient:ℝ) * ∑ a : (ZMod (k+1))ˣ, ‖R (k+1) n a β‖^2) ≤
    (Q:ℝ)*∑ d ∈ Finset.Icc 1 Q, P d n β) := by
  classical
  intro f W g
  refine ⟨prefixBlocks,fun q _ χ B => exceptionalZeros χ B,?_,?_,?_⟩
  · intro m
    rw [prefixBlocks]
    split_ifs <;> rfl
  · intro q _ χ B z
    have hf : f q χ = regularizedL χ := by by_cases h : χ=1 <;> simp [f,regularizedL,h]
    rw [hf]
    exact mem_exceptionalZeros χ B z
  · intro Z R P
    have eqZ (q : ℕ) [NeZero q] (n : ℕ) (χ : DirichletCharacter ℂ q) (β : ℝ) :
        Z q n χ β = characterZeroSum n χ β := by
      have hf : f q χ = regularizedL χ := by by_cases h : χ=1 <;> simp [f,regularizedL,h]
      dsimp only [Z,characterZeroSum,fixedZeroTerm]
      simp_rw [hf]
      rfl
    have eqR (q : ℕ) [NeZero q] (n : ℕ) (a : ZMod q) (β : ℝ) :
        R q n a β = canonicalCorrection n a β := by
      dsimp only [R]
      simp_rw [eqZ]
      exact (canonical_character_expansion n a β).symm
    have eqP (d n : ℕ) (β : ℝ) : P d n β = primitiveEnergy d n β := by
      by_cases hd : d=0
      · simp [P,primitiveEnergy,hd]
      · let : NeZero d := ⟨hd⟩
        simp only [P,dite_eq_right hd,primitiveEnergy_eq,Finset.sum_filter]
        simp_rw [eqZ]
    simp_rw [eqR,eqP]
    exact ⟨fun q _ n β => canonical_primitive_energy (q:=q) n β,summed_primitive_energy_le⟩
