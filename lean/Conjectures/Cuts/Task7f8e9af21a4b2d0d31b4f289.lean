import Mathlib
-- Pair-energy proof adapted from goldbach-proofs a27b20785329b29275499a2969752df0cb7755b8 (Apache-2.0).

section PairDivisorScope
open Finset Filter
namespace PairEnergyInput
/-- Adapted from goldbach-proofs PR #2468, revision
3d9be84b446f4e30f46b52e1c83dc7e49e4535d9 (Apache-2.0). -/
theorem divisorPower (K : ℕ) (hK : 0<K) :
    ∃ C : ℝ,1≤C ∧ ∀ n : ℕ, 0<n → (n.divisors.card:ℝ)^K ≤ C*n := by
  have hl := (isLittleO_pow_const_const_pow_of_one_lt (R:=ℝ) K (by norm_num : (1:ℝ)<2)).bound (by norm_num : (0:ℝ)<1)
  obtain ⟨E,hE⟩ := eventually_atTop.mp hl
  let c : ℝ := (2:ℝ)^K*((E:ℝ)+1)^K
  have hc : 1≤c := by
    dsimp [c]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) E]))
  have small (e : ℕ) : ((e:ℝ)+1)^K ≤ c*(2:ℝ)^e := by
    by_cases he : e<E
    · have hle : ((e:ℝ)+1)^K ≤ ((E:ℝ)+1)^K := pow_le_pow_left₀ (by positivity) (by exact_mod_cast (show e+1≤E+1 by omega)) _
      have h2 : (1:ℝ)≤2^K := one_le_pow₀ (by norm_num)
      have h3 : (1:ℝ)≤2^e := one_le_pow₀ (by norm_num)
      exact hle.trans ((le_mul_of_one_le_left (by positivity) h2).trans (le_mul_of_one_le_right (by positivity) h3))
    · have hs := hE (e+1) (by omega)
      simp only [Real.norm_eq_abs,Nat.cast_add,Nat.cast_one,abs_of_nonneg (pow_nonneg (by positivity : 0≤(e:ℝ)+1) K),one_mul,pow_succ] at hs
      rw [abs_of_nonneg (by positivity)] at hs
      have hK1 : (2:ℝ)≤2^K := by simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hK)
      have hE1 : (1:ℝ)≤((E:ℝ)+1)^K := one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) E])
      have hc2 : (2:ℝ)≤c := hK1.trans (le_mul_of_one_le_right (by positivity) hE1)
      exact hs.trans (by nlinarith [mul_le_mul_of_nonneg_right hc2 (by positivity : 0≤(2:ℝ)^e)])
  let P : ℕ := 2^K
  refine ⟨c^P,one_le_pow₀ hc,?_⟩
  intro n hn
  have hprod : (∏ p ∈ n.primeFactors,(p:ℝ)^(n.factorization p))=n := by
    exact_mod_cast (by simpa [Finsupp.prod,Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hn.ne' :
      (∏ p ∈ n.primeFactors,p^(n.factorization p))=n)
  have hlocal (p : ℕ) (hp : p∈n.primeFactors) :
      ((n.factorization p:ℝ)+1)^K ≤ (if p<P then c else 1)*(p:ℝ)^(n.factorization p) := by
    have h2 : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    split_ifs with h
    · exact (small _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) h2 _) (by linarith))
    · rw [one_mul]
      have he : ∀ e : ℕ,(e:ℝ)+1 ≤ (2:ℝ)^e := by
        intro e; induction e with
        | zero => norm_num
        | succ e ih => push_cast; rw [pow_succ]; linarith [show (0:ℝ)≤e by positivity]
      calc
        _ ≤ ((2:ℝ)^n.factorization p)^K := pow_le_pow_left₀ (by positivity) (he _) _
        _ = ((2:ℝ)^K)^n.factorization p := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
        _ ≤ _ := pow_le_pow_left₀ (by positivity) (by exact_mod_cast (show 2^K≤p by omega)) _
  have hcount : ((n.primeFactors.filter (·<P)).card)≤P := by
    have : n.primeFactors.filter (·<P)⊆range P := fun _ h => mem_range.mpr (mem_filter.mp h).2
    simpa using card_le_card this
  have hfactor : (∏ p ∈ n.primeFactors, if p<P then c else 1)≤c^P := by
    rw [←prod_filter,prod_const]; exact pow_le_pow_right₀ hc hcount
  rw [Nat.card_divisors hn.ne',Nat.cast_prod,←prod_pow]
  simp only [Nat.cast_add,Nat.cast_one]
  calc
    _ ≤ ∏ p ∈ n.primeFactors, (if p<P then c else 1)*(p:ℝ)^(n.factorization p) :=
      prod_le_prod₀ (fun _ _ => by positivity) hlocal
    _ ≤ _ := by rw [prod_mul_distrib,hprod]; exact mul_le_mul_of_nonneg_right hfactor (by positivity)

theorem divisor_envelope_for_product (k : ℕ) (hk : 0 < k) : ∃ C : ℝ, 1 ≤ C ∧ ∀ n m : ℕ, m ≤ n →
    (m.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / (k : ℝ) : ℝ) := by
  obtain ⟨C, CLower, estimate⟩ := divisorPower k hk
  let p : ℝ := 1 / (k : ℝ)
  have CNonnegative : 0 ≤ C := zero_le_one.trans CLower
  refine ⟨C ^ p, Real.one_le_rpow CLower (by unfold p; positivity), fun n m upper => ?_⟩
  by_cases mPositive : 0 < m
  · have mReal : (m : ℝ) ≤ n := by exact_mod_cast upper
    have standard := (estimate m mPositive).trans (mul_le_mul_of_nonneg_left mReal CNonnegative)
    have powered := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg m.divisors.card) k) standard
      (show 0 ≤ p by dsimp [p]; positivity)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m.divisors.card),
      Real.mul_rpow CNonnegative (Nat.cast_nonneg n)] at powered
    have kReal : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have kp : (k : ℝ) * p = 1 := by unfold p; field_simp
    rw [kp, Real.rpow_one] at powered
    exact powered
  · have mZero : m = 0 := by omega
    subst m
    simp only [Nat.divisors_zero, Finset.card_empty, Nat.cast_zero]
    positivity


end PairEnergyInput
end PairDivisorScope

-- The divisor estimate used below was verified in #2977.
-- This is the pair-collision child of #4353.


namespace GoldbachPolynomialDifference

open Finset Polynomial
open scoped BigOperators

noncomputable def differencePolynomial (P : Polynomial ℤ) (h u : ℤ) : Polynomial ℤ :=
  P.taylor h - P - Polynomial.C u

theorem differencePolynomial_ne_zero (P : Polynomial ℤ) (h u : ℤ)
    (hdegree : 2 ≤ P.natDegree) (hh : h ≠ 0) :
    differencePolynomial P h u ≠ 0 := by
  let k := P.natDegree - 1
  let H := P.hasseDeriv k
  have hk0 : k ≠ 0 := by dsimp [k]; omega
  have h1k : 1 + k = P.natDegree := by dsimp [k]; omega
  have hHdeg : H.natDegree ≤ 1 := by
    apply (Polynomial.natDegree_hasseDeriv_le P k).trans
    dsimp [k]
    omega
  have hH_eval : H.eval h = H.coeff 1 * h + H.coeff 0 := by
    conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hHdeg]
    simp
  have hP0 : P ≠ 0 := by
    intro he
    simp [he] at hdegree
  have hH1 : H.coeff 1 ≠ 0 := by
    change (P.hasseDeriv k).coeff 1 ≠ 0
    rw [Polynomial.hasseDeriv_coeff, h1k, Polynomial.coeff_natDegree]
    apply mul_ne_zero
    · exact_mod_cast (Nat.choose_pos (show k ≤ P.natDegree by dsimp [k]; omega)).ne'
    · exact Polynomial.leadingCoeff_ne_zero.mpr hP0
  have hH0 : H.coeff 0 = P.coeff k := by
    change (P.hasseDeriv k).coeff 0 = P.coeff k
    rw [Polynomial.hasseDeriv_coeff]
    simp
  have hC : ((Polynomial.C u : Polynomial ℤ).coeff k) = 0 := by
    exact Polynomial.coeff_C_of_ne_zero hk0
  have hq : (differencePolynomial P h u).coeff k = H.coeff 1 * h := by
    simp only [differencePolynomial, Polynomial.coeff_sub, Polynomial.taylor_coeff, hC]
    change H.eval h - P.coeff k - 0 = H.coeff 1 * h
    rw [hH_eval, hH0]
    ring
  intro he
  rw [he, Polynomial.coeff_zero] at hq
  exact (mul_ne_zero hH1 hh) hq.symm

theorem differencePolynomial_natDegree_le (P : Polynomial ℤ) (h u : ℤ) :
    (differencePolynomial P h u).natDegree ≤ P.natDegree := by
  unfold differencePolynomial
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  · simp

theorem differencePolynomial_eval (P : Polynomial ℤ) (h u x : ℤ) :
    (differencePolynomial P h u).eval x = P.eval (x+h) - P.eval x - u := by
  simp [differencePolynomial, Polynomial.taylor_apply, Polynomial.eval_comp]

def differencePairs (P : Polynomial ℤ) (A : Finset ℤ) (u : ℤ) : Finset (ℤ × ℤ) :=
  (A.product A).filter fun v => P.eval v.2 - P.eval v.1 = u

private def signedDivisors (u : ℤ) : Finset ℤ :=
  (u.natAbs.divisors.image fun d : ℕ => (d : ℤ)) ∪
    (u.natAbs.divisors.image fun d : ℕ => -(d : ℤ))

private theorem signedDivisors_card (u : ℤ) :
    (signedDivisors u).card ≤ 2 * u.natAbs.divisors.card := by
  unfold signedDivisors
  rw [two_mul]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add Finset.card_image_le Finset.card_image_le)

private theorem signedDivisors_mem {u h : ℤ} (hu : u ≠ 0) (hd : h ∣ u) :
    h ∈ signedDivisors u := by
  have habs : u.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hu
  have hh : h.natAbs ∈ u.natAbs.divisors :=
    Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr hd, habs⟩
  unfold signedDivisors
  by_cases hn : 0 ≤ h
  · exact mem_union_left _ (mem_image.mpr ⟨h.natAbs, hh, Int.natAbs_of_nonneg hn⟩)
  · exact mem_union_right _ (mem_image.mpr ⟨h.natAbs, hh,
      (Int.eq_neg_natAbs_of_nonpos (le_of_not_ge hn)).symm⟩)

private theorem signedDivisors_ne_zero {u h : ℤ} (hh : h ∈ signedDivisors u) : h ≠ 0 := by
  have hpos {n : ℕ} (hn : n ∈ u.natAbs.divisors) : 0 < n := Nat.pos_of_mem_divisors hn
  unfold signedDivisors at hh
  rcases mem_union.mp hh with hh | hh
  · obtain ⟨n, hn, rfl⟩ := mem_image.mp hh
    exact Int.ofNat_ne_zero.mpr (hpos hn).ne'
  · obtain ⟨n, hn, rfl⟩ := mem_image.mp hh
    exact neg_ne_zero.mpr (Int.ofNat_ne_zero.mpr (hpos hn).ne')

theorem differencePairs_card_le (P : Polynomial ℤ) (A : Finset ℤ) (u : ℤ)
    (hdegree : 2 ≤ P.natDegree) (hu : u ≠ 0) :
    (differencePairs P A u).card ≤ 2 * P.natDegree * u.natAbs.divisors.card := by
  classical
  let B := signedDivisors u
  let R (h : ℤ) := (differencePolynomial P h u).roots.toFinset
  let f (x : ℤ × ℤ) : Σ _ : ℤ, ℤ := ⟨x.2-x.1, x.1⟩
  have hmaps (x : ℤ × ℤ) (hx : x ∈ differencePairs P A u) : f x ∈ B.sigma R := by
    rcases x with ⟨b,d⟩
    have hd := (mem_filter.mp hx).2
    change P.eval d - P.eval b = u at hd
    have hdvd : d-b ∣ u := hd ▸ Polynomial.sub_dvd_eval_sub d b P
    have hmem : d-b ∈ B := signedDivisors_mem hu hdvd
    have hne := differencePolynomial_ne_zero P (d-b) u hdegree (signedDivisors_ne_zero hmem)
    apply Finset.mem_sigma.mpr
    refine ⟨hmem, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne).mpr ?_)⟩
    change (differencePolynomial P (d-b) u).eval b = 0
    rw [differencePolynomial_eval, show b+(d-b)=d by omega, hd, sub_self]
  have hf : Set.InjOn f (↑(differencePairs P A u) : Set (ℤ × ℤ)) := by
    intro x _ y _ h
    have h1 := congrArg (fun z : Σ _ : ℤ, ℤ => z.2) h
    have h2 := congrArg (fun z : Σ _ : ℤ, ℤ => z.1) h
    change x.1 = y.1 at h1
    change x.2-x.1 = y.2-y.1 at h2
    exact Prod.ext h1 (by omega)
  calc
    _ ≤ (B.sigma R).card := Finset.card_le_card_of_injOn f hmaps hf
    _ = ∑ h ∈ B, (R h).card := Finset.card_sigma _ _
    _ ≤ ∑ _h ∈ B, P.natDegree := by
      apply Finset.sum_le_sum
      intro h _
      exact (Multiset.toFinset_card_le _).trans
        ((Polynomial.card_roots' _).trans (differencePolynomial_natDegree_le P h u))
    _ = B.card * P.natDegree := by simp
    _ ≤ (2*u.natAbs.divisors.card) * P.natDegree :=
      Nat.mul_le_mul_right _ (signedDivisors_card u)
    _ = _ := by ring

theorem evalFiber_card_le (P : Polynomial ℤ) (A : Finset ℤ) (v : ℤ)
    (hdegree : 0 < P.natDegree) :
    (A.filter fun x => P.eval x = v).card ≤ P.natDegree := by
  let Q := P - Polynomial.C v
  have hn : Q ≠ 0 := by
    intro h
    have he : P = Polynomial.C v := sub_eq_zero.mp h
    rw [he, Polynomial.natDegree_C] at hdegree
    exact (lt_irrefl _ hdegree)
  have hQdeg : Q.natDegree ≤ P.natDegree := (Polynomial.natDegree_sub_le _ _).trans (by simp)
  have hsub : (A.filter fun x => P.eval x = v) ⊆ Q.roots.toFinset := by
    intro x hx
    have hxv := (Finset.mem_filter.mp hx).2
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hn).mpr
    change (P - Polynomial.C v).eval x = 0
    simp [hxv]
  exact (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans hQdeg))

theorem differencePairs_zero_le (P : Polynomial ℤ) (A : Finset ℤ)
    (hdegree : 0 < P.natDegree) :
    (differencePairs P A 0).card ≤ A.card * P.natDegree := by
  let T (b : ℤ) := A.filter fun d => P.eval d = P.eval b
  let f (x : ℤ × ℤ) : Σ _ : ℤ, ℤ := ⟨x.1,x.2⟩
  have hm (x : ℤ × ℤ) (hx : x ∈ differencePairs P A 0) : f x ∈ A.sigma T := by
    have h := Finset.mem_filter.mp hx
    obtain ⟨hb, hd⟩ := Finset.mem_product.mp h.1
    exact Finset.mem_sigma.mpr ⟨hb, Finset.mem_filter.mpr ⟨hd, sub_eq_zero.mp h.2⟩⟩
  have hi : Function.Injective f := by
    intro x y h
    exact Prod.ext (congrArg (fun z : Σ _ : ℤ, ℤ => z.1) h)
      (congrArg (fun z : Σ _ : ℤ, ℤ => z.2) h)
  calc
    _ ≤ (A.sigma T).card := Finset.card_le_card_of_injOn f hm hi.injOn
    _ = ∑ b ∈ A, (T b).card := Finset.card_sigma _ _
    _ ≤ ∑ _b ∈ A, P.natDegree :=
      Finset.sum_le_sum fun b _ => evalFiber_card_le P A (P.eval b) hdegree
    _ = _ := by simp

end GoldbachPolynomialDifference



namespace GoldbachPolynomialMagnitude

open Finset

noncomputable def coefficientBound (P : Polynomial ℤ) : ℝ :=
  2 * (1 + ∑ i ∈ range (P.natDegree+1), |(P.coeff i : ℝ)|)

theorem coefficientBound_pos (P : Polynomial ℤ) : 0 < coefficientBound P := by
  unfold coefficientBound
  positivity

private theorem eval_magnitude (P : Polynomial ℤ) (M a : ℕ) (hM : 1 ≤ M) (ha : a ≤ M) :
    |(((P.eval (a : ℤ) : ℤ) : ℝ))| ≤
      (∑ i ∈ range (P.natDegree+1), |(P.coeff i : ℝ)|) * (M : ℝ)^P.natDegree := by
  have hMR : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have haR : (a : ℝ) ≤ M := by exact_mod_cast ha
  rw [Polynomial.eval_eq_sum_range]
  push_cast
  calc
    |∑ i ∈ range (P.natDegree+1), (P.coeff i : ℝ) * (a : ℝ)^i|
      ≤ ∑ i ∈ range (P.natDegree+1), |(P.coeff i : ℝ) * (a : ℝ)^i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range (P.natDegree+1), |(P.coeff i : ℝ)| * (M : ℝ)^P.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (a : ℝ)^i)]
      exact mul_le_mul_of_nonneg_left
        ((pow_le_pow_left₀ (Nat.cast_nonneg a) haR i).trans
          (pow_le_pow_right₀ hMR (by simpa using mem_range.mp hi))) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]

theorem natAbs_eval_sub_le (P : Polynomial ℤ) (M a c : ℕ)
    (hM : 1 ≤ M) (ha : a ≤ M) (hc : c ≤ M) :
    ((P.eval (a : ℤ) - P.eval (c : ℤ)).natAbs : ℝ) ≤
      coefficientBound P * (M : ℝ)^P.natDegree := by
  let S : ℝ := ∑ i ∈ range (P.natDegree+1), |(P.coeff i : ℝ)|
  have haMag : |(((P.eval (a : ℤ) : ℤ) : ℝ))| ≤ S * (M : ℝ)^P.natDegree := eval_magnitude P M a hM ha
  have hcMag : |(((P.eval (c : ℤ) : ℤ) : ℝ))| ≤ S * (M : ℝ)^P.natDegree := eval_magnitude P M c hM hc
  rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]
  calc
    _ ≤ |(((P.eval (a : ℤ) : ℤ) : ℝ))| + |(((P.eval (c : ℤ) : ℤ) : ℝ))| := abs_sub _ _
    _ ≤ S * (M : ℝ)^P.natDegree + S * (M : ℝ)^P.natDegree := add_le_add haMag hcMag
    _ ≤ _ := by
      change _ ≤ 2*(1+S) * (M : ℝ)^P.natDegree
      nlinarith only [show 0 ≤ (M : ℝ)^P.natDegree by positivity]

theorem rpow_natAbs_eval_sub_le (P : Polynomial ℤ) (hP : 0 < P.natDegree)
    (ε : ℝ) (hε : 0 < ε) (M a c : ℕ) (hM : 1 ≤ M) (ha : a ≤ M) (hc : c ≤ M) :
    ((P.eval (a : ℤ) - P.eval (c : ℤ)).natAbs : ℝ)^(ε/(P.natDegree : ℝ)) ≤
      (coefficientBound P)^(ε/(P.natDegree : ℝ)) * (M : ℝ)^ε := by
  have hD : 0 < (P.natDegree : ℝ) := by exact_mod_cast hP
  let δ : ℝ := ε / (P.natDegree : ℝ)
  have hδ : 0 ≤ δ := div_nonneg hε.le hD.le
  change _ ^ δ ≤ (coefficientBound P)^δ * (M : ℝ)^ε
  calc
    _ ≤ (coefficientBound P * (M : ℝ)^P.natDegree)^δ :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (natAbs_eval_sub_le P M a c hM ha hc) hδ
    _ = _ := by
      rw [Real.mul_rpow (coefficientBound_pos P).le (by positivity)]
      congr 1
      rw [← Real.rpow_natCast_mul (by positivity)]
      congr 1
      dsimp [δ]
      field_simp

end GoldbachPolynomialMagnitude


namespace GoldbachPolynomialDivisors

/-- Drop the logarithmic factor from the verified divisor completion loss. -/
theorem divisor_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → (m.divisors.card : ℝ) ≤ C * (m : ℝ) ^ δ := by
  obtain ⟨k,hk⟩ := exists_nat_gt (1/δ)
  have hk' : (0:ℝ)<k := lt_trans (by positivity : (0:ℝ)<1/δ) hk
  obtain ⟨C,hC,h⟩ := PairEnergyInput.divisor_envelope_for_product k (by exact_mod_cast hk')
  refine ⟨C,by linarith,fun m hm => ?_⟩
  apply (h m m le_rfl).trans
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm)
  apply (div_le_iff₀ hk').2
  have := (div_lt_iff₀ hδ).1 hk
  linarith [mul_comm δ (k:ℝ)]

end GoldbachPolynomialDivisors


namespace GoldbachPolyCollision

open Finset Polynomial

/-- View the finite natural support inside the integer polynomial domain. -/
def liftSupport (A : Finset ℕ) : Finset ℤ :=
  A.map ⟨Int.ofNat, fun _ _ h => Int.ofNat.inj h⟩

theorem mem_liftSupport {A : Finset ℕ} {z : ℤ} :
    z ∈ liftSupport A ↔ ∃ a ∈ A, (a : ℤ) = z :=
  mem_map

theorem liftSupport_card (A : Finset ℕ) : (liftSupport A).card = A.card :=
  card_map _

/-- The polynomial value at the second index minus the value at the first. -/
def evalDifference (P : Polynomial ℤ) (z : ℤ × ℤ) : ℤ :=
  P.eval z.2 - P.eval z.1

/-- Move the two right-side terms across the equality to count differences. -/
theorem collision_card_eq_difference_pairs (P : Polynomial ℤ) (A : Finset ℕ) :
    let wt := fun x : Fin 2 → ↥A => ∑ i, P.eval ((x i : ℕ) : ℤ)
    ((univ : Finset ((Fin 2 → ↥A) × (Fin 2 → ↥A))).filter
      (fun z => wt z.1 = wt z.2)).card =
      (((liftSupport A ×ˢ liftSupport A) ×ˢ (liftSupport A ×ˢ liftSupport A)).filter
        (fun z => evalDifference P z.1 = evalDifference P z.2)).card := by
  classical
  dsimp only
  let reorder (z : (Fin 2 → ↥A) × (Fin 2 → ↥A)) : (ℤ × ℤ) × (ℤ × ℤ) :=
    ((((z.2 0 : ℕ) : ℤ), ((z.1 0 : ℕ) : ℤ)), (((z.1 1 : ℕ) : ℤ), ((z.2 1 : ℕ) : ℤ)))
  have hmem (a : ↥A) : ((a : ℕ) : ℤ) ∈ liftSupport A :=
    mem_liftSupport.mpr ⟨a, a.property, rfl⟩
  apply Finset.card_bij (fun z _ => reorder z)
  · intro z hz
    refine mem_filter.mpr ⟨?_, ?_⟩
    · exact mem_product.mpr ⟨mem_product.mpr ⟨hmem _, hmem _⟩,
        mem_product.mpr ⟨hmem _, hmem _⟩⟩
    · have h := (mem_filter.mp hz).2
      rw [Fin.sum_univ_two, Fin.sum_univ_two] at h
      dsimp only [reorder, evalDifference]
      linarith only [h]
  · intro x _ y _ h
    apply Prod.ext
    · funext i
      apply Subtype.ext
      fin_cases i
      · exact Int.ofNat.inj (congrArg (fun z : (ℤ × ℤ) × (ℤ × ℤ) => z.1.2) h)
      · exact Int.ofNat.inj (congrArg (fun z : (ℤ × ℤ) × (ℤ × ℤ) => z.2.1) h)
    · funext i
      apply Subtype.ext
      fin_cases i
      · exact Int.ofNat.inj (congrArg (fun z : (ℤ × ℤ) × (ℤ × ℤ) => z.1.1) h)
      · exact Int.ofNat.inj (congrArg (fun z : (ℤ × ℤ) × (ℤ × ℤ) => z.2.2) h)
  · intro z hz
    obtain ⟨hz, h⟩ := mem_filter.mp hz
    obtain ⟨h1,h2⟩ := mem_product.mp hz
    obtain ⟨h11,h12⟩ := mem_product.mp h1
    obtain ⟨h21,h22⟩ := mem_product.mp h2
    rcases z with ⟨⟨z11,z12⟩,⟨z21,z22⟩⟩
    obtain ⟨c,hc,rfl⟩ := mem_liftSupport.mp h11
    obtain ⟨a,ha,rfl⟩ := mem_liftSupport.mp h12
    obtain ⟨b,hb,rfl⟩ := mem_liftSupport.mp h21
    obtain ⟨d,hd,rfl⟩ := mem_liftSupport.mp h22
    let lhs : Fin 2 → ↥A := ![⟨a,ha⟩, ⟨b,hb⟩]
    let rhs : Fin 2 → ↥A := ![⟨c,hc⟩, ⟨d,hd⟩]
    refine ⟨(lhs,rhs), mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
    simp only [Fin.sum_univ_two, lhs, rhs, Matrix.cons_val_zero, Matrix.cons_val_one]
    dsimp only [evalDifference] at h
    linarith only [h]

/-- Count ordered equal-value pairs by fixing their first member. -/
theorem card_equal_fibers_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (g : α → β) :
    ((S ×ˢ S).filter (fun p => g p.1 = g p.2)).card =
      ∑ x ∈ S, (S.filter (fun y => g y = g x)).card := by
  let R := (S ×ˢ S).filter (fun p => g p.1 = g p.2)
  have hR : R.filter (fun p => p.1 ∈ S) = R :=
    filter_eq_self.mpr (fun _ hp => (mem_product.mp (mem_filter.mp hp).1).1)
  change R.card = _
  rw [← hR, ← sum_card_fiberwise_eq_card_filter R S Prod.fst]
  apply sum_congr rfl
  intro x hx
  let e : α ↪ α × α := ⟨fun y => (x,y), fun _ _ h => congrArg Prod.snd h⟩
  rw [← card_map (s := S.filter (fun y => g y = g x)) e]
  congr 1
  ext p
  rcases p with ⟨a,b⟩
  simp only [R, mem_filter, mem_product, mem_map]
  constructor
  · rintro ⟨⟨⟨_,hb⟩,h⟩,rfl⟩
    exact ⟨b,⟨hb,h.symm⟩,rfl⟩
  · rintro ⟨y,⟨hy,h⟩,he⟩
    change (x,y) = (a,b) at he
    cases he
    exact ⟨⟨⟨hx,hy⟩,h.symm⟩,rfl⟩

/-- The frozen collision count as a sum of ordered difference-fiber sizes. -/
theorem collision_card_eq_difference_sum (P : Polynomial ℤ) (A : Finset ℕ) :
    let wt := fun x : Fin 2 → ↥A => ∑ i, P.eval ((x i : ℕ) : ℤ)
    let B := liftSupport A
    ((univ : Finset ((Fin 2 → ↥A) × (Fin 2 → ↥A))).filter
      (fun z => wt z.1 = wt z.2)).card =
        ∑ z ∈ B ×ˢ B, ((B ×ˢ B).filter (fun w => evalDifference P w = evalDifference P z)).card := by
  exact (collision_card_eq_difference_pairs P A).trans
    (card_equal_fibers_sum (liftSupport A ×ˢ liftSupport A) (evalDifference P))

end GoldbachPolyCollision

namespace GoldbachPolyCollisionAggregation

open Finset GoldbachPolynomialDifference

/-- A bound on every nonzero fibre and a separate bound on the zero fibre. -/
theorem aggregate (P : Polynomial ℤ) (A : Finset ℤ) (hP : 0 < P.natDegree)
    (B : ℝ) (hB : 0 ≤ B)
    (hnonzero : ∀ x ∈ A ×ˢ A, P.eval x.2 - P.eval x.1 ≠ 0 →
      ((differencePairs P A (P.eval x.2 - P.eval x.1)).card : ℝ) ≤ B) :
    (∑ x ∈ A ×ˢ A, ((differencePairs P A (P.eval x.2 - P.eval x.1)).card : ℝ)) ≤
      ((P.natDegree : ℝ)^2 + B) * (A.card : ℝ)^2 := by
  let S := A ×ˢ A
  let f (x : ℤ × ℤ) := P.eval x.2 - P.eval x.1
  let g (x : ℤ × ℤ) := ((differencePairs P A (f x)).card : ℝ)
  let Z := S.filter (fun x => f x = 0)
  let U := S.filter (fun x => f x ≠ 0)
  have hZ : Z = differencePairs P A 0 := rfl
  have hC : (Z.card : ℝ) ≤ (P.natDegree : ℝ) * (A.card : ℝ) := by
    rw [hZ, ← Nat.cast_mul]
    exact_mod_cast (show _ ≤ P.natDegree * A.card by
      simpa only [mul_comm] using differencePairs_zero_le P A hP)
  have hzero : (∑ x ∈ Z, g x) = (Z.card : ℝ)^2 := by
    calc
      _ = ∑ _x ∈ Z, (Z.card : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        dsimp only [g]
        rw [(Finset.mem_filter.mp hx).2, hZ]
      _ = _ := by simp [nsmul_eq_mul, pow_two]
  have hU : (U.card : ℝ) ≤ (A.card : ℝ)^2 := by
    rw [pow_two, ← Nat.cast_mul, ← Finset.card_product]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ S)
  have hup : (∑ x ∈ U, g x) ≤ (U.card : ℝ) * B := calc
    _ ≤ ∑ _x ∈ U, B := Finset.sum_le_sum (fun x hx =>
      hnonzero x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2)
    _ = _ := by simp [nsmul_eq_mul]
  change (∑ x ∈ S, g x) ≤ _
  calc
    _ = (∑ x ∈ Z, g x) + (∑ x ∈ U, g x) :=
      (Finset.sum_filter_add_sum_filter_not S (fun x => f x = 0) g).symm
    _ ≤ (Z.card : ℝ)^2 + (U.card : ℝ) * B := add_le_add hzero.le hup
    _ ≤ ((P.natDegree : ℝ) * (A.card : ℝ))^2 + (A.card : ℝ)^2 * B :=
      (add_le_add (pow_le_pow_left₀ (Nat.cast_nonneg _) hC 2) (mul_le_mul_of_nonneg_right hU hB))
    _ = _ := by ring

end GoldbachPolyCollisionAggregation

open Finset GoldbachPolynomialDifference GoldbachPolynomialMagnitude GoldbachPolyCollision

theorem Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b : (∀ (x1 : Polynomial ℤ),   (2 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : (Fin (2 : ℕ) → ↥x8) → ℤ := fun (x10 : Fin (2 : ℕ) → ↥x8) => ∑ x11 : Fin (2 : ℕ), Polynomial.eval (↑↑(x10 x11)) x1;                   have x11 : Finset ((Fin (2 : ℕ) → ↥x8) × (Fin (2 : ℕ) → ↥x8)) := Finset.univ;                   ↑{x12 ∈ x11 | x10 x12.1 = x10 x12.2}.card ≤ x5 * ↑x6 ^ x3 * ↑x8.card ^ (2 : ℕ)) := by
  intro P hdegree ε hε
  have hP : 0 < P.natDegree := by omega
  let D : ℝ := P.natDegree
  have hD : 0 < D := by
    dsimp only [D]
    exact_mod_cast hP
  let δ : ℝ := ε / D
  have hδ : 0 < δ := div_pos hε hD
  obtain ⟨C, hC, hdiv⟩ := GoldbachPolynomialDivisors.divisor_bound hδ
  let T := 2*D*C*(coefficientBound P)^δ
  have hK : 0 < coefficientBound P := coefficientBound_pos P
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨D^2+T, by positivity, ?_⟩
  intro M hM A hA
  have hM1 : 1 ≤ M := by omega
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hpow : 1 ≤ (M : ℝ)^ε := Real.one_le_rpow hMR hε.le
  let B := liftSupport A
  have hBcard : (B.card : ℝ) = A.card := by
    exact_mod_cast liftSupport_card A
  have hcount := collision_card_eq_difference_sum P A
  dsimp only at hcount ⊢
  rw [hcount]
  push_cast
  have H (z : ℤ × ℤ) (hz : z ∈ B ×ˢ B) (hu : P.eval z.2 - P.eval z.1 ≠ 0) :
      ((differencePairs P B (P.eval z.2 - P.eval z.1)).card : ℝ) ≤ T*(M : ℝ)^ε := by
    obtain ⟨z1,z2⟩ := z
    obtain ⟨hz1,hz2⟩ := Finset.mem_product.mp hz
    obtain ⟨c,hc,rfl⟩ := mem_liftSupport.mp hz1
    obtain ⟨a,ha,rfl⟩ := mem_liftSupport.mp hz2
    let u := P.eval (a : ℤ) - P.eval (c : ℤ)
    change u ≠ 0 at hu
    change ((differencePairs P B u).card : ℝ) ≤ T*(M : ℝ)^ε
    have hm : 0 < u.natAbs := Int.natAbs_pos.mpr hu
    have huMag : (u.natAbs : ℝ)^δ ≤ (coefficientBound P)^δ * (M : ℝ)^ε :=
      rpow_natAbs_eval_sub_le P hP ε hε M a c hM1
        (mem_Icc.mp (hA ha)).2 (mem_Icc.mp (hA hc)).2
    calc
      _ ≤ 2*D*(u.natAbs.divisors.card : ℝ) := by
        dsimp only [D]
        exact_mod_cast differencePairs_card_le P B u hdegree hu
      _ ≤ 2*D*(C*(u.natAbs : ℝ)^δ) := by gcongr; exact hdiv _ hm
      _ ≤ 2*D*(C*((coefficientBound P)^δ*(M : ℝ)^ε)) := by gcongr
      _ = _ := by dsimp [T]; ring
  have hagg := GoldbachPolyCollisionAggregation.aggregate P B hP
    (T*(M : ℝ)^ε) (by positivity) H
  change (∑ z ∈ B ×ˢ B, ((differencePairs P B (P.eval z.2 - P.eval z.1)).card : ℝ)) ≤ _
  have hscaled : D^2 ≤ D^2*(M : ℝ)^ε := le_mul_of_one_le_right (sq_nonneg D) hpow
  calc
    _ ≤ (D^2 + T*(M : ℝ)^ε) * (B.card : ℝ)^2 := hagg
    _ ≤ (D^2*(M : ℝ)^ε + T*(M : ℝ)^ε) * (B.card : ℝ)^2 :=
      mul_le_mul_of_nonneg_right (add_le_add_left hscaled _) (sq_nonneg _)
    _ = _ := by rw [hBcard]; ring



namespace MatchFour
private theorem perm_two {i j : Fin 4} (h : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = i ∧ σ 1 = j := by
  classical
  let s := Equiv.swap (0 : Fin 4) i
  have h0 : s 0 = i := Equiv.swap_apply_left _ _
  have h1 : s 1 ≠ i := by
    rw [← h0]
    exact fun e => (by decide : (1 : Fin 4) ≠ 0) (s.injective e)
  refine ⟨s.trans (Equiv.swap (s 1) j), ?_, ?_⟩
  · change Equiv.swap (s 1) j (s 0) = i
    rw [h0, Equiv.swap_apply_of_ne_of_ne h1.symm h]
  · exact Equiv.swap_apply_left _ _

end MatchFour
namespace MatchFour
open Finset
abbrev V := Fin 4 → ℕ
abbrev Quad := (ℕ × ℕ) × (ℕ × ℕ)
abbrev Key := Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)
def raw {A : Finset ℕ} (z : (Fin 2 → ↥A) × (Fin 2 → ↥A)) : Quad :=
  ((z.1 0,z.1 1),(z.2 0,z.2 1))
def pack (k : Key) (z : V × V) : Quad × Quad :=
  (((z.1 (k.1 0),z.1 (k.1 1)),(z.2 (k.2 0),z.2 (k.2 1))),
   ((z.1 (k.1 2),z.1 (k.1 3)),(z.2 (k.2 2),z.2 (k.2 3))))
theorem pack_inj (k : Key) : Function.Injective (pack k) := by
  intro z w h
  apply Prod.ext <;> funext i
  · obtain ⟨i,rfl⟩ := k.1.surjective i
    fin_cases i <;> first | exact congrArg (fun p : Quad × Quad => p.1.1.1) h | exact congrArg (fun p : Quad × Quad => p.1.1.2) h | exact congrArg (fun p : Quad × Quad => p.2.1.1) h | exact congrArg (fun p : Quad × Quad => p.2.1.2) h
  · obtain ⟨i,rfl⟩ := k.2.surjective i
    fin_cases i <;> first | exact congrArg (fun p : Quad × Quad => p.1.2.1) h | exact congrArg (fun p : Quad × Quad => p.1.2.2) h | exact congrArg (fun p : Quad × Quad => p.2.2.1) h | exact congrArg (fun p : Quad × Quad => p.2.2.2) h
def E (P : Polynomial ℤ) (A : Finset ℕ) := (univ : Finset ((Fin 2 → ↥A) × (Fin 2 → ↥A))).filter
  fun z => ∑ i, P.eval ((z.1 i : ℕ):ℤ) = ∑ i, P.eval ((z.2 i : ℕ):ℤ)
theorem raw_mem {P : Polynomial ℤ} {A : Finset ℕ} {a b c d : ℕ}
    (ha : a∈A) (hb : b∈A) (hc : c∈A) (hd : d∈A)
    (he : P.eval (a:ℤ)+P.eval (b:ℤ)=P.eval (c:ℤ)+P.eval (d:ℤ)) :
    ((a,b),(c,d)) ∈ (E P A).image raw := by
  let z : (Fin 2 → ↥A) × (Fin 2 → ↥A) := (![⟨a,ha⟩,⟨b,hb⟩],![⟨c,hc⟩,⟨d,hd⟩])
  refine mem_image.mpr ⟨z,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
  simpa [z,Fin.sum_univ_two] using he

theorem count (P : Polynomial ℤ) (A : Finset ℕ) (G : Finset (V × V))
    (hG : ∀ z ∈ G, (∀ i, z.1 i ∈ A) ∧ (∀ i, z.2 i ∈ A) ∧
      (∑ i, P.eval (z.1 i : ℤ)) = (∑ i, P.eval (z.2 i : ℤ)) ∧
      ∃ i j l m, i ≠ j ∧ l ≠ m ∧
        P.eval (z.1 i : ℤ)+P.eval (z.1 j : ℤ)=P.eval (z.2 l : ℤ)+P.eval (z.2 m : ℤ)) :
    G.card ≤ Fintype.card Key * (E P A).card^2 := by
  classical
  let Q := (E P A).image raw
  let F (k : Key) := G.filter fun z => pack k z ∈ Q ×ˢ Q
  have cover : G ⊆ univ.biUnion F := by
    intro z hz
    obtain ⟨hl,hr,ht,i,j,l,m,hij,hlm,he⟩ := hG z hz
    obtain ⟨s,hs0,hs1⟩ := perm_two hij
    obtain ⟨t,ht0,ht1⟩ := perm_two hlm
    refine mem_biUnion.mpr ⟨(s,t),mem_univ _,mem_filter.mpr ⟨hz,mem_product.mpr ⟨?_,?_⟩⟩⟩
    · apply raw_mem (hl _) (hl _) (hr _) (hr _)
      simpa [hs0,hs1,ht0,ht1] using he
    · apply raw_mem (hl _) (hl _) (hr _) (hr _)
      have hh := (Equiv.sum_comp s (fun u => P.eval (z.1 u : ℤ))).trans
        (ht.trans (Equiv.sum_comp t (fun u => P.eval (z.2 u : ℤ))).symm)
      simp only [Fin.sum_univ_four,hs0,hs1,ht0,ht1] at hh
      linarith
  have hf (k : Key) : (F k).card ≤ (E P A).card^2 := by
    have hsub : (F k).image (pack k) ⊆ Q ×ˢ Q := by
      intro p hp
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hp
      exact (mem_filter.mp hz).2
    rw [← card_image_of_injective _ (pack_inj k)]
    exact (card_le_card hsub).trans (by rw [card_product,pow_two]; exact Nat.mul_le_mul card_image_le card_image_le)
  calc
    G.card ≤ _ := (card_le_card cover).trans card_biUnion_le
    _ ≤ ∑ _ ∈ (univ : Finset Key), (E P A).card^2 := sum_le_sum fun k _ => hf k
    _ = _ := by simp
end MatchFour

theorem Conjectures.Cuts.Task7f8e9af21a4b2d0d31b4f289 : ∀ (x1 : Polynomial ℤ),   (4 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x10 : Fin (4 : ℕ)) => x8;                   let x11 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (4 : ℕ) → ℕ) => ∑ x12 : Fin (4 : ℕ), Polynomial.eval (↑(x11 x12) : ℤ) x1;                   have x12 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Fin (4 : ℕ) × Fin (4 : ℕ)), x12.1 x13.1 ≠ x12.2 x13.2};                   have x13 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x13 ∈ x12 | ∀ (x14 x15 : Fin (4 : ℕ) × Fin (4 : ℕ)), x14.1 ≠ x14.2 → x15.1 ≠ x15.2 → x13.1 x14.1 + x13.1 x14.2 ≠ x13.2 x15.1 + x13.2 x15.2 ∧ x13.1 x14.1 ^ (2 : ℕ) + x13.1 x14.2 ^ (2 : ℕ) ≠ x13.2 x15.1 ^ (2 : ℕ) + x13.2 x15.2 ^ (2 : ℕ)};                   have x14 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x14 ∈ x13 | (6 : ℕ) ≤ (Finset.image x14.1 Finset.univ ∪ Finset.image x14.2 Finset.univ).card};                   (↑{x15 ∈ x14 | ∃ (x16 : Fin (4 : ℕ) × Fin (4 : ℕ)) (x17 : Fin (4 : ℕ) × Fin (4 : ℕ)), x16.1 ≠ x16.2 ∧ x17.1 ≠ x17.2 ∧ Polynomial.eval (↑(x15.1 x16.1) : ℤ) x1 + Polynomial.eval (↑(x15.1 x16.2) : ℤ) x1 = Polynomial.eval (↑(x15.2 x17.1) : ℤ) x1 + Polynomial.eval (↑(x15.2 x17.2) : ℤ) x1}.card : ℝ) ≤ x5 * (↑x6 : ℝ) ^ x3 * (↑x8.card : ℝ) ^ (4 : ℕ)
:= by
  classical
  intro P hd ε hε
  obtain ⟨C,hC,hE⟩ := Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b P (by omega) (ε/2) (by positivity)
  let K := Fintype.card MatchFour.Key
  refine ⟨((K:ℝ)+1)*C^2,by positivity,?_⟩
  intro M hM A hA T val G H B
  let S := B.filter fun z => ∃ (i j : Fin 4 × Fin 4), i.1 ≠ i.2 ∧ j.1 ≠ j.2 ∧
    P.eval (z.1 i.1 : ℤ) + P.eval (z.1 i.2 : ℤ) = P.eval (z.2 j.1 : ℤ) + P.eval (z.2 j.2 : ℤ)
  have hs := MatchFour.count P A S (by
    intro z hz
    obtain ⟨hB,⟨i,j⟩,⟨l,m⟩,h1,h2,h3⟩ := Finset.mem_filter.mp hz
    obtain ⟨hH,-⟩ := Finset.mem_filter.mp hB
    obtain ⟨hG,-⟩ := Finset.mem_filter.mp hH
    obtain ⟨hT,ht,-⟩ := Finset.mem_filter.mp hG
    obtain ⟨hl,hr⟩ := Finset.mem_product.mp hT
    exact ⟨Fintype.mem_piFinset.mp hl,Fintype.mem_piFinset.mp hr,ht,i,j,l,m,h1,h2,h3⟩)
  have hb : ((MatchFour.E P A).card : ℝ) ≤ C*(M:ℝ)^(ε/2)*(A.card:ℝ)^2 := hE M hM A hA
  have hpow : ((M:ℝ)^(ε/2))^2 = (M:ℝ)^ε := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    congr 1
    push_cast
    ring
  change (S.card:ℝ) ≤ _
  calc
    (S.card:ℝ) ≤ (K:ℝ) * ((MatchFour.E P A).card:ℝ)^2 := by exact_mod_cast hs
    _ ≤ ((K:ℝ)+1)*(C*(M:ℝ)^(ε/2)*(A.card:ℝ)^2)^2 :=
      mul_le_mul (by linarith) (pow_le_pow_left₀ (by positivity) hb 2) (by positivity) (by positivity)
    _ = _ := by rw [mul_pow,mul_pow,hpow]; ring
