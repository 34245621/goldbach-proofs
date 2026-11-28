import Mathlib.Data.Nat.Totient
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

namespace LargeModulusAP

private theorem prod_bound (s : Finset ℕ) (hs : ∀ p ∈ s, 2 ≤ p) :
    (∏ p ∈ s, p) ≤ (s.card+1) * ∏ p ∈ s, (p-1) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hmax ih =>
    have ha : 2 ≤ a := hs _ (Finset.mem_insert_self ..)
    have hs' : ∀ p ∈ s, 2 ≤ p := fun p hp => hs _ (Finset.mem_insert_of_mem hp)
    have hnot : a ∉ s := fun h => (lt_irrefl a) (hmax _ h)
    have hsubset : s ⊆ Finset.Ico 2 a := fun p hp => Finset.mem_Ico.mpr ⟨hs' _ hp,hmax _ hp⟩
    have hcard := Finset.card_le_card hsubset
    rw [Nat.card_Ico] at hcard
    rw [Finset.prod_insert hnot, Finset.prod_insert hnot, Finset.card_insert_of_notMem hnot]
    have hprod := Nat.mul_le_mul_left a (ih hs')
    refine hprod.trans ?_
    rw [← Nat.mul_assoc, ← Nat.mul_assoc]
    apply Nat.mul_le_mul_right
    have ha' : a = a-1+1 := by omega
    have hnew : s.card+1 ≤ a-1 := by omega
    nlinarith only [hnew, show a*(s.card+1) = (a-1)*(s.card+1)+(s.card+1) by
      conv_lhs => lhs; rw [ha']
      ring]

theorem totient_lower (q : ℕ) (hq : 0 < q) :
    (q:ℝ) ≤ (q.totient:ℝ)*(1+(3/2)*Real.log q) := by
  let S := q.primeFactors
  have hprime (p) (hp : p ∈ S) := Nat.prime_of_mem_primeFactors hp
  have hprod := prod_bound S (fun p hp => (hprime p hp).two_le)
  have hn : q ≤ q.totient*(S.card+1) := by
    have hpos : 0 < ∏ p ∈ S, (p-1) := Finset.prod_pos (fun p hp => by have := (hprime p hp).two_le; omega)
    apply (Nat.mul_le_mul_right_iff hpos).mp
    rw [Nat.mul_assoc, ← Nat.totient_mul_prod_primeFactors]
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left q.totient hprod
  have hp2 : 2^S.card ≤ q := calc
    2^S.card = ∏ _p ∈ S, 2 := by simp
    _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod (fun p hp => (hprime p hp).two_le)
    _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have hp2' : (2:ℝ)^S.card ≤ q := by exact_mod_cast hp2
  have hlog := Real.log_le_log (by positivity) hp2'
  rw [Real.log_pow] at hlog
  have hcard : (S.card:ℝ) ≤ (3/2)*Real.log q := by
    nlinarith [Real.log_two_gt_d9,
      mul_nonneg (Nat.cast_nonneg S.card (α:=ℝ))
        (show 0 ≤ Real.log 2 - 2/3 by linarith [Real.log_two_gt_d9])]
  have hreal : (q:ℝ) ≤ (q.totient:ℝ)*((S.card:ℝ)+1) := by exact_mod_cast hn
  exact hreal.trans (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _))

end LargeModulusAP

namespace LargeModulusAP
open ArithmeticFunction

theorem large_modulus (x : ℝ) (d a : ℕ) (hx : 100 ≤ x) (hd : Real.sqrt x ≤ d) :
    |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => Nat.ModEq d n a), vonMangoldt n) -
      x / (Nat.totient d : ℝ)| ≤ Real.sqrt x *
        ((Real.log x)^2/(8*Real.pi) + Real.log (d:ℝ)*Real.log x/(2*Real.pi) +
          (3/4)*Real.log x + (1/2)*Real.log (d:ℝ)) := by
  classical
  let y := Real.sqrt x
  have hx0 : 0 < x := by linarith
  have hy : 0 < y := Real.sqrt_pos.mpr hx0
  have hy2 : y^2 = x := Real.sq_sqrt hx0.le
  have hy10 : 10 ≤ y := by nlinarith [sq_nonneg (y-10)]
  have hd0 : 0 < (d:ℝ) := hy.trans_le hd
  have hdN : 0 < d := by exact_mod_cast hd0
  have ly : 2 ≤ Real.log y := by
    have hb : (2:ℝ)^3 ≤ y := by norm_num; linarith
    have h := Real.log_le_log (by norm_num) hb
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith [Real.log_two_gt_d9]
  have hL : 2*Real.log y = Real.log x := by rw [← hy2, Real.log_pow]; norm_num
  have hlogd := Real.log_le_log hy hd
  have bound_main : x/(d.totient:ℝ) ≤ y*(1+3/4*Real.log x) := by
    let r := (d:ℝ)/y
    have hr : 1 ≤ r := (one_le_div hy).mpr hd
    have hr' : 0 < r := by linarith
    have hrid : (d:ℝ) = r*y := (div_mul_cancel₀ _ hy.ne').symm
    have hlogr : Real.log (d:ℝ) = Real.log r + Real.log y := by
      conv_lhs => rw [hrid, Real.log_mul hr'.ne' hy.ne']
    have hscale : 1+(3/2)*Real.log (d:ℝ) ≤ r*(1+(3/2)*Real.log y) := by
      have hm := mul_le_mul_of_nonneg_left (show (3:ℝ)/2 ≤ 1+(3/2)*Real.log y by linarith) (sub_nonneg.mpr hr)
      calc
        1+(3/2)*Real.log (d:ℝ) ≤ 1+(3/2)*(r-1)+(3/2)*Real.log y := by
          linarith only [hlogr,Real.log_le_sub_one_of_pos hr']
        _ ≤ _ := by nlinarith only [hm]
    have htot := totient_lower d hdN
    have ht0 : 0 < (d.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hdN
    have h := htot.trans (mul_le_mul_of_nonneg_left hscale ht0.le)
    rw [hrid] at h
    have hcancel : y ≤ (d.totient:ℝ)*(1+(3/2)*Real.log y) := by
      apply (mul_le_mul_iff_right₀ hr').mp
      nlinarith only [h]
    rw [div_le_iff₀ ht0]
    calc
      x = y*y := by nlinarith only [hy2]
      _ ≤ y*((d.totient:ℝ)*(1+(3/2)*Real.log y)) := mul_le_mul_of_nonneg_left hcancel hy.le
      _ = _ := by rw [← hL]; ring
  let S := (Finset.Icc 1 ⌊x⌋₊).filter fun n => Nat.ModEq d n a
  have hsCard : (S.card:ℝ) ≤ y+2 := by
    let N := ⌊x⌋₊+1
    have hsub : S ⊆ (Finset.range N).filter (fun n => Nat.ModEq d n a) := by
      intro n hn
      obtain ⟨hn',hcon⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn').2),hcon⟩
    have hc := Finset.card_le_card hsub
    rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card N hdN a] at hc
    have hc' : S.card ≤ N/d+1 := hc.trans (by split_ifs <;> omega)
    have hf : (N:ℝ) ≤ x+1 := by
      dsimp [N]; push_cast; linarith [Nat.floor_le hx0.le]
    have hNd : ((N/d:ℕ):ℝ) ≤ (x+1)/(d:ℝ) := (by exact_mod_cast (Nat.div_mul_le_self N d) :
      ((N/d:ℕ):ℝ)*(d:ℝ) ≤ N) |> fun h => (le_div_iff₀ hd0).mpr (h.trans hf)
    have hcast : (S.card:ℝ) ≤ ((N/d:ℕ):ℝ)+1 := by exact_mod_cast hc'
    have hydiv : (x+1)/(d:ℝ) ≤ y+1 := by
      rw [div_le_iff₀ hd0]
      nlinarith [mul_nonneg (sub_nonneg.mpr hd) (by linarith : 0 ≤ y+1)]
    linarith only [hcast,hNd,hydiv]
  have sum_nonneg : 0 ≤ ∑ n ∈ S, vonMangoldt n := Finset.sum_nonneg (fun _ _ => vonMangoldt_nonneg)
  have sum_le : ∑ n ∈ S, vonMangoldt n ≤ (y+2)*Real.log x := by
    calc
      _ ≤ ∑ _n ∈ S, Real.log x := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hn1,hn2⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
        exact vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast hn1) ((by exact_mod_cast hn2 : (n:ℝ) ≤ ⌊x⌋₊).trans (Nat.floor_le hx0.le)))
      _ = (S.card:ℝ)*Real.log x := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hsCard (Real.log_nonneg (by linarith))
  let B := (Real.log x)^2/(8*Real.pi) + Real.log (d:ℝ)*Real.log x/(2*Real.pi) +
      (3/4)*Real.log x + (1/2)*Real.log (d:ℝ)
  have hpi : Real.pi ≤ 4 := Real.pi_lt_four.le
  have L : 4 ≤ Real.log x := by linarith
  have sqlog : (Real.log x)^2/32 ≤ (Real.log x)^2/(8*Real.pi) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
  have cross : (Real.log x)^2/16 ≤ Real.log (d:ℝ)*Real.log x/(2*Real.pi) := calc
    _ ≤ Real.log (d:ℝ)*Real.log x/8 := by nlinarith [mul_nonneg (show 0 ≤ Real.log (d:ℝ)-Real.log x/2 by linarith) (by linarith : 0 ≤ Real.log x)]
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have Bmain : 1+3/4*Real.log x ≤ B := by dsimp [B]; nlinarith [sq_nonneg (Real.log x)]
  have Bsum : 6/5*Real.log x ≤ B := by
    dsimp [B]
    nlinarith [mul_nonneg (show 0 ≤ Real.log x-4 by linarith) (show 0 ≤ Real.log x by linarith)]
  change |(∑ n ∈ S, vonMangoldt n)- x/(d.totient:ℝ)| ≤ y*B
  rw [abs_le]
  constructor
  · linarith only [sum_nonneg,bound_main,mul_le_mul_of_nonneg_left Bmain hy.le]
  · have hlarge : (y+2)*Real.log x ≤ y*(6/5*Real.log x) := by
      nlinarith [mul_nonneg (show 0 ≤ y-10 by linarith) (show 0 ≤ Real.log x by linarith)]
    linarith only [sum_le,hlarge,mul_le_mul_of_nonneg_left Bsum hy.le,
      div_nonneg hx0.le (Nat.cast_nonneg d.totient (α:=ℝ))]
end LargeModulusAP

theorem Conjectures.Cuts.Task2cd45dcb6a324c35c44bc6fc : (∀ (x : ℝ) (d a : ℕ), 100 ≤ x → Real.sqrt x ≤ (d:ℝ) → |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => Nat.ModEq d n a), ArithmeticFunction.vonMangoldt n) - x / (Nat.totient d : ℝ)| ≤ Real.sqrt x * ((Real.log x) ^ 2 / (8 * Real.pi) + Real.log (d : ℝ) * Real.log x / (2 * Real.pi) + (3 / 4 : ℝ) * Real.log x + (1 / 2 : ℝ) * Real.log (d : ℝ))) := LargeModulusAP.large_modulus
