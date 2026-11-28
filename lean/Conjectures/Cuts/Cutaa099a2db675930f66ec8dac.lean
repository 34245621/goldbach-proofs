import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factors

-- child 1 zh: 四个仿射因子的局部可容许性等价于偶性和移位除以三所得的四种显式条件。
-- child 1 en: Characterize the four affine local factors by parity and the four explicit mod-3 cases, for every integer target and both shifts.
-- child 2 zh: 仅在模三条件给出的目标剩余类上证明陈氏素数对的统一异常集估计。
-- child 2 en: Bound the exceptional shifted Chen pairs uniformly on precisely the target residue classes left by the mod-3 classification.

theorem Conjectures.Cuts.Cutaa099a2db675930f66ec8dac
  (hLocal : ∀ n h k : ℤ, (∀ l : ℕ, l.Prime → ∃ a : ℤ, ¬(l:ℤ) ∣ a*(a+h)*(n-a)*(n-a+k)) ↔
    Even n ∧ Even h ∧ Even k ∧ ((3 ∣ h ∧ 3 ∣ k) ∨ (3 ∣ h ∧ ¬3 ∣ k ∧ ¬3 ∣ (n-k)) ∨
      (¬3 ∣ h ∧ 3 ∣ k ∧ ¬3 ∣ (n-h)) ∨ (¬3 ∣ h ∧ ¬3 ∣ k ∧ 3 ∣ (n-h-k))))
  (hMain : let ok := fun (n : ℕ) (h k : ℤ) => (3 ∣ h ∧ 3 ∣ k) ∨
    (3 ∣ h ∧ ¬3 ∣ k ∧ ¬3 ∣ ((n:ℤ)-k)) ∨ (¬3 ∣ h ∧ 3 ∣ k ∧ ¬3 ∣ ((n:ℤ)-h)) ∨
    (¬3 ∣ h ∧ ¬3 ∣ k ∧ 3 ∣ ((n:ℤ)-h-k)); let reps := fun (n : ℕ) (h k : ℤ) => (Finset.range (n+1)).filter fun p =>
    p.Prime ∧ (n-p).Prime ∧ 1 < (p:ℤ)+h ∧ 1 < ((n-p:ℕ):ℤ)+k ∧
    ((p:ℤ)+h).toNat.primeFactorsList.length ≤ 2 ∧
    (((n-p:ℕ):ℤ)+k).toNat.primeFactorsList.length ≤ 2; ∀ H : ℕ, ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ h k : ℤ, h ≠ 0 → k ≠ 0 → Even h → Even k → (h.natAbs : ℝ) ≤ (Real.log (X : ℝ))^H → (k.natAbs : ℝ) ≤ (Real.log (X : ℝ))^H → let bad := fun n : ℕ => Even n ∧ ok n h k ∧ (reps n h k).card = 0; (((Finset.Icc 4 X).filter bad).card : ℝ) ≤ (X : ℝ)^(1-δ)) : (let ok := fun (n : ℕ) (h k : ℤ) => ∀ l : ℕ, Nat.Prime l → ∃ a : ℤ, ¬ (l : ℤ) ∣ a*(a+h)*((n : ℤ)-a)*((n : ℤ)-a+k); let good := fun (n : ℕ) (h k : ℤ) => ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n ∧ 1 < (p : ℤ)+h ∧ 1 < (q : ℤ)+k ∧ ((p : ℤ)+h).toNat.primeFactorsList.length ≤ 2 ∧ ((q : ℤ)+k).toNat.primeFactorsList.length ≤ 2; ∀ H : ℕ, ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ h k : ℤ, h ≠ 0 → k ≠ 0 → Even h → Even k → (h.natAbs : ℝ) ≤ (Real.log (X : ℝ))^H → (k.natAbs : ℝ) ≤ (Real.log (X : ℝ))^H → let bad := fun n : ℕ => Even n ∧ ok n h k ∧ ¬good n h k; ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Icc 4 X)).card : ℝ) ≤ (X : ℝ)^(1-δ)) := by
  classical
  intro ok good H
  obtain ⟨δ,hδ,hδ',X₀,hmain⟩ := hMain H
  refine ⟨δ,hδ,hδ',X₀,?_⟩
  intro X hX h k hh hk heh hek hhb hkb
  apply le_trans _ (hmain X hX h k hh hk heh hek hhb hkb)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  refine ⟨hn.1,hn.2.1,((hLocal (n:ℤ) h k).mp hn.2.2.1).2.2.2,?_⟩
  rw [Finset.card_eq_zero,Finset.eq_empty_iff_forall_notMem]
  intro p hp
  obtain ⟨pR,pP,pQ,ph,qk,phf,qkf⟩ := Finset.mem_filter.mp hp
  have hpn : p≤n := by simpa using Finset.mem_range.mp pR
  exact hn.2.2.2 ⟨p,n-p,pP,pQ,by omega,ph,qk,phf,qkf⟩
