import Mathlib

/-!
Cut proposal for `L-goldbach-binary-shift-dyadic-band-mass`.

-- child 1 zh: 二进带 I=[k/4+1,k/2] 上的模型主项下界：对充分大的 k，主项
--   main(m) = (if 3 ∣ m then 4m/3 else m/2) 在整条带上的和不小于 (1/4)|I|2^k。
-- child 1 en: Main-term lower bound on the dyadic shift band: for all large k the sum
--   of the model main term main(m) = (if 3 ∣ m then 4m/3 else m/2) over the band is
--   at least (1/4)|I|·2^k.
-- child 2 zh: 模型主项与真实中心配对质量的负部误差界：误差和
--   ∑_e (R(2^k−2^e) − main(2^k−2^e)) 的负部不超过 (1/8)|I|2^k。
-- child 2 en: Negative-part error bound between the true central pair mass and the
--   model main term on the band: the negative part of
--   ∑_e (R(2^k−2^e) − main(2^k−2^e)) is at most (1/8)|I|·2^k.

The bridge theorem proves the frozen statement of the parent task from the two
independent closed premises.  The platform's `reduce` gate accepts exactly one
declaration in the file (matcher-generated helpers aside), so every definition used
by the bridge is written inline instead of as a top-level `def`. -/

namespace Conjectures.Cuts

open Finset

theorem Cut59ed39c2f88142be07213565
    (h₁ : ∀ᶠ k in Filter.atTop,
      (1 / 4 : ℝ) * ((Finset.Icc (k / 4 + 1) (k / 2)).card : ℝ) * (2 : ℝ) ^ k
        ≤ ∑ e ∈ Finset.Icc (k / 4 + 1) (k / 2),
            (if 3 ∣ (2 ^ k - 2 ^ e) then (4 : ℝ) * ((2 ^ k - 2 ^ e : ℕ) : ℝ) / 3
             else ((2 ^ k - 2 ^ e : ℕ) : ℝ) / 2))
    (h₂ : ∀ᶠ k in Filter.atTop,
      max 0 (-(∑ e ∈ Finset.Icc (k / 4 + 1) (k / 2),
          ((∑ p ∈ (Finset.range ((2 ^ k - 2 ^ e) + 1)).filter
                  (fun p => (2 ^ k - 2 ^ e) ≤ 3 * p ∧ 3 * p ≤ 2 * (2 ^ k - 2 ^ e)),
                (if Nat.Prime p then Real.log (p : ℝ) else 0)
                  * (if Nat.Prime ((2 ^ k - 2 ^ e) - p)
                      then Real.log (((2 ^ k - 2 ^ e) - p : ℕ) : ℝ) else 0))
            - (if 3 ∣ (2 ^ k - 2 ^ e) then (4 : ℝ) * ((2 ^ k - 2 ^ e : ℕ) : ℝ) / 3
               else ((2 ^ k - 2 ^ e : ℕ) : ℝ) / 2)))) ≤
        (1 / 8 : ℝ) * ((Finset.Icc (k / 4 + 1) (k / 2)).card : ℝ) * (2 : ℝ) ^ k) :
    (let w := fun p : ℕ => if Nat.Prime p then Real.log (p : ℝ) else 0
     let R := fun m : ℕ => ∑ p ∈ (Finset.range (m + 1)).filter (fun p => m ≤ 3 * p ∧ 3 * p ≤ 2 * m), w p * w (m - p)
     ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ k ≥ K,
       let I := Finset.Icc (k / 4 + 1) (k / 2)
       c * (I.card : ℝ) * ((2 : ℝ) ^ k) ≤ ∑ e ∈ I, R (2 ^ k - 2 ^ e)) := by
  classical
  dsimp only
  obtain ⟨K₁, hK₁⟩ := Filter.eventually_atTop.mp h₁
  obtain ⟨K₂, hK₂⟩ := Filter.eventually_atTop.mp h₂
  refine ⟨1 / 8, by norm_num, max 8 (max K₁ K₂), ?_⟩
  intro k hk
  have hkK : max K₁ K₂ ≤ k := le_trans (le_max_right _ _) hk
  have hk₁ : K₁ ≤ k := le_trans (le_max_left _ _) hkK
  have hk₂ : K₂ ≤ k := le_trans (le_max_right _ _) hkK
  have hm := hK₁ k hk₁
  have hb := hK₂ k hk₂
  have hneg : -(∑ e ∈ Finset.Icc (k / 4 + 1) (k / 2),
      ((∑ p ∈ (Finset.range ((2 ^ k - 2 ^ e) + 1)).filter
              (fun p => (2 ^ k - 2 ^ e) ≤ 3 * p ∧ 3 * p ≤ 2 * (2 ^ k - 2 ^ e)),
            (if Nat.Prime p then Real.log (p : ℝ) else 0)
              * (if Nat.Prime ((2 ^ k - 2 ^ e) - p)
                  then Real.log (((2 ^ k - 2 ^ e) - p : ℕ) : ℝ) else 0))
        - (if 3 ∣ (2 ^ k - 2 ^ e) then (4 : ℝ) * ((2 ^ k - 2 ^ e : ℕ) : ℝ) / 3
           else ((2 ^ k - 2 ^ e : ℕ) : ℝ) / 2)))
      ≤ (1 / 8 : ℝ) * ((Finset.Icc (k / 4 + 1) (k / 2)).card : ℝ) * (2 : ℝ) ^ k :=
    le_trans (le_max_right 0 _) hb
  have hid : (∑ e ∈ Finset.Icc (k / 4 + 1) (k / 2),
        (∑ p ∈ (Finset.range ((2 ^ k - 2 ^ e) + 1)).filter
              (fun p => (2 ^ k - 2 ^ e) ≤ 3 * p ∧ 3 * p ≤ 2 * (2 ^ k - 2 ^ e)),
            (if Nat.Prime p then Real.log (p : ℝ) else 0)
              * (if Nat.Prime ((2 ^ k - 2 ^ e) - p)
                  then Real.log (((2 ^ k - 2 ^ e) - p : ℕ) : ℝ) else 0)))
      = (∑ e ∈ Finset.Icc (k / 4 + 1) (k / 2),
            (if 3 ∣ (2 ^ k - 2 ^ e) then (4 : ℝ) * ((2 ^ k - 2 ^ e : ℕ) : ℝ) / 3
             else ((2 ^ k - 2 ^ e : ℕ) : ℝ) / 2))
        + ∑ e ∈ Finset.Icc (k / 4 + 1) (k / 2),
          ((∑ p ∈ (Finset.range ((2 ^ k - 2 ^ e) + 1)).filter
                (fun p => (2 ^ k - 2 ^ e) ≤ 3 * p ∧ 3 * p ≤ 2 * (2 ^ k - 2 ^ e)),
              (if Nat.Prime p then Real.log (p : ℝ) else 0)
                * (if Nat.Prime ((2 ^ k - 2 ^ e) - p)
                    then Real.log (((2 ^ k - 2 ^ e) - p : ℕ) : ℝ) else 0))
          - (if 3 ∣ (2 ^ k - 2 ^ e) then (4 : ℝ) * ((2 ^ k - 2 ^ e : ℕ) : ℝ) / 3
             else ((2 ^ k - 2 ^ e : ℕ) : ℝ) / 2)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  linarith

end Conjectures.Cuts
