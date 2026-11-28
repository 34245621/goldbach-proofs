import Mathlib

theorem Conjectures.HashCollisionLab.QuadraticAdaptiveCost :
    ∀ (p : ℕ) [Fact (Nat.Prime p)] (a b c x y : ZMod p), let result := if x = y then ((x + 1, y - 1), (2 : ℕ)) else ((y, x), 0); result.1 ≠ (x, y) ∧ a * (result.1.1 + result.1.2) ^ 2 + b * (result.1.1 + result.1.2) + c = a * (x + y) ^ 2 + b * (x + y) + c ∧ result.2 ≤ 2 ∧ (result.2 = 0 ↔ x ≠ y) := by
  intro p hp a b c x y
  by_cases hxy : x = y
  · simp only [if_pos hxy]
    refine ⟨?_, ?_, Nat.le_refl _, by simp [hxy]⟩
    · intro h
      have hx : x + 1 = x := congrArg Prod.fst h
      have hzero : (1 : ZMod p) = 0 := calc
        _ = (x + 1) - x := by ring
        _ = 0 := by rw [hx, sub_self]
      exact one_ne_zero hzero
    · ring
  · simp only [if_neg hxy]
    refine ⟨?_, ?_, Nat.zero_le _, by simp [hxy]⟩
    · intro h
      have hx : y = x := congrArg Prod.fst h
      exact hxy hx.symm
    · ring
