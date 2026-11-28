import Mathlib

namespace Conjectures.Goldbach

open scoped BigOperators

theorem ResidueBlocksUnitSplit :
    ∀ (q X : ℕ) (w : ℕ → ℂ), (∑ k ∈ Finset.range X,w k)=(∑ k ∈ (Finset.range X).filter (fun k => Nat.Coprime k q),w k)+(∑ k ∈ (Finset.range X).filter (fun k => ¬ Nat.Coprime k q),w k) := by
  intro q X w
  exact (Finset.sum_filter_add_sum_filter_not (Finset.range X)
    (fun k => Nat.Coprime k q) w).symm

end Conjectures.Goldbach