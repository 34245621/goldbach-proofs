import Mathlib

open scoped BigOperators

namespace Conjectures.Goldbach

set_option maxHeartbeats 4000000 in
theorem FiniteResidueRough2310 :
    ∀ a : ℕ, a < 2310 → Even a → ∃ p ∈ ({3,5,7,11,29,61,79} : Finset ℕ), Nat.Coprime ((a+2310-p)%2310) 2310 := by
  intro a ha he
  obtain ⟨k, rfl⟩ := he
  have hk : k < 1155 := by omega
  interval_cases k <;> decide

end Conjectures.Goldbach
