import Mathlib

theorem Conjectures.Goldbach.ResidueBlocksSumPartition :
    ∀ (q X : ℕ) (w : ℕ → ℂ), 0<q → (∑ a ∈ Finset.range q, ∑ k ∈ (Finset.range X).filter (fun k => k % q = a), w k)=∑ k ∈ Finset.range X,w k := by
  intro q X w hq
  exact Finset.sum_fiberwise_of_maps_to (s := Finset.range X) (t := Finset.range q)
    (g := fun k => k % q) (fun k _ => Finset.mem_range.mpr (Nat.mod_lt k hq)) w
