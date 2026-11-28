import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Order.Interval.Finset.Nat

set_option maxRecDepth 5000 in
theorem Conjectures.Goldbach.FiniteWitnessTranslateThrough98 :
    let P : Finset ℕ := {2,3,5,7,19}; let Q := (Finset.range 100).filter Nat.Prime; ((Finset.Ico 4 100).filter Even) ⊆ P.biUnion (fun p => Q.image (fun q => p+q)) := by
  decide
