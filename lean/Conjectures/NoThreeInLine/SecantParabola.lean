import Mathlib

namespace Conjectures.NoThreeInLine

open scoped BigOperators

theorem SecantParabola :
    let d := fun (a b c : ℤ × ℤ) => (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1); let ok := fun (S : Finset (ℤ × ℤ)) => ∀ a∈S, ∀ b∈S, ∀ c∈S, a≠b → b≠c → a≠c → d a b c≠0; ∀ a b t : ℤ, d (a,a^2) (b,b^2) (t,t^2)=(b-a)*(t-a)*(t-b) := by
  dsimp only
  intro a b t
  ring

end Conjectures.NoThreeInLine