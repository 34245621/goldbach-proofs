import Mathlib

/-- Cut of `L-goldbach-frontier-type2-b2-b2`.

Child 1: the full band `τ₂` and its large-prime core `core` have deep-arc integrals differing by `o(n)`.
Child 2: the same `o(n)` bound with `τ₂` replaced by `core`.
The registered statement follows from the two by the triangle inequality. -/
theorem Conjectures.Cuts.Cut4a77f788c167dd09c08186ca
    (h₁ : (let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Λ := ArithmeticFunction.vonMangoldt; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊; let B₂ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let τ₂ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₁ n < a ∧ a ≤ B₂ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let core := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₁ n < a ∧ a ≤ B₂ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * (if Nat.sqrt n < m / a then (if Nat.Prime (m / a) then Real.log ((m / a : ℕ) : ℝ) else 0) else 0); let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖Jdeep n (τ₂ n) (τ₂ n) - Jdeep n (core n) (core n)‖ ≤ e * (n : ℝ)))
    (h₂ : (let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Λ := ArithmeticFunction.vonMangoldt; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊; let B₂ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let τ₂ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₁ n < a ∧ a ≤ B₂ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let core := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₁ n < a ∧ a ≤ B₂ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * (if Nat.sqrt n < m / a then (if Nat.Prime (m / a) then Real.log ((m / a : ℕ) : ℝ) else 0) else 0); let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖Jdeep n (core n) (core n)‖ ≤ e * (n : ℝ)))
    : (let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Λ := ArithmeticFunction.vonMangoldt; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊; let B₂ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let τ₂ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₁ n < a ∧ a ≤ B₂ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖Jdeep n (τ₂ n) (τ₂ n)‖ ≤ e * (n : ℝ))  := by
  intro E S Q Q₁ H wideArcs Λ μ U B₁ B₂ τ₂ Jdeep
  let core : ℕ → ℕ → ℝ := fun (n m : ℕ) =>
    ∑ a ∈ (Nat.divisors m).filter (fun a => B₁ n < a ∧ a ≤ B₂ n ∧ U n < m / a),
      (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) *
        (if Nat.sqrt n < m / a then (if Nat.Prime (m / a) then Real.log ((m / a : ℕ) : ℝ) else 0) else 0)
  intro e he
  obtain ⟨Np, hNp⟩ := h₁ (e/2) (by positivity)
  obtain ⟨Nc, hNc⟩ := h₂ (e/2) (by positivity)
  refine ⟨max Np Nc, fun n hn hev => ?_⟩
  have hp := hNp n (le_trans (le_max_left Np Nc) hn) hev
  have hc := hNc n (le_trans (le_max_right Np Nc) hn) hev
  calc ‖Jdeep n (τ₂ n) (τ₂ n)‖
      = ‖(Jdeep n (τ₂ n) (τ₂ n) - Jdeep n (core n) (core n)) + Jdeep n (core n) (core n)‖ := by
          rw [sub_add_cancel]
    _ ≤ ‖Jdeep n (τ₂ n) (τ₂ n) - Jdeep n (core n) (core n)‖ + ‖Jdeep n (core n) (core n)‖ :=
          norm_add_le _ _
    _ ≤ e/2 * (n:ℝ) + e/2 * (n:ℝ) := add_le_add hp hc
    _ = e * (n:ℝ) := by ring
